-- Prove2me | Definitions.Def_DynSort_ADST
-- name    : DynSort_ADST
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:22.509193+00:00
-- url     : https://prove2.me/theorems/5ffb0d14-037c-4d85-ad79-f9eb7646a717
-- title:
--   The Augmented Dynamic Sorting Tree, its updates and its runs
-- statement:
--   An **A-DST** of level $d$ consists of components $D_d,D_{d-1},\dots,D_2,A_1$ from left to right, where $D_j$ is a level-$j$ DST and $A_1$ a sorted array; no ordering is imposed between components. For an array of $n$ cells, $d=1+\lceil\log_2 n\rceil$, and the A-DST starts from $n$ virtual elements of value $0$, sorted into $D_d$ with all transfer sections empty.
--
--   Every update is a deletion–insertion pair $(y,x)$:
--
--   1. **Delete $(y)$.** Remove $y$ from its component $D$ (of level $j$), creating a hole, and apply Any2End $(j)$ to $D$. Then, for each later component $D'$ from left to right, apply SwapHole $(D,D')$ and Start2End to $D'$, and continue with $D'$.
--   2. **Insert $(x)$.** Insert $x$ into its sorted position in $A_1$, using the hole at its end.
--   3. **Re-Sort.** A counter per level $j\ge2$ counts the updates since its last reset. When counter $j$ reaches $2^{j-1}$, the suffix $A_j=D_j,\dots,A_1$ is ready for rebuilding; at the end of the update only the highest ready level $i$ is rebuilt, by sorting all elements of $A_i$ into one level-$i$ DST with empty lower components, and the counters of levels $\le i$ are reset.
--
--   A **run** is a sequence of pairs $(y,x)$ in which each $y$ is stored and each $x$ is new; a state is **reachable** from $n$ virtual elements if a run produces it. The A-DST keeps counters for Delete's element movements, the ReBuild recourse and SwapHole calls with their log, Insert's movements, and the Re-Sort recourse.
--
--   **Formalization Note** Which inactive element $y$ serves an insertion is arbitrary in the paper, so runs allow any stored $y$. The virtual elements are $(0,k)$ for $k<n$. The Re-Sort recourse counts the cells whose content changes.
-- source:
--   Azar, Bhore, Dey, Panigrahi, Vardi, Zhang, Online and Fully-Dynamic Sorting, STOC 2027 submission (manuscript sha256 da7f0d5ef6191ccaa6c70faec62234592c6d108cd2357bda3e5b6dac010acf6c), §2, p.6 (PDF p.8); §5.1–5.3, pp.22–25 (PDF pp.24–27)

import Mathlib
import Definitions.Def_DynSort_any2End

namespace DynSort

/-! # The Augmented Dynamic Sorting Tree, its updates, and its runs

Y. Azar, S. Bhore, D. Dey, D. Panigrahi, O. Vardi, I. Zhang, *Online and Fully-Dynamic Sorting*,
STOC 2027 submission (manuscript sha256 da7f0d5e…), §2, p.6 (PDF p.8, the reduction); §5,
pp.22–25 (PDF pp.24–27).

An A-DST consists of components `D_d, D_{d−1}, …, D₂, A₁`, left to right, where `D_j` is a level-`j`
DST and `A₁` a sorted array, with `d = 1 + ⌈log₂ n⌉` (p.22). It starts from `n` virtual elements of
value `0`, sorted, all transfer sections empty (p.6). Each update is a deletion–insertion pair:
* Delete (x) (p.25): "1. Let D be the level-j component containing x, treating A1 as a level-1 DST.
  Remove x from its cell, creating a hole, and apply Any2End (j) to D to move the hole to its last
  position. 2. If D = A1, the operation is complete. 3. Otherwise, process the remaining components
  from left to right. For each such component D′: (a) Apply SwapHole (D, D′) to transfer ownership
  of the hole to D′. (b) Apply Start2End to D′, moving the hole to its last position. (c) Set
  D = D′ and continue to the next component."
* Insert (x) (p.25): "We insert x into its sorted position in this array, shifting the necessary
  elements to fill the hole."
* Re-Sort (p.24): "For each i, we maintain a counter that counts the number of updates since the
  counter was last reset to 0. When the ith counter reaches 2^{i−1}, we say that the A-DST Ai is
  ready for rebuilding. Rebuilding is performed after element insertion, i.e., at the end of the
  current update. If several levels require rebuilding simultaneously, we perform only the
  highest-level rebuilding and reset its counter and those of all lower levels." Re-Sort (i), for
  `i ≥ 2`, sorts all elements of `A_i = D_i, …, A₁` into one level-`i` DST, leaving the lower
  components empty.

**Formalization Note.**
* `comps` lists the components by level, `comp j` being `comps[j − 1]`; `count j` the Re-Sort
  counter of level `j ≥ 2`. The counters `ctr` collect Delete's moves (`moves`, excluding ReBuild),
  the ReBuild recourse of all SwapHole calls (`rebuildMoves`), the SwapHole calls (`swaps`) and
  their log; `insMoves` collects Insert's shifts and `resortMoves` the recourse of Re-Sort.
* `init n vs` builds the level-`(Nat.clog 2 n + 1)` A-DST holding the elements `vs` in `D_d`
  (`A₁` when `d = 1`). For `Elt`, `initElt n` takes the `n` virtual elements `(0, k)`, `k < n`.
* `step y x` is one deletion–insertion pair: Delete (y), Insert (x), then the Re-Sort schedule.
  Which inactive element `y` serves an insertion is "arbitrary" (p.6): a run is any sequence of
  pairs with `y` stored and `x` new (`ValidRun`); `Reachable n A` says `A` is the state after such a
  run from `initElt n`.
-/

variable {α : Type}

/-- **An A-DST** (§5.1, p.22) with its Re-Sort counters and recourse counters. -/
structure ADST (α : Type) where
  d : ℕ
  comps : List (Sec α)
  counts : List ℕ
  ctr : Ctr
  insMoves : ℕ
  resortMoves : ℕ

/-- An empty level-`j` section. -/
def emptySec (j : ℕ) : Sec α := fill j none []

namespace ADST

/-- The level-`j` component (`A₁` for `j = 1`). -/
def comp (A : ADST α) (j : ℕ) : Sec α := A.comps.getD (j - 1) (.leaf [])

/-- Replace the level-`j` component. -/
def setComp (A : ADST α) (j : ℕ) (S : Sec α) : ADST α := { A with comps := A.comps.set (j - 1) S }

/-- The Re-Sort counter of level `j`. -/
def count (A : ADST α) (j : ℕ) : ℕ := A.counts.getD (j - 1) 0

/-- The levels of the components, left to right: `d, d − 1, …, 1`. -/
def levels (A : ADST α) : List ℕ := (List.range A.d).reverse.map (· + 1)

/-- The cells of the whole array, left to right. -/
def flat (A : ADST α) : List (Option α) := A.levels.flatMap (fun j => (A.comp j).flat)

/-- The stored elements, left to right. -/
def stored (A : ADST α) : List α := A.flat.filterMap id

/-- The number of holes. -/
def holes (A : ADST α) : ℕ := (A.flat.filter Option.isNone).length

/-- The values of the stored elements of an A-DST of `Elt`s. -/
def vals (A : ADST Elt) : List ℝ := A.stored.map (fun e => (ofLex e).1)

/-- The initial A-DST holding the elements `vs`, sorted, with all transfer sections empty (p.6). -/
def init [LinearOrder α] (n : ℕ) (vs : List α) : ADST α :=
  let d := Nat.clog 2 n + 1
  { d := d,
    comps := (List.range d).map (fun k =>
      if k + 1 = d then fill d none ((vs.mergeSort (fun a b => decide (a ≤ b))).map some)
      else emptySec (k + 1)),
    counts := List.replicate d 0, ctr := {}, insMoves := 0, resortMoves := 0 }

/-- **Delete (x)** (p.25). -/
def delete [LinearOrder α] (x : α) (A : ADST α) : ADST α :=
  match A.levels.find? (fun j => decide (x ∈ (A.comp j).stored)) with
  | none => A
  | some j =>
    let st := any2End j j [] { root := (A.comp j).eraseElt x, ctr := A.ctr }
    let A1 := { (A.setComp j st.root) with ctr := st.ctr }
    (List.range (j - 1)).reverse.foldl (fun B k =>
      let r := swapHoleComp (k + 2) (k + 1) (B.comp (k + 2)) (B.comp (k + 1)) B.ctr
      let st2 := start2End (k + 1) (k + 1) [] { root := r.2.1, ctr := r.2.2 }
      { (B.setComp (k + 2) r.1).setComp (k + 1) st2.root with ctr := st2.ctr }) A1

/-- **Insert (x)** (p.25): `A₁` ends with the hole; `x` goes to its sorted position, the larger
elements shifting right by one. -/
def insert [LinearOrder α] (x : α) (A : ADST α) : ADST α :=
  match A.comp 1 with
  | .leaf c =>
    match c.getLast? with
    | some none =>
      let s := c.dropLast
      let pos := (s.filter (fun o => match o with
        | some v => decide (v < x)
        | none => false)).length
      { (A.setComp 1 (.leaf (s.take pos ++ [some x] ++ s.drop pos))) with
        insMoves := A.insMoves + (s.length - pos) }
    | _ => A
  | _ => A

/-- **Re-Sort (i)** (p.24): sort all elements of `A_i` into one level-`i` DST, the lower
components empty; its recourse is the number of cells whose content changed. -/
def resort [LinearOrder α] (i : ℕ) (A : ADST α) : ADST α :=
  let before := ((List.range i).reverse.map (· + 1)).flatMap (fun j => (A.comp j).flat)
  let cells := ((before.filterMap id).mergeSort (fun a b => decide (a ≤ b))).map some
  let newComps := A.comps.zipIdx.map (fun p =>
    if p.2 + 1 = i then fill i none cells
    else if p.2 + 1 < i then emptySec (p.2 + 1) else p.1)
  { A with
    comps := newComps,
    resortMoves := A.resortMoves +
      ((before.zip cells).filter (fun p => decide (p.1 ≠ p.2))).length }

/-- The Re-Sort schedule at the end of an update (p.24). -/
def afterUpdate [LinearOrder α] (A : ADST α) : ADST α :=
  let cnt := A.counts.zipIdx.map (fun p => if 2 ≤ p.2 + 1 then p.1 + 1 else p.1)
  let B := { A with counts := cnt }
  let ready := (List.range (A.d + 1)).filter (fun j => decide (2 ≤ j ∧ 2 ^ (j - 1) ≤ B.count j))
  match ready.max? with
  | none => B
  | some i =>
    let C := B.resort i
    { C with counts := cnt.zipIdx.map (fun p => if p.2 + 1 ≤ i then 0 else p.1) }

/-- **One update**, a deletion–insertion pair (p.6): Delete (y), Insert (x), then Re-Sort. -/
def step [LinearOrder α] (y x : α) (A : ADST α) : ADST α :=
  ((A.delete y).insert x).afterUpdate

/-- The state after a sequence of pairs `(y, x)`. -/
def runFrom [LinearOrder α] (A : ADST α) : List (α × α) → ADST α
  | [] => A
  | p :: ps => runFrom (A.step p.1 p.2) ps

/-- A sequence of pairs `(y, x)` is a run from `A`: each `y` is stored and each `x` is new. -/
def ValidRun [LinearOrder α] : ADST α → List (α × α) → Prop
  | _, [] => True
  | A, p :: ps => p.1 ∈ A.stored ∧ p.2 ∉ A.stored ∧ ValidRun (A.step p.1 p.2) ps

end ADST

/-- The initial A-DST of the reduction (p.6): `n` virtual elements of value `0`. -/
noncomputable def initElt (n : ℕ) : ADST Elt :=
  ADST.init n ((List.range n).map (fun k => toLex ((0 : ℝ), k)))

/-- `A` is reached from `initElt n` by a run of deletion–insertion pairs. -/
def Reachable (n : ℕ) (A : ADST Elt) : Prop :=
  ∃ ps, (initElt n).ValidRun ps ∧ A = (initElt n).runFrom ps

end DynSort



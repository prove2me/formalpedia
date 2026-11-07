-- Prove2me | Definitions.Def_PathCount2k_DP
-- name    : PathCount2k_DP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:43:00.291053+00:00
-- url     : https://prove2.me/theorems/cc11e0c2-566e-4f1a-b7dd-32d3ffb64761
-- title:
--   §2.10 — the dynamic program over exterior coordinates and auxiliary rows, as a charged program
-- statement:
--   For fixed integer samples $g_v$, $H_{i,v}$ (Definition 2.16) the dynamic program computes tables $X_{p,v}[S]\in\mathbb Z^{1\times D}$ for layers $p=1,\dots,k$, vertices $v$ and $|S|=p$:
--   1. *Initialization:* $X_{1,v}[\{j\}]=g_v(j)\,b_0^\top H_{1,v}$.
--   2. *Transitions:* $U_{p,v}[S]=\sum_{u:(u,v)\in E}X_{p-1,u}[S]$ for $|S|=p-1$; then for $|T|=p$,
--   $$
--   V_{p,v}[T]=\sum_{j\in T}(-1)^{\nu(T,j)}g_v(j)\,U_{p,v}[T\setminus\{j\}],\qquad X_{p,v}[T]=V_{p,v}[T]\,H_{p,v},
--   $$
--   with $\nu(T,j)=|\{s\in T: s>j\}|$.
--   3. *Output:* $z=\sum_vX_{k,v}[[k]]$ and the integer $zb_0$.
--
--   The program is written in the cost monad of `CapacitatedAssort.General.Work`, and every arithmetic operation on a table value is charged one unit, as in §2.11 ("Arithmetic operations on scalar values are counted at unit cost").
--
--   **Formalization Note** Subsets are $k$-bit masks; the graph is given by its arc list; rows are functions `Fin D → ℤ`. Charges: row scaling $D$, row addition $D$, $r+c\,s$ $2D$, row–matrix product $2D^2$, mask enumeration $(k+1)2^k$ per layer and side, one per mask bit examined, $k+2$ per sign.
-- source:
--   Panolan, Saurabh, Xue, Zehavi, Counting Paths in Time O*(2^k), with Extensions to Counting Bounded Treewidth Graphs and Multilinear Monomials, STOC 2027 submission manuscript (Nov 2026), §2.10, pp.14–15 (Definitions 2.17–2.18, Observation 2.7, steps 1–3); §2.11, p.16

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work

open CapacitatedAssort.General

namespace PathCount2k

/-! # The dynamic program of §2.10 as a charged program

Panolan, Saurabh, Xue, Zehavi, *Counting Paths in Time O\*(2^k), …*, STOC 2027 submission
manuscript (Nov 2026), §2.10, pp.14–15, and §2.11, p.16.

**Formalization Note.** Programs live in the published cost monad
`CapacitatedAssort.General.Work = StateM ℕ`; `charge c` adds `c` to the operation count. The unit
is the paper's (§2.11, p.16): "Arithmetic operations on scalar values are counted at unit cost".
Every `+`, `−`, `×` and comparison on an integer table value is charged; loop bookkeeping
(enumerating masks, testing a bit, computing `ν(T, j)` and the sign) is charged too, which is more
conservative. A subset `S ⊆ [k]` is its `k`-bit mask `∑_{j ∈ S} 2^j` ("Subsets are represented by
`k`-bit masks", p.16); coordinate `j` of the paper is bit `j − 1`. Rows of length `D` are functions
`Fin D → ℤ`; a table `X_{p,·}[·]` is a function from a vertex and a mask to a row (unset entries
are the zero row). Charge sites: `enumMasks` (`(k+1)·2^k` per call), `scaleRow` (`D`), `addRow`
(`D`), `axpyRow` (`2D`), `rowMul` (`2D²`), one per mask bit examined and `k + 2` per sign
computation in `stepLayer`, one per mask in `initLayer`. -/

/-- The number of set bits among bits `0, …, k − 1` of `T`, i.e. `|S|` for the mask of `S`. -/
def popcount (k T : ℕ) : ℕ := ((List.range k).filter fun j => T.testBit j).length

/-- The masks of all `p`-element subsets of `[k]`, in increasing order. -/
def masksOfCard (k p : ℕ) : List ℕ := (List.range (2 ^ k)).filter fun T => popcount k T = p

/-- The mask `∑_{j ∈ T} 2^j` of a subset `T ⊆ Fin k`. -/
def maskOf {k : ℕ} (T : Finset (Fin k)) : ℕ := ∑ j ∈ T, 2 ^ j.val

/-- `ν(T, j) = |{s ∈ T : s > j}|`, Observation 2.7, p.14, on masks. -/
def nu (k T j : ℕ) : ℕ := ((List.range k).filter fun s => decide (j < s) && T.testBit s).length

/-- `(−1)^e`. -/
def signOf (e : ℕ) : ℤ := if e % 2 = 0 then 1 else -1

/-- A row of length `D`. -/
abbrev Row (D : ℕ) := Fin D → ℤ

/-- A layer table: vertex and subset mask ↦ row. -/
abbrev Table (n D : ℕ) := Fin n → ℕ → Row D

/-- Coordinate `j` of `g_v` (`0` outside `j < k`). -/
def gAt {n k : ℕ} (g : Fin n → Fin k → ℤ) (v : Fin n) (j : ℕ) : ℤ :=
  if h : j < k then g v ⟨j, h⟩ else 0

/-- The matrix at 0-based position `i` and vertex `v` (zero outside `i < k`). -/
def HAt {n k D : ℕ} (H : Fin k → Fin n → Fin D → Fin D → ℤ) (i : ℕ) (v : Fin n) :
    Fin D → Fin D → ℤ :=
  if h : i < k then H ⟨i, h⟩ v else fun _ _ => 0

/-- The first row `b₀ᵀ M` of a `D × D` matrix. -/
def firstRow {D : ℕ} (M : Fin D → Fin D → ℤ) : Row D :=
  fun b => if h : 0 < D then M ⟨0, h⟩ b else 0

/-- The first coordinate `r b₀` of a row. -/
def firstCoord {D : ℕ} (r : Row D) : ℤ := if h : 0 < D then r ⟨0, h⟩ else 0

/-- Overwrite entry `(v, S)` of a table. -/
def update {n D : ℕ} (X : Table n D) (v : Fin n) (S : ℕ) (r : Row D) : Table n D :=
  fun u T => if u = v ∧ T = S then r else X u T

/-- Charged enumeration of the masks of `p`-subsets of `[k]` (popcount of every mask). -/
def enumMasks (k p : ℕ) : Work (List ℕ) := do
  charge ((k + 1) * 2 ^ k)
  return masksOfCard k p

/-- `c · r`, `D` multiplications. -/
def scaleRow {D : ℕ} (c : ℤ) (r : Row D) : Work (Row D) := do
  charge D
  return fun a => c * r a

/-- `r + s`, `D` additions. -/
def addRow {D : ℕ} (r s : Row D) : Work (Row D) := do
  charge D
  return fun a => r a + s a

/-- `r + c · s`, `2D` operations. -/
def axpyRow {D : ℕ} (c : ℤ) (s r : Row D) : Work (Row D) := do
  charge (2 * D)
  return fun a => r a + c * s a

/-- The row-matrix product `r M`, `D²` multiplications and `D²` additions. -/
def rowMul {D : ℕ} (r : Row D) (M : Fin D → Fin D → ℤ) : Work (Row D) := do
  charge (2 * D * D)
  return fun b => ∑ a : Fin D, r a * M a b

/-- **Step 1, Initialization** (§2.10, p.15): "For every `v ∈ V` and `j ∈ [k]`, set
`X_{1,v}[{j}] = g_v(j) b₀ᵀ H_{1,v}`." -/
def initLayer (n k D : ℕ) (g : Fin n → Fin k → ℤ) (H : Fin k → Fin n → Fin D → Fin D → ℤ) :
    Work (Table n D) := do
  let mut X : Table n D := fun _ _ _ => 0
  for v in List.finRange n do
    for j in List.range k do
      charge 1
      let r ← scaleRow (gAt g v j) (firstRow (HAt H 0 v))
      X := update X v (2 ^ j) r
  return X

/-- **Step 2, Transitions, at layer `p`** (§2.10, p.15): "first form the incoming row
`U_{p,v}[S] = ∑_{u:(u,v)∈E} X_{p−1,u}[S]`" for every `|S| = p − 1`, by adding, for each arc
`(u, v)` of the arc list, the rows of `u` into those of `v`; "Next, for every `v ∈ V` and
`T ⊆ [k]` with `|T| = p`, … `V_{p,v}[T] = ∑_{j∈T} (−1)^{ν(T,j)} g_v(j) U_{p,v}[T ∖ {j}]`, and
then … `X_{p,v}[T] = V_{p,v}[T] H_{p,v}`."

**Formalization Note.** `A` is the arc list (adjacency-list input); position `p` is the 0-based
matrix index `p − 1`. -/
def stepLayer (n k D : ℕ) (A : List (Fin n × Fin n)) (g : Fin n → Fin k → ℤ)
    (H : Fin k → Fin n → Fin D → Fin D → ℤ) (p : ℕ) (X : Table n D) : Work (Table n D) := do
  let prev ← enumMasks k (p - 1)
  let cur ← enumMasks k p
  let mut U : Table n D := fun _ _ _ => 0
  for e in A do
    for S in prev do
      let r ← addRow (U e.2 S) (X e.1 S)
      U := update U e.2 S r
  let mut Xn : Table n D := fun _ _ _ => 0
  for v in List.finRange n do
    for T in cur do
      let mut V : Row D := fun _ => 0
      for j in List.range k do
        charge 1
        if T.testBit j then
          charge (k + 2)
          V ← axpyRow (signOf (nu k T j) * gAt g v j) (U v (T - 2 ^ j)) V
      let r ← rowMul V (HAt H (p - 1) v)
      Xn := update Xn v T r
  return Xn

/-- The table of layer `p` (`p = 1`: initialization; `p ≥ 2`: one transition from layer
`p − 1`; "All incoming rows are formed from layer `p − 1` before proceeding to layer `p`"). -/
def layer (n k D : ℕ) (A : List (Fin n × Fin n)) (g : Fin n → Fin k → ℤ)
    (H : Fin k → Fin n → Fin D → Fin D → ℤ) : ℕ → Work (Table n D)
  | 0 => pure fun _ _ _ => 0
  | 1 => initLayer n k D g H
  | p + 2 => do
      let X ← layer n k D A g H (p + 1)
      stepLayer n k D A g H (p + 2) X

/-- **The dynamic program of §2.10** for one trial. Step 3, Output (p.15): "At layer `k`, the only
exterior coordinate is `[k]`. Form the row `z = ∑_{v∈V} X_{k,v}[[k]]`"; the program returns the
integer `z b₀` ("Multiplication by `b₀` selects the first coordinate of `z`"), which §2.12 step 3
retains "before the final squaring and normalization". -/
def dp (n k D : ℕ) (A : List (Fin n × Fin n)) (g : Fin n → Fin k → ℤ)
    (H : Fin k → Fin n → Fin D → Fin D → ℤ) : Work ℤ := do
  let X ← layer n k D A g H k
  let mut z : Row D := fun _ => 0
  for v in List.finRange n do
    z ← addRow z (X v (2 ^ k - 1))
  return firstCoord z

/-- **The output of the dynamic program**, §2.10 step 3, p.15: "return `(z b₀)²/(k! D^{k−1})`".
Runs `dp` and then the normalization: `k!` and `D^{k−1}` by `2k` products, their product, the
square and the one division (`2k + 3` charged operations). The result is the exact rational `Y₀`
(Lemma 2.16). -/
def dpOutput (n k D : ℕ) (A : List (Fin n × Fin n)) (g : Fin n → Fin k → ℤ)
    (H : Fin k → Fin n → Fin D → Fin D → ℤ) : Work ℚ := do
  let z ← dp n k D A g H
  charge (2 * k + 3)
  return ((z * z : ℤ) : ℚ) / ((Nat.factorial k * D ^ (k - 1) : ℕ) : ℚ)

end PathCount2k



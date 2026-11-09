-- Prove2me | Definitions.Def_ForgetAlt_Layouts
-- name    : ForgetAlt_Layouts
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:24:09.616642+00:00
-- url     : https://prove2.me/theorems/0a634294-3871-491d-a762-58f4edfb6b26
-- title:
--   Word-RAM input and output layouts for the running-time milestones
-- statement:
--   Fixed memory layouts for the running-time claims of Lemma 3.1, Lemma 3.7 (R4), Lemma 3.9, Theorem 3.22 and the MIE claim of Section 5.1:
--
--   * a DAG by adjacency lists, with the arrays $\mathrm{cl}$ and $\phi$ and two vertices $y,z$ (Lemma 3.1);
--   * extended vertices numbered $v\mapsto v$, $a_u\mapsto n+u$, $f\mapsto 2n$; parities $\mathrm{even}\mapsto0$, $\mathrm{odd}\mapsto1$; values in $\mathbb N\cup\{\infty\}$ coded $\infty\mapsto 0$, $d\mapsto d+1$;
--   * the **ABT data**: per extended vertex its parent, $\alpha$, its MIE oriented with the inner endpoint second, and $\rho$ of the MIE; then the arguments $s,t,\theta$ of a PathConstruction call and its top-level edge;
--   * the **distance arrays** ($\mathrm{dist}^{\mathrm{even}},\mathrm{dist}^{\mathrm{odd}}$ per extended vertex) and the **parent array** of an ABT;
--   * the extended counts $n'=n+|U|+1$, $m'=m+2|U|$ of Section 3.6.
--
--   **Formalization Note** Every array is read in place; a program may read only what it needs.
-- source:
--   Izumi–Kitamura–Yamaguchi, Forgetting Alternation and Blossoms, STOC 2027 submission (manuscript sha256 b656488c…), Lemma 3.1 (p.16), Lemma 3.7 and 3.9 (pp.20–23), Theorem 3.22 (p.32), Section 5.1 (p.48)

import Mathlib
import Definitions.Def_ForgetAlt_Machine
import Definitions.Def_ForgetAlt_PathConstruction

namespace ForgetAlt

open BergeMatching.Core

/-!
# Machine layouts for the running-time milestones

Izumi–Kitamura–Yamaguchi, *Forgetting Alternation and Blossoms*, STOC 2027 submission
(manuscript sha256 b656488c…): Lemma 3.1 (printed p.16, PDF p.17), Lemma 3.7 (R4) and
Lemma 3.9 (printed pp.20–23, PDF pp.21–24), Theorem 3.22 (printed p.32, PDF p.33), and the
Section 5.1 claim on MIEs (printed p.48, PDF p.49).

**Formalization Notes.** All runs are on the published word RAM `EndStatement`, with `n` (or
`N`) in cell 0, the input words after it, and the output in the cells after the input
(`RunOutputs`).
* **Lemma 3.1.** A DAG on `Fin N` is given by adjacency lists `succ v`, the array `cl`, and the
  array `ϕ`, followed by `y`, `z`. Layout: `y, z`, then for each vertex `v` the four words
  `deg v, start v, cl v, ϕ v` (`start v` = position of `v`'s list inside the adjacency block),
  then the adjacency lists concatenated in vertex order. Output: `|P|, P, |Q|, Q`.
* **Extended vertex indices.** For `V = Fin n`: `orig v ↦ v`, `aux u ↦ n + u`, `f ↦ 2n`.
  Parities: `even ↦ 0`, `odd ↦ 1`. A value of `ℕ∞` is coded `⊤ ↦ 0`, `d ↦ d + 1`, so that
  zero-initialised memory reads as `∞`.
* **ABT data** (PathConstruction): for each extended index `i = 0, …, 2n`, the five words
  `p_T(v), α(v), y, z, ρ(e*_T(v))` where `(y, z)` is `e*_T(v)` oriented with `z ∈ V(T(v))`; then
  `s, t, θ` and the top-level edge `y₀, z₀, ρ(e)` oriented the same way at `t`.
* **Distance arrays**: for each extended index `i`, the two words `dist^even(v)`, `dist^odd(v)`
  (coded). **Parent array**: for each extended index `i`, the word `p_T(v)`.
* The extended counts of Section 3.6 are `n′ = n + |U| + 1` and `m′ = m + 2|U|`.
-/

open EndStatement

/-! ## Lemma 3.1 -/

/-- A DAG on `Fin N` by adjacency lists, with the arrays `cl` and `ϕ` and two vertices `y, z`. -/
structure DagInput (N : ℕ) where
  succ : Fin N → List (Fin N)
  clv : Fin N → Fin N
  phi : Fin N → ℕ
  y : Fin N
  z : Fin N

/-- The arc relation of a `DagInput`. -/
def DagInput.arc {N : ℕ} (x : DagInput N) (a b : Fin N) : Prop := b ∈ x.succ a

/-- The out-degree of `v`. -/
def DagInput.deg {N : ℕ} (x : DagInput N) (v : Fin N) : ℕ := (x.succ v).length

/-- The hypotheses of the construction part of Lemma 3.1: `K` a DAG (no repeated arcs), the
array `cl` is `cl_K`, `ϕ(a) > ϕ(b)` on every arc, `ϕ` constant on the sinks, `y ≠ z` and
`cl_K(y) ≠ cl_K(z)`. -/
def DagInput.Valid {N : ℕ} (x : DagInput N) : Prop :=
  (∀ v, (x.succ v).Nodup) ∧ (∀ a, ¬ Relation.TransGen x.arc a a) ∧
    (∀ v, IsLastPostdom x.arc v (x.clv v)) ∧ (∀ a b, x.arc a b → x.phi b < x.phi a) ∧
    (∀ s s', IsSink x.arc s → IsSink x.arc s' → x.phi s = x.phi s') ∧
    x.y ≠ x.z ∧ x.clv x.y ≠ x.clv x.z

/-- The input words of a `DagInput` (after cell 0, which holds `N`). -/
def dagInput {N : ℕ} (x : DagInput N) : List ℤ :=
  [((x.y : ℕ) : ℤ), ((x.z : ℕ) : ℤ)] ++
    (List.ofFn (fun v : Fin N =>
      [(x.deg v : ℤ), (((List.ofFn (fun w : Fin N => x.deg w)).take v).sum : ℤ),
        ((x.clv v : ℕ) : ℤ), (x.phi v : ℤ)])).flatten ++
    (List.ofFn (fun v : Fin N => (x.succ v).map (fun w => ((w : ℕ) : ℤ)))).flatten

/-- The size `N + Σ deg + max ϕ + 2` of a `DagInput`, which sets the word width. -/
def dagSize {N : ℕ} (x : DagInput N) : ℕ :=
  N + (List.ofFn x.deg).sum + (List.ofFn x.phi).foldr max 0 + 2

/-- The output words `|P|, P, |Q|, Q`. -/
def encTwoPaths {N : ℕ} (P Q : List (Fin N)) : List ℤ :=
  ((P.length : ℤ) :: P.map (fun v => ((v : ℕ) : ℤ))) ++
    ((Q.length : ℤ) :: Q.map (fun v => ((v : ℕ) : ℤ)))

/-! ## Extended systems over `Fin n` -/

/-- The index of an extended vertex: `orig v ↦ v`, `aux u ↦ n + u`, `f ↦ 2n`. -/
def extIdx {n : ℕ} : ExtV (Fin n) → ℕ
  | .orig v => v
  | .aux u => n + u
  | .f => 2 * n

/-- The extended vertex with index `i < 2n + 1`. -/
def extOfIdx {n : ℕ} (i : Fin (2 * n + 1)) : ExtV (Fin n) :=
  if h : (i : ℕ) < n then .orig ⟨i, h⟩
  else if h' : (i : ℕ) < 2 * n then .aux ⟨i - n, by omega⟩ else .f

/-- The code of a parity: `even ↦ 0`, `odd ↦ 1`. -/
def parCode : Parity → ℤ
  | .even => 0
  | .odd => 1

/-- The code of a value of `ℕ∞`: `⊤ ↦ 0`, `d ↦ d + 1`. -/
def enatCode (d : ℕ∞) : ℤ := if d = ⊤ then 0 else ((d.toNat : ℤ) + 1)

/-- The number `|U|` of free vertices of the instance. -/
noncomputable def numFree {n : ℕ} (x : AugInstance n) : ℕ :=
  open Classical in (Finset.univ.filter (fun v => IsNeutral x.matching v)).card

/-- The number `n′ = n + |U| + 1` of vertices of the extended system (p.28). -/
noncomputable def extN {n : ℕ} (x : AugInstance n) : ℕ := n + numFree x + 1

/-- The number `m′ = m + 2|U|` of edges of the extended system (p.28). -/
noncomputable def extM {n : ℕ} (x : AugInstance n) : ℕ := x.edges.length + 2 * numFree x

/-- The ABT data read by PathConstruction (five words per extended vertex). -/
noncomputable def abtData {n : ℕ} (G : SimpleGraph (Fin n)) (M : G.Subgraph)
    (par : ExtV (Fin n) → ExtV (Fin n)) (mie : ExtV (Fin n) → Sym2 (ExtV (Fin n))) : List ℤ :=
  (List.ofFn (fun i : Fin (2 * n + 1) =>
    let v := extOfIdx i
    [(extIdx (par v) : ℤ), parCode (alpha G M v), (extIdx (splitInc G M par v (mie v)).1 : ℤ),
      (extIdx (splitInc G M par v (mie v)).2 : ℤ), parCode (rho G M (mie v))])).flatten

/-- The input of a call `PathConstruction(T, s, t, θ, e)`: the ABT data, then `s, t, θ`, then
the top-level edge `e` oriented at `t` and `ρ(e)`. -/
noncomputable def pcInput {n : ℕ} (G : SimpleGraph (Fin n)) (M : G.Subgraph)
    (par : ExtV (Fin n) → ExtV (Fin n)) (mie : ExtV (Fin n) → Sym2 (ExtV (Fin n)))
    (s t : ExtV (Fin n)) (θ : Parity) (e : Sym2 (ExtV (Fin n))) : List ℤ :=
  abtData G M par mie ++
    [(extIdx s : ℤ), (extIdx t : ℤ), parCode θ, (extIdx (splitInc G M par t e).1 : ℤ),
      (extIdx (splitInc G M par t e).2 : ℤ), parCode (rho G M e)]

/-- The output words of a vertex list of the extended system. -/
def encExtPath {n : ℕ} (L : List (ExtV (Fin n))) : List ℤ :=
  (L.length : ℤ) :: L.map (fun v => (extIdx v : ℤ))

/-- The distance arrays: `dist^even(v), dist^odd(v)` (coded) for each extended index. -/
noncomputable def distArrays {n : ℕ} (G : SimpleGraph (Fin n)) (M : G.Subgraph) : List ℤ :=
  (List.ofFn (fun i : Fin (2 * n + 1) =>
    [enatCode (dist G M .even (extOfIdx i)), enatCode (dist G M .odd (extOfIdx i))])).flatten

/-- The parent array: `p_T(v)` for each extended index. -/
def parArray {n : ℕ} (par : ExtV (Fin n) → ExtV (Fin n)) : List ℤ :=
  List.ofFn (fun i : Fin (2 * n + 1) => (extIdx (par (extOfIdx i)) : ℤ))

end ForgetAlt



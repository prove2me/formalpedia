-- Prove2me | Definitions.Def_GaussLocalMaxColoring_Main_Machine
-- name    : GaussLocalMaxColoring_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:23:21.833687+00:00
-- url     : https://prove2.me/theorems/31e891d2-8627-4439-8b83-08db540103a9
-- title:
--   Machine-layer predicates: independent sets of size $n^{e-o(1)}$, bounded-degree 3-colorable inputs, and the input/output layout of BuildVector
-- statement:
--   Algorithms of the goal, Theorems 1, 5 and Lemma 34 are programs of the published integer RAM `CongruencyTU`, run on the published graph encoding (`encGraph`: $n$, then the $n^2$ adjacency bits).
--   * `GoodIndepO e g`: the output is the characteristic vector of an independent set $S$ with $|S|\ge n^{e-g(n)}$.
--   * `ThreeColDegLe b` / `ThreeColDegLt b`: 3-colorable with maximum degree $\Delta\le n^b$ / $\Delta<n^b$.
--   * **BuildVector's instances**: a graph and the partition $\mathcal P$ as a list of intervals with rational endpoints $(lo,hi,lo\in P,hi\in P)$; size $n+|\mathcal P|$; valid when $n\ge2$, $G$ is 3-colorable, and the intervals are distinct and form a band partition.
--   * **BuildVector's output**: rational matrices — the Gram matrix $X$ of $\{v_i\}$ (row by row) and, for each $r$ and each interval (input order), the $(2n+1)\times(2n+1)$ Gram matrix $Y_{r,P}$ of the witness ($0$ for $x_\emptyset$, $1+2j+c$ for $x_{j,c}$) — each entry as numerator, denominator. `GoodBV`: $X$ and every $Y_{r,P}$ are positive semidefinite and satisfy every guarantee of Lemma 34 with $\varepsilon_{\rm SDP}=e^{-3n}$.
--
--   **Formalization Note.** The vectors $\{v_i\}$ of Lemma 34 are a Gram realization of $X$ (Algorithm 6, line 3), and every property in Lemma 34 depends on the vectors and witnesses only through their Gram matrices, so returning the Gram matrices returns the paper's output up to the choice of realization.
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Theorems 1, 5, 6 (printed pp. 3–5, PDF 5–7), Lemma 34 (p. 33, PDF 35), Algorithm 6 (p. 67, PDF 69)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_RecGaussColoring_Main_Graph
import Definitions.Def_GaussLocalMaxColoring_Main_Bands

open scoped RealInnerProductSpace
open Filter
open RecGaussColoring.Main
open Classical
noncomputable section

namespace GaussLocalMaxColoring.Main

/-! # Machine-layer predicates: independent sets of size `n^{e − o(1)}`, bounded degree, and the
input/output layout of BuildVector (Lemma 34)

Deguchi–Kawarabayashi–Yoneda–Yoneda, arXiv:2610.35859, Theorems 1, 5, 6 (pp. 3–5, PDF 5–7) and
Lemma 34 (p. 33, PDF 35).

Algorithms are programs of the published integer RAM `CongruencyTU` (`DetSolves`, `RandSolves`);
graphs are `RecGaussColoring.Main.Graph3` (`n`, then the `n²` adjacency bits), output sets are
`DecodesSet` (characteristic vectors), colorings are `GoodColoring`.

**Formalization Note (BuildVector).** The program receives the graph and the partition `𝒫` as a
list of intervals with rational endpoints `(lo, hi, lo ∈ P, hi ∈ P)`, and returns the Gram matrix
`X` of the vectors `{v_i}` and, for each vertex `r` and each interval `P` (in input order), the
Gram matrix `Y_{r,P}` of the witness `𝒲_{r,P}` (index `0` for `x_∅`, `1 + 2j + c` for `x_{j,c}`),
all entries rational, each entry written as numerator then denominator. The vectors and witness
vectors are any Gram realizations of these positive semidefinite matrices; every property of
Lemma 34 depends on them only through the Gram matrices. -/

/-- The output decodes to an independent set `S` with `|S| ≥ n^{e − g(n)}`. -/
def GoodIndepO (e : ℝ) (g : ℕ → ℝ) (I : Graph3) (out : List ℤ) : Prop :=
  ∃ S : Finset (Fin I.n), DecodesSet I out S ∧ Independent I S ∧
    (I.n : ℝ) ^ (e - g I.n) ≤ (S.card : ℝ)

/-- A 3-colorable graph with maximum degree at most `n^b`. -/
def ThreeColDegLe (b : ℝ) (I : Graph3) : Prop :=
  ThreeColorable I ∧ (maxDeg I : ℝ) ≤ (I.n : ℝ) ^ b

/-- A 3-colorable graph with maximum degree `Δ < n^b` (Theorem 1's strict inequality). -/
def ThreeColDegLt (b : ℝ) (I : Graph3) : Prop :=
  ThreeColorable I ∧ (maxDeg I : ℝ) < (I.n : ℝ) ^ b

/-- An interval with rational endpoints, as an input record. -/
abbrev QIval := ℚ × ℚ × Bool × Bool

/-- The real interval of an input record. -/
def QIval.toIval (q : QIval) : Ival := ⟨q.1, q.2.1, q.2.2.1, q.2.2.2⟩

/-- The instances of BuildVector: a graph and a partition given as a list of rational intervals. -/
structure BVInstance where
  I : Graph3
  parts : List QIval

/-- The partition `𝒫` of an instance. -/
def BVInstance.partition (a : BVInstance) : Finset Ival := (a.parts.map QIval.toIval).toFinset

/-- Encoding of an instance: the graph's encoding, then `|𝒫|`, then for each interval
`[num lo, den lo, num hi, den hi, [lo ∈ P], [hi ∈ P]]`. -/
def encBV (a : BVInstance) : List ℤ :=
  encGraph a.I ++ (a.parts.length : ℤ) ::
    a.parts.flatMap fun q =>
      [q.1.num, (q.1.den : ℤ), q.2.1.num, (q.2.1.den : ℤ),
        if q.2.2.1 then 1 else 0, if q.2.2.2 then 1 else 0]

/-- Input size of BuildVector: the number of vertices plus the number of intervals. -/
def sizeBV (a : BVInstance) : ℕ := a.I.n + a.parts.length

/-- Valid instances: `n ≥ 2`, `G` 3-colorable, the intervals form a band partition (distinct). -/
def DomBV (a : BVInstance) : Prop :=
  2 ≤ a.I.n ∧ ThreeColorable a.I ∧ (a.parts.map QIval.toIval).Nodup ∧
    IsBandPartition a.I.n a.partition

/-- Position of a witness index: `x_∅ ↦ 0`, `x_{j,c} ↦ 1 + 2j + c`. -/
def wpos {n : ℕ} : WIdx n → ℕ
  | none => 0
  | some (j, c) => 1 + 2 * j.val + c.val

/-- A rational as two integers, numerator then denominator. -/
def encQ (q : ℚ) : List ℤ := [q.num, (q.den : ℤ)]

/-- The output layout of BuildVector: `X` row by row, then for each `r` and each interval index
`p` the `(2n+1) × (2n+1)` matrix `Y r p` row by row (positions `wpos`). -/
def encBVOut (n m : ℕ) (X : Matrix (Fin n) (Fin n) ℚ)
    (Y : Fin n → Fin m → Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℚ) : List ℤ :=
  ((List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => encQ (X i j)) ++
  ((List.finRange n).flatMap fun r => (List.finRange m).flatMap fun p =>
    (List.finRange (2 * n + 1)).flatMap fun a =>
      (List.finRange (2 * n + 1)).flatMap fun b => encQ (Y r p a b))

/-- The witness Gram matrix, indexed by `WIdx n`, of interval `P` for vertex `r`: the matrix of
the first input position carrying `P` (zero if none). -/
def witnessOf {n m : ℕ} (parts : List QIval) (hm : parts.length = m)
    (Y : Fin n → Fin m → Matrix (Fin (2 * n + 1)) (Fin (2 * n + 1)) ℚ) (r : Fin n) (P : Ival) :
    Matrix (WIdx n) (WIdx n) ℝ :=
  match (List.finRange m).find? (fun p => (parts.get (p.cast hm.symm)).toIval = P) with
  | some p => Matrix.of fun a b =>
      if ha : wpos a < 2 * n + 1 then
        if hb : wpos b < 2 * n + 1 then (Y r p ⟨wpos a, ha⟩ ⟨wpos b, hb⟩ : ℝ) else 0
      else 0
  | none => 0

/-- The output of BuildVector is good (**Lemma 34**): it is the layout of rational matrices `X`
and `Y` with `X` and every `Y r p` positive semidefinite, `X` satisfying the vector guarantees and
the witnesses satisfying the band guarantees (i), (ii), with `ε = ε_SDP = e^{−3n}`. -/
def GoodBV (a : BVInstance) (out : List ℤ) : Prop :=
  ∃ (X : Matrix (Fin a.I.n) (Fin a.I.n) ℚ)
    (Y : Fin a.I.n → Fin a.parts.length → Matrix (Fin (2 * a.I.n + 1)) (Fin (2 * a.I.n + 1)) ℚ),
    out = encBVOut a.I.n a.parts.length X Y ∧
    (X.map (fun q : ℚ => (q : ℝ))).PosSemidef ∧
    (∀ r p, ((Y r p).map (fun q : ℚ => (q : ℝ))).PosSemidef) ∧
    BVVectorConds a.I.G (X.map (fun q : ℚ => (q : ℝ))) (epsSDP a.I.n) ∧
    BVWitnessConds a.I.G (X.map (fun q : ℚ => (q : ℝ))) a.partition
      (witnessOf a.parts rfl Y) (epsSDP a.I.n)

end GaussLocalMaxColoring.Main



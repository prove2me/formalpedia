-- Prove2me | Definitions.Def_ClusterDecomp_Supplement_Alg3Run
-- name    : ClusterDecomp_Supplement_Alg3Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T23:57:14.212304+00:00
-- url     : https://prove2.me/theorems/d7c95aba-e15e-4f05-8b8e-c3500804db43
-- title:
--   Algorithm 3 and penalized minimum-cut runs
-- statement:
--   For a finite undirected weighted graph $G$, a set $B$ and a penalty $q$, **PenalizedMinCut** builds the paper's auxiliary graph on $V(G)\cup\{s,t\}$: original edges retain their weights, each $v\in B$ receives an edge $sv$ of capacity $q\deg_G(v)$, and each $v\notin B$ receives an edge $vt$ of the same capacity. It may return the source side, with $s$ removed, of any minimum $s$-$t$ cut.
--
--   **Algorithm 3 (ApproximationBoost)** computes $h=\max_i\phi_G(B_i)$ once and runs rounds $r=0,\ldots,\lceil\log_{3/2}\alpha\rceil$ with $q_r=(2h/\alpha)(3/2)^r$. In each round it performs one penalized minimum-cut computation for every $i$, removes from its result every vertex returned for another index, and stores the resulting positive-volume family only when its maximum conductance is strictly smaller than the previous best. A run records every minimum-cut call and its final optional output.
--
--   The relation deliberately permits every minimum-cut tie-break. Therefore a theorem quantified over all runs establishes the paper's guarantee independently of which minimum cut is returned.
--
--   **Formalization Note** The auxiliary vertices are represented by $V\sqcup\mathrm{Bool}$; capacities are formed from the degrees in $G$, with loops counted once. The minimum is taken over the cuts of this explicit auxiliary graph rather than a substituted closed formula.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Algorithm 3 and §4.1, pp.19–20 (PDF pp.21–22)

import Mathlib
import Definitions.Def_ClusterDecomp_Conductance

open Finset

namespace ClusterDecomp.Supplement

/-!
# Algorithm 3 (ApproximationBoost) and PenalizedMinCut as a run relation

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), §4.1 and Algorithm 3, pp.19–20 (PDF pp.21–22).

**Formalization Note.**
* `IsMinCut c s t S`: `S` is the source side of an `s`-`t` cut (`s ∈ S`, `t ∉ S`) of the raw capacity
  function `c` whose capacity `∑_{u ∈ S} ∑_{v ∉ S} c(u, v)` is at most that of every `s`-`t` cut.
* The auxiliary graph `H` of `PenalizedMinCut(G, B, q)` (lines 22–32) has vertex type `V ⊕ Bool`, with
  `s = inr false` and `t = inr true`. Its capacities `penCap G B q` are `w(u, v)` between vertices of `V`
  (loops of `G` are kept; they never cross a cut), `q·deg(v)` on `{s, v}` for `v ∈ B` and on `{v, t}` for
  `v ∉ B`, with `deg` the weighted degree in `G` (a loop counted once), and `0` otherwise. No closed form of
  the cut capacity is substituted: the minimum is taken over the `s`-`t` cuts of `H`, as on line 33.
* `PenalizedMinCut G B q D` holds for **every** minimum cut `(S, T)` and `D = S ∖ {s}` (line 34): ties are
  not broken, so a theorem stated for every `Alg3Run` holds for every tie-break.
* `hMax = max_i ϕ_G(B_i)` (line 1) is a real `⨆` over the finite index type `Fin k` (its value `0` at
  `k = 0` is never used: Theorem 1.2 has `k ≥ 2`). It is computed once, before the loop.
* The rounds are `r = 0, 1, …, ⌈log_{3/2} α⌉` (line 4), i.e. `numRounds α = ⌈log_{3/2} α⌉ + 1` rounds,
  with `q_r = (2h/α)(3/2)^r` (line 5).
* `C_i^{(r)} = D_i^{(r)} ∖ ⋃_{j ≠ i} D_j^{(r)}` (line 10). A round's candidate is considered only if
  `vol(C_i^{(r)}) > 0` for all `i` (line 12); it replaces the stored one only on **strict** improvement
  `γ_r < best` (line 14), with `best` starting at `+∞` (`⊤ : WithTop ℝ`) and `C*` at `null` (`none`).
* A run records, in order, every call `PenalizedMinCut(G, B_i, q_r)` it made as the triple
  `(B_i, q_r, D_i^{(r)})`; the number of minimum `s`-`t` cut computations of the run is the length of that
  list.
-/

open ClusterDecomp

/-- `S` is the source side of a minimum `s`-`t` cut for the raw capacity function `c`. -/
def IsMinCut {W : Type*} [Fintype W] [DecidableEq W] (c : W → W → ℝ) (s t : W) (S : Finset W) :
    Prop :=
  s ∈ S ∧ t ∉ S ∧ ∀ S' : Finset W, s ∈ S' → t ∉ S' → cutCap c S Sᶜ ≤ cutCap c S' S'ᶜ

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The source `s` of the auxiliary graph `H`. -/
abbrev srcH (V : Type*) : V ⊕ Bool := Sum.inr false

/-- The sink `t` of the auxiliary graph `H`. -/
abbrev snkH (V : Type*) : V ⊕ Bool := Sum.inr true

/-- The capacities of the auxiliary graph `H` of `PenalizedMinCut(G, B, q)` (Algorithm 3, lines 22–32). -/
def penCap (G : WGraph V) (B : Finset V) (q : ℝ) : V ⊕ Bool → V ⊕ Bool → ℝ
  | .inl u, .inl v => G.w u v
  | .inr false, .inl v => if v ∈ B then q * G.deg v else 0
  | .inl v, .inr false => if v ∈ B then q * G.deg v else 0
  | .inl v, .inr true => if v ∈ B then 0 else q * G.deg v
  | .inr true, .inl v => if v ∈ B then 0 else q * G.deg v
  | .inr _, .inr _ => 0

/-- `S ∖ {s}` read as a subset of `V`: the vertices of `G` on the source side. -/
def sourceSide (S : Finset (V ⊕ Bool)) : Finset V :=
  univ.filter fun v => Sum.inl v ∈ S

/-- `D` is a possible return value of `PenalizedMinCut(G, B, q)`: `D = S ∖ {s}` for some minimum `s`-`t`
cut `(S, T)` of the auxiliary graph `H`. -/
def PenalizedMinCut (G : WGraph V) (B : Finset V) (q : ℝ) (D : Finset V) : Prop :=
  ∃ S : Finset (V ⊕ Bool), IsMinCut (penCap G B q) (srcH V) (snkH V) S ∧ D = sourceSide S

/-- `h = max_i ϕ_G(B_i)` (line 1). -/
noncomputable def hMax (G : WGraph V) {k : ℕ} (B : Fin k → Finset V) : ℝ :=
  ⨆ i, G.phiOut (B i)

/-- The number of rounds `r = 0, 1, …, ⌈log_{3/2} α⌉` (line 4). -/
noncomputable def numRounds (α : ℝ) : ℕ :=
  Nat.ceil (Real.logb (3 / 2) α) + 1

/-- `q_r = (2h/α)·(3/2)^r` (line 5). -/
noncomputable def qRound (G : WGraph V) {k : ℕ} (B : Fin k → Finset V) (α : ℝ) (r : ℕ) : ℝ :=
  2 * hMax G B / α * (3 / 2 : ℝ) ^ r

/-- `C_i = D_i ∖ ⋃_{j ≠ i} D_j` (line 10). -/
def candidates {k : ℕ} (D : Fin k → Finset V) (i : Fin k) : Finset V :=
  D i \ (univ.filter fun j => j ≠ i).biUnion D

/-- One pass of lines 12–18 on the round's candidate `C`, updating the pair `(best, C*)`. -/
noncomputable def boostStep (G : WGraph V) {k : ℕ} (acc : WithTop ℝ × Option (Fin k → Finset V))
    (C : Fin k → Finset V) : WithTop ℝ × Option (Fin k → Finset V) := by
  classical
  exact
    if ∀ i, 0 < G.vol (C i) then
      if (((⨆ i, G.phiOut (C i) : ℝ)) : WithTop ℝ) < acc.1 then
        (((⨆ i, G.phiOut (C i) : ℝ) : WithTop ℝ), some C)
      else acc
    else acc

/-- A run of Algorithm 3 on `G`, `k`, `B_1, …, B_k`, `α`: in every round `r < numRounds α` and for every `i`,
`D r i` is a value `PenalizedMinCut(G, B_i, q_r)` may return, and `calls` is the list of the minimum-cut
computations made, in the order of lines 4–8. -/
structure Alg3Run (G : WGraph V) (k : ℕ) (B : Fin k → Finset V) (α : ℝ) where
  /-- `D r i = D_i^{(r)}`. -/
  D : ℕ → Fin k → Finset V
  /-- Line 7: each `D_i^{(r)}` is returned by a minimum `s`-`t` cut computation. -/
  isMinCut : ∀ r < numRounds α, ∀ i, PenalizedMinCut G (B i) (qRound G B α r) (D r i)
  /-- The minimum-cut computations of the run, as `(B_i, q_r, D_i^{(r)})`. -/
  calls : List (Finset V × ℝ × Finset V)
  /-- The calls are those of lines 4–8, in order. -/
  calls_eq : calls = (List.range (numRounds α)).flatMap fun r =>
    (List.finRange k).map fun i => (B i, qRound G B α r, D r i)

/-- The value `C*` returned on line 20 (`none` is `null`). -/
noncomputable def Alg3Run.output {G : WGraph V} {k : ℕ} {B : Fin k → Finset V} {α : ℝ}
    (run : Alg3Run G k B α) : Option (Fin k → Finset V) :=
  ((List.range (numRounds α)).foldl (fun acc r => boostStep G acc (candidates (run.D r)))
    ((⊤ : WithTop ℝ), (none : Option (Fin k → Finset V)))).2

end ClusterDecomp.Supplement



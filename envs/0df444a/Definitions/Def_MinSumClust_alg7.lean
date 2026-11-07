-- Prove2me | Definitions.Def_MinSumClust_alg7
-- name    : MinSumClust_alg7
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:19.573877+00:00
-- url     : https://prove2.me/theorems/a219af9f-b679-46f5-b10f-7de0767a7fdb
-- title:
--   Algorithm 7: client assignment, final clusters and feasible $k$-solutions
-- statement:
--   Algorithm 7 (p.49) opens $\mathcal S_{1,O}=\mathcal S_{1,O}^{(\mathrm{res})}$ and $\mathcal S_{2,O}=\mathcal S_{2,O}^{(\mathrm{res})}\cup\mathcal S_2^{(\mathrm{match})}$, lets $D_{\mathrm{settled}}$ be the union of all opened clusters, and assigns each $j\notin D_{\mathrm{settled}}$: a bad $j$ to $A'(j)$; a good $j$ to $A'(j)$ if $C_1(j)$ is residual and to $\ell_M(C_1(j))$ if $C_1(j)$ is matched. The final clusters are
--
--   $$S_2\cup\{j\notin D_{\mathrm{settled}}:A(j)=S_2\}\ (S_2\in\mathcal S_{2,O}),\qquad (S_1\setminus D_2)\cup\{j\notin D_{\mathrm{settled}}:A(j)=S_1\}\ (S_1\in\mathcal S_{1,O}),$$
--
--   with $D_2=\bigcup\mathcal S_{2,O}$. An outcome is a **feasible $k$-solution** if its final clusters are nonempty, pairwise disjoint, cover $D$, and there are exactly $k$ of them. Its cost is the sum of the cluster costs.
--
--   **Formalization Note** Final clusters are indexed by the opened clusters tagged with their side.
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Algorithm 7, p.49 (PDF p.51); §5, p.42; Claim 59, p.57

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_Bipoint
import Definitions.Def_MinSumClust_alg5
import Definitions.Def_MinSumClust_alg6

namespace MinSumClust

variable {D : Type} [Fintype D] [DecidableEq D]

/-- An output of the rounding: the opened clusters, each tagged by its side (`0` for `𝒮₁`, `1` for
`𝒮₂`), and for each tag its final cluster. -/
abbrev Outcome (D : Type) : Type := Finset (Fin 2 × Finset D) × (Fin 2 × Finset D → Finset D)

/-- **Algorithm 7 (Phase 3: Client Assignments)**, p.49 (PDF p.51).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Algorithm 7, p.49. `𝒮₁,O = 𝒮₁,O^(res)`,
`𝒮₂,O = 𝒮₂,O^(res) ∪ 𝒮₂^(match)`, `D_settled` the union of all opened clusters. For `j ∉ D_settled`:
a bad `j` gets `A(j) = A′(j)`; a good `j` gets `A′(j)` if `C₁(j) ∈ 𝒮₁^(res)` and `ℓ_M(C₁(j))` if
`C₁(j) ∈ 𝒮₁^(match)`. The final clusters are `S₂ ∪ {j ∉ D_settled : A(j) = S₂}` for `S₂ ∈ 𝒮₂,O`
and `(S₁ \ D₂) ∪ {j ∉ D_settled : A(j) = S₁}` for `S₁ ∈ 𝒮₁,O`, with `D₂ = ⋃ 𝒮₂,O`. -/
def alg7 (S₁ S₂ : Finpartition (Finset.univ : Finset D)) (ℓ : Labels D) (o5 : Alg5Out D)
    (o6 : Alg6Out D) : Outcome D :=
  let S1O := o6.open1
  let S2O := o6.open2 ∪ o5.match2
  let Ds := (S1O ∪ S2O).biUnion id
  let D2 := S2O.biUnion id
  let A : D → Option (Fin 2 × Finset D) := fun j =>
    if (S₁.part j).card < (S₂.part j).card then o6.assign j
    else if S₁.part j ∈ o5.res1 then o6.assign j
    else if S₁.part j ∈ o5.match1 then (ℓ.lM (S₁.part j)).map fun S => (1, S)
    else none
  (S1O.image (fun S => ((0 : Fin 2), S)) ∪ S2O.image (fun S => ((1 : Fin 2), S)),
    fun t =>
      if t.1 = 1 then t.2 ∪ Finset.univ.filter (fun j => j ∉ Ds ∧ A j = some t)
      else (t.2 \ D2) ∪ Finset.univ.filter (fun j => j ∉ Ds ∧ A j = some t))

/-- **Feasible k-solution** (§5, p.42; Claim 59, p.57): the final clusters of the opened tags are
nonempty, pairwise disjoint and cover `D`, and there are exactly `k` opened tags. -/
def IsKOutcome (o : Outcome D) (k : ℕ) : Prop :=
  (∀ t ∈ o.1, (o.2 t).Nonempty) ∧
    (∀ t ∈ o.1, ∀ t' ∈ o.1, t ≠ t' → Disjoint (o.2 t) (o.2 t')) ∧
    (∀ j, ∃ t ∈ o.1, j ∈ o.2 t) ∧ o.1.card = k

/-- The cost `∑_S cost(S)` of an outcome (§1, p.1). -/
noncomputable def outCost (d : D → D → ℝ) (o : Outcome D) : ℝ :=
  ∑ t ∈ o.1, cost d (o.2 t)

end MinSumClust



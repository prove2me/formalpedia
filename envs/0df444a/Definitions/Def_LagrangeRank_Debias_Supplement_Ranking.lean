-- Prove2me | Definitions.Def_LagrangeRank_Debias_Supplement_Ranking
-- name    : LagrangeRank_Debias_Supplement_Ranking
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:47:19.958877+00:00
-- url     : https://prove2.me/theorems/0383d9ae-b93a-4b62-9ecf-c83bab693b31
-- title:
--   Ranking properties, legal-pair signal, full-box and top-K tests, FWER, BY FDR and Remark D.1 rates
-- statement:
--   A ranking is a permutation of the items, with smaller rank meaning higher score. Scores are sorted in decreasing order, breaking ties by increasing item index. This tie convention excludes no scores. Two rankings are equivalent with respect to item $i$ if the sets of items preceding $i$ agree. A ranking property $R_i$ is any union of these equivalence classes; no monotonicity restriction is imposed.
--
--   A pair $(i,j)$ is legal at an alternative score $\theta$ when swapping the two scores moves its ranking outside $R_i$. Define
--   $$\Delta(\theta,R_i)=\min_{j:\,(i,j)\text{ legal}}|\theta_i-\theta_j|.$$
--   An empty minimum is $+\infty$, represented in $[0,\infty]$. The family signal is the minimum over true alternative hypotheses, with the same empty-family convention.
--
--   The general test rejects precisely when every vector in the full coordinate box (3.15) has its ranking in $R_i$. The single-test radius is $c_W(\alpha,i)/\sqrt{npL}$. The familywise procedure uses the same box with the common quantile for all ordered pairs, including the diagonals as printed. The simplified top-$K$ test separately rejects when
--   $$\hat\theta_i^d-\frac{c_W(\alpha,i)}{\sqrt{npL}}>\hat\theta^d_{(K+1)}.$$
--   Order statistics retain multiplicities, and the theorem uses $1\le K<n$.
--
--   FWER is the probability of at least one false positive; the family Type II event is at least one false negative. For FDR, calculate each p-value as the infimum of levels at which its full-box test rejects, taking 1 when there is no such level. Sort p-values ascending, put $N=\sum_{k=1}^n1/k$, and let $r=\max\{k:p_{(k)}\le k\alpha/(nN)\}$, or zero if empty. Reject the first $r$ hypotheses and define $\mathrm{FDR}=E[V/(R\vee1)]$. No independence between p-values is assumed. The expectation is integrable because the sample space is finite and its integrand is in $[0,1]$.
--
--   `remarkB` and `remarkR` implement every term, maximum, logarithm and exponent in Remark D.1, pp. 53–54, as reproduced in MODERATION_NOTES.md. Real powers use positive bases eventually under the theorem's regime. This file supplies concrete procedures, rather than p-values or quantiles assumed to satisfy the desired validity properties.
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 10, Definitions 2.1–2.3; p. 19, Definitions 3.1–3.2; pp. 23–27; pp. 53–54, Remark D.1

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_Bootstrap

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped BigOperators ENNReal
attribute [local instance] Classical.propDecidable

abbrev Ranking (n : ℕ) := Equiv.Perm (Fin n)
/-- Index order resolves ties. It excludes no score vector and preserves multiplicities. -/
def ConsistentRanking {n : ℕ} (θ : Vec n) (γ : Ranking n) : Prop :=
  ∀ i j, γ i < γ j ↔ θ j < θ i ∨ (θ i = θ j ∧ i < j)
noncomputable def ranking {n : ℕ} (θ : Vec n) : Ranking n :=
  if h : ∃ γ, ConsistentRanking θ γ then h.choose else Equiv.refl _
def predecessors {n : ℕ} (γ : Ranking n) (i : Fin n) : Set (Fin n) := {j | γ j < γ i}
def RankingProperty {n : ℕ} (i : Fin n) (R : Set (Ranking n)) : Prop :=
  ∀ γ ∈ R, ∀ γ', predecessors γ i = predecessors γ' i → γ' ∈ R
noncomputable def swapScores {n : ℕ} (θ : Vec n) (i j : Fin n) : Vec n :=
  θ ∘ Equiv.swap i j
noncomputable def legalPairs {n : ℕ} (θ : Vec n) (i : Fin n) (R : Set (Ranking n)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ranking θ ∈ R ∧ ranking (swapScores θ i j) ∉ R)
/-- Empty legal-pair minimum is +∞, not the real sInf default zero. -/
noncomputable def signal {n : ℕ} (θ : Vec n) (i : Fin n) (R : Set (Ranking n)) : ℝ≥0∞ :=
  ⨅ j ∈ legalPairs θ i R, ENNReal.ofReal |θ i - θ j|
noncomputable def familySignal {n : ℕ} (θ : Vec n) (R : Fin n → Set (Ranking n)) : ℝ≥0∞ :=
  ⨅ i, ⨅ (_ : ranking θ ∈ R i), signal θ i (R i)

/-- The full coordinate box (3.15), not just a selected vertex. -/
noncomputable def perturbBox {n L : ℕ} (p c α : ℝ) (E : Finset (Fin n × Fin n))
    (s : Data n L) : Set (Vec n) :=
  {θ | ∀ k, θ k ∈ Set.Icc
    (thetaD p c s k - cW p c α E s / Real.sqrt ((n : ℝ) * p * L))
    (thetaD p c s k + cW p c α E s / Real.sqrt ((n : ℝ) * p * L))}
noncomputable def boxReject {n L : ℕ} (p c α : ℝ) (E : Finset (Fin n × Fin n))
    (R : Set (Ranking n)) (s : Data n L) : Prop :=
  ∀ θ ∈ perturbBox p c α E s, ranking θ ∈ R
noncomputable def singleReject {n L : ℕ} (p c α : ℝ) (i : Fin n)
    (R : Set (Ranking n)) (s : Data n L) : Prop := boxReject p c α (star n i) R s

/-- (K+1)-th largest value, with K zero-based here: K=1 gives second largest. -/
noncomputable def orderValue {n : ℕ} (θ : Vec n) (K : Fin n) : ℝ :=
  θ ((ranking θ).symm K)
/-- The simplified test in E.2. K is the number of top items, so 1≤K<n. -/
noncomputable def topReject {n L : ℕ} (p c α : ℝ) (i : Fin n) (K : Fin n)
    (s : Data n L) : Prop :=
  thetaD p c s i - cW p c α (star n i) s / Real.sqrt ((n : ℝ) * p * L) >
    orderValue (thetaD p c s) K

noncomputable def familyReject {n L : ℕ} (p c α : ℝ) (R : Fin n → Set (Ranking n))
    (s : Data n L) (i : Fin n) : Prop := boxReject p c α Finset.univ (R i) s
noncomputable def fwer {n L : ℕ} (p : unitInterval) (c α : ℝ) (θ : Vec n)
    (R : Fin n → Set (Ranking n)) : ℝ :=
  (dataLaw L p θ {s | ∃ i, ranking θ ∉ R i ∧ familyReject p c α R s i}).toReal
noncomputable def familyTypeII {n L : ℕ} (p : unitInterval) (c α : ℝ) (θ : Vec n)
    (R : Fin n → Set (Ranking n)) : ℝ :=
  (dataLaw L p θ {s | ∃ i, ranking θ ∈ R i ∧ ¬familyReject p c α R s i}).toReal

/-- Infimum in [0,1], with 1 when the rejection set is empty. -/
noncomputable def pValue {n L : ℕ} (p c : ℝ) (i : Fin n) (R : Set (Ranking n))
    (s : Data n L) : ℝ :=
  sInf (insert 1 {α : ℝ | α ∈ Set.Ioo (0 : ℝ) 1 ∧ singleReject p c α i R s})
noncomputable def harmonic (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 1 n, 1 / (k : ℝ)
/-- Sort p-values ascending by sorting their negatives descending. -/
noncomputable def pOrder {n : ℕ} (pv : Fin n → ℝ) : Ranking n := ranking (-pv)
noncomputable def byCut {n : ℕ} (α : ℝ) (pv : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun k : Fin n =>
    pv ((pOrder pv).symm k) ≤ ((k.val+1 : ℕ) : ℝ) * α / ((n : ℝ) * harmonic n))).sup
      (fun k => k.val + 1)
noncomputable def byReject {n L : ℕ} (p c α : ℝ) (R : Fin n → Set (Ranking n))
    (s : Data n L) (i : Fin n) : Prop :=
  let pv := fun j => pValue p c j (R j) s
  (pOrder pv i).val < byCut α pv
noncomputable def nullCount {n : ℕ} (θ : Vec n) (R : Fin n → Set (Ranking n)) : ℕ :=
  (Finset.univ.filter (fun i => ranking θ ∉ R i)).card
noncomputable def fdr {n L : ℕ} (p : unitInterval) (c α : ℝ) (θ : Vec n)
    (R : Fin n → Set (Ranking n)) : ℝ :=
  ∫ s, let rejected := Finset.univ.filter (byReject p c α R s)
       let falsePos := rejected.filter (fun i => ranking θ ∉ R i)
       (falsePos.card : ℝ) / max (rejected.card : ℝ) 1 ∂dataLaw L p θ

/-- Exact sufficient expression from Remark D.1, pp. 53–54. -/
noncomputable def remarkB (n L : ℕ) (p : ℝ) : ℝ :=
  max (Real.sqrt ((n : ℝ)^2 * p * Real.log n / L))
    ((n : ℝ)^2 * p * Real.log ((n : ℝ)*L)^2 * Real.log n / L)
noncomputable def remarkR (n L : ℕ) (p cp : ℝ) : ℝ :=
  let B := remarkB n L p
  Real.sqrt B * Real.log n +
  B^(1/6 : ℝ) / (Real.log n)^(1/3 : ℝ) *
    max ((Real.log n + Real.log (Real.log n) - Real.log B / 2)^(2/3 : ℝ)) 1 +
  n * Real.log n * Real.sqrt (Real.log n / L) + (n : ℝ)^(-5 : ℤ) +
  (n : ℝ)^(1/4 : ℝ) * p^(1/8 : ℝ) *
    (Real.log n + (1+cp)*Real.log L)^(7/8 : ℝ) / (L : ℝ)^(1/8 : ℝ) +
  n * Real.sqrt p * Real.log n * (1+cp)*Real.log L *
    (Real.log n + (1+cp)*Real.log L)^(3/2 : ℝ) / Real.sqrt L + (L : ℝ)^(-cp)

end LagrangeRank.Debias.Supplement



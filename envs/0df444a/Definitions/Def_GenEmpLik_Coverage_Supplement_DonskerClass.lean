-- Prove2me | Definitions.Def_GenEmpLik_Coverage_Supplement_DonskerClass
-- name    : GenEmpLik_Coverage_Supplement_DonskerClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T23:11:42.736703+00:00
-- url     : https://prove2.me/theorems/05d788fa-b35a-426b-89db-402c178001cf
-- title:
--   Definition 3 — Donsker class and its tight Gaussian limit
-- statement:
--   A class $H=\{h_i:i\in I\}\subset L^2(P_0)$ is Donsker for the specified independent identically distributed sample when
--   $$\sqrt n(\widehat P_n-P_0)\rightsquigarrow\mathbb G\quad\text{in }\ell^\infty(I),$$
--   where $\mathbb G$ has a tight Borel law $\Gamma$. The limit is the centered Gaussian bridge with covariance
--   $$\operatorname{Cov}(\mathbb G h_i,\mathbb G h_j)=E_{P_0}[h_i h_j]-E_{P_0}[h_i]E_{P_0}[h_j].$$
--   The definition records the Gaussian finite-dimensional laws and covariance, which are already forced by the scalar central limit theorem. It supplies the full uniform central limit hypothesis for Theorems 9 and 10.
--
--   **Formalization Note** Independence, identical distribution and measurable samples are explicit theorem hypotheses. The predicate explicitly requires bounded population coordinates and an almost-everywhere identity with the actual empirical coordinates, allowing null-set modifications; both follow here from the absolute, finite-valued square-integrable envelope. The class may be uncountable, and the prelimit process may be nonmeasurable.
-- source:
--   Duchi, Glynn & Namkoong, Statistics of Robust Optimization: A Generalized Empirical Likelihood Approach, arXiv:1610.03425v3, pp. 21–22, Definition 3; 34, Definition 6

import Mathlib
import Definitions.Def_GenEmpLik_Coverage_Supplement_empiricalProcess

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace GenEmpLik.Coverage.Supplement

/-- Definition 3, p. 22: uniform empirical CLT to a tight Borel Brownian bridge.
The extra displayed moments specify its Gaussian law, already forced by the scalar CLT.
The population boundedness and almost-everywhere coordinate identity guarantee that
the process embeddings have their intended values; null-set modifications are permitted. -/
def IsDonskerWith {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Measure Ξ) (ξ : ℕ → Ω → Ξ) (h : ι → Ξ → ℝ)
    (Γ : Measure (ProcessSpace ι)) : Prop :=
  (∀ i, Measurable (h i) ∧ Integrable (fun z => h i z ^ 2) P) ∧
  Memℓp (fun i => ∫ z, h i z ∂P) ∞ ∧
  (∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < n → ∀ i,
    (empiricalProcess P ξ h n ω) i = Real.sqrt (n : ℝ) *
      (VarianceRegularization.Expansion.empMean (fun j : Fin n => h i (ξ j ω)) -
        ∫ z, h i z ∂P)) ∧
  IsProbabilityMeasure Γ ∧
  (∀ ε : ℝ, 0 < ε → ∃ K : Set (ProcessSpace ι), IsCompact K ∧ Γ Kᶜ < ENNReal.ofReal ε) ∧
  IsGaussianProcess (fun i (v : ProcessSpace ι) => v i) Γ ∧
  (∀ i, (∫ v, v i ∂Γ) = 0) ∧
  (∀ i j, covariance (fun v : ProcessSpace ι => v i) (fun v => v j) Γ =
    (∫ z, h i z * h j z ∂P) - (∫ z, h i z ∂P) * (∫ z, h j z ∂P)) ∧
  OuterWeakly μ (empiricalProcess P ξ h) Γ

/-- Existence of the limit of Definition 3. Envelopes used in Theorems 9–10
make the coordinate identity in IsDonskerWith automatic. -/
def IsDonsker {Ω Ξ ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (P : Measure Ξ) (ξ : ℕ → Ω → Ξ) (h : ι → Ξ → ℝ) : Prop :=
  ∃ Γ : Measure (ProcessSpace ι), IsDonskerWith μ P ξ h Γ

end GenEmpLik.Coverage.Supplement



-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002
-- name    : LevyStochCalc_Poisson_CompensatedDensityMarkSum_F002
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T09:16:08.46219+00:00
-- url     : https://prove2.me/theorems/91bfb749-35eb-400c-8b46-ea0d48de32b8
-- title:
--   Source declarations: LevyStochCalc.Poisson.CompensatedDensityMarkSum
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.CompensatedDensityMarkSum. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_CompensatedDensityBoxIsometry_F000
import Definitions.Def_SourceProof_399c828e93d99ff25ba00883
import Definitions.Def_SourceProof_95e88c3d19a2c672942f0f5a

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Itô–Lévy `L²` isometry (multi-mark, integrand form).** For a shared partition `p`
in `[0,T]`, arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[(∑ᵢ∑ₖ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = E[∫_E ∫_{[0,T]} eval² ds dν]` where
`eval(ω,s,e) = ∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·∑ₖ ξᵢₖ(ω)·𝟙_{Bₖ}(e)`. Both sides equal the
isometry sum-form (`markSumProcess_isometry`, `markSumProcess_L2_eq`). This is the
isometry in the textbook `E[(∫dÑ)²] = E[∫∫|φ|²]` form the `Lp`-limit consumes. -/
lemma markSumProcess_isometry_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k : Fin K,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P :=
  (_root_.Prove2MeSourceProof.h_399c828e93d99ff25ba00883 N ℱ hℱ p hp0 hpmono B hBm hBf ξ hξb hξm h_adapt).trans
    (_root_.Prove2MeSourceProof.h_95e88c3d19a2c672942f0f5a p hp0 hpmono hpleT B hBm hBf ξ hξb hξm).symm
/-- **Difference isometry (Cauchy engine).** For two adapted bounded coefficient families
`ξ, ξ'` on the same partition/marks,
`E[(I(ξ) − I(ξ'))²] = E[∫∫ (eval(ξ) − eval(ξ'))²]`, i.e. the `L²(P)` distance of the
two simple ("Euler") integrals equals the `L²(P⊗vol⊗ν)` distance of their integrands.
Immediate from `markSumProcess_isometry_L2` on the coefficient difference `ξ − ξ'`,
using `ℝ`-linearity of both the integral and the eval in the coefficients. -/
lemma markSumProcess_diff_isometry_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ ξ' : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξ'b : ∀ i k, ∃ M, ∀ ω, |ξ' i k ω| ≤ M)
    (hξm : ∀ i k, Measurable (ξ i k)) (hξ'm : ∀ i k, Measurable (ξ' i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k))
    (h_adapt' : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ' i k)) :
    ∫ ω, ((∑ i : Fin N₀, ∑ k : Fin K,
          ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
        - (∑ i : Fin N₀, ∑ k : Fin K,
          ξ' i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, (ξ i k ω - ξ' i k ω) * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P := by
  -- bounds/measurability/adaptedness of the difference coefficients.
  have hηb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω - ξ' i k ω| ≤ M := by
    intro i k; obtain ⟨M, hM⟩ := hξb i k; obtain ⟨M', hM'⟩ := hξ'b i k
    exact ⟨M + M', fun ω => (abs_sub _ _).trans (add_le_add (hM ω) (hM' ω))⟩
  have hηm : ∀ i k, Measurable (fun ω => ξ i k ω - ξ' i k ω) :=
    fun i k => (hξm i k).sub (hξ'm i k)
  have hηa : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc))
      (fun ω => ξ i k ω - ξ' i k ω) := fun i k => (h_adapt i k).sub (h_adapt' i k)
  have key := markSumProcess_isometry_L2 p hp0 hpmono hpleT N ℱ hℱ B hBm hBf
    (fun i k ω => ξ i k ω - ξ' i k ω) hηb hηm hηa
  rw [show (fun ω => ((∑ i : Fin N₀, ∑ k : Fin K,
            ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
          - (∑ i : Fin N₀, ∑ k : Fin K,
            ξ' i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)) ^ 2)
        = fun ω => (∑ i : Fin N₀, ∑ k : Fin K,
            (ξ i k ω - ξ' i k ω)
              * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 from by
      funext ω
      congr 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  exact key
/-- **`L²`-limit of a Cauchy sequence of integrands/integrals.** If `Mₙ ∈ L²(P)` and the
`Lp` lifts form a Cauchy sequence, there is an `M ∈ L²(P)` with `eLpNorm(Mₙ − M) → 0`.
Lp completeness + `tendsto_Lp_iff_tendsto_eLpNorm''`. The "define the integral as the
`L²`-limit" half of the masterApprox construction. -/
lemma exists_L2_limit_of_memLp_cauchySeq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Mₙ : ℕ → Ω → ℝ} (hmem : ∀ n, MeasureTheory.MemLp (Mₙ n) 2 P)
    (hcs : CauchySeq (fun n => (hmem n).toLp (Mₙ n))) :
    ∃ M : Ω → ℝ, MeasureTheory.MemLp M 2 P ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Mₙ n - M) 2 P) Filter.atTop (nhds 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨g, MeasureTheory.Lp.memLp g, ?_⟩
  rw [← MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Mₙ hmem (↑↑g)
    (MeasureTheory.Lp.memLp g)]
  rwa [MeasureTheory.Lp.toLp_coeFn g (MeasureTheory.Lp.memLp g)]
end LevyStochCalc.Poisson.Compensated



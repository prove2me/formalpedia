-- Prove2me | Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
-- name    : LevyStochCalc_Brownian_CrossOrthogonalityLimit_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:19:08.537524+00:00
-- url     : https://prove2.me/theorems/11c6d6b5-cfe5-4327-8efd-40255b7dbde2
-- title:
--   Source declarations: LevyStochCalc.Brownian.CrossOrthogonalityLimit
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Brownian.CrossOrthogonalityLimit. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_CrossOrthogonalityLimit_F000
import Definitions.Def_SourceProof_1cb4c7ea0c92fae7e2063274

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

Cross terms over intervals in any relative position reduce to the direct cross identity by
splitting at the later left endpoint, so elementary integrals against two distinct coordinates
`Wⁱ` and `Wʲ` of a `d`-dimensional Brownian motion have zero pairing. Continuity of the `L²`
pairing carries that vanishing to the limit along approximating simple integrands, giving the
orthogonality in `L²` of the Itô integrals against `Wⁱ` and against `Wʲ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

/-- **The cross term vanishes.** For distinct coordinates the two increments are uncorrelated
against bounded coefficients measurable at the left endpoints, in either order. -/
theorem integral_cross_increment_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpq : p < q) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact _root_.Prove2MeSourceProof.h_1cb4c7ea0c92fae7e2063274 W hij hcoord hp hr hrv hpr hξ hξm hξb hη hηm hηb
  · have h := _root_.Prove2MeSourceProof.h_1cb4c7ea0c92fae7e2063274 W hij.symm hcoord (q := v) hr hp hpq hrp.le
      hη hηm hηb hξ hξm hξb
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
/-- A single clamped cross term is integrable and has zero mean. -/
lemma integrable_and_integral_cross_clamped (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hpq : p < q)
    (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
    ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0 := by
  rcases min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
        * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
          * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
        funext ω; rw [hc']; ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨integrable_cross_term (W.W i) (W.W j) hp hplt.le hr hrlt.le hξm hηm hξb hηb,
        integral_cross_increment_eq_zero W hij hcoord hp hr hrlt hplt hξ hξm hξb hη hηm hηb⟩
/-- **Orthogonality on simple integrands.** Elementary integrals against distinct Brownian
coordinates have zero pairing, at any pair of times. -/
theorem integral_simpleIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
    (H : SimplePredictable Ω TH)
    (K : SimplePredictable Ω TK)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
    (t t' : ℝ) :
    ∫ ω, simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hKnn : ∀ b : Fin K.N, 0 ≤ K.partition b.castSucc := fun b => by
    have h := K.partition_strictMono.monotone (Fin.zero_le b.castSucc)
    rwa [K.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have hKlt : ∀ b : Fin K.N, K.partition b.castSucc < K.partition b.succ := fun b =>
    K.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (b : Fin K.N),
      Integrable (fun ω => (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω))) P
      ∧ ∫ ω, (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) ∂P = 0 := by
    intro a b
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := K.ξ_bounded b
    exact integrable_and_integral_cross_clamped W hij hcoord (hHnn a) (hHlt a) (hKnn b) (hKlt b)
      (hH a) (H.ξ_measurable a) hMξ (hK b) (K.ξ_measurable b) hMη t t'
  have hexp : (fun ω => simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ b : Fin K.N,
        (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) := by
    funext ω
    rw [simpleIntegral, simpleIntegral]
    exact Finset.sum_mul_sum _ _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (key a b).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (key a b).1]
  exact Finset.sum_eq_zero fun b _ => (key a b).2
end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian



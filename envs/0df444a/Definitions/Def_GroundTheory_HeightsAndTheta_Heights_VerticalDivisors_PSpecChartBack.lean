-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
-- name    : GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartBack
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:47.307967+00:00
-- url     : https://prove2.me/theorems/53ba3275-6487-474c-84d3-8a38840c5354
-- title:
--   PSpec Chart Back
-- statement:
--   Definitions and structural lemmas for PSpec Chart Back, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecChartBack.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecChartIso
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_C_toBase_mem_Q_0755be110dc4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_90452924d03a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___C_e65327d6784a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_04365f072597
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart___X_30d1d988806a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_baseToBn_toBase_2f2e4d6deddf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inl_e5d50e568d36
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_sum_val_inr_a6548b36d2a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SpecChart_val_free_5c8e5b809709

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
set_option linter.unusedSectionVars false
namespace SpecChart
variable {K : Type} [Field K] [NumberField K] {n e : ℕ} {I : Ideal (MvPolynomial (Fin n) K)} {j : Fin n}
  {v : HeightOneSpectrum (𝓞 K)} {W : Ideal (MvPolynomial (Fin n) (𝓞 K))}
section Back
variable [(Q e I j W).IsPrime]
def ρ (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    ParDVR e n v →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl)
    (g := (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (σ e I j)) fun s => by
      rw [RingHom.comp_apply, ← IsLocalRing.notMem_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
      exact hσ s s.2
theorem ρ_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (s : MvPolynomial (Par e n) (𝓞 K)) :
    ρ hσ (algebraMap _ (ParDVR e n v) s) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (σ e I j s) :=
  IsLocalization.lift_eq _ _
theorem ρ_parY (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) (p : Par e n) :
    ρ hσ (parY e n v p) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (val e I j p) := by
  rw [parY, ρ_algebraMap, σ_X]
def G' (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    MvPolynomial (Fin n) (ParDVR e n v) →+* Localization.AtPrime (Q e I j W) :=
  eval₂Hom (ρ hσ) fun l => algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (cx e I j l)
theorem G'_map (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) :
    G' hσ (g.map (algebraMap (𝓞 K) (ParDVR e n v))) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  have h : (G' hσ).comp (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v))) =
      (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp (C.comp (toBase I j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, map_C, G', eval₂Hom_C]
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
        ρ_algebraMap, MvPolynomial.algebraMap_eq, σ_C]
    · intro l
      simp only [RingHom.comp_apply, map_X, G', eval₂Hom_X', cx]
  exact RingHom.congr_fun h g
theorem G'_kills (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    secIdeal (modelR e I v) (parY e n v) ≤ RingHom.ker (G' hσ) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [modelR, Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, RingHom.mem_ker, G'_map, toBase, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hg, map_zero, map_zero, map_zero]
  · rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    rw [SetLike.mem_coe, RingHom.mem_ker, secForm, linForm, map_sum]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inl e I j i)
    simpa only [map_sum, map_mul, map_zero] using h
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    rw [SetLike.mem_coe, RingHom.mem_ker, chartForm, linForm, map_sub, map_sum, map_one]
    simp only [map_mul, G', eval₂Hom_C, eval₂Hom_X', ρ_parY]
    have h := congrArg (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))) (sum_val_inr e I j)
    simpa only [map_sum, map_mul, map_sub, map_one, map_zero] using h
def G (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W) :
    SecB e I v →+* Localization.AtPrime (Q e I j W) :=
  Ideal.Quotient.lift _ (G' hσ) fun _ ha => RingHom.mem_ker.mp (G'_kills hσ ha)
theorem G_toSecB (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (g : MvPolynomial (Fin n) (𝓞 K)) : G hσ (toSecB e I v g) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g)) := by
  rw [toSecB, RingHom.comp_apply, G, Ideal.Quotient.lift_mk, G'_map]
theorem G_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (r : ParDVR e n v) : G hσ (algebraMap _ (SecB e I v) r) = ρ hσ r := by
  rw [← Ideal.Quotient.mk_algebraMap, G, Ideal.Quotient.lift_mk, MvPolynomial.algebraMap_eq, G', eval₂Hom_C]
theorem G_mem (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    {𝔫 : Ideal (SecB e I v)} (h𝔫 : W.map (toSecB e I v) = 𝔫) {b : SecB e I v} (hb : b ∈ 𝔫) :
    G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← h𝔫] at hb
  have h : W.map (toSecB e I v) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (G hσ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, Ideal.mem_comap, G_toSecB, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)]
    exact C_toBase_mem_Q e j hw
  exact h hb
variable {𝔫 : Ideal (SecB e I v)} [𝔫.IsPrime]
def Gloc (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    Localization.AtPrime 𝔫 →+* Localization.AtPrime (Q e I j W) :=
  IsLocalization.lift (M := 𝔫.primeCompl) (g := G hσ) fun b =>
    IsLocalRing.notMem_maximalIdeal.mp fun h => b.2 (hG _ h)
theorem Gloc_algebraMap (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (b : SecB e I v) : Gloc hσ hG (algebraMap _ _ b) = G hσ b :=
  IsLocalization.lift_eq _ _
theorem Gloc_max (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) {x : Localization.AtPrime 𝔫}
    (hx : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime 𝔫)) :
    Gloc hσ hG x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal] at hx
  have h : 𝔫.map (algebraMap (SecB e I v) (Localization.AtPrime 𝔫)) ≤
      (IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W))).comap (Gloc hσ hG) := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap, Gloc_algebraMap]
    exact G_mem hσ h𝔫 hb
  exact h hx
theorem Gloc_Φ (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫) :
    (Gloc hσ hG).comp (Φ hj) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) := by
  apply MvPolynomial.ringHom_ext
  · intro b
    simp only [RingHom.comp_apply, Φ_C]
    have h : (Gloc hσ hG).comp (baseToBn hj) =
        (algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W))).comp C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (integralModel I) (X j)))
      apply Ideal.Quotient.ringHom_ext
      refine RingHom.ext fun g => ?_
      change Gloc hσ hG (baseToBn hj (toBase I j g)) = algebraMap (Poly e I j) (Localization.AtPrime (Q e I j W)) (C (toBase I j g))
      rw [baseToBn_toBase, Gloc_algebraMap, G_toSecB]
    exact RingHom.congr_fun h b
  · intro y
    simp only [RingHom.comp_apply, Φ_X, parB, Gloc_algebraMap, G_algebraMap, ρ_parY, val_free]
theorem Φ_isUnit (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) (c : Poly e I j) (hc : c ∈ (Q e I j W).primeCompl) :
    IsUnit (Φ hj c) := by
  by_contra hu
  rw [← IsLocalRing.notMem_maximalIdeal, not_not] at hu
  have h2 := Gloc_max hσ hG h𝔫 hu
  rw [← RingHom.comp_apply, Gloc_Φ, IsLocalization.AtPrime.to_map_mem_maximal_iff _ (Q e I j W)] at h2
  exact hc h2
def Φloc (hj : toSecB e I v (X j) ∉ 𝔫)
    (hσ : ∀ s ∈ (parPrime e n v).primeCompl, σ e I j s ∉ Q e I j W)
    (hG : ∀ b, G hσ b ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (Q e I j W)) → b ∈ 𝔫)
    (h𝔫 : W.map (toSecB e I v) = 𝔫) : Localization.AtPrime (Q e I j W) →+* Localization.AtPrime 𝔫 :=
  IsLocalization.lift (M := (Q e I j W).primeCompl) (g := Φ hj) fun c => Φ_isUnit hj hσ hG h𝔫 c c.2
end Back
end SpecChart
end
end GroundTheory.Heights₂.Heights.Vertical



-- Prove2me | Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
-- name    : GroundTheory_GlobalFields_TateThesis_HeckeLFunction
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:08.561813+00:00
-- url     : https://prove2.me/theorems/1a5fa107-8e4d-43d2-b074-9a75273ef0ba
-- title:
--   Hecke LFunction
-- statement:
--   Definitions and structural lemmas for Hecke LFunction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply


set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
namespace GroundTheory.Global
noncomputable section
section Factored
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
def factoredIdeals (S : Finset (HeightOneSpectrum R)) : Set (Ideal R) :=
  {I | I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum R, v.asIdeal ∣ I → v ∈ S}
end Factored
section Euler
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)
end Euler
section Summable
variable {K : Type*} [Field K] [NumberField K]
end Summable
section Coprime
variable {K : Type*} [Field K] [NumberField K]
omit [NumberField K] in
theorem not_dvd_of_isCoprime {I 𝔪 : Ideal (𝓞 K)} (h : IsCoprime I 𝔪)
    {v : HeightOneSpectrum (𝓞 K)} (hv : v.asIdeal ∣ 𝔪) : ¬ v.asIdeal ∣ I := by
  intro hI
  rw [Ideal.isCoprime_iff_sup_eq] at h
  exact v.isPrime.ne_top (top_le_iff.1 (h ▸ sup_le (Ideal.le_of_dvd hI) (Ideal.le_of_dvd hv)))
theorem count_coeIdeal_eq_zero {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {v : HeightOneSpectrum (𝓞 K)}
    (hv : ¬ v.asIdeal ∣ I) : count K v (I : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  have hI0 : I ≠ 0 := by simpa [Submodule.zero_eq_bot] using hI
  rw [count_coe K v hI0, Nat.cast_eq_zero]
  by_contra h
  exact hv ((Associates.count_ne_zero_iff_dvd hI0 (HeightOneSpectrum.prime v).irreducible).1 h)
def idealUnit (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K) (coeIdeal_ne_zero.2 hI)
theorem idealUnit_mem_idealsPrimeTo {I 𝔪 : Ideal (𝓞 K)} (hI : I ≠ ⊥) (h : IsCoprime I 𝔪) :
    idealUnit I hI ∈ idealsPrimeTo 𝔪 :=
  fun _ hv ↦ count_coeIdeal_eq_zero hI (not_dvd_of_isCoprime h hv)
end Coprime
namespace HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)
open Classical in

def coeff (I : Ideal (𝓞 K)) : ℂ :=
  if h : I ≠ ⊥ ∧ IsCoprime I χ.conductor then
    (χ.idealCharacter ⟨idealUnit I h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : ℂ)
  else 0
theorem coeff_of_not {I : Ideal (𝓞 K)} (h : ¬ (I ≠ ⊥ ∧ IsCoprime I χ.conductor)) :
    χ.coeff I = 0 :=
  dif_neg h
@[simp]
theorem coeff_bot : χ.coeff ⊥ = 0 :=
  χ.coeff_of_not fun h ↦ h.1 rfl
@[simp]
theorem coeff_top : χ.coeff ⊤ = 1 := by
  have h : (⊤ : Ideal (𝓞 K)) ≠ ⊥ ∧ IsCoprime (⊤ : Ideal (𝓞 K)) χ.conductor :=
    ⟨top_ne_bot, by rw [← Ideal.one_eq_top]; exact isCoprime_one_left⟩
  rw [coeff, dif_pos h]
  have h1 : (⟨idealUnit ⊤ h.1, idealUnit_mem_idealsPrimeTo h.1 h.2⟩ : idealsPrimeTo χ.conductor) =
      1 :=
    Subtype.ext (Units.ext (by simp [idealUnit]))
  rw [h1, map_one, Circle.coe_one]
theorem coeff_mul (I J : Ideal (𝓞 K)) : χ.coeff (I * J) = χ.coeff I * χ.coeff J := by
  by_cases hI : I ≠ ⊥ ∧ IsCoprime I χ.conductor
  · by_cases hJ : J ≠ ⊥ ∧ IsCoprime J χ.conductor
    · have hIJ : I * J ≠ ⊥ ∧ IsCoprime (I * J) χ.conductor :=
        ⟨fun h ↦ (Ideal.mul_eq_bot.1 h).elim hI.1 hJ.1, hI.2.mul_left hJ.2⟩
      rw [coeff, coeff, coeff, dif_pos hI, dif_pos hJ, dif_pos hIJ, ← Circle.coe_mul, ← map_mul]
      congr 2
      exact Subtype.ext (Units.ext (by simp [idealUnit, coeIdeal_mul]))
    · rw [χ.coeff_of_not hJ, mul_zero]
      refine χ.coeff_of_not fun h ↦ hJ ⟨fun hJ0 ↦ h.1 (by rw [hJ0, Ideal.mul_bot]), ?_⟩
      exact (IsCoprime.mul_left_iff.1 h.2).2
  · rw [χ.coeff_of_not hI, zero_mul]
    refine χ.coeff_of_not fun h ↦ hI ⟨fun hI0 ↦ h.1 (by rw [hI0, Ideal.bot_mul]), ?_⟩
    exact (IsCoprime.mul_left_iff.1 h.2).1
def coeffTerm (s : ℂ) : Ideal (𝓞 K) →* ℂ where
  toFun I := χ.coeff I / (absNorm I : ℂ) ^ s
  map_one' := by
    rw [Ideal.one_eq_top, coeff_top, Ideal.absNorm_top, Nat.cast_one, Complex.one_cpow, _root_.div_one]
  map_mul' I J := by
    rw [coeff_mul, map_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]
def LCoeff (n : ℕ) : ℂ :=
  ∑' I : {I : Ideal (𝓞 K) // absNorm I = n}, χ.coeff I
def LFunction (s : ℂ) : ℂ :=
  LSeries χ.LCoeff s
end HeckeCharacter
end
end GroundTheory.Global



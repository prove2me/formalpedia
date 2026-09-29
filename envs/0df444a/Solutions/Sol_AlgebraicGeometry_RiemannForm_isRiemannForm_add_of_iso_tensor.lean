-- Prove2me | solution 1 for AlgebraicGeometry.RiemannForm.isRiemannForm_add_of_iso_tensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/38268aad-805a-51c9-9d1e-14272f0a2efa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_MonoidalV2
import Theorems.Thm_AlgebraicGeometry_RiemannForm_isLevelPairingValue_mul_of_iso_tensor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RiemannForm CategoryTheory.MonoidalCategory"

theorem solution
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (ζ : ℕ → k) (hζ : ∀ n : ℕ, IsPrimitiveRoot (ζ n) (ℓ ^ n)) (hζℓ : ∀ n : ℕ, ζ (n + 1) ^ ℓ = ζ n)
    (e : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he : IsRiemannForm f L hc 𝓛 ℓ ζ e)
    (𝓜 : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜)
    (e' : TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] TateModule ℓ (L.AlgPoints hc k) →ₗ[ℤ_[ℓ]] ℤ_[ℓ])
    (he' : IsRiemannForm f L hc 𝓜 ℓ ζ e')
    (𝓝 : A.Modules) (h𝓝 : Nonempty (𝓝 ≅ 𝓛 ⊗ 𝓜)) :
    IsRiemannForm f L hc 𝓝 ℓ ζ (e + e') := by
  intro n a b
  have hn : ((ℓ ^ n : ℕ) : k) ≠ 0 := by exact_mod_cast pow_ne_zero n hℓ
  have hta : (ℓ ^ n) • ((a : ℕ → L.AlgPoints hc k) n) = 0 := by
    have h__af := TateModule.torsion a n
    simp [Nat.cast_smul_eq_nsmul] at h__af
    exact h__af
  have htb : (ℓ ^ n) • ((b : ℕ → L.AlgPoints hc k) n) = 0 := by
    have h__af := TateModule.torsion b n
    simp [Nat.cast_smul_eq_nsmul] at h__af
    exact h__af
  have h := AlgebraicGeometry.RiemannForm.isLevelPairingValue_mul_of_iso_tensor k f L hc hA 𝓛 h𝓛 𝓜 h𝓜 𝓝 h𝓝 (ℓ ^ n) hn
    _ _ hta htb _ _ (he n a b) (he' n a b)

  have hexp : ζ n ^ (e a b).appr n * ζ n ^ (e' a b).appr n = ζ n ^ ((e + e') a b).appr n := by
    have hmod : ((e a b).appr n + (e' a b).appr n) ≡ ((e + e') a b).appr n [MOD ℓ ^ n] := by
      rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_add]
      change PadicInt.toZModPow n (e a b) + PadicInt.toZModPow n (e' a b) = PadicInt.toZModPow n ((e + e') a b)
      rw [← map_add]
      simp only [LinearMap.add_apply]
    have hpm : ∀ m : ℕ, ζ n ^ m = ζ n ^ (m % ℓ ^ n) := fun m => by
      conv_rhs => rw [(hζ n).eq_orderOf, pow_mod_orderOf]
    rw [← pow_add, hpm ((e a b).appr n + (e' a b).appr n), hpm (((e + e') a b).appr n)]
    exact congrArg _ hmod
  rw [← hexp]
  exact h

end S_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor
end P2MW
export P2MW.S_AlgebraicGeometry_RiemannForm_isRiemannForm_add_of_iso_tensor (solution)

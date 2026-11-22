-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:17.555657+00:00
-- url     : https://prove2.me/theorems/46f5337c-c4b8-40de-aaa0-f8444ae620a8
-- title:
--   Ext PPow Le Span Sup
-- statement:
--   Definitions and structural lemmas for Ext PPow Le Span Sup, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtPPowLeSpanSup.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSqAbsNormOfInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
section DedekindLFunctions
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {P : Ideal R}
end DedekindLFunctions
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
theorem coe_iota_eq_algebraMap_coe (a : 𝓞 F) : ((ι a : 𝓞 K) : K) = algebraMap F K (a : F) := by
  first
  | rfl
  | exact (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K a).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K a)
theorem coe_conjO_eq_star_coe (z : 𝓞 K) : ((conjO K z : 𝓞 K) : K) = star (z : K) := by
  first
  | rfl
  | (unfold conjO; rfl)
theorem conjO_map (hF : IsFixF K F) (a : 𝓞 F) : conjO K (ι a) = ι a := by
  apply RingOfIntegers.ext
  rw [coe_conjO_eq_star_coe, coe_iota_eq_algebraMap_coe]
  exact (hF _).mpr ⟨_, rfl⟩
theorem exists_iota_eq_of_star_coe_eq (hF : IsFixF K F) (w : 𝓞 K) (hw : star (w : K) = (w : K)) :
    ∃ a : 𝓞 F, ι a = w := by
  obtain ⟨f, hf⟩ := (hF _).mp hw
  have hfi : IsIntegral ℤ f := by
    have h1 : IsIntegral ℤ (algebraMap F K f) := by
      rw [hf]
      exact RingOfIntegers.isIntegral_coe w
    exact (isIntegral_algHom_iff ((algebraMap F K).toIntAlgHom) (algebraMap F K).injective).mp h1
  refine ⟨⟨f, by
    first
    | exact hfi
    | exact (mem_integralClosure_iff ℤ F).mpr hfi
    | exact (NumberField.mem_ringOfIntegers F f).mpr hfi
    | simpa [integralClosure] using hfi⟩, ?_⟩
  apply RingOfIntegers.ext
  exact (coe_iota_eq_algebraMap_coe _).trans hf
theorem exists_tr (hF : IsFixF K F) (z : 𝓞 K) : ∃ a : 𝓞 F, ι a = z + conjO K z := by
  apply exists_iota_eq_of_star_coe_eq hF
  have e : ((z + conjO K z : 𝓞 K) : K) = (z : K) + star (z : K) := by
    rw [← coe_conjO_eq_star_coe]
    rfl
  rw [e, star_add, star_star, add_comm]
theorem ι_inj : Function.Injective (ι) := by
  intro a b hab
  have h : Ideal.comap ι (Ideal.map ι (⊥ : Ideal (𝓞 F))) = ⊥ :=
    Ideal.comap_map_eq_self_of_faithfullyFlat _
  rw [Ideal.map_bot] at h
  have h1 : a - b ∈ Ideal.comap ι (⊥ : Ideal (𝓞 K)) := by
    rw [Ideal.mem_comap, map_sub, hab, sub_self]
    exact Ideal.zero_mem _
  rw [h, Ideal.mem_bot, sub_eq_zero] at h1
  exact h1
def trf (hF : IsFixF K F) (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_tr hF z)
theorem trf_spec (hF : IsFixF K F) (z : 𝓞 K) : ι (trf hF z) = z + conjO K z := Classical.choose_spec (exists_tr hF z)
def trF (hF : IsFixF K F) : 𝓞 K →ₗ[𝓞 F] 𝓞 F where
  toFun z := trf hF z
  map_add' x y := by
    apply ι_inj (K := K)
    rw [map_add, trf_spec, trf_spec, trf_spec, map_add]
    ring
  map_smul' a x := by
    apply ι_inj (K := K)
    rw [RingHom.id_apply, smul_eq_mul, map_mul, trf_spec, trf_spec, Algebra.smul_def, map_mul,
      conjO_map hF]
    ring
end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds



-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
-- name    : Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:33:48.173861+00:00
-- url     : https://prove2.me/theorems/e61e5d14-58cb-4525-9e5b-b3fd35b2b158
-- title:
--   Exists Det Equiv Of Subsingleton
-- statement:
--   Definitions and structural lemmas for Exists Det Equiv Of Subsingleton, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/ExistsDetEquivOfSubsingleton.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Theorems.Thm_GlobalTheory_SymAlg_baseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SymAlg.baseChangeEquiv_tmul


set_option autoImplicit false
open TensorProduct Module Function
namespace GlobalTheory
namespace TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
variable (R H) in

noncomputable def wedgeMul (a b : ℕ) : (⋀[R]^a H) ⊗[R] (⋀[R]^b H) →ₗ[R] ⋀[R]^(a + b) H :=
  LinearMap.codRestrict _
    (LinearMap.mul' R (ExteriorAlgebra R H) ∘ₗ
      TensorProduct.map (⋀[R]^a H).subtype (⋀[R]^b H).subtype) fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul x.2 y.2
@[simp] theorem coe_wedgeMul_tmul {a b : ℕ} (x : ⋀[R]^a H) (y : ⋀[R]^b H) :
    (wedgeMul R H a b (x ⊗ₜ y) : ExteriorAlgebra R H) = (x : ExteriorAlgebra R H) * y := rfl
noncomputable def wedgeMap (i : F →ₗ[R] H) (s : L →ₗ[R] H) (a b : ℕ) :
    (⋀[R]^a F) ⊗[R] (⋀[R]^b L) →ₗ[R] ⋀[R]^(a + b) H :=
  wedgeMul R H a b ∘ₗ TensorProduct.map (exteriorPower.map a i) (exteriorPower.map b s)
section Exact
variable {i : F →ₗ[R] H} {π : H →ₗ[R] L}
end Exact
section Dual
theorem pairingDual_map_dualMap (φ : F →ₗ[R] H) (n : ℕ) (ξ : ⋀[R]^n (Dual R H)) :
    exteriorPower.pairingDual R F n (exteriorPower.map n φ.dualMap ξ) =
      (exteriorPower.map n φ).dualMap (exteriorPower.pairingDual R H n ξ) := by
  have : exteriorPower.pairingDual R F n ∘ₗ exteriorPower.map n φ.dualMap =
      (exteriorPower.map n φ).dualMap ∘ₗ exteriorPower.pairingDual R H n := by
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun f => ?_
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun v => ?_
    simp
  exact LinearMap.congr_fun this ξ
theorem pairingDual_bijective_of_basis {κ : Type*} [Finite κ] [LinearOrder κ] (b : Basis κ R F)
    (n : ℕ) : Bijective (exteriorPower.pairingDual R F n) := by
  classical
  have : exteriorPower.pairingDual R F n =
      ((b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)).toLinearMap := by
    refine (b.dualBasis.exteriorPower n).ext fun s => ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, Basis.coe_dualBasis,
      exteriorPower.basis_coord, exteriorPower.basis_apply, Basis.coe_dualBasis]
    rfl
  rw [this]
  exact LinearEquiv.bijective _
variable (R F) in

theorem pairingDual_bijective [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    Bijective (exteriorPower.pairingDual R F n) := by
  obtain ⟨k, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R F
  have hb := pairingDual_bijective_of_basis (Pi.basisFun R (Fin k)) n
  have h₁ : ∀ ξ : ⋀[R]^n (Dual R F),
      exteriorPower.map n g.dualMap (exteriorPower.map n f.dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap, hfg,
      LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply]
  have h₂ : ∀ ξ : Dual R (⋀[R]^n F),
      (exteriorPower.map n g).dualMap ((exteriorPower.map n f).dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← exteriorPower.map_comp, hfg,
      exteriorPower.map_id, LinearMap.dualMap_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    rw [← h₁ x, ← h₁ y]
    congr 1
    apply hb.1
    rw [pairingDual_map_dualMap, pairingDual_map_dualMap, hxy]
  · intro ξ
    obtain ⟨x, hx⟩ := hb.2 ((exteriorPower.map n f).dualMap ξ)
    exact ⟨exteriorPower.map n g.dualMap x, by rw [pairingDual_map_dualMap, hx, h₂]⟩
variable (R F) in

noncomputable def dualEquiv [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    (⋀[R]^n (Dual R F)) ≃ₗ[R] Dual R (⋀[R]^n F) :=
  LinearEquiv.ofBijective _ (pairingDual_bijective R F n)
end Dual
end TopExt
end GlobalTheory



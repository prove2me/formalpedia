-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ShortExactMulPrimeZmodTensorComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:07.764331+00:00
-- url     : https://prove2.me/theorems/cc9a8159-15e7-4b76-9705-aa2b9c0ae0c3
-- title:
--   Short Exact Mul Prime Zmod Tensor Complex
-- statement:
--   Definitions and structural lemmas for Short Exact Mul Prime Zmod Tensor Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ShortExactMulPrimeZmodTensorComplex.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
noncomputable section
namespace GlobalTheory
abbrev pMultiples (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] : Submodule ℤ M :=
  LinearMap.range ((p : ℤ) • LinearMap.id : M →ₗ[ℤ] M)
lemma zmultiples_mkQ_p (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    zmultiplesHom (M →+ M ⧸ pMultiples p M) (pMultiples p M).mkQ.toAddMonoidHom (p : ℤ) = 0 := by
  ext m
  simp only [zmultiplesHom_apply, AddMonoidHom.coe_smul, Pi.smul_apply, AddMonoidHom.zero_apply]
  show (p : ℤ) • Submodule.Quotient.mk m = (0 : M ⧸ pMultiples p M)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨m, by simp⟩
def modPPairing (p : ℕ) (M : Type) [AddCommGroup M] [Module ℤ M] :
    ZMod p →+ M →+ (M ⧸ pMultiples p M) :=
  ZMod.lift p ⟨zmultiplesHom _ (pMultiples p M).mkQ.toAddMonoidHom, zmultiples_mkQ_p p M⟩
abbrev zmodOverInt (p : ℕ) : ModuleCat.{0} ℤ :=
  (ModuleCat.restrictScalars (Int.castRingHom (ZMod p))).obj (ModuleCat.of (ZMod p) (ZMod p))
def tensorToModP (p : ℕ) (M : ModuleCat.{0} ℤ) :
    TensorProduct ℤ (zmodOverInt p) M →+ (M ⧸ pMultiples p M) :=
  TensorProduct.liftAddHom (modPPairing p M) (fun r a m => by
    have key : ∀ b : ZMod p, modPPairing p M ((r : ZMod p) * b) m = r • modPPairing p M b m := by
      intro b
      rw [← zsmul_eq_mul, map_zsmul]
      rfl
    refine (key a).trans ?_
    rw [← map_zsmul]
    congr 1
    exact (int_smul_eq_zsmul _ r m).symm)
end GlobalTheory
end
noncomputable section
namespace GlobalTheory
def oneZ (p : ℕ) : zmodOverInt p := (1 : ZMod p)
end GlobalTheory
end



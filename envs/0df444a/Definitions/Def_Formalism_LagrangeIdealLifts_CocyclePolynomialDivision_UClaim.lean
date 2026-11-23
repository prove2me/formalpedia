-- Prove2me | Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
-- name    : Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:38.679616+00:00
-- url     : https://prove2.me/theorems/c9bc4b79-d815-4b1c-a3b6-305ad3c9b6d2
-- title:
--   UClaim
-- statement:
--   Definitions and structural lemmas for UClaim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LagrangeIdealLifts/CocyclePolynomialDivision/UClaim.lean

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.LIFT
namespace CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
def QS : Submodule A D where
  carrier := {y | W.QInv y}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, WD.QInv, smul_add] at *
    exact W.N.add_mem ha hb
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, WD.QInv, smul_zero]
    exact W.N.zero_mem
  smul_mem' c y hy := by
    simp only [Set.mem_ofPred_eq, WD.QInv] at *
    rw [smul_smul, mul_comm, mul_smul]
    exact W.N.smul_mem c hy
def CS : Submodule A D where
  carrier := {ω | W.C2 ω}
  add_mem' := by
    rintro a b ⟨y1, h1, rfl⟩ ⟨y2, h2, rfl⟩
    exact ⟨y1 + y2, (QS W).add_mem h1 h2, (smul_add _ _ _).symm⟩
  zero_mem' := ⟨0, (QS W).zero_mem, (smul_zero _).symm⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    exact ⟨c • y, (QS W).smul_mem c hy, by rw [smul_smul, smul_smul, mul_comm]⟩
end CocyclePolynomialSubmodules
end Formalism.LIFT



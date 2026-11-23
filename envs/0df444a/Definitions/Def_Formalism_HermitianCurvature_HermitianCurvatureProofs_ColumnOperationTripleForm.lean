-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:33.563337+00:00
-- url     : https://prove2.me/theorems/68383606-2228-415d-97d0-3b9626b69337
-- title:
--   Column Operation Triple Form
-- statement:
--   Definitions and structural lemmas for Column Operation Triple Form, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ColumnOperationTripleForm.lean

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val


set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
namespace Formalism.FourierDecayAlt.P.A5x2
open Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
section
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
theorem psiKR_mk (hψ : ∀ r ∈ R, ψ r = 1) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a) = ψ a := by
  unfold psiKR
  have h1 : (Submodule.Quotient.mk (Quotient.out (Submodule.Quotient.mk a : KR R)) : KR R)
      = Submodule.Quotient.mk a := Quotient.out_eq _
  rw [Submodule.Quotient.eq] at h1
  obtain ⟨r, hr⟩ := h1
  have h2 : Quotient.out (Submodule.Quotient.mk a : KR R) = a + (r : K) := by
    have : (r : K) = Quotient.out (Submodule.Quotient.mk a : KR R) - a := hr
    rw [this]; ring
  rw [h2, AddChar.map_add_eq_mul, hψ r r.2, mul_one]
noncomputable def psiB (hψ : ∀ r ∈ R, ψ r = 1) : AddChar (KR R) ℂ where
  toFun := psiKR R ψ
  map_zero_eq_one' := by
    have := psiKR_mk R ψ hψ 0
    rw [AddChar.map_zero_eq_one] at this
    exact this
  map_add_eq_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [← Submodule.Quotient.mk_add, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ, psiKR_mk R ψ hψ,
      AddChar.map_add_eq_mul]
end
section ColumnOp
variable {K : Type} [CommRing K] {n : ℕ}
end ColumnOp
section Triple
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
variable {R}
variable (R)
def liftSub (k : ℕ) (Z Z' : Matrix (Fin n) (Fin n) K) (φ : coker R Z ≃ₗ[R] coker R Z') :
    Submodule R ((Fin n → R) × (Fin n → R)) where
  carrier := {p | LiftRel R k Z Z' φ p.1 p.2}
  add_mem' := by
    rintro p q ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by simp only [Prod.fst_add, Prod.snd_add, Submodule.Quotient.mk_add, map_add, h1, h3],
      fun j hj => by simp only [Prod.fst_add, Prod.snd_add, map_add, h2 j hj, h4 j hj]⟩
  zero_mem' := ⟨by simp, fun j _ => by simp⟩
  smul_mem' := by
    rintro r p ⟨h1, h2⟩
    exact ⟨by simp only [Prod.smul_fst, Prod.smul_snd, Submodule.Quotient.mk_smul, map_smul, h1],
      fun j hj => by simp only [Prod.smul_fst, Prod.smul_snd, map_smul, h2 j hj]⟩
end Triple
end Formalism.FourierDecayAlt.P.A5x2
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x2 Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Phase
end Formalism.FourierDecayAlt.P



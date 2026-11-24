-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducible
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_InducedScalarIrreducible
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:13:18.610219+00:00
-- url     : https://prove2.me/theorems/5ff7fe25-e4bb-41ff-b00c-ee4f049ca00c
-- title:
--   Induced Scalar Irreducible
-- statement:
--   Definitions and structural lemmas for Induced Scalar Irreducible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/InducedScalarIrreducible.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRankSB
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_BernsteinUnitaryProductIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct
namespace GlobalTheory.RankFibre
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem indScal_lift_law (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    (fun x => f x ⊗ₜ[ℂ] (1:ℂ)) ∈ indSpace (parab k (blocks a b))
      ((twist ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) (deltaHalf k (Two (Fin a) (Fin b)))).comp
        (leviProj k (blocks a b))) := by
  intro p x
  have h := hf.2 p x
  apply (TensorProduct.lid ℂ ℂ).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, twist_apply, MonoidHom.coe_coe] at h ⊢
  rw [h]
  simp [parChar, detRep, ofChar_apply]
  ring
def indScalLift (ν β : kˣ →* ℂˣ) (a b : ℕ) {f : GL (Fin (a + b)) k → ℂ} (hf : f ∈ indScal ν β a b) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
  ⟨⟨fun x => f x ⊗ₜ[ℂ] (1:ℂ), indScal_lift_law ν β a b hf⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((show IsOpen {g : GL (Fin (a + b)) k | rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f} from hf.1).mem_nhds (by simp)) fun g hg => by
      have hg' : rightReg ℂ (GL (Fin (a + b)) k) ℂ g f = f := hg
      apply Subtype.ext
      funext x
      show f (x * g) ⊗ₜ[ℂ] (1:ℂ) = f x ⊗ₜ[ℂ] (1:ℂ)
      rw [show f (x * g) = f x from congrFun hg' x])⟩
def indScalVal (ν β : kˣ →* ℂˣ) (a b : ℕ) :
    IndSp (two (stdSum (rfl : a + b = a + b)))
      ((extTensor (detRep (Fin a) (ν * β)) (detRep (Fin b) β)).comp
        (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) →ₗ[ℂ] (GL (Fin (a + b)) k → ℂ) where
  toFun F x := TensorProduct.lid ℂ ℂ (F.1.1 x)
  map_add' F G := by
    funext x
    show TensorProduct.lid ℂ ℂ (F.1.1 x + G.1.1 x) = _
    rw [map_add]
    rfl
  map_smul' c F := by
    funext x
    show TensorProduct.lid ℂ ℂ (c • F.1.1 x) = _
    rw [map_smul]
    rfl
end GlobalTheory.RankFibre



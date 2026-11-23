-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IrreducibleTensorCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:24:45.89144+00:00
-- url     : https://prove2.me/theorems/d51eddd8-cd0d-4858-aaf1-6e457cafe6e5
-- title:
--   Irreducible Tensor Character
-- statement:
--   Definitions and structural lemmas for Irreducible Tensor Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/IrreducibleTensorCharacter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
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
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter
def firstLast {n β : ℕ} (h : β ≤ n) : Fin β ⊕ Fin (n - β) ≃ Fin n :=
  stdSum (Nat.add_sub_cancel' h)
section
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def CentralExponentBoundOver : Prop :=
  ∀ (n β : ℕ) (_ : 1 ≤ β) (hβn : β ≤ n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π₀ : Representation ℂ (GL (Fin n) k) V),
    π₀.IsIrreducible → IsUnitarisable π₀ → IsSmooth π₀ →
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (s : Representation ℂ (GL (Fin β) k) S)
      (S' : Type) [AddCommGroup S'] [Module ℂ S'] (s' : Representation ℂ (GL (Fin (n - β)) k) S'),
      (extTensor s s').IsIrreducible →
      IsSubquotient (extTensor s s') (jac₂ (firstLast hβn) π₀) →
      ∀ (ω : kˣ →* ℂˣ) (c : ℝ), HasCentralChar s ω →
        (∀ z : kˣ, ‖(ω z : ℂ)‖ = nabs k z ^ (-((β : ℝ) * c))) →
        c ≤ ((n : ℝ) - (β : ℝ)) / 2
end
def CentralExponentBound : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    CentralExponentBoundOver k
section Sharp
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def tensorChar {G H : Type} [Group G] [Group H] (χ : G →* ℂˣ) (ψ : H →* ℂˣ) :
    (ofChar (χ.comp (MonoidHom.fst G H) * ψ.comp (MonoidHom.snd G H))).IntertwiningMap
      (extTensor (ofChar χ) (ofChar ψ)) where
  toLinearMap := (TensorProduct.lid ℂ ℂ).symm.toLinearMap
  isIntertwining' g := by
    ext
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, extTensor_tmul,
      ofChar_apply, mul_one, MonoidHom.mul_apply, MonoidHom.comp_apply, Units.val_mul]
    apply (TensorProduct.lid ℂ ℂ).injective
    simp
end Sharp
end GlobalTheory.IndefiniteRowSideFullHecke.IrreducibleTensorCharacter



-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HypothesesAbsDet_6833bb21ab80e2a5
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_GaloisGeometry__HypothesesAbsDet_6833bb21ab80e2a5
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:44.566334+00:00
-- url     : https://prove2.me/theorems/9545cd6a-3113-4a1e-9fac-e2844e5b1aea
-- title:
--   Hypotheses Abs Det
-- statement:
--   Definitions and structural lemmas for Hypotheses Abs Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/GaloisGeometry₂/HypothesesAbsDet.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GaloisGeometry_IsParahoricVec
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct
namespace GlobalTheory.Published
def MinguezThetaGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n m : ℕ), 1 ≤ n → 1 ≤ m →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin n) k) W), IsSmooth π → π.IsIrreducible →
    (∃ f : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] W, f ≠ 0 ∧ ∀ (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
      (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 (1 : GL (Fin m) k) h Φ → f Φ' = π h (f Φ)) →
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (π' : Representation ℂ (GL (Fin m) k) V),
      IsSmooth π' ∧ π'.IsIrreducible ∧ OmQuot 1 π' π ∧
      (∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (π'' : Representation ℂ (GL (Fin m) k) V'),
        IsSmooth π'' → π''.IsIrreducible → OmQuot 1 π'' π → Nonempty (π''.Equiv π')) ∧
      ∀ f f' : SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W,
        (∀ F ∈ ({f, f'} : Set (SB (Matrix (Fin n) (Fin m) k) →ₗ[ℂ] V ⊗[ℂ] W)),
          ∀ (g : GL (Fin m) k) (h : GL (Fin n) k) (Φ Φ' : SB (Matrix (Fin n) (Fin m) k)),
            (Φ' : Matrix (Fin n) (Fin m) k → ℂ) = om 1 g h Φ → F Φ' = TensorProduct.map (π' g) (π h) (F Φ)) →
        f ≠ 0 → ∃ c : ℂ, f' = c • f
namespace MinguezThetaGL
end MinguezThetaGL
end GlobalTheory.Published



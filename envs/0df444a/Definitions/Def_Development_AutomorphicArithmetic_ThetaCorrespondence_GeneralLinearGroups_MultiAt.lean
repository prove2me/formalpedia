-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
-- name    : Development_AutomorphicArithmetic_ThetaCorrespondence_GeneralLinearGroups_MultiAt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:17.967803+00:00
-- url     : https://prove2.me/theorems/22758880-9963-4ec0-816c-d32def895452
-- title:
--   Multi At
-- statement:
--   Definitions and structural lemmas for Multi At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/ThetaCorrespondence/GeneralLinearGroups/MultiAt.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsIrreducibleIffOfLinearEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct
namespace UpperTheory.Lit.Mix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (k) in

def TwoAt : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ → IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible
end UpperTheory.Lit.Mix
end



-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomInjLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomInjLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:17.759234+00:00
-- url     : https://prove2.me/theorems/13967d3d-397e-4b8d-9a53-ac3caa4b59bd
-- title:
--   Statements Spread Hom Inj Loc
-- statement:
--   Definitions and structural lemmas for Statements Spread Hom Inj Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHomInjLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
def SpreadHomInjLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ ψ₁ ψ₂ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj G,
        pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₁ =
          pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ₂ →
        ψ₁ = ψ₂
end
end GroundTheory.Heights₂.Heights.Model



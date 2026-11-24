-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:35:13.366803+00:00
-- url     : https://prove2.me/theorems/6c0b8a3c-b41d-41b3-9d74-19442d45e55c
-- title:
--   Statements Spread Hom Loc
-- statement:
--   Definitions and structural lemmas for Statements Spread Hom Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHomLoc.lean

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
def SpreadHomLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ⟶
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∃ ψ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj F ⟶
          (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U))).obj G,
        pullbackHomAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f n)) ≫
            X.homOfLE (inf_le_left : U ⊓ invOpen f n ≤ U) = _) ψ =
          pullbackHomAlong (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) (U ⊓ invOpen f n) U
            inf_le_left).symm φ
end
end GroundTheory.Heights₂.Heights.Model



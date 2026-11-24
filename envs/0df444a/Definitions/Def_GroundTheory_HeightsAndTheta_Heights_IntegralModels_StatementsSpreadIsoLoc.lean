-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadIsoLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadIsoLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:21.5058+00:00
-- url     : https://prove2.me/theorems/e5abe274-f12e-4039-bad1-8d8d76023f8d
-- title:
--   Statements Spread Iso Loc
-- statement:
--   Definitions and structural lemmas for Statements Spread Iso Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadIsoLoc.lean

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
def SpreadIsoLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ β : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ≅
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ (m : ℕ) (_ : 0 < m) (_ : ¬ (p : ℕ) ∣ m)
      (ψ : (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj F ≅
        (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U))).obj G),
      pullbackIsoAlong (rfl : (baseChangeMap f (ZLoc p) ∣_ (U ⊓ invOpen f m)) ≫
          X.homOfLE (inf_le_left : U ⊓ invOpen f m ≤ U) = _) ψ =
        pullbackIsoAlong (morphismRestrict_homOfLE (baseChangeMap f (ZLoc p)) (U ⊓ invOpen f m) U
          inf_le_left).symm β
end
end GroundTheory.Heights₂.Heights.Model



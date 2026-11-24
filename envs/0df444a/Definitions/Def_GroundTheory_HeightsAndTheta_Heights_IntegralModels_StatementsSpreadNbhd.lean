-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:23.732542+00:00
-- url     : https://prove2.me/theorems/7543f681-1ecf-4862-bd8d-edc6225cb8d9
-- title:
--   Statements Spread Nbhd
-- statement:
--   Definitions and structural lemmas for Statements Spread Nbhd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadNbhd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
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
variable {X : Scheme.{0}}
def toOpen (f : X ⟶ SpecZ) (R : Type) [CommRing R] (W : X.Opens)
    (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι) : baseChange f R ⟶ (W : Scheme.{0}) :=
  IsOpenImmersion.lift W.ι (baseChangeMap f R) hW
def SpreadBundleNbhd.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (E : (baseChange f (ZLoc p)).Modules), IsVectorBundle E →
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f (ZLoc p) W hW)).obj E' ≅ E)
end
end GroundTheory.Heights₂.Heights.Model



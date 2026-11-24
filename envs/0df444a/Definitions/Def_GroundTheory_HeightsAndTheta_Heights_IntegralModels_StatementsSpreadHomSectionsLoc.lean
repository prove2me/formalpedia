-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSectionsLoc
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:30.150798+00:00
-- url     : https://prove2.me/theorems/b89b985d-2b11-4037-9da4-6b3b79d1b467
-- title:
--   Statements Spread Hom Sections Loc
-- statement:
--   Definitions and structural lemmas for Statements Spread Hom Sections Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHomSectionsLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
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
open CategoryTheory AlgebraicGeometry
noncomputable section
def SpreadHomSectionsLoc.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (p : Nat.Primes)
    (U : X.Opens) (F G : (U : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj F ⟶
      (Scheme.Modules.pullback (baseChangeMap f (ZLoc p) ∣_ U)).obj G,
    ∃ m : ℕ, 0 < m ∧ ¬ (p : ℕ) ∣ m ∧ ∀ n : ℕ, 0 < n → m ∣ n → ¬ (p : ℕ) ∣ n →
      ∀ V : (U : Scheme.{0}).Opens, V ≤ invOpen (U.ι ≫ f) n →
        ∀ s : Γ(F, V), ∃ t : Γ(G, V),
          pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) G V t =
            φ.app ((baseChangeMap f (ZLoc p) ∣_ U) ⁻¹ᵁ V)
              (pullSectionOn (baseChangeMap f (ZLoc p) ∣_ U) F V s)
end
end GroundTheory.Heights₂.Heights.Model



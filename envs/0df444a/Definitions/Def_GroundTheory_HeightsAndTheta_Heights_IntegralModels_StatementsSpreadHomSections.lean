-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadHomSections
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:49:50.116524+00:00
-- url     : https://prove2.me/theorems/a8114387-4e98-466a-890d-a195c5b8ed7f
-- title:
--   Statements Spread Hom Sections
-- statement:
--   Definitions and structural lemmas for Statements Spread Hom Sections, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/StatementsSpreadHomSections.lean

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
def SpreadHomSections.Statement : Prop :=
  ∀ (X : Scheme.{0}) (f : X ⟶ SpecZ) [LocallyOfFiniteType f] [QuasiCompact f] (a : ℕ) (ha : 0 < a)
    (F G : (invOpen f a : Scheme.{0}).Modules), IsVectorBundle F → IsVectorBundle G →
    ∀ φ : (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj F ⟶
      (Scheme.Modules.pullback (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne')))).obj G,
    ∃ m : ℕ, 0 < m ∧ ∀ n : ℕ, 0 < n → m ∣ n →
      ∀ V : (invOpen f a : Scheme.{0}).Opens, V ≤ invOpen ((invOpen f a).ι ≫ f) ((a : ℤ) * n) →
        ∀ s : Γ(F, V), ∃ t : Γ(G, V),
          pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) G V t =
            φ.app ((toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) ⁻¹ᵁ V)
              (pullSectionOn (toInvOpen f ℚ a (isUnit_intCast_rat a (by exact_mod_cast ha.ne'))) F V s)
end
end GroundTheory.Heights₂.Heights.Model



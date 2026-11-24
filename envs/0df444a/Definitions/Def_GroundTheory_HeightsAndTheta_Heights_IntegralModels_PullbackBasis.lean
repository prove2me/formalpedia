-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
-- name    : GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:19:31.691649+00:00
-- url     : https://prove2.me/theorems/6eb5f6ec-3eca-4d60-8f6e-f075dff2cbfe
-- title:
--   Pullback Basis
-- statement:
--   Definitions and structural lemmas for Pullback Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PullbackBasis.lean

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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
def pullSectionOn {T Z : Scheme.{u}} (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) :
    Γ(M, U) →+ Γ((Scheme.Modules.pullback g).obj M, g ⁻¹ᵁ U) :=
  (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U).hom
def PullbackBasis.Statement : Prop :=
  ∀ (T Z : Scheme.{u}) (g : T ⟶ Z) (M : Z.Modules) (U : Z.Opens) (n : ℕ) (s : Fin n → Γ(M, U)),
    IsBasisOn M U s →
      IsBasisOn ((Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) (fun i => pullSectionOn g M U (s i))
end
end GroundTheory.Heights₂.Heights.Model



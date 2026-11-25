-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StCoordLatticeFullRank
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:47:29.527276+00:00
-- url     : https://prove2.me/theorems/29102178-71c7-4492-a7f4-441047abdd10
-- title:
--   St Coord Lattice Full Rank
-- statement:
--   Definitions and structural lemmas for St Coord Lattice Full Rank, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StCoordLatticeFullRank.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module
noncomputable section
variable {E : Type*} [Field E] [NumberField E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι]
def CoordLatticeFullRank.Statement (v : Basis ι E W) : Prop :=
  ∀ La : AddSubgroup W, IsLattice E La →
    (La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom).FG ∧
      Submodule.span ℚ ((La.map (v.equivFun : W →ₗ[E] ι → E).toAddMonoidHom : Set (ι → E))) = ⊤
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



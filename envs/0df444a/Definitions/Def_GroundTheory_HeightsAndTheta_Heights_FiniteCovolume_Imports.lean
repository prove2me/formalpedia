-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:57.606666+00:00
-- url     : https://prove2.me/theorems/c8d91ae1-14a3-4cfd-97f6-ba6e569a64ac
-- title:
--   Imports
-- statement:
--   Definitions and structural lemmas for Imports, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Imports.lean

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
open NumberField GroundTheory.Automorphic Module Matrix
noncomputable section
section Spaces
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def LatticePointsBelowFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (La : AddSubgroup W) (g : archUnitary h v) (t : ℝ), IsLattice E La →
    {x : W | x ∈ La ∧ M.len (invApply g (vecAt v x)) < t}.Finite
end Spaces
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



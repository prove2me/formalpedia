-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsEvalKerKrullDim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:06.4455+00:00
-- url     : https://prove2.me/theorems/ca346c51-5abf-4285-a5a9-f68db9592d96
-- title:
--   Statements Eval Ker Krull Dim
-- statement:
--   Definitions and structural lemmas for Statements Eval Ker Krull Dim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsEvalKerKrullDim.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsMoreTail
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
def EvalKerKrullDim.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (F L : Type) [Field F] [Field L] [Algebra F L]
    (y : (Σ k, ι k) → L),
    ringKrullDim (MRingOver F ι ⧸ RingHom.ker (aeval y : MRingOver F ι →ₐ[F] L)) =
      ((Algebra.trdeg F (IntermediateField.adjoin F (Set.range y))).toENat : WithBot ℕ∞)
end GroundTheory.Heights₂.Heights.Inter



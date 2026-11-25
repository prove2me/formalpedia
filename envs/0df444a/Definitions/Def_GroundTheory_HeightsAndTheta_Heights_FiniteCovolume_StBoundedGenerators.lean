-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedGenerators
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T02:37:16.915006+00:00
-- url     : https://prove2.me/theorems/4a0eb0ca-26a8-426c-9dc8-7144a8a23514
-- title:
--   St Bounded Generators
-- statement:
--   Definitions and structural lemmas for St Bounded Generators, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/StBoundedGenerators.lean

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
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def BoundedGenerators.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (t : ℝ), 0 < t →
    ∃ (n : ℕ) (C : ℝ), ∀ (La : AddSubgroup W) (g : archUnitary h v), IsDIntegral h D La →
      (∀ x ∈ La, x ≠ 0 → t ≤ M.len (invApply g (vecAt v x))) →
      ∃ e : Fin n → W, AddSubgroup.closure (Set.range e) = La ∧
        ∀ a, M.len (invApply g (vecAt v (e a))) ≤ C
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



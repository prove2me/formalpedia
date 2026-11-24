-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_NoCommonZeroComplex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:41:29.388812+00:00
-- url     : https://prove2.me/theorems/200af644-3b32-4471-9f46-8b49a4d170ce
-- title:
--   No Common Zero Complex
-- statement:
--   Definitions and structural lemmas for No Common Zero Complex, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightsOfSets/NoCommonZeroComplex.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
def NoCommonZeroComplex.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (P : ArithVariety n) (a : ι → ℤ)
    (J : Type) [Fintype J] (s : J → IntegralSection P a),
    (∀ x ∈ P.points (AlgebraicClosure ℚ), ∃ j, (s j).NonzeroAt x) →
    ∀ z ∈ P.points ℂ, ∃ (j : J) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ)
      (e : MvPolynomial (Coord n) ℤ),
      IsChartForm P a (s j).num (s j).den c d e ∧ (∀ k, z k (c k) ≠ 0) ∧ evalCone z e ≠ 0
end GroundTheory.Heights₂.Heights



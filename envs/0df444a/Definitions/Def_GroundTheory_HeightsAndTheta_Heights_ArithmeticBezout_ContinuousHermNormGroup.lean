-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:16.06811+00:00
-- url     : https://prove2.me/theorems/f15a4043-a8bd-44c2-9eab-8d554687a2d7
-- title:
--   Continuous Herm Norm Group
-- statement:
--   Definitions and structural lemmas for Continuous Herm Norm Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ContinuousHermNormGroup.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
def ChowHeightConst.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n k : ℕ) (H : ArchData K n) (c : K), c ≠ 0 →
    chowHt H k 0 (C c : MvPolynomial (Fin k × Fin n) K) = 0
section Ball
open Matrix
variable {n : ℕ}
def ballProd (h : HermNorm n) (k : ℕ) : Set (Fin k × Fin n → ℂ) :=
  {u | ∀ i, h.norm (fun j => u (i, j)) < 1}
end Ball
section ProductFormula
variable {K : Type*} [Field K] [NumberField K]
end ProductFormula
end
end GroundTheory.Heights₂.Heights



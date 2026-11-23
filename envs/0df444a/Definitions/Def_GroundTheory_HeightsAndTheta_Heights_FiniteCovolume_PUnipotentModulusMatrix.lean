-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnipotentModulusMatrix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:59.804792+00:00
-- url     : https://prove2.me/theorems/4e327444-0174-424b-af4e-d6eed3fec632
-- title:
--   PUnipotent Modulus Matrix
-- statement:
--   Definitions and structural lemmas for PUnipotent Modulus Matrix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PUnipotentModulusMatrix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open Matrix
noncomputable section
variable {ι : Type*} [Fintype ι]
def hForm (H : Matrix ι ι ℂ) (u z : ι → ℂ) : ℂ := star u ⬝ᵥ (H *ᵥ z)
section Form
variable (H : Matrix ι ι ℂ)
variable [DecidableEq ι]
end Form
def heisS (H : Matrix ι ι ℂ) (y : ι → ℂ) (t : ℝ) : ℂ :=
  ⟨-(hForm H y y).re / 2, t⟩
section S
variable {H : Matrix ι ι ℂ}
end S
variable [DecidableEq ι]
def heisMat (H : Matrix ι ι ℂ) (a y : ι → ℂ) (s : ℂ) : Matrix ι ι ℂ :=
  1 + vecMulVec (y + s • a) (star a ᵥ* H) - vecMulVec a (star y ᵥ* H)
section Heis
variable {H : Matrix ι ι ℂ} {a : ι → ℂ}
variable (hH : H.IsHermitian) (ha : hForm H a a = 0)
include hH ha
end Heis
end
end GroundTheory.Heights₂.Heights.FiniteCovolume



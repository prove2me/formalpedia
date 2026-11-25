-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
-- name    : GroundTheory_HeightsAndTheta_Heights_LocalDensities_FlagPsLine
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:01.848013+00:00
-- url     : https://prove2.me/theorems/9252f645-f003-4f32-b741-ae41bbd19f72
-- title:
--   Flag Ps Line
-- statement:
--   Definitions and structural lemmas for Flag Ps Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/FlagPsLine.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FourB
open Polynomial Matrix
noncomputable section
variable {N : ℕ}
def sigSign (p : ℕ) (a : Fin N) : ℝ := if a.val < p then 1 else -1
def tailSum (p i : ℕ) (L : Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  ∑ b : Fin N, ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0
section Poly
variable (p i : ℕ) (hi : i ≤ N) (L : Matrix (Fin N) (Fin N) ℂ)
def colPoly : Matrix (Fin N) (Fin i) ℂ[X] :=
  Matrix.of fun c b => (if c = Fin.castLE hi b then 1 else 0) + X * C (L c (Fin.castLE hi b))
def rowPoly : Matrix (Fin i) (Fin N) ℂ[X] :=
  Matrix.of fun a c =>
    (if c = Fin.castLE hi a then 1 else 0) + X * C (star (L c (Fin.castLE hi a)))
def topPoly : Matrix (Fin i) (Fin i) ℂ[X] := (colPoly i hi L).submatrix (Fin.castLE hi) id
def topPoly' : Matrix (Fin i) (Fin i) ℂ[X] := (rowPoly i hi L).submatrix id (Fin.castLE hi)
def sigTop : Matrix (Fin i) (Fin i) ℂ :=
  diagonal fun a => ((sigSign p (Fin.castLE hi a) : ℝ) : ℂ)
def tailForm : Matrix (Fin i) (Fin i) ℂ :=
  Matrix.of fun a b => ∑ c : Fin N, if i ≤ c.val then
    star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi b) else 0
def kerPoly : Matrix (Fin i) (Fin i) ℂ[X] :=
  (sigTop p i hi).map C * (topPoly' i hi L).adjugate * (tailForm p i hi L).map C *
    (topPoly i hi L).adjugate
variable {L}
end Poly
end
end GroundTheory.Heights₂.Heights.FourB



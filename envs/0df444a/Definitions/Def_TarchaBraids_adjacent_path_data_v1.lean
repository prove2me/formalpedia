-- Prove2me | Definitions.Def_TarchaBraids_adjacent_path_data_v1
-- name    : TarchaBraids_adjacent_path_data_v1
-- status  : Definition
-- author  : @WillR
-- created : 2026-09-21T08:12:29.880128+00:00
-- url     : https://prove2.me/theorems/c93c5932-b105-4024-9247-d4836fbd49cd
-- title:
--   Tarcha adjacent braid raw path and interpolation data
-- statement:
--   Raw explicit coordinate maps used to prove the adjacent Artin braid relation: the left and right three-half-twist paths, the common outer rotation, and the linear interpolation maps between them.
-- source:
--   Source-faithful extraction from the explicit geometric proof of TarchaBraids.thm_3_15_half_twists_satisfy_relations.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

noncomputable section

open BraidsLinksMCG

def leftBraidFun (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) (k : Fin n) : ℂ :=
  if q ≤ 1 / 2 then
    halfTwistFun n i (2 * q) k
  else if q ≤ 3 / 4 then
    halfTwistFun n j (4 * q - 2)
      ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k)
  else
    halfTwistFun n i (4 * q - 3)
      ((Equiv.swap (strandIdx j) (strandIdxSucc j))
        ((Equiv.swap (strandIdx i) (strandIdxSucc i)) k))

def rightBraidFun (n : ℕ) (i j : Fin (n - 1)) (q : ℝ) (k : Fin n) : ℂ :=
  if q ≤ 1 / 2 then
    halfTwistFun n j (2 * q) k
  else if q ≤ 3 / 4 then
    halfTwistFun n i (4 * q - 2)
      ((Equiv.swap (strandIdx j) (strandIdxSucc j)) k)
  else
    halfTwistFun n j (4 * q - 3)
      ((Equiv.swap (strandIdx i) (strandIdxSucc i))
        ((Equiv.swap (strandIdx j) (strandIdxSucc j)) k))

def outerRotateFun (n : ℕ) (i : Fin (n - 1)) (q : ℝ) (k : Fin n) : ℂ :=
  if (k : ℕ) = (i : ℕ) then
    twistPoint ((i : ℕ) + 2) (-2) q
  else if (k : ℕ) = (i : ℕ) + 1 then
    ((((i : ℕ) : ℝ) + 2 : ℝ) : ℂ)
  else if (k : ℕ) = (i : ℕ) + 2 then
    twistPoint ((i : ℕ) + 2) 2 q
  else
    (((k : ℕ) + 1 : ℝ) : ℂ)

def braidInterp (u : ℝ) (z w : ℂ) : ℂ := (1 - u) • z + u • w

def leftOuterInterpFun (n : ℕ) (i j : Fin (n - 1)) (u q : ℝ) (k : Fin n) : ℂ :=
  braidInterp u (leftBraidFun n i j q k) (outerRotateFun n i q k)

def rightOuterInterpFun (n : ℕ) (i j : Fin (n - 1)) (u q : ℝ) (k : Fin n) : ℂ :=
  braidInterp u (rightBraidFun n i j q k) (outerRotateFun n i q k)

end

end TarchaBraids



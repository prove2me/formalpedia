-- Prove2me | Definitions.Def_Transport_Candidate
-- name    : Transport_Candidate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:25:28.802201+00:00
-- url     : https://prove2.me/theorems/992ea23f-17b6-4c70-ba1c-cb0f64606d11
-- title:
--   Candidate
-- statement:
--   Definitions and structural lemmas for Candidate, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Candidate.lean

import Definitions.Def_Transport_LocalBounds
set_option autoImplicit false
namespace RH.Transport.Candidate
open RH.Transport.Geometry
open RH.Transport.LocalBounds
noncomputable section
def p : ℝ := 68479 / 400000000
def B : ℝ := boundary p
def cushion : ℝ := 1 / 40000000000
def zeta : ℝ := 1 / 320000000000
inductive SideCondition where
  | lowSubset
  | minimumWidth
  | minimumLx
  | minimumLy
  | gram
  | floor
  | intermediate
  | small
  | selectedSupply
  | strongSupply
  | bufferedUpperScale
  | principalW
  | principalZ
  | goodTail
  | principalMixed
  | smallFirstRegion
def sideMargin (term : SideCondition) : ℝ :=
  match term with
  | .lowSubset => 1 / 5 - ell p
  | .minimumWidth => 1 - 3 * ell p
  | .minimumLx => lx p - ell p
  | .minimumLy => ly p - ell p
  | .gram => ly p - ell p - 11 * b / 6
  | .floor => 7 / 1200 - (32 / 25) * p
  | .intermediate => 241 / 9600 - (329 / 400) * p
  | .small => 63 / 800 - (51 / 100) * p
  | .selectedSupply => ell p / (h p + zeta) - 7 / 37
  | .strongSupply => 5 * ell p - h p - zeta
  | .bufferedUpperScale => 1 - h p - zeta
  | .principalW => ly p / 20
  | .principalZ => h p / 600
  | .goodTail => goodTailDecay p - 4 / 5
  | .principalMixed => 4 * B - 301 / 100
  | .smallFirstRegion => B - 1 / 2
def sideMarginValue (term : SideCondition) : ℝ :=
  match term with
  | .lowSubset => 39794563 / 1200000000
  | .minimumWidth => 199794563 / 400000000
  | .minimumLx => 149794563 / 800000000
  | .minimumLy => 249794563 / 800000000
  | .gram => 199383689 / 2400000000
  | .floor => 5263313 / 937500000
  | .intermediate => 11982411227 / 480000000000
  | .small => 3146507571 / 40000000000
  | .selectedSupply => 464355264379 / 28869121402911
  | .strongSupply => 20575223597 / 960000000000
  | .bufferedUpperScale => 59917825199 / 320000000000
  | .principalW => 1149794563 / 48000000000
  | .principalZ => 650205437 / 480000000000
  | .goodTail => 23931521 / 1600000000
  | .principalMixed => 195931521 / 400000000
  | .smallFirstRegion => 599931521 / 1600000000
end
end RH.Transport.Candidate



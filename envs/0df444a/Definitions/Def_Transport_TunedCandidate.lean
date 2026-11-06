-- Prove2me | Definitions.Def_Transport_TunedCandidate
-- name    : Transport_TunedCandidate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:26:01.176807+00:00
-- url     : https://prove2.me/theorems/c18d45cb-b8ae-453d-945c-dc5e69ca694f
-- title:
--   Tuned Candidate
-- statement:
--   Definitions and structural lemmas for Tuned Candidate, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/TunedCandidate.lean

import Definitions.Def_Transport_LocalBounds
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
namespace RH.Transport.TunedCandidate
open RH.Transport.LocalBounds
noncomputable section
def lxAt (e b : ℝ) : ℝ := (1 - e - b) / 2
def lyAt (e b : ℝ) : ℝ := (1 - e + b) / 2
def hAt (e b : ℝ) : ℝ := (1 + 3 * e + b) / 2
def widthAt (e : ℝ) : ℝ := 1 - e
def boundaryAt (e : ℝ) : ℝ := 11 / 12 - e / 4
def signalAt (e b s : ℝ) : ℝ := s + lxAt e b / 2 - 1 + hAt e b / 6
def lowExponentAt (e b : ℝ) : ℝ := lxAt e b / 2 + b / 12
def p : ℝ := 214651 / 1250000000
def b : ℝ := 192821 / 1562500
def ell : ℝ := Geometry.ell p
def lx : ℝ := lxAt ell b
def ly : ℝ := lyAt ell b
def h : ℝ := hAt ell b
def width : ℝ := widthAt ell
def B : ℝ := boundaryAt ell
def signal (s : ℝ) : ℝ := signalAt ell b s
def lowExponent : ℝ := lowExponentAt ell b
def cushion : ℝ := 1 / 1000000000000
def zeta : ℝ := 1 / 8000000000000
def intermediateExponent (δ x : ℝ) : ℝ :=
  let a := (1 + δ) / 2
  let q := δ * x
  let R := 76 / 75 - 2 * δ / 3
  a - B + h * (17 / 50 - 1 / 6) - a * ly - ell / 2 + q * ell
    + (1 / 2) * (R + δ / 2 - 17 / 50)
inductive SideCondition where
  | gramScale | lowSubset | minimumWidth | minimumLx | minimumLy | gram
  | floor | intermediate | small | selectedSupply | strongSupply
  | bufferedUpperScale | principalW | principalZ | goodTail
  | principalMixed | smallFirstRegion
def sideMargin (term : SideCondition) : ℝ :=
  match term with
  | .gramScale => b
  | .lowSubset => 1 / 5 - ell
  | .minimumWidth => 1 - 3 * ell
  | .minimumLx => lx - ell
  | .minimumLy => ly - ell
  | .gram => ly - ell - 11 * b / 6
  | .floor => 7 / 1200 - (32 / 25) * p - (b - 1 / 8) / 6
  | .intermediate => -intermediateExponent (3 / 4) (1 / 2)
  | .small => ly / 2 - h * (17 / 50 - 1 / 6) - 1 / 50
  | .selectedSupply => ell / (h + zeta) - 7 / 37
  | .strongSupply => 5 * ell - h - zeta
  | .bufferedUpperScale => 1 - h - zeta
  | .principalW => ly / 20
  | .principalZ => h / 600
  | .goodTail => goodTailDecay p - 4 / 5
  | .principalMixed => 4 * B - 301 / 100
  | .smallFirstRegion => B - 1 / 2
def sideMarginValue (term : SideCondition) : ℝ :=
  match term with
  | .gramScale => 192821 / 1562500
  | .lowSubset => 124356047 / 3750000000
  | .minimumWidth => 624356047 / 1250000000
  | .minimumLx => 470099247 / 2500000000
  | .minimumLy => 778612847 / 2500000000
  | .gram => 639013741 / 7500000000
  | .floor => 34448969 / 5859375000
  | .intermediate => 36605252263 / 1500000000000
  | .small => 9800247199 / 125000000000
  | .selectedSupply => 1067559769889 / 65547340678701
  | .strongSupply => 533559267197 / 24000000000000
  | .bufferedUpperScale => 1504317590399 / 8000000000000
  | .principalW => 3587126447 / 150000000000
  | .principalZ => 2029900753 / 1500000000000
  | .goodTail => 74785349 / 5000000000
  | .principalMixed => 612285349 / 1250000000
  | .smallFirstRegion => 1874785349 / 5000000000
end
end RH.Transport.TunedCandidate



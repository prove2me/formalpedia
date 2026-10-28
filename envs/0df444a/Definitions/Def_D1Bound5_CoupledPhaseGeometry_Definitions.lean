-- Prove2me | Definitions.Def_D1Bound5_CoupledPhaseGeometry_Definitions
-- name    : D1Bound5_CoupledPhaseGeometry_Definitions
-- status  : Definition
-- author  : @tp
-- created : 2026-10-23T23:09:17.155192+00:00
-- url     : https://prove2.me/theorems/338b7ab6-e4b1-4359-9437-ceda3b256259
-- title:
--   Coupled Phase Geometry
-- statement:
--   Definitions for coupled phase geometry in the argument bounding Diophantine D(1) sets in imaginary quadratic integer rings. The named objects in this bundle include `coupledPhasePolynomial`, `phaseVandermondeRatio`, `phasePhi`.
-- source:
--   D1Bound5/CoupledPhaseGeometry.lean, lines 7-8, SHA-256 1d918f05136e1da2113d9f7f69074992938e37e254dbb6171ec1af3edcc8f694; D1Bound5/CoupledPhaseGeometry.lean, lines 10-11, SHA-256 1d918f05136e1da2113d9f7f69074992938e37e254dbb6171ec1af3edcc8f694; D1Bound5/CoupledPhaseGeometry.lean, lines 13-14, SHA-256 1d918f05136e1da2113d9f7f69074992938e37e254dbb6171ec1af3edcc8f694. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

section
namespace D1Bound5

noncomputable def coupledPhasePolynomial (q x : ℝ) : ℝ :=
  (4-x^2)^4*(1+(1/q)^2+x/q)^2

noncomputable def phaseVandermondeRatio (a b s : ℂ) : ℝ :=
  ‖(a-b)*(a-s)*(b-s)‖/(‖b‖*‖s‖^2)

noncomputable def phasePhi (b s : ℂ) : ℝ :=
  max ((‖b-s‖/‖s‖)^6) ((‖b‖/‖s‖)*(‖b-s‖/‖s‖)^5)



end D1Bound5
end



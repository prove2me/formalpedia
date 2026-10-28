-- Prove2me | Definitions.Def_rc_curve_witness
-- name    : rc_curve_witness
-- status  : Definition
-- author  : @Eyal1990
-- created : 2026-10-25T07:27:59.084052+00:00
-- url     : https://prove2.me/theorems/851cef54-b60e-460f-8951-953680be0e35
-- title:
--   Artin-algebra coordinate witness
-- statement:
--   Defines the two coordinate values ε+η and ε−η in the four-dimensional local Artin algebra C[ε,η]/(ε²,η²), the evaluation homomorphism from the polynomial ring, and its kernel ideal.
-- source:
--   openai/math Ampleness stack: WeightedIdealCurveBound implies eps-ample exceptional twist, hence Serre vanishing and eventual generation of I^n by weight ≤ n(rho+eps) sections.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.MvPolynomial.Eval

noncomputable section

abbrev rcDual := TrivSqZeroExt Complex Complex
abbrev rcFour := TrivSqZeroExt rcDual rcDual

def rcVars : Fin 2 → rcFour :=
  ![((0, 1), (1, 0)), ((0, 1), (-1, 0))]

def rcEval : MvPolynomial (Fin 2) Complex →ₐ[Complex] rcFour :=
  MvPolynomial.aeval rcVars

def rcIdeal : Ideal (MvPolynomial (Fin 2) Complex) :=
  RingHom.ker rcEval.toRingHom



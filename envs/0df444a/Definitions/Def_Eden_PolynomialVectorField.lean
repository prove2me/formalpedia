-- Prove2me | Definitions.Def_Eden_PolynomialVectorField
-- name    : Eden_PolynomialVectorField
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:00:01.033306+00:00
-- url     : https://prove2.me/theorems/12e3839c-0b5b-49db-88d6-1033386b5fa9
-- title:
--   Polynomial Vector Field
-- statement:
--   Definitions and structural lemmas for Polynomial Vector Field, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PolynomialVectorField.lean

import Definitions.Def_Eden_Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Tactic
set_option autoImplicit true
noncomputable section
namespace Eden
open MvPolynomial
def radiusPolynomial (i j : Fin 5) : MvPolynomial (Fin 5) ℝ := X i ^ 2 + X j ^ 2
def ratePolynomial (i j : Fin 5) : MvPolynomial (Fin 5) ℝ :=
  -(radiusPolynomial i j - C 1) * (radiusPolynomial i j - C 2)
def vectorFieldPolynomial (c : ℝ) : Fin 5 → MvPolynomial (Fin 5) ℝ :=
  ![ratePolynomial 0 1 * X 0 - X 1,
    ratePolynomial 0 1 * X 1 + X 0,
    ratePolynomial 2 3 * X 2 - C (Real.sqrt 2) * X 3,
    ratePolynomial 2 3 * X 3 + C (Real.sqrt 2) * X 2,
    C (-c) * X 4]
end Eden



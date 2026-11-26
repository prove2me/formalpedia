-- Prove2me | Definitions.Def_Malliavin_BrownianHermite
-- name    : Malliavin_BrownianHermite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:02:24.359797+00:00
-- url     : https://prove2.me/theorems/dbd00dd5-6ed8-5eff-9d26-340d786b12dc
-- title:
--   Brownian Hermite
-- statement:
--   Definitions and structural lemmas for Brownian Hermite, from Ezzeri Esa (savarin/lean-malliavin; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Malliavin calculus and Clark-Ocone representation on Gaussian Banach spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Malliavin.BrownianIteratedConstruction
noncomputable def hermiteReal (n : ℕ) : Polynomial ℝ :=
  (Polynomial.hermite n).map (Int.castRingHom ℝ)
noncomputable def varianceHermite (variance : ℝ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.X
  | n + 2 =>
      Polynomial.X * varianceHermite variance (n + 1) -
        Polynomial.C (variance * (n + 1)) * varianceHermite variance n
variable {M : Type*} [AddCommMonoid M] [Module ℝ M]
noncomputable def polynomialFamilyLinearMap (xpow : ℕ → M) :
    Polynomial ℝ →ₗ[ℝ] M :=
  (Polynomial.basisMonomials ℝ).constr ℝ xpow
variable {W : Type*} [MeasurableSpace W] {P : Measure W}
end Malliavin.BrownianIteratedConstruction



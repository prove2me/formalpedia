-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
-- name    : OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:42:05.38266+00:00
-- url     : https://prove2.me/theorems/50f6bce0-2053-45be-9234-91f7141175ac
-- title:
--   Arithmetic data associated with interpolation minors
-- statement:
--   Let $p_i\in\mathbb Z$ and $q_i\in\mathbb N$ be numerators and denominators. For real parameters $F,v_0,H$ and a natural row multiplicity $K$, define
--
--   $$w_i=\lceil\log q_i\rceil_+,\qquad r_i=\frac{2\mathrm i p_i}{q_i},\qquad T_i=\left\lceil\frac{F w_i}{v_0}\right\rceil_+.$$
--
--   Here the ceiling symbols denote natural ceilings. The weighted row sum is the sum of $\sum_i b_iw_i$ over the exact source row domain. Its normalized mean divides this sum by the row count times $H$. For any selection of columns indexed by the rows, the selected minor is the resulting square submatrix of the logarithmic interpolation matrix. These quantities are the data used in the later determinant estimates.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/MatrixArithmetic.lean

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

namespace OAI.PiExponent.MatrixArithmetic

open scoped BigOperators

noncomputable def logWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℝ :=
  (⌈Real.log (q i)⌉₊ : ℝ)

noncomputable def rationalCenters {m : ℕ} (p : Fin m → ℤ) (q : Fin m → ℕ) : Fin m → ℂ :=
  fun i => 2 * Complex.I * (p i : ℂ) / (q i : ℂ)

noncomputable def truncationOrders {m : ℕ} (q : Fin m → ℕ) (F v0 : ℝ) : Fin m → ℕ :=
  fun i => ⌈F * logWeights q i / v0⌉₊

noncomputable def rowWeightedSum {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  ∑ ρ : InterpolationMatrix.Row K v0 θ (logWeights q) H,
    ∑ i, (ρ.2.1 i.succ : ℝ) * logWeights q i

noncomputable def meanRowWeight {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  rowWeightedSum K v0 θ q H /
    ((Fintype.card (InterpolationMatrix.Row K v0 θ (logWeights q) H) : ℝ) * H)

noncomputable def selectedMinor {m : ℕ} (K : ℕ) (w0 v0 θ F H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (selection : InterpolationMatrix.Row K v0 θ (logWeights q) H →
      InterpolationMatrix.Column w0 (logWeights q) H) :
    Matrix (InterpolationMatrix.Row K v0 θ (logWeights q) H)
      (InterpolationMatrix.Row K v0 θ (logWeights q) H) ℂ :=
  (InterpolationMatrix.truncatedLogMatrix K w0 v0 θ (logWeights q) H
    (rationalCenters p q) (truncationOrders q F v0)).submatrix id selection

end OAI.PiExponent.MatrixArithmetic



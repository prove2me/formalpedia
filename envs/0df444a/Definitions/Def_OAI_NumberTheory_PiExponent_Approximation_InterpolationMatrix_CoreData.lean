-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
-- name    : OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_CoreData
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-11T12:37:38.031852+00:00
-- url     : https://prove2.me/theorems/555d4701-6886-4e12-b3cb-0fc0f0705cdb
-- title:
--   Core polynomial data for interpolation matrices
-- statement:
--   For natural exponent vectors $a,b$ indexed by $m$ coordinates, complex centers $r_i$, polynomials $G_i$, and natural numbers $j,h,s$, define the monomial image and its coefficient entry by
--
--   $$M_{j,h,a}= (1+X)^h\prod_i(jr_i+G_i+Y_i)^{a_i},\qquad A_{(j,s,b),(h,a)}=[X^sY^b]M_{j,h,a}.$$
--
--   The finite exponent vector is the finitely supported form of $a$. The truncated logarithm of order $T$ is the polynomial truncation of the formal series $\log(1+X)$. The interpolation matrix uses these entries on the exact weighted row and column domains; its logarithmic specialization sets $G_i$ equal to the corresponding truncated logarithm. These definitions supply the matrix data of the conditional determinant argument.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

end OAI.PiExponent.InterpolationMatrix



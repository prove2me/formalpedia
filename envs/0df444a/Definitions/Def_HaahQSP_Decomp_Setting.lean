-- Prove2me | Definitions.Def_HaahQSP_Decomp_Setting
-- name    : HaahQSP_Decomp_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:28:13.139769+00:00
-- url     : https://prove2.me/theorems/63280e77-7ad3-4978-99d4-d302a17d2e24
-- title:
--   Equations (2)–(5) and Definition 1: primitive matrices and the Laurent polynomial classes
-- statement:
--   For $n\ge0$, a matrix Laurent polynomial is $F(t)=\sum_{j=-n}^{n}C_jt^j$, with $2\times2$ complex coefficients and zero coefficients outside this interval. Its coefficientwise adjoint is $F^\dagger(t)=\sum_jC_j^\dagger t^j$.
--
--   The class $\mathcal P_n$ contains those polynomials satisfying $F(\eta)\in SU(2)$ for every $|\eta|=1$. The class $\mathcal E_n$ is the subclass with $C_{-n+k}=0$ for every odd integer $k$. Degree $n$ means $C_n\ne0$ or $C_{-n}\ne0$. A rank one orthogonal projector is a Hermitian idempotent matrix of trace one. Its primitive matrix and an ordered product are
--
--   $$
--   E_P(t)=tP+t^{-1}(I-P),\qquad F(t)=E_0E_{P_1}(t)\cdots E_{P_n}(t).
--   $$
--
--   These definitions are the shared objects in the product decomposition theorem.
--
--   **Formalization Note** Coefficients are integer indexed families with explicit width support; evaluation is used at nonzero complex $t$. The factor $P_1$ is the leftmost factor.
-- source:
--   J. Haah, Product Decomposition of Periodic Functions in Quantum Signal Processing, arXiv:1806.10236v4 (2020), pp. 3–4, Eq. (2)–(5), Definition 1

import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Int.Interval

namespace HaahQSP.Decomp

open scoped Matrix

abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

noncomputable def eval (n : ℕ) (C : ℤ → Mat2) (t : ℂ) : Mat2 :=
  ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), t ^ j • C j

noncomputable def daggerEval (n : ℕ) (C : ℤ → Mat2) (t : ℂ) : Mat2 :=
  ∑ j ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), t ^ j • (C j)ᴴ

def PSet (n : ℕ) (C : ℤ → Mat2) : Prop :=
  (∀ j : ℤ, (n : ℤ) < |j| → C j = 0) ∧
  ∀ η : ℂ, ‖η‖ = 1 → eval n C η ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ

def ESet (n : ℕ) (C : ℤ → Mat2) : Prop :=
  PSet n C ∧ ∀ k : ℤ, Odd k → C (-(n : ℤ) + k) = 0

def HasDegree (n : ℕ) (C : ℤ → Mat2) : Prop :=
  C (n : ℤ) ≠ 0 ∨ C (-(n : ℤ)) ≠ 0

def IsRankOneProj (P : Mat2) : Prop :=
  P.IsHermitian ∧ P * P = P ∧ Matrix.trace P = 1

noncomputable def prim (P : Mat2) (t : ℂ) : Mat2 :=
  t • P + t⁻¹ • (1 - P)

noncomputable def prodPrim (n : ℕ) (Ps : Fin n → Mat2) (t : ℂ) : Mat2 :=
  (List.ofFn fun j => prim (Ps j) t).prod

end HaahQSP.Decomp



-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_Decomposition
-- name    : IsingVectorBalancing_Subgaussian_Supplement_Decomposition
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:17:32.299528+00:00
-- url     : https://prove2.me/theorems/740c9e22-286d-468c-90ba-5215885e2d45
-- title:
--   Positive-vector Lorentz decomposition and normalized diagonal constant
-- statement:
--   A positive-vector decomposition consists of a finite dimension $r\ge0$, numbers $\rho_a>0$ and row vectors $R_a\in\mathbb R^r$ satisfying
--
--   $$A_{ab}=\rho_a\rho_b-\langle R_a,R_b\rangle.$$
--
--   Set $v_a=R_a/\rho_a$ and $c_A=\min_a A_{aa}/\rho_a^2$. By the decomposition identity this is also $\min_a(1-\|v_a\|_2^2)$. The minimum is used for $q\ge2$. The data contains only the algebraic identity and positivity of $\rho$, with no analytic bound. In particular $r=0$, singular interactions and zero diagonal entries are permitted. Quantifying over all such decompositions includes the Perron–Frobenius choice made in the source.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), p. 17 (PDF 18), (23)–(24)

import Definitions.Def_IsingVectorBalancing_Subgaussian_Supplement_SpinLaw

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian.Supplement

/-- Actual algebraic data (23), without any gap or variance certificate. -/
structure PositiveDecomposition {q : ℕ} (A : Matrix (Fin q) (Fin q) ℝ) (r : ℕ) where
  ρ : Fin q → ℝ
  row : Fin q → Vec r
  positive : ∀ a, 0 < ρ a
  identity : ∀ a b, A a b = ρ a * ρ b - inner ℝ (row a) (row b)

noncomputable def normalizedRow {q r : ℕ} {A : Matrix (Fin q) (Fin q) ℝ}
    (D : PositiveDecomposition A r) (a : Fin q) : Vec r :=
  (D.ρ a)⁻¹ • D.row a

/-- Equation (24). All theorem uses have q≥2, so this is a finite minimum. -/
noncomputable def cA {q r : ℕ} {A : Matrix (Fin q) (Fin q) ℝ}
    (D : PositiveDecomposition A r) : ℝ :=
  ⨅ a : Fin q, A a a / (D.ρ a) ^ 2

end IsingVectorBalancing.Subgaussian.Supplement



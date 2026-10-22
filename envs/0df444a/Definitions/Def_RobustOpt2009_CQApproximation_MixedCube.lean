-- Prove2me | Definitions.Def_RobustOpt2009_CQApproximation_MixedCube
-- name    : RobustOpt2009_CQApproximation_MixedCube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:43:20.957979+00:00
-- url     : https://prove2.me/theorems/de7ce092-0e9d-4b11-bcf1-5e0c1e77c0cf
-- title:
--   Mixed scalar and full matrix-cube predicates
-- statement:
--   Fix real symmetric $m\times m$ matrices $B_0,B_1,\ldots,B_p$ and full-block factors $L_j\in\mathbb R^{p_j\times m}$, $R_j\in\mathbb R^{q_j\times m}$ with positive row counts. Define $\mathcal A(\rho)$ to mean
--   $$B_0+\sum_i\theta_iB_i+\sum_j(L_j^T\Theta_jR_j+R_j^T\Theta_j^TL_j)\succeq0$$
--   for all independent $|\theta_i|\le\rho$ and $\|\Theta_j\|_{2,2}\le\rho$.
--   Define $\mathcal B(\rho)$ to mean that symmetric matrices $U_i,V_j$ exist such that
--   $$U_i\succeq\pm B_i,\qquad V_j\succeq L_j^T\Theta R_j+R_j^T\Theta^TL_j\quad(\|\Theta\|_{2,2}\le1),$$
--   $$B_0-\rho\sum_iU_i-\rho\sum_jV_j\succeq0.$$
--   These predicates distinguish original robust feasibility from a separable matrix-envelope certificate.
--
--   **Formalization Note** Either block family may be empty. No positivity of $B_0$ or nonzero condition on full-block factors is imposed. All sums are finite and the norm bound uses Euclidean spaces. This is the mixed-block model, not the scalar-only matrix cube already in the library.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, DOI 10.1515/9781400831050, Theorem 7.1.3, printed p. 183 (PDF p. 209).

import Definitions.Def_RobustOpt2009_CQApproximation_Basic

open Matrix
open scoped BigOperators

namespace RobustOpt2009.CQApproximation

/-- Data of Theorem 7.1.3. Either block family can be empty. -/
structure CubeData (m p q : ℕ) where
  B0 : Matrix (Fin m) (Fin m) ℝ
  B : Fin p → Matrix (Fin m) (Fin m) ℝ
  symm0 : B0.IsHermitian
  symm : ∀ i, (B i).IsHermitian
  rowsL : Fin q → ℕ
  rowsR : Fin q → ℕ
  posL : ∀ j, 0 < rowsL j
  posR : ∀ j, 0 < rowsR j
  L : ∀ j, Matrix (Fin (rowsL j)) (Fin m) ℝ
  R : ∀ j, Matrix (Fin (rowsR j)) (Fin m) ℝ

/-- Predicate A(ρ) of Theorem 7.1.3. -/
def CubeData.Robust {m p q : ℕ} (D : CubeData m p q) (ρ : ℝ) : Prop :=
  ∀ (θ : Fin p → ℝ) (Θ : ∀ j, Matrix (Fin (D.rowsL j)) (Fin (D.rowsR j)) ℝ),
    (∀ i, |θ i| ≤ ρ) → (∀ j, OperatorBound (Θ j) ρ) →
    (D.B0 + ∑ i, θ i • D.B i + ∑ j, blockTerm (D.L j) (D.R j) (Θ j)).PosSemidef

/-- Predicate B(ρ) of Theorem 7.1.3, retaining the unit-ball full-block envelopes. -/
def CubeData.Envelope {m p q : ℕ} (D : CubeData m p q) (ρ : ℝ) : Prop :=
  ∃ (U : Fin p → Matrix (Fin m) (Fin m) ℝ)
    (V : Fin q → Matrix (Fin m) (Fin m) ℝ),
    (∀ i, (U i).IsHermitian) ∧ (∀ j, (V j).IsHermitian) ∧
    (∀ i, (U i - D.B i).PosSemidef ∧ (U i + D.B i).PosSemidef) ∧
    (∀ j Θ, OperatorBound Θ 1 → (V j - blockTerm (D.L j) (D.R j) Θ).PosSemidef) ∧
    (D.B0 - ρ • ∑ i, U i - ρ • ∑ j, V j).PosSemidef

end RobustOpt2009.CQApproximation



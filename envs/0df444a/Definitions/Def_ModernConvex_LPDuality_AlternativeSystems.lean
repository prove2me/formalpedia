-- Prove2me | Definitions.Def_ModernConvex_LPDuality_AlternativeSystems
-- name    : ModernConvex_LPDuality_AlternativeSystems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:31:51.192244+00:00
-- url     : https://prove2.me/theorems/0957beab-70ee-4a43-a404-29fdecb2ccdd
-- title:
--   The systems $(\mathcal S)$, $\mathcal T_{\rm I}$, $\mathcal T_{\rm II}$ of the general theorem on the alternative
-- statement:
--   Let $a_1,\dots,a_m \in \mathbb R^n$, $b \in \mathbb R^m$, and let $m_s$ be the number of strict inequalities ($0 \le m_s \le m$). Following Proposition 1.3.1 of Ben-Tal and Nemirovski (pp. 13–14), the file defines three systems.
--
--   1. The system $(\mathcal S)$ in the unknown $x \in \mathbb R^n$:
--   $$a_i^Tx > b_i \ (i = 1,\dots,m_s), \qquad a_i^Tx \ge b_i \ (i = m_s+1,\dots,m).$$
--   2. The system $\mathcal T_{\rm I}$ in the unknown $\lambda \in \mathbb R^m$:
--   $$\lambda \ge 0,\qquad \sum_{i=1}^m \lambda_i a_i = 0,\qquad \sum_{i=1}^m \lambda_i b_i \ge 0,\qquad \sum_{i=1}^{m_s} \lambda_i > 0.$$
--   3. The system $\mathcal T_{\rm II}$ in the unknown $\lambda \in \mathbb R^m$:
--   $$\lambda \ge 0,\qquad \sum_{i=1}^m \lambda_i a_i = 0,\qquad \sum_{i=1}^m \lambda_i b_i > 0.$$
--
--   A solution of $\mathcal T_{\rm I}$ or $\mathcal T_{\rm II}$ is a certificate that $(\mathcal S)$ is infeasible; the general theorem on the alternative says that such a certificate always exists when $(\mathcal S)$ is infeasible.
--
--   **Formalization Note** Indices are $0$-based in Lean ($i \in \{0,\dots,m-1\}$), so the strict rows are those with $i < m_s$. When $m_s = 0$ the last condition of $\mathcal T_{\rm I}$ is an empty sum $> 0$ and cannot hold, so only $\mathcal T_{\rm II}$ can certify, as in the book. The bound $m_s \le m$ is a hypothesis of the theorems that use these systems.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, pp. 13–14, Proposition 1.3.1 (systems (S), T_I, T_II)

import Mathlib

open Matrix

namespace ModernConvex.LPDuality

/-- The system `(S)` of Proposition 1.3.1 (p. 13) in the unknown `x ∈ ℝⁿ`:
`aᵢᵀx > bᵢ` for `i = 1, …, m_s` and `aᵢᵀx ≥ bᵢ` for `i = m_s + 1, …, m`.
Indices are 0-based in Lean, so the strict rows are those with `i < ms`. -/
def SystemS {m n : ℕ} (ms : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    Prop :=
  ∀ i : Fin m, ((i : ℕ) < ms → b i < a i ⬝ᵥ x) ∧ (ms ≤ (i : ℕ) → b i ≤ a i ⬝ᵥ x)

/-- The system `T_I` of Proposition 1.3.1 (p. 14) in the unknown `λ ∈ ℝᵐ`:
`(a) λ ≥ 0`, `(b) ∑ λᵢaᵢ = 0`, `(c_I) ∑ λᵢbᵢ ≥ 0`, `(d_I) ∑_{i ≤ m_s} λᵢ > 0`. -/
def SystemTI {m n : ℕ} (ms : ℕ) (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (l : Fin m → ℝ) :
    Prop :=
  0 ≤ l ∧ ∑ i, l i • a i = 0 ∧ 0 ≤ ∑ i, l i * b i ∧
    0 < ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l i

/-- The system `T_II` of Proposition 1.3.1 (p. 14) in the unknown `λ ∈ ℝᵐ`:
`(a) λ ≥ 0`, `(b) ∑ λᵢaᵢ = 0`, `(c_II) ∑ λᵢbᵢ > 0`. -/
def SystemTII {m n : ℕ} (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (l : Fin m → ℝ) : Prop :=
  0 ≤ l ∧ ∑ i, l i • a i = 0 ∧ 0 < ∑ i, l i * b i

end ModernConvex.LPDuality



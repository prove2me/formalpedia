-- Prove2me | Definitions.Def_OnlinePerceptronIsolation_Binary_Supplement_SolutionsK
-- name    : OnlinePerceptronIsolation_Binary_Supplement_SolutionsK
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:06:43.795619+00:00
-- url     : https://prove2.me/theorems/d6bcc238-65c3-41b5-a1e9-1c6c83f1fc4d
-- title:
--   Equation (2.2) — general perceptron solutions
-- statement:
--   Let $G\in\mathbb R^{m\times n}$ and $K\subseteq\mathbb R$. A signing $\sigma$ has each coordinate exactly $-1$ or $+1$. Its feasibility is
--   $$\sigma\in S(G,K)\quad\Longleftrightarrow\quad\sigma\in\{-1,+1\}^n\ \text{and}\ \frac{\sum_{i=1}^nG_{ji}\sigma_i}{\sqrt n}\in K\quad\text{for every }j.$$
--   The normalized score is tested against the actual set $K$, without imposing a margin or replacing $K$ by its closure. This reuses the published sign predicate. Lean uses zero-based finite indices; at $n=0$ the total quotient is zero, an irrelevant finite-size convention for the asymptotic theorem.
-- source:
--   Shuangping Li, Gabe Schoenbach, STOC 2027 submission #485 (October 2026), Definition 2.1, Eq. (2.2), printed p. 6, PDF p. 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/485.pdf

import Mathlib
import Definitions.Def_OnlinePerceptronIsolation_Binary_Solutions
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OnlinePerceptronIsolation.Binary.Supplement

/-- Equation (2.2): the normalized score belongs to K in every row. -/
noncomputable def IsSolutionK {m n : ℕ} (G : Fin m × Fin n → ℝ)
    (K : Set ℝ) (σ : Fin n → ℝ) : Prop :=
  IsSigning σ ∧ ∀ j : Fin m, (∑ i : Fin n, G (j, i) * σ i) / Real.sqrt n ∈ K

end OnlinePerceptronIsolation.Binary.Supplement



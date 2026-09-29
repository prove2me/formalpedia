-- Prove2me | Definitions.Def_ImprovedLinBandits_OFUL_gramMatrix
-- name    : ImprovedLinBandits_OFUL_gramMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:18:31.736898+00:00
-- url     : https://prove2.me/theorems/19ce0027-d2a6-4a70-a3e9-c599e6883f4d
-- title:
--   Regularized Gram matrix $\overline V_t = V + \sum_{s\le t} X_s X_s^\top$
-- statement:
--   Let $V$ be a $d\times d$ real matrix and let $X_1, X_2, \dots$ be $\mathbb R^d$-valued random vectors on a sample space $\Omega$. For $t \ge 0$ and an outcome $\omega$, the **regularized Gram matrix** is
--
--   $$\overline V_t(\omega) = V + \sum_{s=1}^{t} X_s(\omega) X_s(\omega)^\top .$$
--
--   At $t = 0$ the sum is empty and $\overline V_0 = V$. When $V$ is positive definite, so is every $\overline V_t$, and the weighted norm $\|x\|_{\overline V_t^{-1}} = \sqrt{x^\top \overline V_t^{-1} x}$ is well defined.
--
--   This is the matrix $\overline V_t$ of Theorem 1, for a general positive definite $V$; with $V = \lambda I$ it is the platform's regularized design matrix.
--
--   **Formalization Note** Rounds are indexed by $s+1$ for $s \in \{0,\dots,t-1\}$, so the value $X_0$ is never used.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 4, Theorem 1 (definition of $\overline V_t$)

import Mathlib

open Matrix

namespace ImprovedLinBandits.OFUL

/-- The regularized Gram matrix of Theorem 1 (Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, p. 4):
for a `d × d` matrix `V` and actions `X 1, X 2, …`,
`V̄_t = V + ∑_{s=1}^t X_s X_sᵀ`. Rounds are indexed `s + 1` for `s ∈ Finset.range t`, so
`gramMatrix V X 0 ω = V` and the value `X 0` is never used. -/
noncomputable def gramMatrix {Ω : Type*} {d : ℕ} (V : Matrix (Fin d) (Fin d) ℝ)
    (X : ℕ → Ω → Fin d → ℝ) (t : ℕ) (ω : Ω) : Matrix (Fin d) (Fin d) ℝ :=
  V + ∑ s ∈ Finset.range t, vecMulVec (X (s + 1) ω) (X (s + 1) ω)

end ImprovedLinBandits.OFUL



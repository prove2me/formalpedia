-- Prove2me | Definitions.Def_RandomLPIPM_centralX
-- name    : RandomLPIPM_centralX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:16.227654+00:00
-- url     : https://prove2.me/theorems/e1693fd6-7532-4e2c-8c0f-90861db07f33
-- title:
--   The central path $\mu\mapsto x(\mu)$ of $(\mathrm{LP})$
-- statement:
--   For data $(A,b,c)$ and $\mu>0$, $x(\mu)$ denotes the minimizer of the normalized log-barrier $F_\mu(x)=c^\top x/\mu-\sum_i\log x_i$ over the strictly feasible points $\{x: Ax=b,\ x>0\}$. When (LP) satisfies the paper's standing assumptions ($A$ of full row rank, primal and dual strictly feasible), this minimizer exists and is unique for every $\mu>0$, and $\mu\mapsto x(\mu)$ is the primal central path; it satisfies $x(\mu)\cdot s(\mu)=\mu\mathbf 1$ with $s(\mu)=c-A^\top y(\mu)$ dual feasible.
--
--   The central path is the curve followed by Algorithm 1 and measured by the proximity $E_\mu$.
--
--   **Formalization Note** When no minimizer exists the value is the junk vector $0$. Every statement that uses $x(\mu)$ for a general (LP) assumes the standing hypotheses, under which the junk value never occurs; for LP(A) the point $\mathbf 1$ is strictly feasible and the minimizer always exists.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), p.4 and §9.1, p.77; (1), p.6 and p.22 for LP(A)

import Mathlib
import Definitions.Def_RandomLPIPM_IsCentralPoint

open Matrix

namespace RandomLPIPM

/-- **The central path `μ ↦ x(μ)` of (LP).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), p.4 and p.77 (barrier form); for LP(A)
also (1), p.6 and p.22.

`centralX A b c μ` is the minimizer of `F_μ` over the strictly feasible points (`IsCentralPoint`)
when one exists, and `0` otherwise.

**Formalization Note.** The paper's standing assumptions on (LP) (p.4: full row rank, primal and
dual strictly feasible) guarantee that the minimizer exists for every `μ > 0`, and it is unique
because `F_μ` is strictly convex on the feasible set; every statement that uses `centralX` for a
general (LP) carries these assumptions. The junk value `0` is never used under them. For LP(A)
(`b = A1`, `c = 1`) the point `(1, 0, 1)` is strictly feasible, so the minimizer always exists. -/
noncomputable def centralX {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (b : Fin d → ℝ)
    (c : Fin n → ℝ) (μ : ℝ) : Fin n → ℝ := by
  classical
  exact if h : ∃ x, IsCentralPoint A b c μ x then h.choose else 0

end RandomLPIPM



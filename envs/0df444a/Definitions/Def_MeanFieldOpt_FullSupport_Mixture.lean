-- Prove2me | Definitions.Def_MeanFieldOpt_FullSupport_Mixture
-- name    : MeanFieldOpt_FullSupport_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:41.468732+00:00
-- url     : https://prove2.me/theorems/06c54d89-0f84-4896-84dd-cc49210be463
-- title:
--   Mixture $\xi(t)=\sum_{k\ge2}c_k^2t^k$ with $\xi(1+\varepsilon)<\infty$, and its derivatives $\xi'$, $\xi''$
-- statement:
--   The Ising mixed $p$-spin model is parametrized by real coefficients $(c_k)_{k\ge 2}$, encoded in the **mixture**
--
--   $$
--   \xi(t) = \sum_{k\ge 2} c_k^2\, t^k .
--   $$
--
--   Throughout the paper one assumes $\xi(1+\varepsilon) < \infty$ for some $\varepsilon > 0$, i.e. $\sum_{k} c_k^2 (1+\varepsilon)^k < \infty$. The first two derivatives are the power series
--
--   $$
--   \xi'(t) = \sum_{k\ge 2} k\, c_k^2\, t^{k-1}, \qquad \xi''(t) = \sum_{k\ge 2} k(k-1)\, c_k^2\, t^{k-2},
--   $$
--
--   which converge on $[0,1]$ under the standing assumption. Since all coefficients are non-negative, $\xi'$ and $\xi''$ are non-negative and non-decreasing on $[0,1]$, and $\xi''$ is continuous there.
--
--   The mixture enters every object of the variational principle: the Parisi PDE, the space $\mathscr L$, the Parisi functional, and the SDE driving the analysis.
--
--   **Formalization Note** A mixture is a sequence `c : ℕ → ℝ` with `c 0 = c 1 = 0` (the indices $k = 0, 1$ do not occur in the paper) and the summability of $c_k^2(1+\varepsilon)^k$ for some $\varepsilon>0$. The functions $\xi$, $\xi'$, $\xi''$ are defined as explicit series (`tsum`), not as derivatives of $\xi$; for $k=0,1$ the natural-number exponents $k-1$, $k-2$ are truncated, but the corresponding terms vanish because $c_0=c_1=0$. Outside the disc of convergence `tsum` returns $0$; only $t\in[0,1]$ is ever used.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 2, Section 1 (definition of the mixture and the assumption ξ(1+ε) < ∞)

import Mathlib

namespace MeanFieldOpt.FullSupport

/-- The mixture of a mixed p-spin model (El Alaoui–Montanari–Sellke, arXiv:2001.00904v1, p. 2):
coefficients `c k` (only `k ≥ 2` occur, so `c 0 = c 1 = 0`) with the standing assumption
`ξ(1 + ε) = ∑ c_k² (1 + ε)^k < ∞` for some `ε > 0`. -/
structure Mixture where
  c : ℕ → ℝ
  c_zero : c 0 = 0
  c_one : c 1 = 0
  summable : ∃ ε : ℝ, 0 < ε ∧ Summable (fun k : ℕ => c k ^ 2 * (1 + ε) ^ k)

namespace Mixture

/-- `ξ(t) = ∑_{k ≥ 2} c_k² t^k`. -/
noncomputable def xi (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, ξ.c k ^ 2 * t ^ k

/-- `ξ'(t) = ∑_{k ≥ 2} k c_k² t^{k-1}` (the terms `k = 0, 1` vanish since `c 0 = c 1 = 0`). -/
noncomputable def d1 (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ξ.c k ^ 2 * t ^ (k - 1)

/-- `ξ''(t) = ∑_{k ≥ 2} k (k - 1) c_k² t^{k-2}` (the terms `k = 0, 1` vanish). -/
noncomputable def d2 (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * ξ.c k ^ 2 * t ^ (k - 2)

end Mixture

end MeanFieldOpt.FullSupport



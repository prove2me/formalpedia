-- Prove2me | Definitions.Def_MeanFieldOpt_NoOverlapGap_Mixture
-- name    : MeanFieldOpt_NoOverlapGap_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T02:45:27.955931+00:00
-- url     : https://prove2.me/theorems/5b5e62ad-ec38-4194-8231-7ba665c30c0c
-- title:
--   Mixture $\xi(t)=\sum_{k\ge2}c_k^2t^k$ with $\xi(1+\varepsilon)<\infty$, and its series $\xi'$, $\xi''$
-- statement:
--   A **mixed $p$-spin model** is described by real coefficients $(c_k)_{k\ge 2}$, encoded in the **mixture**
--
--   $$\xi(t) = \sum_{k\ge 2} c_k^2\, t^k .$$
--
--   Throughout, one assumes the standing condition $\xi(1+\varepsilon) < \infty$ for some $\varepsilon > 0$, that is, $\sum_k c_k^2 (1+\varepsilon)^k$ converges. Under this condition the series
--
--   $$\xi'(t) = \sum_{k\ge 2} k\, c_k^2\, t^{k-1}, \qquad \xi''(t) = \sum_{k\ge 2} k(k-1)\, c_k^2\, t^{k-2}$$
--
--   converge on $[0,1]$ and are the first and second derivatives of $\xi$ there. Since all coefficients $c_k^2$ are non-negative, $\xi''$ is non-negative and non-decreasing on $[0,1]$, and it is strictly positive on $(0,1]$ as soon as some $c_k \neq 0$.
--
--   The mixture is the only datum of the model that enters the Parisi variational principle: the Parisi PDE, the functional $\mathsf P$ and the spaces $\mathscr U$ and $\mathscr L$ are all built from $\xi'$ and $\xi''$.
--
--   **Formalization Note** The coefficients are a sequence $c : \mathbb N \to \mathbb R$ with $c_0 = c_1 = 0$ imposed, so that every sum may run over all $k \in \mathbb N$; the terms $k = 0, 1$ vanish, which also neutralises the truncated natural-number exponents $k-1$, $k-2$. The functions $\xi, \xi', \xi''$ are the explicit power series, not derivatives of a series.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 2, Section 1 (definition of the mixture and the standing assumption ξ(1+ε) < ∞)

import Mathlib

namespace MeanFieldOpt.NoOverlapGap

/-- The mixture of a mixed p-spin model (El Alaoui–Montanari–Sellke, arXiv:2001.00904v1, p. 2):
coefficients `(c_k)_{k ≥ 2}`, encoded as a sequence `c : ℕ → ℝ` with `c 0 = c 1 = 0`, together
with the standing assumption `ξ(1 + ε) < ∞` for some `ε > 0`. -/
structure Mixture where
  /-- The coefficients `c_k`; only `k ≥ 2` occur. -/
  c : ℕ → ℝ
  c_zero : c 0 = 0
  c_one : c 1 = 0
  /-- Standing assumption (p. 2): `ξ(1 + ε) = Σ_k c_k² (1 + ε)^k < ∞` for some `ε > 0`. -/
  summable_one_add : ∃ ε : ℝ, 0 < ε ∧ Summable (fun k : ℕ => c k ^ 2 * (1 + ε) ^ k)

namespace Mixture

/-- `ξ(t) = Σ_{k ≥ 2} c_k² t^k`. -/
noncomputable def xi (m : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, m.c k ^ 2 * t ^ k

/-- `ξ'(t) = Σ_{k ≥ 2} k c_k² t^{k-1}` (the terms `k = 0, 1` vanish since `c 0 = c 1 = 0`). -/
noncomputable def xi' (m : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * m.c k ^ 2 * t ^ (k - 1)

/-- `ξ''(t) = Σ_{k ≥ 2} k (k-1) c_k² t^{k-2}` (the terms `k = 0, 1` vanish since `c 0 = c 1 = 0`). -/
noncomputable def xi'' (m : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * m.c k ^ 2 * t ^ (k - 2)

end Mixture

end MeanFieldOpt.NoOverlapGap



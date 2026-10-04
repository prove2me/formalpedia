-- Prove2me | Definitions.Def_MeanFieldOpt_ControlDuality_Mixture
-- name    : MeanFieldOpt_ControlDuality_Mixture
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T03:26:06.679488+00:00
-- url     : https://prove2.me/theorems/c002ca33-7bd5-4cd3-884d-0f7349733ee3
-- title:
--   Mixture $\xi(t)=\sum_{k\ge2}c_k^2t^k$ with $\xi(1+\varepsilon)<\infty$, and its derivatives $\xi'$, $\xi''$
-- statement:
--   A mixed $p$-spin model is encoded by real coefficients $(c_k)_{k\ge 2}$ through its **mixture**
--   $$\xi(t)=\sum_{k\ge 2}c_k^2\,t^k .$$
--   Throughout the paper it is assumed that $\xi(1+\varepsilon)<\infty$ for some $\varepsilon>0$, i.e. the series $\sum_k c_k^2(1+\varepsilon)^k$ converges. Under this assumption the series and its termwise derivatives converge on $[0,1]$, and we write
--   $$\xi'(t)=\sum_{k\ge 2}k\,c_k^2\,t^{k-1},\qquad \xi''(t)=\sum_{k\ge 2}k(k-1)\,c_k^2\,t^{k-2}.$$
--   Since all coefficients $c_k^2$ are nonnegative, $\xi'$ and $\xi''$ are nonnegative and nondecreasing on $[0,1]$, and $\xi'(0)=0$.
--
--   These are the basic data of every object in the mission: $\xi''$ is the diffusion coefficient of the control problem and of the Parisi PDE, and $\xi'$ fixes the variances in the Cole–Hopf formula.
--
--   **Formalization Note** The coefficients are a sequence $c:\mathbb N\to\mathbb R$ with $c_0=c_1=0$ imposed (the paper's sums start at $k=2$). $\xi'$ and $\xi''$ are defined as the explicit termwise series, not as derivatives of $\xi$; they agree with the derivatives on $[0,1]$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 2, Section 1 (mixture ξ and the standing assumption ξ(1+ε) < ∞)

import Mathlib

namespace MeanFieldOpt.ControlDuality

/-- The mixture `ξ(t) = ∑_{k ≥ 2} c_k² t^k` of a mixed p-spin model (El Alaoui–Montanari–Sellke,
arXiv:2001.00904v1, p. 2). The coefficients are a sequence `c : ℕ → ℝ`; the indices `k = 0, 1`
do not occur in the paper, so `c 0 = c 1 = 0` is imposed. The standing assumption of the paper,
`ξ(1 + ε) < ∞` for some `ε > 0`, is the summability field. -/
structure Mixture where
  /-- The coefficients `c_k`; only `k ≥ 2` occur. -/
  c : ℕ → ℝ
  c_zero : c 0 = 0
  c_one : c 1 = 0
  /-- Standing assumption (p. 2): `ξ(1 + ε) = ∑ c_k² (1 + ε)^k < ∞` for some `ε > 0`. -/
  summable : ∃ ε : ℝ, 0 < ε ∧ Summable (fun k : ℕ => c k ^ 2 * (1 + ε) ^ k)

namespace Mixture

/-- `ξ(t) = ∑_k c_k² t^k`. -/
noncomputable def xi (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, ξ.c k ^ 2 * t ^ k

/-- `ξ'(t) = ∑_k k c_k² t^{k-1}`, the termwise derivative (the `k = 0` term vanishes). -/
noncomputable def xi' (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ξ.c k ^ 2 * t ^ (k - 1)

/-- `ξ''(t) = ∑_k k (k - 1) c_k² t^{k-2}`, the termwise second derivative (the `k = 0, 1` terms
vanish). -/
noncomputable def xi'' (ξ : Mixture) (t : ℝ) : ℝ :=
  ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * ξ.c k ^ 2 * t ^ (k - 2)

end Mixture

end MeanFieldOpt.ControlDuality



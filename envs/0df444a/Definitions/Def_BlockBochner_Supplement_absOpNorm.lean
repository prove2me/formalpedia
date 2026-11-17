-- Prove2me | Definitions.Def_BlockBochner_Supplement_absOpNorm
-- name    : BlockBochner_Supplement_absOpNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:28:25.472456+00:00
-- url     : https://prove2.me/theorems/9a9c7005-2135-443f-bb66-10c622ff21be
-- title:
--   Operator norm $\|J_{\mathrm{abs}}\|_{\mathrm{op}}$ of the entrywise absolute value
-- statement:
--   For a real $V\times V$ matrix $J$, let $J_{\mathrm{abs}}=(|J_{xy}|)_{x,y\in V}$ be its entrywise absolute value. $\|J_{\mathrm{abs}}\|_{\mathrm{op}}$ is the operator norm of $J_{\mathrm{abs}}$ acting on the Euclidean space $\ell^2(V)$, i.e. its largest singular value (for symmetric $J$, the largest eigenvalue of the nonnegative matrix $J_{\mathrm{abs}}$).
--
--   This is the interaction strength in Theorem 5: the Glauber spectral gap of the $O(N)$ model is at least $(1-\|J_{\mathrm{abs}}\|_{\mathrm{op}}/N)/n$.
--
--   **Formalization Note** The norm of `Matrix.toEuclideanCLM` applied to `J.map (|·|)`.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Sec. 1.3, p.4 (PDF p.5); Theorem 5, p.5 (PDF p.6)

import Mathlib

namespace BlockBochner.Supplement

/-- **`‖J_abs‖_op`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 1.3, p.4 (`J_abs = (|J_xy|)_{x,y∈V}`) and
Theorem 5, p.5 / p.26: the operator norm of the entrywise absolute value of `J`.

**Formalization Note** The norm of `J_abs` as a continuous linear operator on the Euclidean space
`ℓ²(V)` (`Matrix.toEuclideanCLM`), i.e. its spectral norm (largest singular value). -/
noncomputable def absOpNorm {V : Type*} [Fintype V] [DecidableEq V] (J : Matrix V V ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (J.map fun a => |a|)‖

end BlockBochner.Supplement



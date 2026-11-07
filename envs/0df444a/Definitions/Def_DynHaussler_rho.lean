-- Prove2me | Definitions.Def_DynHaussler_rho
-- name    : DynHaussler_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:34:41.502674+00:00
-- url     : https://prove2.me/theorems/7551fe75-4e76-460c-b157-f37fa29e746c
-- title:
--   Normalized $\ell_p$ distance $\rho_{p,T}$
-- statement:
--   For $u,v\in\mathbb R^T$ and $1\le p<\infty$, the **normalized $\ell_p$ distance** is
--   $$
--   \rho_{p,T}(u,v)=\Bigl(\frac1T\sum_{t=1}^T|u_t-v_t|^p\Bigr)^{1/p}.
--   $$
--
--   This is the accuracy measure of the global dynamic covers of Definition 4; for binary vectors $\rho_{p,T}(u,v)^p$ is the normalized Hamming distance.
--
--   **Formalization Note** Vectors are maps `Fin T → ℝ` (0-based rounds), and both powers are real powers (`Real.rpow`). The statements using $\rho$ assume $1\le p$ and, where the paper does, $T\ge1$.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eq. (18), p.13 (PDF p.15)

import Mathlib

set_option autoImplicit false

namespace DynHaussler

/-- The **normalized `ℓ_p` distance** on `ℝ^T`,
`ρ_{p,T}(u, v) = ((1/T) ∑_{t=1}^T |u_t − v_t|^p)^{1/p}`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eq. (18), p.13 (PDF p.15).

**Formalization Note** Rounds are 0-based (`Fin T`). Both powers are `Real.rpow`; the paper takes
`1 ≤ p < ∞` and `T ≥ 1`, and every statement using `rho` assumes both. -/
noncomputable def rho (p : ℝ) {T : ℕ} (u v : Fin T → ℝ) : ℝ :=
  ((1 / (T : ℝ)) * ∑ t, |u t - v t| ^ p) ^ (1 / p)

end DynHaussler



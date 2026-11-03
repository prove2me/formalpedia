-- Prove2me | Definitions.Def_MonoInclCLC_phi
-- name    : MonoInclCLC_phi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:21.598983+00:00
-- url     : https://prove2.me/theorems/192a0d75-d60a-44c6-9c51-f1a6421f3643
-- title:
--   §2.1, p.4 — the function $\varphi(\lambda,x)=\lambda^{1/(p-1)}\|x-(I+\lambda A)^{-1}x\|$
-- statement:
--   For an integer $p\ge 2$, the function $\varphi:[0,+\infty)\times\mathcal H\to[0,+\infty)$ is
--   $$
--   \varphi(\lambda,x)=\lambda^{\frac{1}{p-1}}\big\|x-(I+\lambda A)^{-1}x\big\|,\qquad \varphi(0,x)=0.
--   $$
--   The algebraic equation of the closed-loop system says exactly that $\varphi(\lambda(t),x(t))=\theta^{1/(p-1)}$, so the monotonicity of $\varphi$ in $\lambda$ determines the feedback law.
--
--   **Formalization Note** The resolvent is passed as a family $J$, the exponent is a real power, and the function takes the value $0$ for $\lambda\le 0$; negative $\lambda$ occurs in no statement of the mission. All theorems about $\varphi$ assume $p\ge 2$, since $1/(p-1)$ has no meaning at $p=1$.
-- source:
--   Lin, Jordan, Monotone Inclusions, Acceleration and Closed-Loop Control, arXiv:2111.08093v4, §2.1, p.4 (the display defining ϕ)

import Mathlib

namespace MonoInclCLC

/-- **The function `ϕ`** (Lin, Jordan, *Monotone Inclusions, Acceleration and Closed-Loop Control*, arXiv:2111.08093v4, §2.1, p.4): for `p ≥ 2`, `ϕ : [0, +∞) × H ↦ [0, +∞)` is given by
`ϕ(λ, x) = λ^(1/(p-1)) ‖x - (I + λA)⁻¹x‖` and `ϕ(0, x) = 0`.

**Formalization Note.** `J l` is the resolvent `(I + l A)⁻¹` for `l > 0`. The exponent `1/(p-1)` is
a real power and is only used for `p ≥ 2` (for `p = 1` it would be the junk value `1/0 = 0`; every
theorem on `phi` assumes `2 ≤ p`). The value is `0` for `l ≤ 0`; the paper's domain is `l ≥ 0`, and
negative `l` occurs in no statement of this mission. -/
noncomputable def phi {H : Type*} [NormedAddCommGroup H]
    (J : ℝ → H → H) (p : ℕ) (l : ℝ) (x : H) : ℝ :=
  if 0 < l then l ^ (1 / ((p : ℝ) - 1)) * ‖x - J l x‖ else 0

end MonoInclCLC



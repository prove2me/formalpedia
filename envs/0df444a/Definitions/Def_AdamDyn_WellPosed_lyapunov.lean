-- Prove2me | Definitions.Def_AdamDyn_WellPosed_lyapunov
-- name    : AdamDyn_WellPosed_lyapunov
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T22:07:03.901381+00:00
-- url     : https://prove2.me/theorems/e9c74773-a7c1-4cca-8d49-dc77d5a282da
-- title:
--   The Lyapunov functions $V(t,z)$ (3.4), $U(t,v)$ (3.5), and their limits $U_\infty, V_\infty$
-- statement:
--   In the setting of the continuous-time Adam field (constants $a, b, \varepsilon$, a function $F : \mathbb R^d \to \mathbb R$, states $z = (x, m, v) \in \mathbb R^d \times \mathbb R^d \times \mathbb R^d$), define for $t > 0$ and a coordinate $v_i \ge 0$
--   $$U(t, v_i) := a\,(1 - e^{-at})\left(\varepsilon + \sqrt{\frac{v_i}{1 - e^{-bt}}}\right), \qquad U_\infty(v_i) := a\,(\varepsilon + \sqrt{v_i}),$$
--   and, for $z = (x,m,v)$ with $v \ge 0$,
--   $$V(t, z) := F(x) + \frac12 \sum_{i=1}^d \frac{m_i^2}{U(t, v_i)}, \qquad V_\infty(z) := F(x) + \frac12 \sum_{i=1}^d \frac{m_i^2}{U_\infty(v_i)}.$$
--   Thus $V(t,z) = F(x) + \tfrac12\|m\|^2_{U(t,v)^{-1}}$ with the weighted norm $\|m\|^2_w = \sum_i w_i m_i^2$, and $U_\infty(v) = \lim_{t\to\infty} U(t,v)$, $V_\infty(z) = \lim_{t\to\infty} V(t,z)$ when $a, b, \varepsilon > 0$.
--
--   $V$ is the Lyapunov function of the non-autonomous Adam equation and $V_\infty$ that of its autonomous limit: the monotonicity of $t \mapsto V(t, z(t))$ along solutions is the key estimate of the existence and boundedness proof.
--
--   **Formalization Note.** $U_\infty$ and $V_\infty$ are defined by their closed forms (the limits computed on p. 12 of the paper), not as limits. All objects are only meaningful for $t > 0$ and $v \ge 0$; the theorems using them only evaluate them there. The debiasing map $\bar e$ (p. 13) is not declared here; it is `AdamDyn.ODEConv.ebar` in the module of the Adam fields, which this file imports.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5, Eqs. (3.4)–(3.5); p. 12 (U∞, V∞)

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField
import Definitions.Def_AdamDyn_ODEConv_AdamField

namespace AdamDyn.WellPosed

variable {d : ℕ}

/-- `U(t, v) = a(1 − e^{−at})(ε + √(v / (1 − e^{−bt})))` of (3.5), one coordinate `v = v_i ≥ 0`,
`t > 0`. -/
noncomputable def lyapU (a b ε t vi : ℝ) : ℝ :=
  a * (1 - Real.exp (-(a * t))) * (ε + Real.sqrt (vi / (1 - Real.exp (-(b * t)))))

/-- The Lyapunov function (3.4): `V(t, z) = F(x) + ½ ‖m‖²_{U(t,v)⁻¹} = F(x) + ½ Σᵢ mᵢ² / U(t, vᵢ)`,
for `t > 0` and `z = (x, m, v) ∈ 𝒵₊`. -/
noncomputable def lyapV (a b ε : ℝ) (F : Vec d → ℝ) (t : ℝ) (z : State d) : ℝ :=
  F z.1 + (1 / 2) * ∑ i, (z.2.1 i) ^ 2 / lyapU a b ε t (z.2.2 i)

/-- `U∞(v) = lim_{t→∞} U(t, v) = a(ε + √v)` (p. 12), one coordinate `v = v_i ≥ 0`. -/
noncomputable def lyapUInf (a ε vi : ℝ) : ℝ := a * (ε + Real.sqrt vi)

/-- `V∞(z) = lim_{t→∞} V(t, z) = F(x) + ½ Σᵢ mᵢ² / U∞(vᵢ)` (p. 12), for `z ∈ 𝒵₊`. -/
noncomputable def lyapVInf (a ε : ℝ) (F : Vec d → ℝ) (z : State d) : ℝ :=
  F z.1 + (1 / 2) * ∑ i, (z.2.1 i) ^ 2 / lyapUInf a ε (z.2.2 i)

end AdamDyn.WellPosed



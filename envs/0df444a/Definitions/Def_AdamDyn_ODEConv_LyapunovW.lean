-- Prove2me | Definitions.Def_AdamDyn_ODEConv_LyapunovW
-- name    : AdamDyn_ODEConv_LyapunovW
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:10:27.061186+00:00
-- url     : https://prove2.me/theorems/8c766e5e-f556-49c3-baf6-f8701b5a5fa3
-- title:
--   $U_\infty$, $V_\infty$, the function $W_\delta$ of (7.9) and the equilibrium set $\mathcal E$
-- statement:
--   With $a, \varepsilon$, $F$, $S$ as in the definition of the Adam field and $z = (x, m, v) \in \mathcal Z_+$:
--
--   1. $U_\infty(v) = a(\varepsilon + \sqrt v)$ coordinatewise, the limit as $t \to \infty$ of $U(t, v)$ in (3.5).
--   2. $V_\infty(z) = \lim_{t\to\infty} V(t,z)$, where $V$ is (3.4):
--   $$V_\infty(x, m, v) = F(x) + \frac12 \|m\|^2_{U_\infty(v)^{-1}} = F(x) + \frac12 \sum_{i=1}^d \frac{m_i^2}{a(\varepsilon + \sqrt{v_i})}.$$
--   3. For $\delta > 0$, the function of (7.9):
--   $$W_\delta(x, m, v) = V_\infty(x, m, v) - \delta \langle \nabla F(x), m\rangle + \delta \|S(x) - v\|^2 .$$
--   4. The set of equilibrium points of $(\mathrm{ODE}_\infty)$:
--   $$\mathcal E = h_\infty^{-1}(\{0\}) = \{ (x, m, v) \in \mathcal Z_+ : \nabla F(x) = 0,\ m = 0,\ v = S(x) \}.$$
--
--   $V_\infty$ decreases along $h_\infty$ (Lemma 7.5) and $W_\delta$, for small $\delta$, is a strict Lyapunov function of the autonomous Adam semiflow (Proposition 7.15); $\mathcal E$ is its set of equilibria.
--
--   **Formalization Note** $\|\cdot\|$ and $\langle\cdot,\cdot\rangle$ are the Euclidean norm and inner product of $\mathbb R^d$. $V_\infty$ uses $\sqrt{v_i}$ and is meant on $\mathcal Z_+$ only, as in the paper (Lean's square root of a negative number is $0$).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 5 (Eqs. (3.4), (3.5)), p. 12 (U∞, V∞), p. 18 (Eq. (7.9), the set ℰ)

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

namespace AdamDyn.ODEConv

/-- `U∞(v) = a(ε + √v)` coordinatewise (p. 12), the limit of `U(t, v)` of (3.5) as `t → ∞`. -/
noncomputable def Uinf {d : ℕ} (a ε : ℝ) (v : AdamDyn.WellPosed.Vec d) : AdamDyn.WellPosed.Vec d :=
  WithLp.toLp 2 (fun i => a * (ε + Real.sqrt (v i)))

/-- `V∞(z) = lim_{t→∞} V(t, z) = F(x) + ½ ‖m‖²_{U∞(v)^{−1}} = F(x) + ½ ∑ᵢ mᵢ² / (a(ε + √vᵢ))`
for `z = (x, m, v) ∈ 𝒵₊` (pp. 5, 12; (3.4)). -/
noncomputable def Vinf {d : ℕ} (a ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (z : AdamDyn.WellPosed.State d) : ℝ :=
  F z.1 + (1 / 2) * ∑ i, (z.2.1 i) ^ 2 / Uinf a ε z.2.2 i

/-- `W_δ(x, m, v) = V∞(x, m, v) − δ⟨∇F(x), m⟩ + δ‖S(x) − v‖²` of (7.9) (p. 18), for
`z = (x, m, v) ∈ 𝒵₊`. -/
noncomputable def Wdelta {d : ℕ} (a ε δ : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (z : AdamDyn.WellPosed.State d) : ℝ :=
  Vinf a ε F z - δ * inner ℝ (gradient F z.1) z.2.1 + δ * ‖S z.1 - z.2.2‖ ^ 2

/-- The set `ℰ = h∞⁻¹({0}) = {(x, m, v) ∈ 𝒵₊ : ∇F(x) = 0, m = 0, v = S(x)}` of equilibrium points
of `(ODE_∞)` (p. 18). -/
def equilibriumSet {d : ℕ} (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d) : Set (AdamDyn.WellPosed.State d) :=
  {z | (∀ i, 0 ≤ z.2.2 i) ∧ gradient F z.1 = 0 ∧ z.2.1 = 0 ∧ z.2.2 = S z.1}

end AdamDyn.ODEConv



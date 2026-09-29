-- Prove2me | Definitions.Def_AdSCFTFocusingProfiles
-- name    : AdSCFTFocusingProfiles
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-15T11:37:32.882851+00:00
-- url     : https://prove2.me/theorems/44144db4-55bf-41f6-80d2-a5367c5a2dbe
-- title:
--   Focusing profiles and Riccati data for conformally compact metrics
-- statement:
--   This definition bundle fixes the analytic objects used in Anderson's boundary-distance estimate for conformally compact metrics ([arXiv:hep-th/0403087v2](https://arxiv.org/abs/hep-th/0403087), §4 and §6).
--
--   Let $(M, g)$ be an $(n+1)$-dimensional $C^3$ conformally compact metric, let $\partial_0 M$ be a boundary component with boundary metric $\gamma$, and let $\rho$ be the associated geodesic defining function, so that $\bar g = \rho^2 g$ is the partial geodesic compactification and $\rho(x) = \operatorname{dist}_{\bar g}(x, \partial_0 M)$. Along the $\bar g$-geodesics normal to $\partial_0 M$ write $\bar\Delta\rho$ for the mean curvature of the level set $S(\rho)$, $\bar D^2\rho$ for the second fundamental form, and $T = \bar\nabla\rho$ for the unit normal. The quantity that drives the argument is
--
--   $$\varphi(\rho) \;=\; -\frac{\bar\Delta\rho}{\rho}.$$
--
--   **1. `FocusingProfileAH n L phi phi'`** records the Riemannian focusing inequality (4.7): the function $\varphi$, represented by `phi`, is differentiable at every point of the parameter interval $[0, L]$ with derivative `phi'`, and satisfies
--
--   $$\varphi'(\rho) \;\ge\; \frac{\rho\,\varphi(\rho)^2}{n}, \qquad \rho \in [0, L].$$
--
--   **2. `FocusingProfileDS n L phi phi'`** records the Lorentzian counterpart (6.17), where the Raychaudhuri equation reverses the sign:
--
--   $$\varphi'(\rho) \;\le\; -\frac{\rho\,\varphi(\rho)^2}{n}, \qquad \rho \in [0, L].$$
--
--   **3. `RiccatiData n L`** packages the geometric input of the proof as data about real functions of $\rho \in (0, L)$: the mean curvature $H = \bar\Delta\rho$ with its derivative $H'$, the squared norm $|K|^2 = |\bar D^2\rho|^2$, and the energy term $S = (\mathrm{Ric}_g + n g)(T, T)$, subject to the Riccati equation (4.3) in the form
--
--   $$H'(\rho) + |K|^2(\rho) - \frac{H(\rho)}{\rho} + \frac{S(\rho)}{\rho^2} \;=\; 0,$$
--
--   which is (4.3) after substituting the conformal-change identity $\overline{\mathrm{Ric}}(T,T) = -\bar\Delta\rho/\rho + (\mathrm{Ric}_g + n g)(T,T)/\rho^2$ of (4.4)–(4.5), together with the trace inequality $|K|^2 \ge H^2/n$ and the curvature hypothesis $S \ge 0$ coming from $\mathrm{Ric}_g + n g \ge 0$ in (4.1).
--
--   These three items are the interface every statement of the mission is phrased against; they isolate exactly the one-dimensional data that the comparison argument of §4 consumes.
--
--   **Formalization Note** Mathlib presently has no Ricci curvature of a Riemannian manifold, so the geometry of §4 is not available as a formal object. The definitions above therefore carry the geometric input as hypotheses on real functions of the distance parameter $\rho$: no manifold, metric, or curvature tensor appears. The dimension enters only through the natural number $n$, which is coerced to a real number in the inequalities; the parameter interval is $[0, L]$ with $L$ an arbitrary real, and $L = 0$ is allowed.
-- source:
--   M. T. Anderson, Geometric aspects of the AdS/CFT correspondence, arXiv:hep-th/0403087v2, https://arxiv.org/abs/hep-th/0403087, pp. 13-14, Section 4, equations (4.1) and (4.3)-(4.7); p. 19, Section 6, equation (6.17)

import Mathlib

namespace AdSCFT

/-- Focusing profile in the Riemannian (asymptotically hyperbolic) case:
inequality (4.7) of M. T. Anderson, "Geometric aspects of the AdS/CFT
correspondence", arXiv:hep-th/0403087v2, §4.

Here `phi` stands for the function `φ(ρ) = -Δ̄ρ/ρ` built from the geodesic
compactification `ḡ = ρ²g` of an asymptotically hyperbolic metric `g` along the
`ḡ`-geodesics normal to the boundary component `∂₀M`, where `ρ(x) = dist_ḡ(x, ∂₀M)`
and `Δ̄ρ` is the mean curvature of the level set `S(ρ)`; `phi'` is the derivative of
`phi` in `ρ`, and `[0, L]` is the parameter interval on which the profile is
defined. -/
def FocusingProfileAH (n : ℕ) (L : ℝ) (phi phi' : ℝ → ℝ) : Prop :=
  (∀ r ∈ Set.Icc (0 : ℝ) L, HasDerivAt phi (phi' r) r) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) L, r * (phi r) ^ 2 / n ≤ phi' r)

/-- Focusing profile in the Lorentzian (de Sitter) case: inequality (6.17) of
M. T. Anderson, "Geometric aspects of the AdS/CFT correspondence",
arXiv:hep-th/0403087v2, §6.

Along the timelike geodesics orthogonal to past conformal infinity the
Raychaudhuri equation reverses the sign of the focusing inequality, so the same
function `φ(ρ) = -Δ̄ρ/ρ` satisfies `φ' ≤ -ρφ²/n` on the parameter interval
`[0, L]`. -/
def FocusingProfileDS (n : ℕ) (L : ℝ) (phi phi' : ℝ → ℝ) : Prop :=
  (∀ r ∈ Set.Icc (0 : ℝ) L, HasDerivAt phi (phi' r) r) ∧
  (∀ r ∈ Set.Icc (0 : ℝ) L, phi' r ≤ -(r * (phi r) ^ 2 / n))

/-- Riccati data along the geodesics normal to the boundary: equations
(4.3)–(4.5) of M. T. Anderson, "Geometric aspects of the AdS/CFT correspondence",
arXiv:hep-th/0403087v2, §4, recorded as data about real functions of the distance
parameter `r = ρ ∈ (0, L)`.

* `H r` is the mean curvature `Δ̄ρ` of the level set `S(ρ)` in the compactified
  metric `ḡ = ρ²g`, and `H' r` is its derivative in `ρ`;
* `Ksq r` is `|D̄²ρ|²`, the squared norm of the second fundamental form of `S(ρ)`;
* `S r` is the energy term `(Ric_g + n g)(T, T)` evaluated on the unit normal `T`.

The field `riccati` is the Riccati equation `H̄' + |K̄|² + R̄ic(T,T) = 0` of (4.3)
after substituting the conformal-change identity
`R̄ic(T,T) = -Δ̄ρ/ρ + (Ric_g + n g)(T,T)/ρ²` of (4.4)–(4.5); `cauchySchwarz` is the
trace inequality `|D̄²ρ|² ≥ (Δ̄ρ)²/n`; and `energy` is the curvature hypothesis
`Ric_g + n g ≥ 0` of (4.1) evaluated on `T`. -/
structure RiccatiData (n : ℕ) (L : ℝ) where
  H : ℝ → ℝ
  H' : ℝ → ℝ
  Ksq : ℝ → ℝ
  S : ℝ → ℝ
  hasDeriv : ∀ r ∈ Set.Ioo (0 : ℝ) L, HasDerivAt H (H' r) r
  riccati : ∀ r ∈ Set.Ioo (0 : ℝ) L, H' r + Ksq r - H r / r + S r / r ^ 2 = 0
  cauchySchwarz : ∀ r ∈ Set.Ioo (0 : ℝ) L, (H r) ^ 2 / n ≤ Ksq r
  energy : ∀ r ∈ Set.Ioo (0 : ℝ) L, 0 ≤ S r

end AdSCFT



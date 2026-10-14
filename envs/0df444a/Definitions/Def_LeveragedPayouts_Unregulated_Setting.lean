-- Prove2me | Definitions.Def_LeveragedPayouts_Unregulated_Setting
-- name    : LeveragedPayouts_Unregulated_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:23:45.238414+00:00
-- url     : https://prove2.me/theorems/64b8e41a-d7a1-4736-9448-17c2e36abb1b
-- title:
--   §2.1, §3.1–3.4 and (59) — Inada conditions, the economy (20), effort (8)/(34), labour demand (8)/(35), the date-0 surplus (59) and an optimal date-0 rate
-- statement:
--   This file fixes the date-0 economy of Acharya and Plantin's model of monetary easing with a downward-rigid wage.
--
--   **Inada conditions.** A function $f:\mathbb R\to\mathbb R$ satisfies the *Inada conditions* (with twice continuous differentiability) if $f(0)=0$, $f$ is continuous on $[0,\infty)$ and $C^2$ on $(0,\infty)$, $f'>0$ and $f''<0$ on $(0,\infty)$, $f'(l)\to+\infty$ as $l\downarrow 0$ and $f'(l)\to 0$ as $l\to\infty$. The $C^1$ version used for $g$ asks for $C^1$ on $(0,\infty)$ and $g'$ strictly decreasing there instead of $g''<0$.
--
--   **The economy.** An economy consists of
--   1. a discount rate $R>1$ and an effort-cost parameter $\pi\in(0,1)$ (not the circle constant);
--   2. the capital-good technology $f$ (Inada, $C^2$) and the consumption-good technology $g$ (Inada, $C^1$);
--   3. the laissez-faire steady-state labour $l^*\in(0,1)$ supplied to entrepreneurs and the wage $w^*$, which solve (20):
--   $$\frac{\pi}{2R}f'(l^*)=g'(1-l^*)=w^*.$$
--
--   **First-best date-0 labour.** When the date-0 consumption-good technology is $\rho g$, the first-best date-0 labour $l_\rho\in(0,1)$ solves
--   $$\frac{\pi f'(l_\rho)}{2R}=\rho\,g'(1-l_\rho).$$
--
--   **Entrepreneurs' response to the date-0 rate.** With $\bar r(r)=\min\{r;R\}$, a date-0 rate $r>0$ induces the effort
--   $$e(r)=\frac{\pi R}{2R-\bar r(r)},$$
--   and $l$ is a labour demand at $r$ when $0<l\le 1$ and
--   $$\frac{\pi R f'(l)}{2(2R-\bar r(r))}=r\,w^*.$$
--   For $r<R$ these are (34) and (35); for $r\ge R$ they are Proposition 2 with $\bar r=R$ (effort $\pi$). The bound $l\le 1$ is the labour endowment of the young workers.
--
--   **Date-0 surplus and optimal rate.** The date-0 social surplus of effort $e$ and labour $l$ is (59):
--   $$\Sigma_\rho(e,l)=\Big(e-\frac{e^2}{2\pi}\Big)\frac{f(l)}{R}+\rho\,g(1-l).$$
--   A rate $r_u>0$ with labour demand $l_u$ is *optimal* when $\Sigma_\rho(e(r_u),l_u)\ge\Sigma_\rho(e(r),l)$ for every rate $r>0$ and every labour demand $l$ at $r$.
--
--   These objects are the common ground of both missions drawn from the paper: Proposition 11 (under-investment with unregulated leverage) and Proposition 12 (the shock-size threshold), together with their milestones, are stated about them.
--
--   **Formalization Note** The paper's $\pi$ is the structure field `E.π`; `Real.pi` is never used. Derivatives are `deriv`, used only at points where the Inada conditions give differentiability. $l^*$, $w^*$ and $l_\rho$ are parameters tied to their defining equations rather than functions of the data; the equations determine them uniquely. The planner may choose any rate $r>0$, including $r>R$ (Proposition 2's $\bar r$); the paper's proof restricts to $r\le R$ ("$r\le 1$", a misprint).
--   The paper says only that "$f$ and $g$ satisfy the Inada conditions and $f$ is twice continuously differentiable" (p. 21); this file reads that as stated above, with strict concavity of $f$ in the form $f''<0$ on $(0,\infty)$ and $g$ continuously differentiable on $(0,\infty)$. Rates at which the labour-demand equation would require $l>1$ admit no labour demand, as with the paper's lower bound $\underline r$ (p. 58).
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), pp. 11–31, §2.1 (5)–(8), §3.1, (20), (26), (33)–(35), and p. 56, (59)

import Mathlib

open Filter Topology

namespace LeveragedPayouts.Unregulated

/-- The Inada conditions with twice continuous differentiability (p. 21): `f 0 = 0`, `f` continuous
on `[0, ∞)`, `C²` on `(0, ∞)`, strictly increasing (`f' > 0`), strictly concave (`f'' < 0`),
`f'(0⁺) = +∞` and `f'(+∞) = 0`. -/
def IsInada (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ContinuousOn f (Set.Ici 0) ∧ ContDiffOn ℝ 2 f (Set.Ioi 0) ∧
    (∀ l, 0 < l → 0 < deriv f l) ∧ (∀ l, 0 < l → deriv (deriv f) l < 0) ∧
    Tendsto (deriv f) (𝓝[>] 0) atTop ∧ Tendsto (deriv f) atTop (𝓝 0)

/-- The Inada conditions for a `C¹` function (p. 21): `g 0 = 0`, `g` continuous on `[0, ∞)`, `C¹` on
`(0, ∞)`, `g' > 0`, `g'` strictly decreasing, `g'(0⁺) = +∞` and `g'(+∞) = 0`. -/
def IsInadaC1 (g : ℝ → ℝ) : Prop :=
  g 0 = 0 ∧ ContinuousOn g (Set.Ici 0) ∧ ContDiffOn ℝ 1 g (Set.Ioi 0) ∧
    (∀ l, 0 < l → 0 < deriv g l) ∧ StrictAntiOn (deriv g) (Set.Ioi 0) ∧
    Tendsto (deriv g) (𝓝[>] 0) atTop ∧ Tendsto (deriv g) atTop (𝓝 0)

/-- The economy of §3.1–3.3: discount rate `R > 1`, effort-cost parameter `π ∈ (0, 1)`, the
capital-good technology `f`, the consumption-good technology `g`, and the laissez-faire steady-state
labour `lstar ∈ (0, 1)` and wage `wstar` solving (20): `(π/(2R)) f'(l*) = g'(1 − l*) = w*`. -/
structure Economy where
  R : ℝ
  π : ℝ
  f : ℝ → ℝ
  g : ℝ → ℝ
  lstar : ℝ
  wstar : ℝ
  hR : 1 < R
  hπ0 : 0 < π
  hπ1 : π < 1
  hf : IsInada f
  hg : IsInadaC1 g
  hl0 : 0 < lstar
  hl1 : lstar < 1
  h20 : π / (2 * R) * deriv f lstar = deriv g (1 - lstar)
  hw : deriv g (1 - lstar) = wstar

/-- `l` is the first-best date-0 labour `l_ρ` when the date-0 consumption-good technology is `ρ g`:
(26) with `g_0 = ρ g`, `π f'(l_ρ)/(2R) = ρ g'(1 − l_ρ)`, with `0 < l_ρ < 1`. -/
def IsFirstBestLabor (E : Economy) (ρ l : ℝ) : Prop :=
  0 < l ∧ l < 1 ∧ E.π * deriv E.f l / (2 * E.R) = ρ * deriv E.g (1 - l)

/-- Entrepreneurs' effort at the date-0 rate `r`: (8) with `r̄(r) = min{r; R}`, i.e. (34) for `r < R`
and `π` for `r ≥ R`. -/
noncomputable def effort (E : Economy) (r : ℝ) : ℝ :=
  E.π * E.R / (2 * E.R - min r E.R)

/-- `l` is the date-0 labour demand at the rate `r` under the rigid wage `w*`: (8) with `I = w* l`,
i.e. (35) for `r < R`, with `0 < l ≤ 1` (one unit of labour per young worker). -/
def IsLaborDemand (E : Economy) (r l : ℝ) : Prop :=
  0 < l ∧ l ≤ 1 ∧ E.π * E.R * deriv E.f l / (2 * (2 * E.R - min r E.R)) = r * E.wstar

/-- The date-0 social surplus (59): `(e − e²/(2π)) f(l)/R + ρ g(1 − l)`. -/
noncomputable def surplus (E : Economy) (ρ e l : ℝ) : ℝ :=
  (e - e ^ 2 / (2 * E.π)) * E.f l / E.R + ρ * E.g (1 - l)

/-- `ru` is an optimal date-0 rate with labour response `lu`: the pair is feasible and its surplus
(59) is at least that of every feasible pair `(r, l)` with `r > 0`. -/
def IsOptimalRate (E : Economy) (ρ ru lu : ℝ) : Prop :=
  0 < ru ∧ IsLaborDemand E ru lu ∧
    ∀ r l, 0 < r → IsLaborDemand E r l → surplus E ρ (effort E r) l ≤ surplus E ρ (effort E ru) lu

end LeveragedPayouts.Unregulated



-- Prove2me | Definitions.Def_StrategicQR_Game_Equilibrium
-- name    : StrategicQR_Game_Equilibrium
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:02:29.135576+00:00
-- url     : https://prove2.me/theorems/efe2045c-39be-4ac2-b2d1-d082ad954fc9
-- title:
--   Sec. 5–6 — fill rate, waiting surplus (3), consumer best response $v^*(\hat q)$, RE equilibrium (Definition 2), and the no-rationing assumption
-- statement:
--   **Sale-period rationing (p. 14–15).** In the sale period, strategic consumers and bargain hunters form a queue served from the front until the inventory $I=q-\xi x$ runs out, with strategic consumers every $1/\theta$-th customer. Strategic consumers then effectively face the inventory $\theta I$. At demand level $x$, the fill rate of the $(1-\xi)x$ waiting strategic consumers is
--   $$\mathrm{fill}(x)=\frac{\min\{(1-\xi)x,\ \theta(q-\xi x)\}}{(1-\xi)x},$$
--   taken to be $1$ whenever $(1-\xi)x\le\theta(q-\xi x)$, including when no strategic consumer waits.
--
--   **Waiting surplus (3).** The probability that the threshold consumer buys at the low price $s_l=v_B$ and receives a unit is $\Pr(D<D_l\text{ and a unit is received})=\int_{[0,D_l)}\mathrm{fill}(x)f(x)\,dx$. The expected sale-period surplus of the consumer with value $\hat v$ is
--   $$\psi(\hat v)=(\hat v-v_B)\Pr(D<D_l\text{ and a unit is received}).$$
--
--   **Consumer best response.** A threshold $v\in[\underline v,\bar v]$ is a best response to the belief $\hat q$ about the order quantity if $\psi(v)\le v_M-p$ whenever $v>\underline v$, and $\psi(v)\ge v_M-p$ whenever $v<\bar v$. At an interior threshold the threshold consumer is indifferent between the first-period surplus $v_M-p$ and $\psi(v)$; at $v=\bar v$ every strategic consumer weakly prefers to buy early, and at $v=\underline v$ every one weakly prefers to wait.
--
--   **Rational expectations equilibrium (Definition 2).** $(q^*,v^*)$ is an RE equilibrium at unit cost $c$ if $q^*\ge0$ maximizes $\pi(\cdot,v^*)$ over $q\ge0$ and $v^*$ is a consumer best response to $q^*$, i.e. beliefs equal the equilibrium values. The equilibrium with quick response is the same with $\pi_r$ in place of $\pi$.
--
--   **No rationing.** For every belief $\hat v\in[\underline v,\bar v]$, $s_l\bar G(\hat v)\le\theta s_m\bar G(s_m)$; equivalently $D_l\le D_\theta$, where $D_\theta=\theta q/(1-\xi+\theta\xi)$.
--
--   **Formalization Note**
--   - **Best-response predicate.** The correspondence $v^*(\hat q)$ is encoded by the best-response predicate, which is the threshold form that Lemma 1 justifies.
--   - **No rationing.** The page assumes "$\theta_c\le\theta$" with $\theta_c=s_l/s_m$ (p. 15). That condition is equivalent to $D_l\le D_\theta$ only when $s_m=\hat v$. The no-rationing condition here is exactly $D_l\le D_\theta$, which is what the page uses it for.
--   - **Fill-rate convention.** The convention $\mathrm{fill}=1$ when nobody waits matters: at the belief $\hat v=\bar v$ the probability term is $F(q)$, as in the proof of Theorem 2 (iii). A junk value $0/0=0$ would instead make $\bar v$ a best response to every order.
-- source:
--   Cachon, Swinney, Purchasing, Pricing, and Quick Response in the Presence of Strategic Consumers, working paper (rev. Nov. 25, 2007), p. 11, Definition 2; p. 14, eq. (3); pp. 14–15, the sale-period queue and θ; p. 15, Lemma 4 (D_θ, θ_c) and the assumption θ_c ≤ θ; Technical Appendix p. 4 (PDF 36), proof of Lemma 4

import Mathlib
import Definitions.Def_StrategicQR_Game_CriticalLevels

namespace StrategicQR.Game

open MeasureTheory

/-- The sale-period fill rate of strategic consumers at demand `x` (§5, pp. 14–15; Technical
Appendix p. 4): strategic consumers effectively face the inventory `θ I`, `I = q - ξ x`, so the
fill rate is `min((1 - ξ) x, θ I) / ((1 - ξ) x)`. It is written as `1` whenever
`(1 - ξ) x ≤ θ I`, in particular when no strategic consumer waits (`(1 - ξ) x = 0`). -/
noncomputable def fillFrac (M : Model) (α q vhat x : ℝ) : ℝ :=
  if (1 - xi M α vhat) * x ≤ M.θ * (q - xi M α vhat * x) then 1
  else M.θ * (q - xi M α vhat * x) / ((1 - xi M α vhat) * x)

/-- The probability term of (3), p. 14: `Pr(D < D_l and the consumer receives a unit)
= ∫_{[0, D_l)} fill(x) f(x) dx`. -/
noncomputable def fillProb (M : Model) (α q vhat : ℝ) : ℝ :=
  ∫ x in Set.Ico 0 (Dl M α q vhat), fillFrac M α q vhat x * M.f x

/-- The expected sale-period surplus (3) of the strategic consumer with value `v̂` when
consumers believe the order quantity is `q`: `(v̂ - vB) × Pr(D < D_l and a unit is received)`. -/
noncomputable def waitSurplus (M : Model) (α q vhat : ℝ) : ℝ :=
  (vhat - M.vB) * fillProb M α q vhat

/-- `v ∈ v*(q̂)`: the threshold `v ∈ [v̲, v̄]` is a consumer best response to the belief `q̂`
(Lemma 1, p. 10, and Definition 2, item 2, p. 11). An interior threshold makes the threshold
consumer weakly prefer waiting from the left and buying early from the right: if `v > v̲` then
`ψ(v) ≤ vM - p`, and if `v < v̄` then `vM - p ≤ ψ(v)`, with `ψ` the waiting surplus (3). -/
def IsConsumerBR (M : Model) (α qhat v : ℝ) : Prop :=
  v ∈ Set.Icc M.vlo M.vhi ∧
    (M.vlo < v → waitSurplus M α qhat v ≤ M.vM - M.p) ∧
    (v < M.vhi → M.vM - M.p ≤ waitSurplus M α qhat v)

/-- A rational expectations equilibrium `(q*, v*)` (Definition 2, p. 11) at unit cost `c`, with
beliefs replaced by the equilibrium values (item 3): `q*` maximizes `π(·, v*)` over `q ≥ 0`
(item 1) and `v* ∈ v*(q*)` (item 2). -/
def IsEquilibrium (M : Model) (α c q v : ℝ) : Prop :=
  q ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun q' => profit M α c q' v) (Set.Ici 0) q ∧
    IsConsumerBR M α q v

/-- A rational expectations equilibrium `(q*_r, v*_r)` of the game with quick response (§7,
Theorem 2, p. 20): Definition 2 with the profit `π_r`. The consumer best response is the same
as without quick response (p. 19). -/
def IsQREquilibrium (M : Model) (α c₁ c₂ q v : ℝ) : Prop :=
  q ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun q' => qrProfit M α c₁ c₂ q' v) (Set.Ici 0) q ∧
    IsConsumerBR M α q v

/-- The no-rationing assumption, the corrected form of "`θ_c ≤ θ`" (p. 15): for every belief
`v̂ ∈ [v̲, v̄]`, `s_l Ḡ(v̂) ≤ θ s_m Ḡ(s_m)`, which is `D_l ≤ D_θ`, `D_θ = θ q / (1 - ξ + θ ξ)`. -/
def NoRationing (M : Model) : Prop :=
  ∀ vhat ∈ Set.Icc M.vlo M.vhi, M.vB * Gbar M vhat ≤ M.θ * sm M vhat * Gbar M (sm M vhat)

/-- `D_θ = θ q / (1 - ξ + θ ξ)` (Lemma 4 (i), p. 15). -/
noncomputable def Dtheta (M : Model) (α q vhat : ℝ) : ℝ :=
  M.θ * q / (1 - xi M α vhat + M.θ * xi M α vhat)

end StrategicQR.Game



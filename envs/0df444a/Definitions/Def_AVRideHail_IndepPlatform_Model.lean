-- Prove2me | Definitions.Def_AVRideHail_IndepPlatform_Model
-- name    : AVRideHail_IndepPlatform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:46.142453+00:00
-- url     : https://prove2.me/theorems/6e17046c-f2e6-4d77-8579-e91160fb748f
-- title:
--   §3.1, §4, App. A.1, B.2, pp. 7–14, 25, 38, 46 — ride-hailing market, labor cost per ride-hour w(n̲)/ū, the bound (19), independent-platform coexistence (48), (51)
-- statement:
--   This file sets up the ride-hailing market of Lian and van Ryzin and the objects needed to compare an independent-platform market with a pure human-driver (HV) market.
--
--   **Parameters.** A market is described by six real numbers: the constants $a$ and $r$ of the expected-pickup-time (ETA) function $t_1(s)=a\,s^{-r}$, where $s$ is the number of open (idle) cars, (4); the mean trip time $t_2$; the riders' maximal value $V$ (rider values are uniform on $[0,V]$); and the HV supply curve
--   $$w(n)=w_0+\alpha n,\qquad (1)$$
--   the hourly reservation earnings needed to attract a fleet of $n$ human drivers.
--
--   **Supply.** With
--   $$\tilde a=r^{\frac{1}{r+1}}a^{\frac{1}{r+1}}+r^{-\frac{r}{r+1}}a^{\frac{1}{r+1}},$$
--   the minimal fleet that can serve a demand rate $d$ (ride-hours per hour) is
--   $$\underline n(d)=\tilde a\,d^{\frac{1}{r+1}}+t_2 d \qquad (12)$$
--   and the maximal on-trip utilization is $\bar u(d)=d\,t_2/\underline n(d)$, (22).
--
--   **Demand and revenue.** In a scenario with potential demand mass $m$, the inverse demand is $p(d)=V(1-d/m)$ for $d\in[0,m]$, (3), and total revenue is $r(d)=d\,p(d)\,t_2$. The minimal HV cost of serving $d$ is $w(\underline n(d))\,\underline n(d)$.
--
--   **Pure-HV equilibrium.** A demand rate $d\in[0,m]$ is an equilibrium when $r(d)=w(\underline n(d))\,\underline n(d)$, (13). It is *stable* (Definition 1) when there is no $\varepsilon>0$ with $r(d-\varepsilon)<w(\underline n(d-\varepsilon))\underline n(d-\varepsilon)$ and $r(d+\varepsilon)>w(\underline n(d+\varepsilon))\underline n(d+\varepsilon)$. The *maximal stable equilibrium* $d^*_{HV}$ is the greatest stable equilibrium. The *loose labor market* condition (33) is $r(m/2)>w(\underline n(m/2))\,\underline n(m/2)$.
--
--   **Mission-specific objects.**
--   1. The labor cost per ride-hour of an HV fleet serving demand $d$: $\;w(\underline n(d))/\bar u(d)$.
--   2. The bound of (19) and (243) at demand $d$:
--   $$B(d)=\frac{w_0}{\underline n(d)}\cdot\frac{\dfrac{\tilde a r}{t_2(r+1)}}{\dfrac{\tilde a(1-r)}{t_2(r+1)}+d^{\frac{r}{r+1}}}.$$
--   3. A *coexistence equilibrium of the independent platform market* in scenario $m$: HVs serve $d_{HV}>0$, AVs serve $d_{AV}>0$ on a separate platform, $d_{HV}+d_{AV}\le m$, and HV revenue equals HV cost (Definition 2, (48)) with the HV fleet at its own minimal size $n_{HV}=\underline n(d_{HV})$, (51):
--   $$d_{HV}\,p(d_{HV}+d_{AV})\,t_2=w(\underline n(d_{HV}))\,\underline n(d_{HV}).$$
--
--   These are the objects of Proposition 4: the price of the independent-platform market when AVs and HVs coexist is compared with the pure-HV price through the ratio $w(\underline n)/\bar u$ and the bound $B$.
--
--   **Formalization Note** The shared block (parameters through the loose-market condition) is written identically in each mission of this series. Stability quantifies over $0<\varepsilon\le d$ with $d+\varepsilon\le m$, so that $d\pm\varepsilon$ stays in the domain $[0,m]$ of (3). Real powers follow Mathlib's `Real.rpow`, so at $d=0$ one gets $\bar u(0)=0/0=0$ and the ratio $w(\underline n(0))/\bar u(0)=0$; every statement of the mission about the ratio is made at $d>0$. Coexistence records only the HV side of the independent-platform equilibrium (Definition 2 with (51)); the AV fleet size, the AV supplier's decision and the stability of Definition 3 are not part of it, because Proposition 4 and its proof use only (48), (51) and $d_{AV}>0$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), pp. 7–14, 38, (1)–(4), (12)–(13), (22), Definition 1, (33); p. 25 (Proposition 4) and p. 24, (19); App. B.2, p. 46, Definition 2, (48), (51); App. D.3.1, p. 77, (223)

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.IndepPlatform

/-- The labor cost per ride-hour w(n̲(d)) / ū(d) of an HV fleet serving demand d (p. 25). -/
noncomputable def hvRatio (P : AVRideHail.PureHV.MarketParams) (d : ℝ) : ℝ := AVRideHail.PureHV.wage P (AVRideHail.PureHV.nMin P d) / AVRideHail.PureHV.uBar P d

/-- The right-hand side of (19) / (243) at demand d:
(w₀ / n̲(d)) · (ã r / (t₂ (r+1))) / (ã (1−r) / (t₂ (r+1)) + d^{r/(r+1)}). -/
noncomputable def alphaBound (P : AVRideHail.PureHV.MarketParams) (d : ℝ) : ℝ :=
  P.w0 / AVRideHail.PureHV.nMin P d *
    ((AVRideHail.PureHV.aTilde P * P.r / (P.t2 * (P.r + 1))) /
      (AVRideHail.PureHV.aTilde P * (1 - P.r) / (P.t2 * (P.r + 1)) + d ^ (P.r / (P.r + 1))))

/-- AVs and HVs serve scenario m together on independent platforms: Definition 2's (48),
d_HV · p_i(d_HV + d_AV) · t₂ = w(n_HV) n_HV, with n_HV = n̲(d_HV) (51), both demands positive
and the total demand in the domain [0, m] of (3) (App. B.2, p. 46). -/
def IsIPMCoexistence (P : AVRideHail.PureHV.MarketParams) (m dHV dAV : ℝ) : Prop :=
  0 < dHV ∧ 0 < dAV ∧ dHV + dAV ≤ m ∧
    dHV * AVRideHail.PureHV.priceFn P m (dHV + dAV) * P.t2 = AVRideHail.PureHV.hvCost P dHV

end AVRideHail.IndepPlatform



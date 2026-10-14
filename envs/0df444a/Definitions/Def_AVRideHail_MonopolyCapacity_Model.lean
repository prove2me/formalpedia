-- Prove2me | Definitions.Def_AVRideHail_MonopolyCapacity_Model
-- name    : AVRideHail_MonopolyCapacity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:09:36.927497+00:00
-- url     : https://prove2.me/theorems/44be59bc-cae0-45f9-aaaf-a18c1f89f0ce
-- title:
--   §3.1, §3.3.1, §4, App. A.1, E.1.1 — ride-hailing market, d̄(n), π^C_i (251), the monopoly objective (5) and its simplification (20)
-- statement:
--   This file fixes the ride-hailing market of Lian and van Ryzin and the objects needed for a monopoly supplier of autonomous vehicles (AVs) operating on a common platform with human drivers (HVs).
--
--   **Market parameters.** A market is described by six real numbers: the constant $a$ and the elasticity $r$ of the pickup-time (ETA) function $t_1(s) = a s^{-r}$, where $s$ is the number of open vehicles; the trip time $t_2$; the maximal rider value $V$ (rider values are uniform on $[0, V]$); and the HV reservation-earnings curve $w(n) = w_0 + \alpha n$.
--
--   **Supply and demand.** With $\tilde a = r^{1/(r+1)} a^{1/(r+1)} + r^{-r/(r+1)} a^{1/(r+1)}$, the minimal fleet needed to serve the demand rate $d$ is
--   $$\underline{n}(d) = \tilde a\, d^{1/(r+1)} + t_2 d,$$
--   the maximal utilization is $\bar u(d) = d t_2 / \underline{n}(d)$, and in a scenario with potential demand mass $m$ the inverse demand is $p(d) = V(1 - d/m)$ and the market revenue is $r(d) = d\, p(d)\, t_2$. The minimal HV cost of serving $d$ is $w(\underline{n}(d))\,\underline{n}(d)$.
--
--   **Pure-HV equilibrium.** A demand rate $d \in [0, m]$ is an equilibrium when $r(d) = w(\underline{n}(d))\,\underline{n}(d)$ (condition (13)). It is stable when there is no $\varepsilon > 0$ with $r(d-\varepsilon) < w(\underline{n}(d-\varepsilon))\underline{n}(d-\varepsilon)$ and $r(d+\varepsilon) > w(\underline{n}(d+\varepsilon))\underline{n}(d+\varepsilon)$ (Definition 1). The maximal stable equilibrium $d^*$ is the greatest stable equilibrium, and $n^*_{HV} = \underline{n}(d^*)$. The market is loose when $r(m/2) > w(\underline{n}(m/2))\,\underline{n}(m/2)$ (condition (33), the paper's Assumption 2).
--
--   **Monopoly AV supplier on a common platform.** Let $\bar d$ be the inverse of $\underline{n}$ on $[0, \infty)$. For an AV variable cost $c_v$, the variable profit per AV at fleet size $n_{AV}$ in a scenario is (251)
--   $$\pi^C(n_{AV}) = \begin{cases} w_0 - c_v, & n_{AV} < n^*_{HV},\\ p(\bar d(n_{AV}))\,\bar u(\bar d(n_{AV})) - c_v, & n_{AV} \ge n^*_{HV}.\end{cases}$$
--   Given scenarios $i = 1, \dots, I$ with probabilities $P(m_i)$ and a fixed AV cost $c_f$, the monopoly objective (5) at capacity $N$ is
--   $$\sum_{i=1}^I P(m_i) \Big\{ \max_{0 \le n_{AV,i} \le N} \pi^C_i(n_{AV,i})\, n_{AV,i} \Big\} - c_f N,$$
--   and the file also defines, for arbitrary breakpoints $n_1, \dots, n_I$, the newsvendor-type function (20)
--   $$\Pi(N) = (w_0 - c_v) \sum_{i=1}^I P(m_i) \min\{N, n_i\} - c_f N.$$
--
--   These objects are shared by every statement of the mission: the goal (Proposition 8) asks for a maximizer of (5), and (20) is the form into which the paper rewrites it.
--
--   **Formalization Note.** Fleet sizes and demands are real numbers. Scenarios are indexed by `Fin I`, i.e. from $0$ to $I - 1$ (the paper's scenario $i$ is index $i - 1$). Definition 1's $\varepsilon$ is restricted so that $d \pm \varepsilon$ stays in $[0, m]$, the domain of the inverse demand (3). $\bar d$ is `Function.invFunOn` of $\underline{n}$ on $[0, \infty)$; it is the true inverse at every $n \ge 0$ once Lemma 1 Item 2 holds and is not used elsewhere. The paper's Proposition 6 (the common-platform equilibrium for an exogenous AV fleet) is taken in its summary form (251) as the definition of $\pi^C$. The inner maximum of (5) is a real supremum over $[0, N]$ (`sSup` of the image of the compact interval); Proposition 7 shows it is attained. For $N < 0$ the interval is empty and the supremum is $0$ by Lean's convention, so (5) is only ever considered for $N \ge 0$.
-- source:
--   Lian & van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), pp. 7–14, 38, 83: (1)–(4), (5) on p. 10, (12)–(13), Definition 1 on p. 13, (22) and Lemma 1 on p. 38, (33) on p. 42, (251) on p. 83, (20) on p. 29

import Mathlib
import Definitions.Def_AVRideHail_PureHV_Model

namespace AVRideHail.MonopolyCapacity

/-! ### Objects specific to the monopoly AV supplier on a common platform (§3.3.1, §6.2.1) -/

/-- d̄(n), the inverse of n̲ on [0, ∞) (Lemma 1 Item 2, p. 38). -/
noncomputable def dBar (P : AVRideHail.PureHV.MarketParams) (n : ℝ) : ℝ := Function.invFunOn (AVRideHail.PureHV.nMin P) (Set.Ici 0) n

/-- π^C_i(n_AV), (251), p. 83: the variable profit per AV on a common platform in a scenario of
mass m whose pure-HV equilibrium demand is dstar (so n*_{HV,i} = n̲(dstar)). -/
noncomputable def piC (P : AVRideHail.PureHV.MarketParams) (cv m dstar nAV : ℝ) : ℝ :=
  if nAV < AVRideHail.PureHV.nMin P dstar then P.w0 - cv
  else AVRideHail.PureHV.priceFn P m (dBar P nAV) * AVRideHail.PureHV.uBar P (dBar P nAV) - cv

/-- The inner maximum of (5), p. 10: the supremum over 0 ≤ n_AV ≤ N of π^C_i(n_AV) n_AV. -/
noncomputable def monoValue (P : AVRideHail.PureHV.MarketParams) (cv m dstar N : ℝ) : ℝ :=
  sSup ((fun n => piC P cv m dstar n * n) '' Set.Icc 0 N)

/-- The monopoly objective (5), p. 10, with D = C, as a function of the capacity N. -/
noncomputable def monoProfit (P : AVRideHail.PureHV.MarketParams) (cv cf : ℝ) {I : ℕ} (prob m dstar : Fin I → ℝ)
    (N : ℝ) : ℝ :=
  ∑ i, prob i * monoValue P cv (m i) (dstar i) N - cf * N

/-- The simplified objective (20), p. 29, for any breakpoints ns. -/
noncomputable def profit20 (P : AVRideHail.PureHV.MarketParams) (cv cf : ℝ) {I : ℕ} (prob ns : Fin I → ℝ)
    (N : ℝ) : ℝ :=
  (P.w0 - cv) * ∑ i, prob i * min N (ns i) - cf * N

end AVRideHail.MonopolyCapacity



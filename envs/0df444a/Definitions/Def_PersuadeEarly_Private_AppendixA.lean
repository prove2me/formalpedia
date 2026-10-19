-- Prove2me | Definitions.Def_PersuadeEarly_Private_AppendixA
-- name    : PersuadeEarly_Private_AppendixA
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:34.039535+00:00
-- url     : https://prove2.me/theorems/bd6bbd4d-508c-404e-9ad0-a44f963040f4
-- title:
--   App. A, pp. 35, 41–44 — $\phi$ (A.4), $\beta$ and $\delta$ (A.7), the program (A.16) and $\bar D(p_1,p_2)$, the $(t,p_1,p_2)$-mechanism
-- statement:
--   This file defines the objects of the paper's proofs in Appendix A.
--
--   **The public-threshold profit** ((A.4)–(A.5), p. 35). For a threshold $t$ and period-2 price $p$,
--   $$\phi(t,p)=(t-p)\,\bar F(t)\,\big(\mathrm{avail}(q_L,\bar F(t))-\mathrm{avail}((q_L-\bar F(t))^+,\ \bar F(p)-\bar F(t))\big),$$
--   the gap between the L-state period-1 and period-2 availabilities when customers above $t$ buy in period 1 and those in $[p,t)$ wait.
--
--   **The fixed-price program** ((A.7), (A.16), pp. 41–43). Fix prices $p_1>p_2\ge0$. For a mass $x$ told *Buy* in state $L$,
--   $$\beta(x)=p_1\min\{x,q_L\}+p_2\min\{\bar F(p_2)-x,(q_L-x)^+\},$$
--   $$\delta(v,x)=(v-p_2)\,\mathrm{avail}((q_L-x)^+,\bar F(p_2)-x)-(v-p_1)\,\mathrm{avail}(q_L,x).$$
--   For a threshold $t$, let $g_H(v)=\max\big\{\min\{\tfrac{P(L)}{P(H)}\tfrac{-\delta(v,\bar F(t))}{p_1-p_2},1\},0\big\}$ and
--   $$J(t)=P(H)(p_1-p_2)\int_{v\ge t}g_H(v)\,dF(v)+P(L)\beta(\bar F(t))+P(H)p_2\bar F(p_2).$$
--   A threshold is *feasible* when $t\ge p_1$ and, if $\bar F(t)>0$, $\delta(t,\bar F(t))\le0$. The value of (A.16) is $\bar D(p_1,p_2)=\sup\{J(t):t\text{ feasible}\}$.
--
--   **The $(t,p_1,p_2)$-mechanism** ((A)–(B), p. 44), with one latent signal: in state $L$, *Buy* to $v\ge t$, *Wait* to $p_2\le v<t$, *No* below $p_2$; in state $H$, *Buy* with probability $g_H(v)$ and *Wait* otherwise to $v\ge t$, *Wait* to $p_2\le v<t$, *No* below $p_2$.
--
--   These objects state Lemmas 2–4, the steps of the proof of Theorem 2.
--
--   **Formalization Note** Availabilities are encoded with $\mathrm{avail}$, which agrees with (A.5) and (A.7) whenever the demand in the denominator is positive. (B) is printed without the $\min$ and is read with $\min\{\cdot,1\}$ as in (A.15)–(A.16); the truncation at $0$ only matters on a null set. (A.16) as printed drops the no-Buy mechanism of (A.15) ($x=0$); the mission keeps it as a threshold $t$ with $\bar F(t)=0$, for which $\delta(t,\bar F(t))\le0$ is not imposed, so the supremum is never over an empty set.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), p. 35, (A.4)–(A.5); p. 41, (A.7); p. 43, (A.15)–(A.16); p. 44, (A)–(B)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation
import Definitions.Def_PersuadeEarly_Private_Mechanism

open MeasureTheory Set

namespace PersuadeEarly.Private

variable (M : Model)

/-- The L-state profit of a public threshold `t` at period-2 price `p` ((A.4) with (A.5), p. 35):
`ϕ(t, p) = (t − p) F̄(t) (P(A1 | qL, t) − P(A2 | qL, t))`, where the period-1 availability is that
of stock `qL` facing demand `F̄(t)` and the period-2 availability that of the leftover stock
`(qL − F̄(t))⁺` facing demand `F̄(p) − F̄(t)`.

**Formalization Note** Availabilities are encoded with `avail`; this agrees with (A.5) whenever
`F̄(p) > F̄(t)`, and both vanish at `t = p`. -/
noncomputable def phi (t p : ℝ) : ℝ :=
  (t - p) * M.Fbar t * (avail M.qL (M.Fbar t) - avail (max (M.qL - M.Fbar t) 0) (M.Fbar p - M.Fbar t))

/-- The L-state revenue `β(x)` of (A.7), p. 41, when a mass `x` of customers is told *Buy* and the
rest of `[p2, ∞)` waits: `β(x) = p1 min{x, qL} + p2 min{F̄(p2) − x, (qL − x)⁺}`. -/
noncomputable def beta (p1 p2 x : ℝ) : ℝ :=
  p1 * min x M.qL + p2 * min (M.Fbar p2 - x) (max (M.qL - x) 0)

/-- `δ(v, x)` of (A.7), p. 41: the L-state gain of waiting over buying for a `v`-customer told *Buy*,
when a mass `x` is told *Buy*: `(v − p2) α2 − (v − p1) α1` with `α1 = min{x, qL}/x` and
`α2 = min{F̄(p2) − x, (qL − x)⁺}/(F̄(p2) − x)`, encoded with `avail`. -/
noncomputable def delta (p1 p2 v x : ℝ) : ℝ :=
  (v - p2) * avail (max (M.qL - x) 0) (M.Fbar p2 - x) - (v - p1) * avail M.qL x

/-- The H-state *Buy* probability of the `(t, p1, p2)`-mechanism ((B), p. 44, and (A.16)):
`min{ P(L)/P(H) · (−δ(v, F̄(t)))/(p1 − p2), 1 }`, truncated below at `0`.

**Formalization Note** (B) is printed without the `min`; it is read with `min{·, 1}` as in
(A.15)–(A.16). The truncation at `0` (as in (A.3)) only matters when `F̄(t) = 0`, where the
customers concerned form a null set; for feasible `t` with `F̄(t) > 0` the expression is already
nonnegative on `v ≥ t`. -/
noncomputable def gH (p1 p2 t v : ℝ) : ℝ :=
  max (min (M.pL / M.pH * (-delta M p1 p2 v (M.Fbar t)) / (p1 - p2)) 1) 0

/-- The objective of (A.16), p. 43, at threshold `t`:
`P(H)(p1 − p2) ∫_{v ≥ t} g_H dF + P(L) β(F̄(t)) + P(H) p2 F̄(p2)`. -/
noncomputable def J (p1 p2 t : ℝ) : ℝ :=
  M.pH * (p1 - p2) * (∫ v in Ici t, gH M p1 p2 t v ∂M.mu) + M.pL * beta M p1 p2 (M.Fbar t) +
    M.pH * p2 * M.Fbar p2

/-- Feasibility in (A.16): `t ≥ p1` and `δ(t, F̄(t)) ≤ 0`, the latter imposed only when `F̄(t) > 0`.

**Formalization Note** (A.15) maximizes over `x = |g_L|₁ ∈ [0, F̄(p1)]`, and `x = 0` (nobody is told
to buy) is always feasible; after the substitution `t = F̄^{-1}(x)` this is a threshold `t` with
`F̄(t) = 0`. Imposing `δ(t, F̄(t)) ≤ 0` there would drop it and could leave (A.16) without a feasible
point. -/
def feasible (p1 p2 t : ℝ) : Prop :=
  p1 ≤ t ∧ (0 < M.Fbar t → delta M p1 p2 t (M.Fbar t) ≤ 0)

/-- The value `D̄(p1, p2)` of (A.16), p. 43: the supremum of `J` over feasible thresholds. -/
noncomputable def Dbar (p1 p2 : ℝ) : ℝ :=
  sSup (J M p1 p2 '' {t | feasible M p1 p2 t})

/-- The `(t, p1, p2)`-mechanism of (A)–(B), p. 44, with a single latent index:
* state `L`: *Buy* to `v ≥ t`, *Wait* to `p2 ≤ v < t`, *No* below `p2`;
* state `H`: *Buy* with probability `g_H(v)` and *Wait* otherwise to `v ≥ t`, *Wait* to
  `p2 ≤ v < t`, *No* below `p2`.

**Formalization Note** (A)–(B) specify only the *Buy* signals; customers of `[p2, ∞)` not told to
buy wait, as in (A.7) where `|s|₂ = F̄(p2) − |s|₁`. -/
noncomputable def tMech (p1 p2 t : ℝ) : Mech M 1 where
  p1 := p1
  p2 := p2
  piH := fun _ => 1
  piL := fun _ => 1
  buyH := fun _ v => if t ≤ v then gH M p1 p2 t v else 0
  buyL := fun _ v => if t ≤ v then 1 else 0
  waitH := fun _ v => if t ≤ v then 1 - gH M p1 p2 t v else if p2 ≤ v then 1 else 0
  waitL := fun _ v => if t ≤ v then 0 else if p2 ≤ v then 1 else 0

end PersuadeEarly.Private



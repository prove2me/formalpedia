-- Prove2me | Definitions.Def_CrossLayerControl_ECCA_Downlink
-- name    : CrossLayerControl_ECCA_Downlink
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:07.613042+00:00
-- url     : https://prove2.me/theorems/02ab6d64-8590-486a-826a-ab410e2be810
-- title:
--   Data of the multi-user wireless downlink
-- statement:
--   A downlink model with $L$ links and channel-state space $\mathcal S$ consists of
--
--   1. a rate function $C=(C_1,\dots,C_L)$, where $C_i(P,s)$ is the transmission rate of link $i$ when the power vector is $P=(P_1,\dots,P_L)\in\mathbb R^L$ and the channel state is $s\in\mathcal S$;
--   2. a peak power $P_{max}$, an average power budget $P_{av}$, and a bound $\hat R$ on the arrivals of each link;
--   3. a rate bound $\mu_{max}$ (the constant of (3.4)) and the constant $\beta$ of the $\beta$-condition.
--
--   This is the setting of §6.3.1: a base station transmits to $L$ users over $L$ channels, chooses the power vector every slot subject to $\sum_i P_i\le P_{max}$, and must keep the time-average power at most $P_{av}$. The assumptions on these data are collected separately (signs and (3.4) in the rate hypothesis, the $\beta$-condition and cross-monotonicity in the downlink hypothesis).
--
--   **Formalization Note** Links are indexed $0,\dots,L-1$; the state space is an arbitrary type.
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, §6.3.1, p. 113; (3.4), p. 27; p. 115 (β-condition)

import Mathlib

namespace CrossLayerControl.ECCA

/-- **The data of the multi-user wireless downlink of §6.3.1.**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), §6.3.1, p. 113 (unnumbered): "Consider a multi-user wireless
downlink that transmits to L users over L distinct channels. Let S(t) describe the collective
channel state process, and let C(P(t),S(t)) = (C1(P(t),S(t)),...,CL(P(t),S(t))) represent the link
transmission rate function, where P(t) = (P1(t),...,PL(t)) is the vector of power allocations for
each link. Power is constrained so that Σ_{i=1}^L Pi(t) ≤ Pmax for all t. The goal is to maximize
throughput subject to an average power constraint Pav (where Pav < Pmax). Arrival processes Ai(t)
satisfy Ai(t) ≤ R̂ for all i." The rate bound µmax is that of (3.4), p. 27, and β is the constant
of the β-condition, p. 115.

A value `M : Downlink L 𝒮` consists of
* the rate function `M.C i P s` = Cᵢ(P, s) of link `i` under the power vector `P` in state `s`;
* the peak power `M.Pmax`, the average power budget `M.Pav`, the arrival bound `M.Rhat` = R̂,
  the rate bound `M.muMax` = µmax of (3.4), and the constant `M.β` of the β-condition (p. 115).

The assumptions the paper places on these data are collected in `RateHyp` and `DownlinkHyp`.

**Formalization Note.** Links are indexed by `Fin L` (0-based: the paper's link `i` is the Lean
link `i - 1`). The channel state space `𝒮` is an arbitrary type (the paper's topology state set,
which p. 27 takes finite). -/
structure Downlink (L : ℕ) (𝒮 : Type*) where
  /-- the link rate function: `C i P s` is the rate of link `i` under power vector `P` in state `s` -/
  C : Fin L → (Fin L → ℝ) → 𝒮 → ℝ
  /-- the peak total power `Pmax` -/
  Pmax : ℝ
  /-- the average power budget `Pav` -/
  Pav : ℝ
  /-- the bound `R̂` on the arrivals -/
  Rhat : ℝ
  /-- the rate bound `µmax` of (3.4) -/
  muMax : ℝ
  /-- the constant `β` of the β-condition (p. 115) -/
  β : ℝ

end CrossLayerControl.ECCA



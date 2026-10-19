-- Prove2me | Definitions.Def_AVHighway_DPolicy_Setting
-- name    : AVHighway_DPolicy_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:11.087145+00:00
-- url     : https://prove2.me/theorems/cadbede8-4092-44e4-b387-a5b14f47d046
-- title:
--   §3.2, p. 9; p. 16; p. 18 — benchmark W^B, D-policy W^D = pW^DA + (1 − p)W^DH, and the threshold p^(D,W)
-- statement:
--   The benchmark highway and the designated-lane (D) policy.
--
--   The highway has $N \ge 2$ lanes, each with capacity $c$ (vehicles per lane on the segment), and the segment has length $L$. Vehicles arrive at rate $\lambda$; a fraction $p \in [0,1]$ of them are autonomous vehicles (AVs). Write $W(L, V, \kappa, \lambda)$ for the mean travel time of the $M/G_n/\kappa/\kappa$ loss queue with segment length $L$, speeds $V$, capacity $\kappa$ and arrival rate $\lambda$ (definition `LossQueue`).
--
--   1. **Benchmark** (no AV policy, §3.2.1): all lanes are pooled in one queue of capacity $Nc$ with speeds $V^B_n$:
--   $$W^B(\lambda) = W(L, V^B, Nc, \lambda).$$
--
--   2. **D policy** (§3.2.2, p. 9): AVs must use one designated lane, human-driven vehicles (HVs) the other $N-1$. This gives two independent queues: the AV queue with capacity $c$, speeds $V^{DA}_n$ and arrival rate $p\lambda$, and the HV queue with capacity $(N-1)c$, speeds $V^{DH}_n$ and arrival rate $(1-p)\lambda$. The overall mean travel time is the weighted average (p. 18)
--   $$W^D(p, \lambda) = p\,W(L, V^{DA}, c, p\lambda) + (1-p)\,W(L, V^{DH}, (N-1)c, (1-p)\lambda).$$
--
--   3. **Threshold** of Proposition 1(a) (p. 16), a function of the three **jam speeds** $V^B_{Nc}$, $V^{DH}_{(N-1)c}$, $V^{DA}_c$ (the speeds when each queue is full):
--   $$p^{(D,W)} = \frac{V^{DA}_c V^B_{Nc} - V^{DA}_c V^{DH}_{(N-1)c}}{V^{DA}_c V^B_{Nc} - V^B_{Nc} V^{DH}_{(N-1)c}}.$$
--
--   **Formalization Note** Here $c$ is the per-lane capacity, the convention of §5 (§3.1.1 uses $c$ for the whole highway's capacity). $N - 1$ is natural-number subtraction, harmless since every theorem assumes $N \ge 2$. At $p = 0$ (resp. $p = 1$) the AV (resp. HV) queue receives rate $0$ and its travel time is Lean's junk value $0$, but its weight $p$ (resp. $1 - p$) is then $0$, so $W^D$ is the travel time of the other queue, as intended. The threshold divides by $V^B_{Nc}(V^{DA}_c - V^{DH}_{(N-1)c})$, which the theorems keep nonzero by assuming positive jam speeds and $V^{DH}_{(N-1)c} < V^{DA}_c$.
-- source:
--   Mirzaeian, Cho & Scheller-Wolf, A Queueing Model and Analysis for Autonomous Vehicles on Highways, SSRN 3278330 (version of May 5, 2020; Manag. Sci. doi:10.1287/mnsc.2020.3692), §3.2.1–§3.2.2, p. 9; §5, p. 16 (jam speeds, Proposition 1(a) threshold); §5.1, p. 18 (W^D = pW^DA + (1 − p)W^DH)

import Mathlib
import Definitions.Def_AVHighway_DPolicy_LossQueue

namespace AVHighway.DPolicy

/-- The benchmark mean travel time `W^B` (§3.2.1, p. 9; p. 16): one `M/G_n/c/c` queue for the whole
`N`-lane highway, with `c` the per-lane capacity, total capacity `N c`, speeds `V^B_n` and arrival
rate `λ`. -/
noncomputable def benchmarkW (L : ℝ) (N c : ℕ) (VB : ℕ → ℝ) (lam : ℝ) : ℝ :=
  meanTravelTime L VB (N * c) lam

/-- The D-policy mean travel time `W^D = p W^DA + (1 − p) W^DH` (p. 18), where (§3.2.2, p. 9) the AV
queue is an `M/G_n/c/c` queue with one lane, capacity `c`, speeds `V^DA_n` and arrival rate `pλ`, and
the HV queue has `N − 1` lanes, capacity `(N − 1) c`, speeds `V^DH_n` and arrival rate `(1 − p)λ`. -/
noncomputable def dPolicyW (L : ℝ) (N c : ℕ) (VDA VDH : ℕ → ℝ) (p lam : ℝ) : ℝ :=
  p * meanTravelTime L VDA c (p * lam) +
    (1 - p) * meanTravelTime L VDH ((N - 1) * c) ((1 - p) * lam)

/-- The threshold `p^(D,W)` of Proposition 1(a), p. 16, exactly as printed:
`(V^DA_c V^B_Nc − V^DA_c V^DH_(N−1)c) / (V^DA_c V^B_Nc − V^B_Nc V^DH_(N−1)c)`, a function of the
three jam speeds. -/
noncomputable def pDW (N c : ℕ) (VB VDA VDH : ℕ → ℝ) : ℝ :=
  (VDA c * VB (N * c) - VDA c * VDH ((N - 1) * c)) /
    (VDA c * VB (N * c) - VB (N * c) * VDH ((N - 1) * c))

end AVHighway.DPolicy



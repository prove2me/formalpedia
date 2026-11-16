-- Prove2me | Definitions.Def_FeedbackSwitching_Supplement_comparisonProbing
-- name    : FeedbackSwitching_Supplement_comparisonProbing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:20:10.0795+00:00
-- url     : https://prove2.me/theorems/fc5ad20c-b3d2-4eef-87d0-7f2c7ff04eaf
-- title:
--   ComparisonProbing (Algorithm 5) with probe rate $\kappa$, as a policy on apple tasting
-- statement:
--   **ComparisonProbing** with probe rate $\kappa$ is the following learner for apple tasting. Write $d_t=\ell_t(1)-\ell_t(2)\in[-1,1]$ for the advantage of the blind action over the revealing action in round $t$, and $D_t=\sum_{u\le t}d_u$ with $D_0=0$.
--
--   The learner starts **resting**. In each round $t=1,\dots,T$:
--
--   1. If it is resting, it tosses an independent coin $c_t$ with $\Pr(c_t=1)=\kappa$; if $c_t=1$ it sets $t_0\leftarrow t$ and starts a **probe** in this same round.
--   2. If it is probing, it plays the revealing action $1$, observes $d_t$, and returns to resting (from round $t+1$ on) if the break-even statistic satisfies $D_t-D_{t_0-1}\ge0$; otherwise (resting) it plays the blind action $2$.
--
--   A probe that never breaks even continues through round $T$. The waiting times between probes are geometric, and a probe stops as soon as the blind action has done at least as well as the revealing action since the probe began.
--
--   **Formalization Note** The policy runs on the base mission's coins, an i.i.d. sequence $\omega_0,\omega_1,\dots$ uniform on $[0,1]$, with $c_t=\mathbf 1\{\omega_t<\kappa\}$; the coin of a round is read only when the learner rests at its start. The state (resting, or probing with the running statistic) is recomputed from the feedback vectors recorded in the history, so the policy sees the losses only through the feedback mask. The break-even statistic $D_t-D_{t_0-1}$ is computed as the probe's own sum $\sum_{u=t_0}^t d_u$ of the observed advantages, which is the same number. Lean action `0` is the revealing action and `1` the blind action; rounds are 0-based.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Appendix A.1, Algorithm 5, pp.42–43 (PDF pp.44–45)

import Mathlib
import Definitions.Def_FeedbackSwitching_Policy
import Definitions.Def_FeedbackSwitching_sampleFin

open scoped Classical

namespace FeedbackSwitching.Supplement

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…), App. A.1, p.42.

The advantage `d_t = ℓ_t(1) − ℓ_t(2)` read off a feedback vector `v` of the revealing action:
in Lean actions, `v 0 − v 1` (revealing minus blind). -/
def cpAdv (v : Fin 2 → ℝ) : ℝ := v 0 - v 1

/-- The **state of ComparisonProbing at the start of round `t`** (0-based), computed from the
feedback vectors `fb r` of the earlier rounds `r < t` and the coins `ω`:
`none` means *resting*; `some s` means a probe started at some round `t₀ < t` is still running,
with break-even statistic `s = D_{t−1} − D_{t₀−1} = ∑_{u=t₀}^{t−1} d_u < 0` (paper's rounds).

Round `t` is a probe round (`cpProbe`) if a probe is running, or if the learner rests and the
coin of round `t` succeeds (`ω t < κ`); a probe started by the coin starts in this same round.
After a probe round the statistic is updated by the observed advantage of the round, and the
learner returns to resting from round `t + 1` on iff it is `≥ 0` (break-even rule). -/
noncomputable def cpState (κ : ℝ) (fb : ℕ → Fin 2 → ℝ) (ω : Coins) : ℕ → Option ℝ
  | 0 => none
  | t + 1 =>
      match cpState κ fb ω t with
      | some s =>
          if 0 ≤ s + cpAdv (fb t) then none else some (s + cpAdv (fb t))
      | none =>
          if (ω t : ℝ) < κ then
            (if 0 ≤ cpAdv (fb t) then none else some (cpAdv (fb t)))
          else none

/-- Round `t` is a probe round: a probe is running, or the learner rests and the coin
`c_t = 1{ω_t < κ}` succeeds. The coin of round `t` is read only in resting rounds. -/
def cpProbe (κ : ℝ) (fb : ℕ → Fin 2 → ℝ) (ω : Coins) (t : ℕ) : Prop :=
  match cpState κ fb ω t with
  | some _ => True
  | none => (ω t : ℝ) < κ

/-- **ComparisonProbing** (Algorithm 5, p.43 = PDF p.45) with probe rate `κ`, as a policy on
two actions with i.i.d. uniform coins: "Start resting. For `t = 1, …, T`: If resting, toss an
independent coin `c_t` with success probability `κ`; if `c_t = 1`, set `t₀ ← t` and start a
probe. If probing, play action 1, observe `d_t`, and return to resting if `D_t − D_{t₀−1} ≥ 0`;
otherwise play action 2."

**Formalization Note.** Lean action `0` is the revealing action, `1` the blind action. The coin
of round `t` (0-based) is `c_t = 1{ω_t < κ}` with `ω` i.i.d. uniform on `[0,1]` (`coinLaw`), so
`P(c_t = 1) = κ` for `κ ∈ [0,1]`. The policy reads only the feedback vectors recorded in the
history (round `r < t`, else `0`). The break-even statistic `D_t − D_{t₀−1}` is computed as the
probe's own sum `∑_{u=t₀}^{t} d_u` of the advantages observed in the probe rounds, which is the
same number. A probe that never breaks even continues through the last round. -/
noncomputable def comparisonProbing (κ : ℝ) : Policy 2 where
  Ω := Coins
  μ := coinLaw
  act := fun t h ω =>
    if cpProbe κ (fun r => if hr : r < t then (h ⟨r, hr⟩).2 else 0) ω t then 0 else 1

end FeedbackSwitching.Supplement



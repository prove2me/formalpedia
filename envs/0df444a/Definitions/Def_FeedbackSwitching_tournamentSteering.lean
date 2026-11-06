-- Prove2me | Definitions.Def_FeedbackSwitching_tournamentSteering
-- name    : FeedbackSwitching_tournamentSteering
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:05.648789+00:00
-- url     : https://prove2.me/theorems/fa56e9fa-338e-4a11-8a38-3365d36d0416
-- title:
--   TournamentSteering (Algorithm 1) with the parameters of §4.6, as a policy
-- statement:
--   **TournamentSteering** for a tournament orientation and a choice of LP solutions. If $K=1$, $T=1$ or $\kappa_\star>1/32$, play a fixed action. Otherwise, with $\kappa=2^{-m}$ and the parameters (28):
--
--   1. Split the horizon into blocks of $H$ rounds (the last may be shorter) and set $\pi_1=\mathbf 1/K$.
--   2. For each block $b$: smooth $w=(1-\varepsilon)\pi_b+\varepsilon\mathbf 1/K$; prepare $(p,x,(\Psi_s)_s)$ by PrepareBlock$(w,\kappa)$; run the block procedure (rate, restarts, ProbeChunk with the tournament scores) to obtain $\hat G_b$; update $\pi_{b+1,i}\propto\pi_{b,i}e^{-\eta\hat G_{b,i}}$.
--
--   The policy uses only the comparisons revealed by the played actions.
--
--   **Formalization Note** The policy reads only the feedback vectors of its history; in each round it recomputes the run from the history and the coins. "A solution of the LP" is an arbitrary selection of optimal points. $\pi_b$ is exponential weights from the uniform distribution (`wmWeights`). Coins: three per round (rate at block starts, boundary, action).
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Algorithm 1, p.18 (PDF p.20); §4.5–§4.6, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_FeedbackSwitching_Policy
import Definitions.Def_FeedbackSwitching_blockRun
import Definitions.Def_FeedbackSwitching_CSet
import Definitions.Def_FeedbackSwitching_tScore
import Definitions.Def_FeedbackSwitching_prepareBlock
import Definitions.Def_FeedbackSwitching_eq28Params
open Matrix
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

The inputs of one iteration of Algorithm 1 (lines 3–4): smooth `π` to
`w = (1 − ε)π + ε 1/K`, take the assignment `sel w` (a solution of the LP (19) with anchor `w`),
run PrepareBlock, and score with the tournament scores (21) for `P_τ`. -/
noncomputable def tsBlockInput {K : ℕ} (A : Fin K → Fin K → Prop)
    (sel : (Fin K → ℝ) → (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ))
    (m : ℕ) (M η ε : ℝ) (π : Fin K → ℝ) : BlockInput K :=
  let w : Fin K → ℝ := fun i => (1 - ε) * π i + ε / K
  let κ := baseRate m
  let p := prepP κ w (sel w).2
  let x := prepX κ w (sel w).2
  { p := p, x := x, Ψ := prepareBlock κ w (sel w), m := m, M := M, η := η,
    d := fun τ _ ℓ s j => tScore A (holdingP p x τ) ℓ s j }

/-- The block estimates `Ĝ_0, …, Ĝ_{b−1}` of Algorithm 1 after `b` blocks (entries `≥ b` are `0`),
when the observed vectors are `fb` and the coins `ω`. Block `b` covers rounds
`[bH, bH + h_b)`, `h_b = min(H, T − bH)`; its weights are `π_b = wmWeights η Ĝ b`
(exponential weights from `π_1 = 1/K`, line 8); its coins are `ω (3(bH))` (rate),
`ω (3t + 1)` (boundary after round `t`), `ω (3t + 2)` (action of round `t`). -/
noncomputable def tsEsts {K : ℕ} [NeZero K] (A : Fin K → Fin K → Prop)
    (sel : (Fin K → ℝ) → (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ))
    (m H T : ℕ) (M η ε : ℝ) (fb : ℕ → Fin K → ℝ) (ω : Coins) : ℕ → ℕ → Fin K → ℝ
  | 0 => fun _ => 0
  | b + 1 =>
      let prev := tsEsts A sel m H T M η ε fb ω b
      let B := tsBlockInput A sel m M η ε (UnderstandingML.wmWeights η prev b)
      let s := b * H
      Function.update prev b
        (truncate η (blockZOf B (fun r _ => fb (s + r)) (ω (3 * s))
          (fun r => ω (3 * (s + r) + 1)) (fun r => ω (3 * (s + r) + 2)) (min H (T - s))))

/-- The action of Algorithm 1 in round `t` (0-based): block `b = ⌊t/H⌋`, block round `t − bH`. -/
noncomputable def tsAction {K : ℕ} [NeZero K] (A : Fin K → Fin K → Prop)
    (sel : (Fin K → ℝ) → (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ))
    (m H T : ℕ) (M η ε : ℝ) (fb : ℕ → Fin K → ℝ) (ω : Coins) (t : ℕ) : Fin K :=
  let b := t / H
  let s := b * H
  let B := tsBlockInput A sel m M η ε
    (UnderstandingML.wmWeights η (tsEsts A sel m H T M η ε fb ω b) b)
  (blockTrace B (fun r _ => fb (s + r)) (ω (3 * s)) (fun r => ω (3 * (s + r) + 1))
    (fun r => ω (3 * (s + r) + 2)) (t - s)).X

/-- The feedback vectors recorded in a history of `t` rounds (`0` from round `t` on). -/
def histFeedback {K t : ℕ} (h : Hist K t) (r : ℕ) : Fin K → ℝ :=
  if hr : r < t then (h ⟨r, hr⟩).2 else 0

/-- **TournamentSteering** (Algorithm 1, p.18 = PDF p.20, with the parameters of §4.6, p.23) for
the horizon `T`, the tournament orientation `A` and the LP selection `sel`, as a policy on i.i.d.
uniform coins. If `K = 1`, `T ≤ 1` or `κ⋆ > 1/32` it plays a fixed action (action `0`) throughout.
Otherwise `m = ⌊log₂(1/κ⋆)⌋`, `κ = 2^{−m}`, and Algorithm 1 runs with the parameters (28):
`H = 1/(8κ)`, `δ = (KT)^{−20}`, `M = 100 log(2/δ)`, `η = κ/(2^{25} M m Λ)`, `ε = 1/T`.

**Formalization Note.** The policy reads only the recorded feedback vectors of the history
(`reveal`); its scores and estimates are computed on them. "A solution of the LP" is an arbitrary
selection `sel`; Theorem 2 quantifies over every selection returning optimal points. In each round
`t` the policy recomputes the whole run from the history and the coins; the actions it recomputes
for past rounds are the ones it played. -/
noncomputable def tournamentSteering {K : ℕ} [NeZero K] (A : Fin K → Fin K → Prop)
    (sel : (Fin K → ℝ) → (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ)) (T : ℕ) :
    Policy K where
  Ω := Coins
  μ := coinLaw
  act := fun t h ω =>
    if K = 1 ∨ T ≤ 1 ∨ 1 / 32 < kappaStar K T then 0
    else
      tsAction A sel (tsExponent K T) (eq28H (tsExponent K T)) T (eq28M K T)
        (eq28Eta K T (tsExponent K T)) (1 / (T : ℝ)) (histFeedback h) ω t

end FeedbackSwitching



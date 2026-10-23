-- Prove2me | Definitions.Def_DriftLinBandit_BOB_Bob
-- name    : DriftLinBandit_BOB_Bob
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:56.772502+00:00
-- url     : https://prove2.me/theorems/9b055c99-6cd8-4176-899a-8c8a3cc69f7c
-- title:
--   §7.1, pp. 14–15 — the Bandit-over-Bandit algorithm: parameters (11)–(12), EXP3 over window sizes (13)–(14), restarted SW-UCB blocks
-- statement:
--   This file defines the **Bandit-over-Bandit (BOB)** algorithm (Algorithm 2), which runs SW-UCB without knowing the variation budget by letting an EXP3 learner choose the window size.
--
--   **Parameters (11)–(12).** For dimension $d$ and horizon $T$,
--   $$
--   H=\lfloor dT^{1/2}\rfloor,\quad \Delta=\lceil\ln H\rceil,\quad J=\{H^0,\lfloor H^{1/\Delta}\rfloor,\dots,H\},\quad Q=2H+4R\sqrt{H\ln(T/\sqrt H)},
--   $$
--   $$
--   \gamma=\min\Big\{1,\sqrt{\frac{(\Delta+1)\ln(\Delta+1)}{(e-1)\lceil T/H\rceil}}\Big\},\qquad s_{j,1}=1\quad(j=0,\dots,\Delta).
--   $$
--
--   **Blocks.** The horizon is cut into $\lceil T/H\rceil$ blocks; block $i$ consists of the rounds $(i-1)H+1,\dots,iH\wedge T$. Before block $i$, BOB forms the distribution (13)
--   $$
--   p_{j,i}=(1-\gamma)\frac{s_{j,i}}{\sum_{u=0}^{\Delta}s_{u,i}}+\frac{\gamma}{\Delta+1},
--   $$
--   draws $j_i=j$ with probability $p_{j,i}$, and runs SW-UCB with window size $w_i=\lfloor H^{j_i/\Delta}\rfloor$ restarted from scratch at the first round of the block. After the block, (14) sets
--   $$
--   s_{j_i,i+1}=s_{j_i,i}\exp\Big(\frac{\gamma}{(\Delta+1)p_{j_i,i}}\Big(\frac12+\frac{\sum_{t=(i-1)H+1}^{iH\wedge T}Y_t}{Q}\Big)\Big),
--   $$
--   and leaves the other weights unchanged. The **dynamic regret of BOB** is the expectation of the realised regret over both the noise and EXP3's draws.
--
--   These objects state Lemma 1, Proposition 1 and Theorem 4.
--
--   **Formalization Note.** EXP3's draws are modelled exactly as a finite mixture: for a choice sequence $j_1,\dots,j_{\lceil T/H\rceil}$, `bobProb` is $\prod_i p_{j_i,i}$ (each factor computed from the rewards of the earlier blocks on the noise realisation $\omega$), and `bobRegretMix` is $\sum_{j_1,\dots}\prod_i p_{j_i,i}\cdot\mathrm{Regret}_T$. Its integral against the noise law is $\mathcal R_T(\text{BOB})$. Inside block $i$, SW-UCB uses the window $[\max((i-1)H+1,t-w_i),t-1]$, i.e. window size $w_i\wedge(t-(i-1)H-1)$ as in Appendix E, with $\lambda$ an input and $\delta=1/T$ in its radius $\beta$ (the choices of Appendix C). Block rewards are not clipped. $|J|$ is taken as $\Delta+1$ (indices $j=0,\dots,\Delta$), as in the paper, even if two floors coincide; at $\Delta=0$ the only window is $1$.
-- source:
--   Cheung, Simchi-Levi & Zhu, arXiv:1903.01461v4, pp. 14–15, §7.1, Algorithm 2, (11)–(14); Appendix E, p. 40

import Mathlib
import Definitions.Def_DriftLinBandit_BOB_Model

namespace DriftLinBandit.BOB

open MeasureTheory Matrix

noncomputable section

/-! # The Bandit-over-Bandit (BOB) algorithm

Cheung, Simchi-Levi & Zhu, *Hedging the Drift*, arXiv:1903.01461v4, §7.1, Algorithm 2 and
(11)–(14), pp. 14–15; the restart convention of Appendix E, p. 40. -/

/-- The block length `H = ⌊d T^{1/2}⌋` of (11). -/
def bobH (d T : ℕ) : ℕ := ⌊(d : ℝ) * Real.sqrt T⌋₊

/-- `Δ = ⌈ln H⌉` of (11). -/
def bobDelta (d T : ℕ) : ℕ := ⌈Real.log (bobH d T)⌉₊

/-- The candidate window sizes `J = {H⁰, ⌊H^{1/Δ}⌋, …, H}` of (11), indexed by
`j = 0, …, Δ`: the `j`-th one is `⌊H^{j/Δ}⌋` (for `Δ = 0` the only index is `j = 0`, giving `1`). -/
def bobJ (d T : ℕ) (j : Fin (bobDelta d T + 1)) : ℕ :=
  ⌊(bobH d T : ℝ) ^ ((j : ℝ) / (bobDelta d T : ℝ))⌋₊

/-- The normalisation constant `Q = 2H + 4R √(H ln(T/√H))` of (11). -/
def bobQ (R : ℝ) (d T : ℕ) : ℝ :=
  2 * (bobH d T : ℝ) +
    4 * R * Real.sqrt ((bobH d T : ℝ) * Real.log ((T : ℝ) / Real.sqrt (bobH d T)))

/-- The number of blocks `⌈T/H⌉`. -/
def bobBlocks (d T : ℕ) : ℕ := ⌈(T : ℝ) / (bobH d T : ℝ)⌉₊

/-- The EXP3 exploration rate `γ = min{1, √((Δ+1) ln(Δ+1) / ((e−1)⌈T/H⌉))}` of (12). -/
def bobGamma (d T : ℕ) : ℝ :=
  min 1 (Real.sqrt (((bobDelta d T : ℝ) + 1) * Real.log ((bobDelta d T : ℝ) + 1) /
    ((Real.exp 1 - 1) * (bobBlocks d T : ℝ))))

/-- The first round `(i − 1)H + 1` of block `i` (blocks are numbered from `1`). -/
def blockStart (H i : ℕ) : ℕ := (i - 1) * H + 1

/-- The last round `i·H ∧ T` of block `i`. -/
def blockEnd (H T i : ℕ) : ℕ := min (i * H) T

/-- The block `⌊(t − 1)/H⌋ + 1` containing round `t ≥ 1`. -/
def blockOf (H t : ℕ) : ℕ := (t - 1) / H + 1

/-- A sequence of EXP3 choices: one index `j_i ∈ {0, …, Δ}` for each block `i = 1, …, ⌈T/H⌉`
(block `i` is stored at position `i − 1`). -/
abbrev ChoiceSeq (d T : ℕ) : Type := Fin (bobBlocks d T) → Fin (bobDelta d T + 1)

/-- The index `j_i` that the choice sequence `js` selects for block `i` (`0` outside the blocks). -/
def choiceAt {d T : ℕ} (js : ChoiceSeq d T) (i : ℕ) : Fin (bobDelta d T + 1) :=
  if h : i - 1 < bobBlocks d T then js ⟨i - 1, h⟩ else 0

/-- The action BOB plays in round `t` (Algorithm 2, lines 5–6, and Appendix E, p. 40) when EXP3's
choices are `js`: if `t` lies in block `i`, it is the action of the SW-UCB algorithm with window
size `w_i = ⌊H^{j_i/Δ}⌋`, restarted from scratch at the first round `(i − 1)H + 1` of block `i`
(so its window is `[max((i−1)H+1, t − w_i), t − 1]`), with regularisation `λ` and `δ = 1/T` in the
radius (3). -/
def bobActs {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (js : ChoiceSeq d I.T)
    (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  let H := bobH d I.T
  let i := blockOf H t
  swucb I R L S lam (bobJ d I.T (choiceAt js i)) (1 / (I.T : ℝ)) (blockStart H i) η t ω

/-- The total reward `∑_{t=(i−1)H+1}^{i·H∧T} Y_t` collected by BOB in block `i`, where
`Y_t = ⟨X_t, θ_t⟩ + η_t`. -/
def blockReward {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (js : ChoiceSeq d I.T)
    (η : ℕ → Ω → ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  let H := bobH d I.T
  ∑ t ∈ Finset.Icc (blockStart H i) (blockEnd H I.T i),
    (bobActs I R L S lam js η t ω ⬝ᵥ I.θ t + η t ω)

/-- The EXP3 sampling distribution (13): `p_j = (1 − γ) s_j / ∑_{u=0}^Δ s_u + γ/(Δ + 1)` for
weights `s`. -/
def bobP {d T : ℕ} (s : Fin (bobDelta d T + 1) → ℝ) (j : Fin (bobDelta d T + 1)) : ℝ :=
  (1 - bobGamma d T) * s j / (∑ u, s u) + bobGamma d T / ((bobDelta d T : ℝ) + 1)

/-- The EXP3 weights `s_{j,i}` of (12) and (14) along the choice sequence `js` and the noise
realisation `ω`: `s_{j,1} = 1`; after block `i`, the weight of the chosen index `j_i` is multiplied
by `exp(γ/((Δ+1) p_{j_i,i}) · (1/2 + ∑_{t=(i−1)H+1}^{i·H∧T} Y_t / Q))` and the other weights are
unchanged. (`bobWeights … 0` is an unused placeholder.) -/
def bobWeights {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (js : ChoiceSeq d I.T)
    (η : ℕ → Ω → ℝ) (ω : Ω) : ℕ → Fin (bobDelta d I.T + 1) → ℝ
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | i + 2 =>
      let s := bobWeights I R L S lam js η ω (i + 1)
      let ji := choiceAt js (i + 1)
      let p := bobP s ji
      fun j =>
        if j = ji then
          s j * Real.exp (bobGamma d I.T / (((bobDelta d I.T : ℝ) + 1) * p) *
            (1 / 2 + blockReward I R L S lam js η (i + 1) ω / bobQ R d I.T))
        else s j

/-- The probability `∏_{i=1}^{⌈T/H⌉} p_{j_i,i}` that EXP3 makes the choices `js`, given the noise
realisation `ω` (each `p_{·,i}` depends on the rewards of the blocks before `i`). -/
def bobProb {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (js : ChoiceSeq d I.T)
    (η : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  ∏ i : Fin (bobBlocks d I.T), bobP (bobWeights I R L S lam js η ω (i.val + 1)) (js i)

/-- The realised dynamic regret of BOB averaged over EXP3's internal randomisation:
`∑_{js} P(js | ω) · Regret_T(BOB with choices js)(ω)`. Its expectation over the noise is the dynamic
regret `R_T(BOB algorithm)`. -/
def bobRegretMix {d : ℕ} {Ω : Type*} (I : Instance d) (R L S lam : ℝ) (η : ℕ → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ js : ChoiceSeq d I.T,
    bobProb I R L S lam js η ω * regret I (bobActs I R L S lam js η) ω

end

end DriftLinBandit.BOB



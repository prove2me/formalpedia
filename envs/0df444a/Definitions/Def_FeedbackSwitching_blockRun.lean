-- Prove2me | Definitions.Def_FeedbackSwitching_blockRun
-- name    : FeedbackSwitching_blockRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:33.802837+00:00
-- url     : https://prove2.me/theorems/9aeeba59-bb05-4fb0-b347-5df92d4778a5
-- title:
--   The block procedure: lines 5–8 of Algorithm 1 with ProbeChunk (Algorithm 2)
-- statement:
--   Inputs: sampling law $p$, refresh law $x$, estimation matrices $(\Psi_s)_s$, $\kappa=2^{-m}$, score threshold $M$ (steering strength $\beta=1/(4M)$), learning rate $\eta$, and scores $d$ for each reference chain $P_\tau$. For a block of $h$ rounds:
--
--   1. Draw the rate $\tau$ from the dyadic law (25).
--   2. Cut each internal boundary independently with probability $\tau$; the pieces are the chunks.
--   3. In each chunk (ProbeChunk): draw $X_1\sim p$, set $S\leftarrow0$, $G\leftarrow0$. In each round play $s=X_t$ and add $\Psi_s\ell_t$ to $G$. If the chunk continues, set $\hat d_j=0$ if $|S|>M-1$ (scoring has stopped) and $\hat d_j=d_t(s,j)$ otherwise, draw $X_{t+1}=j$ with probability $P_\tau(j\mid s)[1+\beta(S+\hat d_j)]/(1+\beta S)$, and update $S\leftarrow S+\hat d_{X_{t+1}}$. The chunk returns $G/(1+\beta S)$.
--   4. $Z=\sum_JG_J/R_J$, $R_J=1+\beta S_J$, and the output is $\hat G=\mathbf 1\{\eta\|Z\|_\infty\le1\}Z$ (Eq. (27)).
--
--   The internal switch count of a block path is $N_{\rm int}=\sum_{t=1}^{h-1}\mathbf 1\{X_{t+1}\ne X_t\}$.
--
--   **Formalization Note** The procedure is written round by round; it reads, in each round, a vector (the loss vector, or the feedback of the played action). Coins: one for the rate, one per internal boundary (cut iff below $\tau$), one per round for the action (a fresh draw from $p$ at a chunk start, the tilted transition otherwise), all i.i.d. uniform.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Algorithm 1 lines 5–8, p.18; §4.4 and Algorithm 2, pp.20–22; Eq. (27) (PDF pp.20–24)

import Mathlib
import Definitions.Def_FeedbackSwitching_holdingP
import Definitions.Def_FeedbackSwitching_rateLaw
import Definitions.Def_FeedbackSwitching_sampleFin
open Matrix
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

The inputs of the block procedure (lines 5–8 of Algorithm 1): sampling law `p`, refresh law
`x`, estimation matrices `(Ψ_s)_s`, base-rate exponent `m` (`κ = 2^{−m}`), score threshold `M`,
learning rate `η` (used only in the truncation of line 8), and the score rule:
`d τ t ℓ s j` is the score `d_t(s, j)` for the reference chain `P_τ` in block round `t` when the
loss (or feedback) vector of that round is `ℓ`. -/
structure BlockInput (K : ℕ) where
  /-- Sampling law. -/
  p : Fin K → ℝ
  /-- Refresh law. -/
  x : Fin K → ℝ
  /-- Estimation matrices. -/
  Ψ : Fin K → Matrix (Fin K) (Fin K) ℝ
  /-- `κ = 2^{−m}`. -/
  m : ℕ
  /-- Score threshold. -/
  M : ℝ
  /-- Learning rate of the truncation `1{η‖Z‖_∞ ≤ 1}`. -/
  η : ℝ
  /-- Scores, indexed by the rate `τ` of the reference chain `P_τ`. -/
  d : ℝ → ℕ → (Fin K → ℝ) → Fin K → Fin K → ℝ

/-- State of the block procedure after a round: the action `X` just played, the score sum `S` of
the current chunk, the current chunk estimate `G` (Algorithm 2), and the sum `Z` of the corrected
estimates `G_J / R_J` of the chunks already finished. -/
structure BlockState (K : ℕ) where
  /-- Action of the round. -/
  X : Fin K
  /-- Score sum of the current chunk. -/
  S : ℝ
  /-- Chunk estimate `G = ∑ Ψ_{X_t} ℓ_t` of the current chunk. -/
  G : Fin K → ℝ
  /-- Sum of the corrected estimates of the finished chunks. -/
  Z : Fin K → ℝ

/-- The restart rate `τ` drawn from the dyadic law (25) with the coin `uτ` (line 5). -/
noncomputable def blockRate {K : ℕ} (B : BlockInput K) (uτ : ℝ) : ℝ :=
  rateVal B.m (sampleFin (rateProb B.m) uτ)

/-- **The block procedure** (lines 5–8 of Algorithm 1 with ProbeChunk, Algorithm 2, pp.18–22 =
PDF pp.20–24), round by round. `fb t s` is the vector the procedure reads in block round `t` when
it plays `s` (the loss vector `ℓ_t`, or the feedback revealed by `s`); `uτ` is the rate coin,
`c t` the coin of the boundary between rounds `t` and `t + 1` (cut, i.e. restart, iff `c t < τ`),
and `a t` the coin of the action of round `t`.

Round `0` and every round after a cut start a chunk: the action is drawn from `p`, `S ← 0`,
`G ← Ψ_X ℓ`, and the finished chunk contributes `G/(1 + βS)` to `Z`. Inside a chunk, with
`s = X_t`, the scores are `d̂_j = 0` if `|S| > M − 1` (scoring has stopped) and `d̂_j = d_t(s, j)`
otherwise; `X_{t+1} = j` with probability `P_τ(j | s)[1 + β(S + d̂_j)]/(1 + βS)`; then
`S ← S + d̂_{X_{t+1}}` and `G ← G + Ψ_{X_{t+1}} ℓ_{t+1}`. Here `β = 1/(4M)`. -/
noncomputable def blockTrace {K : ℕ} [NeZero K] (B : BlockInput K) (fb : ℕ → Fin K → Fin K → ℝ)
    (uτ : ℝ) (c a : ℕ → ℝ) : ℕ → BlockState K
  | 0 =>
      let X := sampleFin B.p (a 0)
      ⟨X, 0, B.Ψ X *ᵥ fb 0 X, 0⟩
  | t + 1 =>
      let st := blockTrace B fb uτ c a t
      let τ := blockRate B uτ
      let β := 1 / (4 * B.M)
      if c t < τ then
        let X := sampleFin B.p (a (t + 1))
        ⟨X, 0, B.Ψ X *ᵥ fb (t + 1) X, st.Z + (1 + β * st.S)⁻¹ • st.G⟩
      else
        let dh : Fin K → ℝ := fun j =>
          if B.M - 1 < |st.S| then 0 else B.d τ t (fb t st.X) st.X j
        let X := sampleFin
          (fun j => holdingP B.p B.x τ st.X j * (1 + β * (st.S + dh j)) / (1 + β * st.S)) (a (t + 1))
        ⟨X, st.S + dh X, st.G + B.Ψ X *ᵥ fb (t + 1) X, st.Z⟩

/-- The raw corrected estimate `Z = ∑_{J} G_J / R_J` of a block of `h ≥ 1` rounds (Eq. (27)),
`R_J = 1 + βS_J`. -/
noncomputable def blockZOf {K : ℕ} [NeZero K] (B : BlockInput K) (fb : ℕ → Fin K → Fin K → ℝ)
    (uτ : ℝ) (c a : ℕ → ℝ) (h : ℕ) : Fin K → ℝ :=
  let st := blockTrace B fb uτ c a (h - 1)
  st.Z + (1 + 1 / (4 * B.M) * st.S)⁻¹ • st.G

/-- The truncated output `Ĝ = 1{η‖Z‖_∞ ≤ 1} Z` (Eq. (27); line 8 of Algorithm 1). -/
noncomputable def truncate {K : ℕ} (η : ℝ) (Z : Fin K → ℝ) : Fin K → ℝ :=
  if ∀ i, η * |Z i| ≤ 1 then Z else 0

/-- The block procedure on the i.i.d. uniform coins `ω`: rate coin `ω 0`, boundary coins
`ω (2t + 1)`, action coins `ω (2t + 2)`. -/
noncomputable def blockRun {K : ℕ} [NeZero K] (B : BlockInput K) (fb : ℕ → Fin K → Fin K → ℝ)
    (ω : Coins) : ℕ → BlockState K :=
  blockTrace B fb (ω 0) (fun t => ω (2 * t + 1)) (fun t => ω (2 * t + 2))

/-- Raw corrected estimate `Z` of a block of length `h` run on the coins `ω`. -/
noncomputable def blockZ {K : ℕ} [NeZero K] (B : BlockInput K) (fb : ℕ → Fin K → Fin K → ℝ)
    (h : ℕ) (ω : Coins) : Fin K → ℝ :=
  blockZOf B fb (ω 0) (fun t => ω (2 * t + 1)) (fun t => ω (2 * t + 2)) h

/-- Internal switch count `N_int = ∑_{t=1}^{h−1} 1{X_{t+1} ≠ X_t}` of an action path of a block of
length `h` (Corollary 2). -/
noncomputable def internalSwitches {K : ℕ} (X : ℕ → Fin K) (h : ℕ) : ℝ :=
  ∑ t ∈ Finset.range (h - 1), if X (t + 1) ≠ X t then (1 : ℝ) else 0

end FeedbackSwitching



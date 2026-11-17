-- Prove2me | Definitions.Def_CalibeatBandit_Supplement_BanditAlg
-- name    : CalibeatBandit_Supplement_BanditAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:29:05.983202+00:00
-- url     : https://prove2.me/theorems/c793587b-478c-4fd1-8bcf-00aeceba36f7
-- title:
--   Bandit algorithms and their expected swap regret against a deterministic oblivious reward sequence
-- statement:
--   A **$K$-action bandit algorithm** is described by its conditional mixed strategies. In round $t$, given its past actions $a_1,\dots,a_{t-1}$ and the observed rewards $y_1(a_1),\dots,y_{t-1}(a_{t-1})$, it plays action $i$ with probability $A_t(a_{<t};y_{<t}(a_{<t}))(i)$.
--
--   Against a **deterministic oblivious** reward sequence $y_1,\dots,y_T\in\mathbb R^K$, fixed before the algorithm runs, the probability that the algorithm plays $a=(a_1,\dots,a_T)\in[K]^T$ is
--   $$\mathbb P_{A,y}[a]=\prod_{t=1}^T A_t\big(a_{<t};y_{<t}(a_{<t})\big)(a_t),$$
--   and its **expected swap regret** is
--   $$\mathbb E[\mathrm{SR}_T]=\sum_{a\in[K]^T}\mathbb P_{A,y}[a]\cdot\max_{\sigma:[K]\to[K]}\sum_{t=1}^T\big(y_t(\sigma(a_t))-y_t(a_t)\big).$$
--
--   This is the quantity bounded from below in Theorem 4.1.
--
--   **Formalization Note** An algorithm with private randomness and internal state induces, against a fixed reward sequence, the same law of actions as these conditionals. The conditionals depend on the rewards only through the observed ones, so this description covers every bandit algorithm. Rounds are $0,\dots,T-1$, and the history is a prefix, so the algorithm cannot read the future. The expectation is an explicit finite sum, so it is never vacuous.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §2.1 (definition of SR_T), p.8 (PDF 8); §4, pp.13–14 (PDF 13–14)

import Mathlib

set_option autoImplicit false

namespace CalibeatBandit

namespace Supplement

/-- A **`K`-action bandit algorithm** (no recommendation), given by its conditional mixed
strategies: in round `t` (rounds `0, 1, …`), from its past actions `I_0, …, I_{t−1}` and the
observed rewards `y_0(I_0), …, y_{t−1}(I_{t−1})`, it plays action `i` with probability
`A t I r i`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §4, p.13–14
("every K-action bandit algorithm"; p.14: "q_t(i) = P[I_t = i | O_{t−1}]", the learner's
conditional mixed strategy given its information and private state).

**Formalization Note.** Against a reward sequence fixed in advance, an algorithm with private
randomness and internal state induces the same law of its actions as the behavioural strategy
`P[I_t = i | I_0, …, I_{t−1}]`, which depends on the rewards only through the observed ones; so
these conditionals represent every bandit algorithm in Theorem 4.1. The inputs are prefixes
(`Fin t`), so the algorithm cannot read the current or future rounds. -/
abbrev BanditAlg (K : ℕ) : Type := (t : ℕ) → (Fin t → Fin K) → (Fin t → ℝ) → Fin K → ℝ

/-- The probability that the bandit algorithm `A` plays the action sequence `a = (a_0, …, a_{T−1})`
against the deterministic oblivious reward sequence `y`: the product of its conditional
probabilities `∏_t A_t(a_0, …, a_{t−1}; y_0(a_0), …, y_{t−1}(a_{t−1}))(a_t)`. -/
def obliviousSeqProb {K : ℕ} (A : BanditAlg K) (T : ℕ) (y : ℕ → Fin K → ℝ)
    (a : Fin T → Fin K) : ℝ :=
  ∏ t : Fin T, A t (fun s => a (Fin.castLE t.isLt.le s))
    (fun s => y s (a (Fin.castLE t.isLt.le s))) (a t)

/-- The swap regret `SR_T = max_σ ∑_{t=1}^T (y_t(σ(a_t)) − y_t(a_t))` of an action sequence
`a : Fin T → Fin K` (the base mission's `swapRegret`, written over `Fin T`). -/
def seqSwapRegret {K : ℕ} (T : ℕ) (y : ℕ → Fin K → ℝ) (a : Fin T → Fin K) : ℝ :=
  Finset.univ.sup' ⟨id, Finset.mem_univ _⟩
    (fun σ : Fin K → Fin K => ∑ t : Fin T, (y t (σ (a t)) - y t (a t)))

/-- **Expected swap regret of a bandit algorithm against a deterministic oblivious reward
sequence**: `E[SR_T] = ∑_a P[I = a] · SR_T(a)`, the sum over all action sequences
`a ∈ [K]^T` of the probability (`obliviousSeqProb`) that the algorithm plays `a`, times the swap
regret of `a`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §2.1, p.8
(definition of `SR_T`) and Theorem 4.1, p.13.

**Formalization Note.** Rounds are `0, …, T − 1`. Because the rewards are fixed in advance, the
law of the action sequence is the explicit product of the algorithm's conditional probabilities
(a law that always exists), so `E[SR_T]` is a finite sum and never vacuous. -/
def expectedSwapRegret {K : ℕ} (A : BanditAlg K) (T : ℕ) (y : ℕ → Fin K → ℝ) : ℝ :=
  ∑ a : Fin T → Fin K, obliviousSeqProb A T y a * seqSwapRegret T y a

end Supplement

end CalibeatBandit



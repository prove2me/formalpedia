-- Prove2me | Definitions.Def_MeanOnlyProphet_Supplement_HistAlg
-- name    : MeanOnlyProphet_Supplement_HistAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:27:46.118026+00:00
-- url     : https://prove2.me/theorems/6304053e-02bd-4ae2-be0a-2acab3acf820
-- title:
--   Randomized, history-dependent online algorithms for $n$ values
-- statement:
--   Fix $n\ge1$. A **randomized, history-dependent online algorithm** $A$ for $n$ arriving values has a private random seed $\omega$ from a probability space $(\Omega,P)$, independent of the values. When the $i$-th value arrives it decides, as a measurable function of $\omega$ and of the values $X_1,\dots,X_i$ seen so far, whether to stop and accept $X_i$. It accepts at most one value; its reward $\mathrm{ALG}_A$ is the accepted value, or $0$ if it accepts nothing. For a law $F$ on $\mathbb R$, $\mathbb E_F[\mathrm{ALG}_A]$ is the expected reward when $X_1,\dots,X_n$ are i.i.d. with law $F$.
--
--   This is the most general online algorithm in the i.i.d. model, the class over which Theorem C.2 proves its impossibility result.
--
--   **Formalization Note** The algorithm is given by stopping sets $D_i\subseteq\Omega\times\mathbb R^n$ (0-based $i$). Each set is measurable, and membership depends only on $\omega$ and the first $i+1$ coordinates. The algorithm stops at the first $i$ with $(\omega,x)\in D_i$. The expectation is a Bochner integral over $P\otimes F^{\otimes n}$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), §2, p.5 (PDF p.6); Theorem C.2, p.42 (PDF p.43); App. C.1, p.43 (PDF p.44)

import Mathlib

open MeasureTheory

namespace MeanOnlyProphet.Supplement

/-- **Randomized, history-dependent online algorithm for `n` values.** Feng, Jin, Wu, Xiang,
*Mean-only Prophet Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), §2, p.5 (PDF p.6):
"The online algorithm … may accept at most one value, and must decide whether to accept a value when
it arrives. Its reward is ALG, with reward zero if it accepts nothing."; App. C.1, Theorem C.2, p.42
(PDF p.43): "every randomized, history-dependent algorithm A"; App. C.1, p.43 (PDF p.44): "Its decision
at time t may depend only on the points observed up to time t and a private random seed".

An algorithm with private seed space `Ω` is given by its stopping sets: after seeing the `i`-th value
it stops (and accepts that value) when `(ω, x) ∈ stopSet i`.

**Formalization Note.** Indices are 0-based (`i : Fin n` is the paper's `i + 1`-st arrival). Each
stopping set is measurable in the product σ-algebra of `Ω × ℝⁿ`, and it is non-anticipating: whether
the algorithm stops at `i` depends only on the seed `ω` and on `x_0, …, x_i`. -/
structure HistAlg (n : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The event "stop at arrival `i` if still active". -/
  stopSet : Fin n → Set (Ω × (Fin n → ℝ))
  /-- The stopping sets are measurable. -/
  measurableSet_stopSet : ∀ i, MeasurableSet (stopSet i)
  /-- The decision at arrival `i` depends only on the seed and the values seen so far. -/
  nonanticipating : ∀ (i : Fin n) (ω : Ω) (x y : Fin n → ℝ), (∀ k, k ≤ i → x k = y k) →
    ((ω, x) ∈ stopSet i ↔ (ω, y) ∈ stopSet i)

namespace HistAlg

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- **Reward `ALG_A`**: the value at the first arrival where `A` stops, or `0` if it never stops. -/
noncomputable def reward (A : HistAlg n Ω) (ω : Ω) (x : Fin n → ℝ) : ℝ := by
  classical
  exact if h : (Finset.univ.filter fun i => (ω, x) ∈ A.stopSet i).Nonempty then
    x ((Finset.univ.filter fun i => (ω, x) ∈ A.stopSet i).min' h) else 0

/-- **Expected reward `E_F[ALG_A]`** on `n` i.i.d. values with law `F`, the seed having law `P`
independently of the values. Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), Theorem C.2, p.42
(PDF p.43).

**Formalization Note.** Bochner integral over `P ⊗ F^{⊗n}`; the reward is measurable because the
stopping sets are, and it lies between `0` and `max_i x_i` for nonnegative values. -/
noncomputable def expectedReward (A : HistAlg n Ω) (P : Measure Ω) (F : Measure ℝ) : ℝ :=
  ∫ p, A.reward p.1 p.2 ∂(P.prod (Measure.pi fun _ : Fin n => F))

end HistAlg

end MeanOnlyProphet.Supplement



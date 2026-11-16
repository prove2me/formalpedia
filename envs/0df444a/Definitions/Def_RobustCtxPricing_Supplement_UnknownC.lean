-- Prove2me | Definitions.Def_RobustCtxPricing_Supplement_UnknownC
-- name    : RobustCtxPricing_Supplement_UnknownC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:03:59.237133+00:00
-- url     : https://prove2.me/theorems/3388e2fb-a6df-4a55-8c43-4eb0af5d96da
-- title:
--   The unknown-$C$ adaptive adversary against a randomized seller, and the law of the seller's coins
-- statement:
--   This module fixes the probabilistic interaction of §2.2 of Castiglioni–Stradi in the unknown-$C$ setting.
--
--   1. **Coins.** The seller's randomness is a sequence $\xi=(\xi_1,\xi_2,\dots)$ of i.i.d. uniform variables on $[0,1]$; its law is the infinite product of Lebesgue measure on $[0,1]$.
--   2. **Executions.** An interaction is described by its executions indexed by the randomness $\omega$: contexts $u_t(\omega)$, a corrupted set $S(\omega)$, observed feedback $Y_t(\omega)$, posted prices $p_t(\omega)$, and the seller's tie-breaking choices $w_t(\omega)$.
--   3. **Admissibility.** For every $\omega$: $S(\omega)\subseteq[T]$, $|S(\omega)|\le C$, and $Y_t(\omega)=\mathbb I\{p_t(\omega)\le\langle\theta^\star,u_t(\omega)\rangle\}$ for $t\notin S(\omega)$. For any two executions whose histories $(u_s,p_s,Y_s)_{s<t}$ coincide, the context $u_t$, the decision whether $t\in S$ and the seller's tie-break $w_t$ coincide; if the posted prices $p_t$ also coincide, so does the feedback $Y_t$.
--
--   Clause 3 is the paper's requirement that the corruption decision be made "after observing $u_t$ but before the seller draws $p_t$, without access to the seller's current randomization", while the corrupted feedback may be chosen "after observing the realized price". This is the adversary of Theorem 5.4.
--
--   **Formalization Note** The adversary and the tie-breaking rule are deterministic functions of the history; a randomized adversary whose randomness is independent of the seller's coins is a mixture of deterministic ones.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §2.2, p.11 (corrupted set S, adaptive choice of corrupted rounds in the unknown-C setting); Algorithm 5, Line 9, p.24

import Mathlib
import Definitions.Def_RobustCtxPricing_Model

open MeasureTheory

namespace RobustCtxPricing.Supplement

/-- **The law of the learner's coins.** The coins `ξ_1, ξ_2, …` are i.i.d. uniform on `[0,1]`:
`coinLaw` is the infinite product of the Lebesgue (uniform) probability measure on
`unitInterval = [0,1]`. A randomized seller (Algorithm 5, Line 9: "Post `U_t` with probability
`q_t`", Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust Contextual Pricing*,
arXiv:2607.11210, p.24) uses coin `ξ_t` in round `t`. -/
noncomputable def coinLaw : Measure (ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

/-- **Equal histories up to round `t`.** The interaction histories `(u_s, p_s, Y_s)_{s<t}`
(contexts, posted prices, observed feedback) of two executions coincide before round `t`. -/
def SameHistory {d : ℕ} (u u' : ℕ → EuclideanSpace ℝ (Fin d)) (p p' : ℕ → ℝ)
    (Y Y' : ℕ → Bool) (t : ℕ) : Prop :=
  ∀ s < t, u s = u' s ∧ p s = p' s ∧ Y s = Y' s

/-- **The unknown-`C` adaptive adversary (§2.2) against a randomized seller, with history-driven
tie-breaking.** Castiglioni–Stradi, arXiv:2607.11210, §2.2, p.11: "There is a set of corrupted
rounds `S ⊆ [T]` with `|S| ≤ C` such that `Y_t = y_t` for every `t ∉ S`, while for `t ∈ S`, the
corrupted signal `Y_t` may be chosen arbitrarily—in particular, as a function of the full history,
the current context `u_t`, and the hidden parameter `θ⋆`. … In the unknown-`C` setting, we require
this decision [whether `t ∈ S`] to be made after observing `u_t` but before the seller draws `p_t`,
without access to the seller's current randomization. Once a round is selected for corruption, the
adversary may still choose `Y_t` after observing the realized price."

The executions are indexed by the learner's randomness `ω : Ω`: `u ω t` is the context, `S ω` the
set of corrupted rounds, `Y ω t` the observed feedback, `p ω t` the posted price and `w ω t` the
seller's tie-breaking choice of round `t` made before its coin is used.
`IsUnknownCInteraction T C θ u S Y w p` says:

1. for every `ω`, `S ω ⊆ {0, …, T−1}`, `|S ω| ≤ C`, and `Y ω t = 𝕀{p ω t ≤ ⟨θ, u ω t⟩}` for every
   round `t < T` outside `S ω`;
2. (non-anticipation) for any two executions with equal histories before round `t < T`, the
   context `u_t`, the decision `t ∈ S`, and the seller's tie-breaking choice `w_t` coincide; if
   moreover the posted prices `p_t` coincide, so does the feedback `Y_t`.

**Formalization Note.** Clause 2 says that the adversary's context and corruption decisions of
round `t`, and the seller's tie-breaks, are functions of the history before round `t` (and of `θ⋆`,
which is fixed), so they cannot see the coin of round `t`; the corrupted feedback `Y_t` is a
function of the history and the realized price `p_t`. This is a deterministic adversary strategy;
a randomized adversary whose randomness is independent of the seller's is a mixture of
deterministic ones. -/
def IsUnknownCInteraction {d : ℕ} {Ω : Type*} (T C : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (u : Ω → ℕ → EuclideanSpace ℝ (Fin d)) (S : Ω → Finset ℕ) (Y : Ω → ℕ → Bool)
    (w p : Ω → ℕ → ℝ) : Prop :=
  (∀ ω, S ω ⊆ Finset.range T ∧ (S ω).card ≤ C ∧
    ∀ t < T, t ∉ S ω → Y ω t = decide (p ω t ≤ inner ℝ θ (u ω t))) ∧
  (∀ ω ω' t, t < T → SameHistory (u ω) (u ω') (p ω) (p ω') (Y ω) (Y ω') t →
    u ω t = u ω' t ∧ (t ∈ S ω ↔ t ∈ S ω') ∧ w ω t = w ω' t ∧
    (p ω t = p ω' t → Y ω t = Y ω' t))

end RobustCtxPricing.Supplement



-- Prove2me | Definitions.Def_WildeQIT_Feedback_IsAchievableWithFeedback
-- name    : WildeQIT_Feedback_IsAchievableWithFeedback
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:37:21.366242+00:00
-- url     : https://prove2.me/theorems/8438f9c4-0580-4efd-bd90-9777d0689626
-- title:
--   Rate $C$ achievable for $p_{Y|X}$ with feedback
-- statement:
--   Let $\mathcal N=p_{Y|X}$ be a classical channel on finite alphabets. A rate $C\in\mathbb R$ is **achievable for $p_{Y|X}$ with feedback** if for every $\varepsilon\in(0,1)$ and every $\delta>0$ there is $N_0$ such that for every block length $n\ge N_0$ there is an $(n,C-\delta,\varepsilon)$ classical feedback code: a feedback code with $M$ messages,
--   $$
--   M\ge 2^{n(C-\delta)},
--   $$
--   whose error probability for a uniformly distributed message satisfies $\Pr\{M'\neq M\}\le\varepsilon$ (21.115).
--
--   The feedback capacity is the supremum of the rates achievable with feedback; Theorem 21.5.1 identifies it with $\max_{p_X}I(X;Y)$.
--
--   **Formalization Note** The book does not spell out "achievable with feedback"; the quantifiers are those of achievability in §14.10 (p. 454), with the feedback code and error criterion (21.115) of p. 604. "Rate $C-\delta$" is read as $M\ge 2^{n(C-\delta)}$, as in the published `WildeQIT.IsAchievableChannelRate`, because $2^{n(C-\delta)}$ is rarely an integer; with the average error criterion a code with more messages yields one with fewer by keeping the messages of smallest error.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, p. 604 ((n, C − δ, ε) feedback code, (21.115)); achievability quantifiers of §14.10, p. 454

import Definitions.Def_WildeQIT_Feedback_FeedbackCode_errorProb
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Theorem 21.5.1 and its
proof, p. 604: a rate achievable with feedback.
-/

namespace WildeQIT.Feedback

variable {α β : Type} [Fintype β] [DecidableEq β]

/-- **Rate achievable with feedback.** Wilde, arXiv:1106.1445v8, Theorem 21.5.1, p. 604
("`C` is achievable for `p_{Y|X}` with feedback"), with the achievability quantifiers of
§14.10, p. 454: for every `ε ∈ (0, 1)`, `δ > 0` and all sufficiently large `n` there is an
`(n, C − δ, ε)` classical feedback code, that is, a feedback code of block length `n` with at
least `2^{n(C−δ)}` messages and error probability `Pr{M′ ≠ M} ≤ ε` (21.115) for a uniform
message.

**Formalization Note.** "Rate `C − δ`" is read as `|𝓜| ≥ 2^{n(C−δ)}` (message counts are
integers), as in the published `WildeQIT.IsAchievableChannelRate`; "sufficiently large `n`" is
`∃ N₀, ∀ n ≥ N₀`. -/
def IsAchievableWithFeedback (N : Channel α β) (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ M : ℕ, (2 : ℝ) ^ ((n : ℝ) * (C - δ)) ≤ M ∧
      ∃ c : FeedbackCode α β n M, c.errorProb N ≤ ε

end WildeQIT.Feedback



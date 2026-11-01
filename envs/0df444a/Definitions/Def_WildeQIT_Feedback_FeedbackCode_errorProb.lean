-- Prove2me | Definitions.Def_WildeQIT_Feedback_FeedbackCode_errorProb
-- name    : WildeQIT_Feedback_FeedbackCode_errorProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:56.330307+00:00
-- url     : https://prove2.me/theorems/dba1fc14-ff08-43d9-99a4-027dc3411323
-- title:
--   Error probability $\Pr\{M^\prime\neq M\}$ of a feedback code for a uniform message
-- statement:
--   Let $\mathcal N=p_{Y|X}$ be a classical channel on finite alphabets and let a feedback code with $M$ messages, encoders $x_i(m,y^{i-1})$ and decoder $g$ be given. The message $M$ is uniformly distributed on $\{1,\dots,M\}$, and the receiver's estimate is $M'\equiv g(Y^n)$. The **error probability** of the code is
--   $$
--   \Pr\{M'\neq M\}=\frac1M\sum_{m=1}^{M}\ \sum_{y^n:\ g(y^n)\neq m}\ \prod_{i=1}^{n}p_{Y|X}\bigl(y_i\bigm| x_i(m,y^{i-1})\bigr),
--   $$
--   the quantity bounded by $\varepsilon$ in (21.115).
--
--   This is an *average* error probability over a uniformly distributed message, which is the criterion used in the feedback-capacity theorem; the channel coding theorem of Chapter 14 uses the maximal error probability instead.
--
--   **Formalization Note** With $M=0$ messages the value is $0$ (Lean's $1/0=0$); the achievability notion that uses this quantity requires $M\ge 2^{n(C-\delta)}>0$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, p. 604, eq. (21.115), and p. 605 ("we assume that the message M is uniformly distributed")

import Definitions.Def_WildeQIT_Feedback_FeedbackCode_outputProb

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.5.1, proof of
Theorem 21.5.1, pp. 604–605: the error probability (21.115) of a feedback code under a
uniformly distributed message.
-/

namespace WildeQIT.Feedback

variable {α β : Type} [Fintype β]

/-- **Error probability of a feedback code**, Wilde, *From Classical to Quantum Shannon
Theory*, arXiv:1106.1445v8, (21.115), p. 604: `Pr{M′ ≠ M}` with `M′ ≡ g(Yⁿ)` and the message
`M` uniformly distributed on its `M` values ("we assume that the message `M` is uniformly
distributed", p. 605):
`Pr{M′ ≠ M} = (1/|𝓜|) ∑_m ∑_{yⁿ : g(yⁿ) ≠ m} ∏ᵢ N(yᵢ | xᵢ(m, y^{i−1}))`.

**Formalization Note.** This is the *average* error probability over a uniform message, as in
(21.115), not the maximal error of §14.10. With `M = 0` messages the value is `0`; the
achievability notion that uses it requires `M ≥ 2^{n(C−δ)} > 0`. -/
noncomputable def FeedbackCode.errorProb [DecidableEq β] {n M : ℕ} (N : Channel α β)
    (c : FeedbackCode α β n M) : ℝ :=
  (1 / (M : ℝ)) * ∑ m, ∑ y, if c.dec y = m then 0 else c.outputProb N m y

end WildeQIT.Feedback



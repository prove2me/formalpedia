-- Prove2me | Definitions.Def_WildeQIT_Feedback_FeedbackCode_outputProb
-- name    : WildeQIT_Feedback_FeedbackCode_outputProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T18:36:22.731863+00:00
-- url     : https://prove2.me/theorems/a50e023b-6d4d-4716-8e07-8b14d89c6d39
-- title:
--   Output law of a feedback code: $p(y^n\mid m)=\prod_i p_{Y|X}(y_i\mid x_i(m,y^{i-1}))$
-- statement:
--   Let $\mathcal N=p_{Y|X}$ be a classical channel on finite alphabets and let $(x_i(\cdot,\cdot))_{i\le n},g$ be a feedback code. When the message is $m$ and the channel is used $n$ times memorylessly, the output word $y^n$ occurs with probability
--   $$
--   p(y^n\mid m)=\prod_{i=1}^{n}p_{Y|X}\bigl(y_i\bigm| x_i(m,y^{i-1})\bigr).
--   $$
--   Each channel use acts only on its current input $X_i=x_i(m,Y^{i-1})$: given $X_i$, the output $Y_i$ is independent of the message and of the earlier outputs ($Y^{i-1}M\to X_i\to Y_i$ is a Markov chain). The outputs are in general neither independent nor identically distributed, because each input depends on the earlier outputs.
--
--   **Formalization Note** The product runs over the 0-based times `Fin n`, and $y^{i-1}$ is `pastOutputs y i`. The channel is the published `WildeQIT.Channel α β`, with `(N x).prob y` $=p_{Y|X}(y|x)$.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, proof of Theorem 21.5.1, pp. 604–605 (memoryless channel with feedback; "Y_k is conditionally independent of Y^{k−1} and M through X_k")

import Definitions.Def_WildeQIT_Channel
import Definitions.Def_WildeQIT_Feedback_FeedbackCode
import Definitions.Def_WildeQIT_Feedback_pastOutputs

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, §21.5.1, proof of
Theorem 21.5.1, pp. 604–605: the law of the outputs of a feedback code over a memoryless
channel.
-/

namespace WildeQIT.Feedback

variable {α β : Type} [Fintype β]

/-- **Output law of a feedback code.** Wilde, *From Classical to Quantum Shannon Theory*,
arXiv:1106.1445v8, proof of Theorem 21.5.1, pp. 604–605. With message `m`, the memoryless
channel `N = p_{Y|X}` used `n` times with feedback produces the output word `yⁿ` with
probability `p(yⁿ | m) = ∏ᵢ N(yᵢ | xᵢ(m, y^{i−1}))`: each use sees the input `xᵢ`, which depends
on the message and on the earlier outputs ("`Y_k` is conditionally independent of `Y^{k−1}`
and `M` through `X_k`", p. 605).

**Formalization Note.** The product is over the 0-based times `Fin n`; the earlier outputs
are `pastOutputs y i`. The outputs are not i.i.d.: the factor at time `i` depends on
`y₀, …, y_{i−1}` through the encoder. -/
noncomputable def FeedbackCode.outputProb {n M : ℕ} (N : Channel α β) (c : FeedbackCode α β n M)
    (m : Fin M) (y : Fin n → β) : ℝ :=
  ∏ i, (N (c.enc m i (pastOutputs y i))).prob (y i)

end WildeQIT.Feedback



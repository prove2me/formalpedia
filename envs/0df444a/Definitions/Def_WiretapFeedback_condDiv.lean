-- Prove2me | Definitions.Def_WiretapFeedback_condDiv
-- name    : WiretapFeedback_condDiv
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:24:51.465571+00:00
-- url     : https://prove2.me/theorems/0a9a4f28-0098-4223-b321-ada8e5d337d3
-- title:
--   Conditional divergence $D(W\|V|P_X)$
-- statement:
--   For channels $W,V:\mathcal X\to\mathcal O$ on finite alphabets and an input distribution $P_X$, the **conditional divergence** is
--   $$
--   D(W\|V|P_X)=D(P_XW\,\|\,P_XV)=\sum_x P_X(x)\,D(W_x\|V_x)\in[0,+\infty],
--   $$
--   in bits, where $D(P\|Q)=\sum_x P(x)\log_2\frac{P(x)}{Q(x)}$ with $0\log(0/0)=0$, and $D(P\|Q)=+\infty$ unless the support of $P$ is contained in that of $Q$.
--
--   It is the exponent in the active Stein lemma (Theorem 4) and the objective of the minimax chain in the proof of Theorem 1.
--
--   **Formalization Note** Defined in the joint form $D(P_XW\|P_XV)$, the relative entropy of the two joint laws; this equals the per-row average by the chain rule, with the convention $0\cdot\infty=0$.
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, Theorem 4 and proof of Theorem 1, p.3; D(P‖Q) p.2

import Mathlib
import Definitions.Def_WildeQIT_relEntropy
import Definitions.Def_WiretapFeedback_jointLaw

namespace WiretapFeedback

/-- The **conditional divergence** `D(W‖V|P_X)` of two channels `W, V : X → O` given an input
distribution `P_X`, Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, Theorem 4 and proof of Theorem 1,
p. 3, in bits, as an extended real.

**Formalization Note** It is written in joint form, `D(P_X W ‖ P_X V)`, the relative entropy
(`WildeQIT.relEntropy`, `+∞` off support, base 2) of the two joint input–output laws. By the
chain rule this equals `Σ_x P_X(x) D(W_x‖V_x)` with the convention `0 · ∞ = 0`; the joint form
avoids that `EReal` bookkeeping. -/
noncomputable def condDiv {X O : Type} [Fintype X] [Fintype O] (W V : WildeQIT.Channel X O)
    (p : WildeQIT.FinDist X) : EReal :=
  WildeQIT.relEntropy (jointLaw p W) (jointLaw p V).prob

end WiretapFeedback



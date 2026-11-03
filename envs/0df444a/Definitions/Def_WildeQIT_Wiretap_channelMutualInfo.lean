-- Prove2me | Definitions.Def_WildeQIT_Wiretap_channelMutualInfo
-- name    : WildeQIT_Wiretap_channelMutualInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:27:14.355678+00:00
-- url     : https://prove2.me/theorems/bda271a2-32d4-42fe-b7b1-e7f2482279b0
-- title:
--   Mutual information $I(N)=\max_{p_X} I(X;Y)$ of a classical channel
-- statement:
--   The **mutual information of a classical channel** $N\equiv p_{Y|X}$ (Definition 13.1.1) is
--
--   $$
--   I(N)\equiv\max_{p_X(x)} I(X;Y),
--   $$
--
--   where $(X,Y)$ has the joint distribution $p_X(x)\,p_{Y|X}(y|x)$ and the maximum ranges over all probability distributions $p_X$ on the input alphabet.
--
--   It measures the largest correlation, in bits, that a single use of the channel can establish between its input and output, and it is the single-letter quantity whose additivity (Theorem 13.1.1) makes it the capacity formula of a classical channel.
--
--   **Formalization Note** Alphabets are finite types (the book's setting) and information is measured in bits ($\log_2$). Distributions are the published `WildeQIT.FinDist`, channels the published `WildeQIT.Channel`, and $I(\cdot\,;\cdot)$ is the published `WildeQIT.mutualInfo` of a joint distribution (first component against second). The maximum is written as a supremum; the set of values is bounded above by $\log_2|\mathcal Y|$, so the supremum is a finite real number whenever the input alphabet is nonempty (for an empty input alphabet Lean returns the junk value $0$, and every theorem assumes a nonempty input alphabet). The supremum is attained, but attainment is not part of the definition.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, Definition 13.1.1, eq. (13.5), p. 389

import Definitions.Def_WiretapFeedback_jointLaw
import Definitions.Def_WildeQIT_mutualInfo

namespace WildeQIT.Wiretap

open WildeQIT

/-- **Mutual information of a classical channel** (Definition 13.1.1).
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, Definition 13.1.1, (13.5),
p. 389: `I(N) ≡ max_{p_X(x)} I(X; Y)` for a classical channel `N ≡ p_{Y|X}`.

`channelMutualInfo N` is the supremum, over all input distributions `p` on the input alphabet,
of the mutual information (in bits) of the joint distribution `p_X(x) p_{Y|X}(y|x)`.

**Formalization Note.** The book's `max` is a supremum here (it is attained, since `I(X;Y)` is a
continuous function on the compact probability simplex, but attainment is not part of the
definition). The set of values is bounded above by `log₂ |𝒴|`, so the real supremum is the
book's quantity whenever the input alphabet is nonempty; for an empty input alphabet there is no
input distribution and the value is the junk `0`, so every theorem assumes a nonempty input
alphabet. -/
noncomputable def channelMutualInfo {α β : Type} [Fintype α] [Fintype β] (N : Channel α β) : ℝ :=
  ⨆ p : FinDist α, mutualInfo (WiretapFeedback.jointLaw p N)

end WildeQIT.Wiretap



-- Prove2me | Definitions.Def_NSWBetter_meanVal
-- name    : NSWBetter_meanVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:53:48.258893+00:00
-- url     : https://prove2.me/theorems/a61557b4-25fc-4348-a522-b847a0aa9a1c
-- title:
--   Mean value $\mu=v(G\setminus L)/\Delta$
-- statement:
--   The **mean value** of an instance with $\Delta$ identical agents is $\mu=\dfrac{v(G\setminus L)}{\Delta}$, where $L$ is its set of large goods (Definition 3.4). Note the division by $\Delta$, not by $\Delta-\ell$.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.4, p.11 (Mean Value)

import Mathlib
import Definitions.Def_NSWBetter_tailSum
import Definitions.Def_NSWBetter_largeCount

namespace NSWBetter

/-- **Mean value (Definition 3.4).**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.4, p.11: "we define the mean value of the instance (denoted µ) to be the value v(G\L)/∆, where L is the set of large goods of the instance and ∆ is the number of agents."

`meanVal Δ s = tailSum s ℓ / Δ` (divided by `Δ`, not by `Δ − ℓ`). -/
noncomputable def meanVal (Δ : ℕ) (s : Multiset ℝ) : ℝ := tailSum s (largeCount Δ s) / Δ

end NSWBetter



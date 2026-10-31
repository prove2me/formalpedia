-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_edim
-- name    : FoundationsRL_EluderUCB_edim
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:42.273146+00:00
-- url     : https://prove2.me/theorems/6a1cb9bc-4a02-459a-abe9-85b7fdf37a8f
-- title:
--   Definition 6: the eluder dimension $\mathrm{Edim}(\mathcal F,\varepsilon)$ of a class
-- statement:
--   The eluder dimension of the class $\mathcal F$ at scale $\varepsilon$ is
--
--   $$
--   \mathrm{Edim}(\mathcal F,\varepsilon)=\max_{f^\star\in\mathcal F}\mathrm{Edim}_{f^\star}(\mathcal F,\varepsilon).
--   $$
--
--   This is the complexity measure in the regret bound of Proposition 12.
--
--   **Formalization Note** The maximum is a supremum in $\mathbb N\cup\{\infty\}$, so it exists for every class. It equals $0$ on the empty class, which no theorem of this mission uses.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 6, p. 59

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edimFstar

namespace FoundationsRL.EluderUCB

/-- **The eluder dimension of a class.** Foster & Rakhlin, arXiv:2312.16730v1, Definition 6, p. 59:
`Edim(F, ε) = max_{f⋆ ∈ F} Edim_{f⋆}(F, ε)`.

**Formalization Note.** The maximum is a supremum in `ℕ∞`, so that it exists for every class and
can be `⊤`. On the empty class it is `0`; every theorem of this mission has `F` nonempty. -/
noncomputable def edim {Act : Type*} (F : Set (Act → ℝ)) (ε : ℝ) : ℕ∞ :=
  ⨆ fstar ∈ F, edimFstar F fstar ε

end FoundationsRL.EluderUCB



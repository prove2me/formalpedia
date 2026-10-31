-- Prove2me | Definitions.Def_FoundationsRL_EluderUCB_edimFstar
-- name    : FoundationsRL_EluderUCB_edimFstar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:14.707472+00:00
-- url     : https://prove2.me/theorems/1c8c4bac-227c-4ac6-897a-085a98853adc
-- title:
--   Definition 6: the eluder dimension $\mathrm{Edim}_{f^\star}(\mathcal F,\varepsilon)$ at $f^\star$
-- statement:
--   The eluder dimension of $\mathcal F$ at $f^\star$ and scale $\varepsilon$ is
--
--   $$
--   \mathrm{Edim}_{f^\star}(\mathcal F,\varepsilon)=\sup_{\varepsilon'\ge\varepsilon}\underline{\mathrm{Edim}}_{f^\star}(\mathcal F,\varepsilon')\vee 1.
--   $$
--
--   The supremum over larger scales makes the quantity nonincreasing in $\varepsilon$, which the regret analysis uses, and the maximum with $1$ keeps it at least $1$.
--
--   **Formalization Note** The source writes both layers with the same letters, one underlined. In Lean they are `edimRaw` and `edimFstar`. The value lies in $\mathbb N\cup\{\infty\}$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Definition 6, p. 59

import Mathlib
import Definitions.Def_FoundationsRL_EluderUCB_edimRaw

namespace FoundationsRL.EluderUCB

/-- **The eluder dimension at `f⋆`.** Foster & Rakhlin, arXiv:2312.16730v1, Definition 6, p. 59:
`Edim_{f⋆}(F, ε) = sup_{ε' ≥ ε} Edim̲_{f⋆}(F, ε') ∨ 1`, the monotone version of `edimRaw`, floored
at `1`.

**Formalization Note.** The source uses one symbol, with and without an underline; Lean needs two
names, `edimRaw` for the underlined one and `edimFstar` for this one. The supremum and the
maximum with `1` are taken in `ℕ∞`, so the value can be `⊤`. -/
noncomputable def edimFstar {Act : Type*} (F : Set (Act → ℝ)) (fstar : Act → ℝ) (ε : ℝ) : ℕ∞ :=
  (⨆ (ε' : ℝ) (_ : ε ≤ ε'), edimRaw F fstar ε') ⊔ 1

end FoundationsRL.EluderUCB



-- Prove2me | Definitions.Def_DivideChooseBayes_dividerUtility
-- name    : DivideChooseBayes_dividerUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:29:14.054986+00:00
-- url     : https://prove2.me/theorems/9bcdc668-e6ca-4fe3-ad0e-6ef642709371
-- title:
--   The divider's payoff $u^D$
-- statement:
--   If the chooser picks pile 1, the divider receives $u^D=\sum_i (1-p_i)g^D_i$; if she picks pile 2, he receives $u^D=\sum_i p_i g^D_i$. Here $p_i=q_i/2+1/2$, the divider's values $g^D$ are fixed and $g^C$ is the chooser's realized values; the chooser's pick follows her higher-valued pile with ties broken for the divider.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, payoff paragraph

import Mathlib
import Definitions.Def_DivideChooseBayes_ChoosesPileOne

namespace DivideChooseBayes

/-- **The divider's payoff `uᴰ`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5: "If the chooser picks pile 1, then the divider receives a payoff of
`uᴰ = ∑ᵢ (1 − pᵢ) gᴰᵢ` … if the chooser picks pile 2, then the divider receives a payoff of
`uᴰ = ∑ᵢ pᵢ gᴰᵢ`."

The divider's values `gᴰ` are fixed (p.6, footnote 2); `gᶜ` is the chooser's realized values. -/
noncomputable def dividerUtility {ι : Type*} [Fintype ι] (gD q gC : ι → ℝ) : ℝ :=
  by classical exact if ChoosesPileOne gD q gC then pileTwoValue gD q else pileOneValue gD q

end DivideChooseBayes



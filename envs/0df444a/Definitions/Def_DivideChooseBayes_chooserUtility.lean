-- Prove2me | Definitions.Def_DivideChooseBayes_chooserUtility
-- name    : DivideChooseBayes_chooserUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:29:01.016782+00:00
-- url     : https://prove2.me/theorems/26848cd1-5f83-48cf-9e0b-9b69247d7823
-- title:
--   The chooser's payoff $u^C$
-- statement:
--   If the chooser picks pile 1 she receives $u^C=\sum_i p_i g^C_i$; if she picks pile 2 she receives $u^C=\sum_i (1-p_i)g^C_i$, with $p_i=q_i/2+1/2$ and the pick given by her higher-valued pile, ties broken for the divider.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, payoff paragraph

import Mathlib
import Definitions.Def_DivideChooseBayes_ChoosesPileOne

namespace DivideChooseBayes

/-- **The chooser's payoff `uᶜ`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5: if the chooser picks pile 1 she receives `uᶜ = ∑ᵢ pᵢ gᶜᵢ`, and if she picks pile 2
she receives `uᶜ = ∑ᵢ (1 − pᵢ) gᶜᵢ`. -/
noncomputable def chooserUtility {ι : Type*} [Fintype ι] (gD q gC : ι → ℝ) : ℝ :=
  by classical exact if ChoosesPileOne gD q gC then pileOneValue gC q else pileTwoValue gC q

end DivideChooseBayes



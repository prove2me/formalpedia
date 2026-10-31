-- Prove2me | Definitions.Def_DivideChooseBayes_ChoosesPileOne
-- name    : DivideChooseBayes_ChoosesPileOne
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:28:10.661991+00:00
-- url     : https://prove2.me/theorems/d1ccd7bb-2d15-4d8d-a07b-9d067e50e92f
-- title:
--   The chooser picks pile 1 (ties broken in favour of the divider)
-- statement:
--   The chooser picks her higher-valued pile, and an indifferent chooser breaks her indifference in favour of the divider. Given the divider's values $g^D$, a division $q$ (with $p_i=q_i/2+1/2$) and the chooser's values $g^C$, the chooser picks pile 1 exactly when
--
--   1. $\sum_i p_i g^C_i > \sum_i (1-p_i) g^C_i$, or
--   2. $\sum_i p_i g^C_i = \sum_i (1-p_i) g^C_i$ and the divider strictly prefers pile 2: $\sum_i p_i g^D_i < \sum_i (1-p_i) g^D_i$.
--
--   Equivalently, $\sum_i q_i g^C_i > 0$, or $\sum_i q_i g^C_i = 0$ and $\sum_i q_i g^D_i < 0$.
--
--   **Formalization Note** When both players are indifferent the chooser takes pile 2; the divider's payoff is the same either way.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5, (iii) and the tie-breaking assumption; p.31

import Mathlib
import Definitions.Def_DivideChooseBayes_pileOneValue
import Definitions.Def_DivideChooseBayes_pileTwoValue

namespace DivideChooseBayes

/-- **The chooser picks pile 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5, (iii): "The chooser picks her higher-valued pile"; p.5: "indifference is always broken
in favor of the other player"; p.31: "an indifferent chooser breaks her indifference in favor of
the divider".

With the divider's values `gᴰ`, a division `q` and the chooser's values `gᶜ`, the chooser takes
pile 1 iff she values it strictly more than pile 2, or she is indifferent and the divider strictly
prefers pile 2 (so the divider gets his preferred pile).

**Formalization Note.** When both players are indifferent, the chooser takes pile 2; the
divider's utility is the same either way, so this convention changes no utility. -/
def ChoosesPileOne {ι : Type*} [Fintype ι] (gD q gC : ι → ℝ) : Prop :=
  pileTwoValue gC q < pileOneValue gC q ∨
    (pileOneValue gC q = pileTwoValue gC q ∧ pileOneValue gD q < pileTwoValue gD q)

end DivideChooseBayes



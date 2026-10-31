-- Prove2me | Definitions.Def_DivideChooseBayes_pileOneProb
-- name    : DivideChooseBayes_pileOneProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:29:10.824084+00:00
-- url     : https://prove2.me/theorems/40de2772-3c7c-4e0c-9d33-db093b4b4e77
-- title:
--   The probability $P$ that the chooser picks pile 1
-- statement:
--   Let $\mu$ be the prior: the distribution of the chooser's values $g^C\in\mathbb R^n$ conditioned on the divider's (fixed) values $g^D$. For a division $q$,
--
--   $$P := \Pr_{g^C\sim\mu}\big[\text{the chooser picks pile 1}\big].$$
--
--   **Formalization Note** The pick includes the tie rule (an indifferent chooser favours the divider); $P$ is the measure of that event as a real number.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.5 ("we refer to the probability that the chooser picks pile 1 as P"); p.6, footnote 2

import Mathlib
import Definitions.Def_DivideChooseBayes_ChoosesPileOne

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **The probability `P` that the chooser picks pile 1.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.5: "Given a division p, we refer to the probability that the chooser picks pile 1 as P."

`μ` is the prior: the law of the chooser's values `gᶜ ∈ ℝⁿ` conditioned on the divider's (fixed)
values `gᴰ` (p.6, footnote 2).

**Formalization Note.** `μ.real` is the measure as a real number; the event is closed under the
tie rule of `ChoosesPileOne` and is measurable. -/
noncomputable def pileOneProb {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) (gD q : ι → ℝ) : ℝ :=
  μ.real {gC | ChoosesPileOne gD q gC}

end DivideChooseBayes



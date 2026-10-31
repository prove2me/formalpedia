-- Prove2me | Definitions.Def_DivideChooseBayes_interimUtility
-- name    : DivideChooseBayes_interimUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:29:52.318657+00:00
-- url     : https://prove2.me/theorems/f1e9da5c-17ca-4835-9305-a313c0577ea9
-- title:
--   The divider's interim expected utility $\mathbb E_{g^C\sim\mu}[u^D]$
-- statement:
--   For a prior $\mu$ on the chooser's values and the divider's fixed values $g^D$, the divider's **interim expected utility** of a division $q$ is
--
--   $$U(q) := \mathbb E_{g^C\sim\mu}\big[u^D(q,g^C)\big].$$
--
--   **Formalization Note** A Bochner integral. $u^D$ takes two values and is measurable in $g^C$, so it is integrable for every probability measure and the integral is never a default value.
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, p.6, Lemma 3.1 (ii) and Lemma 3.2

import Mathlib
import Definitions.Def_DivideChooseBayes_dividerUtility

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **The divider's interim expected utility `E_{gᶜ∼Ḡᶜ}[uᴰ]`.**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, p.6, Lemma 3.1 (ii) and Lemma 3.2 ("interim expected utility").

The expectation of `uᴰ` over the chooser's values `gᶜ ∼ μ`, at the divider's fixed values `gᴰ`.

**Formalization Note.** A Bochner integral; `uᴰ` takes two values and is measurable, so for a
probability measure it is integrable (no junk value). -/
noncomputable def interimUtility {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ)) (gD q : ι → ℝ) : ℝ :=
  ∫ gC, dividerUtility gD q gC ∂μ

end DivideChooseBayes



-- Prove2me | Definitions.Def_LearnManip_InClass
-- name    : LearnManip_InClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:51.668128+00:00
-- url     : https://prove2.me/theorems/fdf103dc-f986-4f92-b4ee-92a2e731b890
-- title:
--   Growth class of solutions of the BDP equation
-- statement:
--   The class of measurable functions $w(\mu,s,c)$ with
--   $$\Bigl|w(\mu,s,c)-\frac{\mu}{1-\alpha}\Bigr|\le A(1+s)$$
--   for some constant $A$ and all $\mu$, $s,c\ge0$.
--
--   Lemma 1 as printed asserts uniqueness without a class, which is false: no bounded solution exists, and at $\alpha=1/2$, $\eta=2$ adding the function $c$ to a solution gives a second one. This weighted class is the setting in which uniqueness holds.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 1, p.12, proof, pp.ec6–ec7 (PDF 45–46), corrected

import Mathlib
import Definitions.Def_LearnManip_Params

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The growth class of solutions of the BDP equation: measurable, with
`|w(μ, s, c) − μ/(1−α)| ≤ A (1 + s)`.

**Formalization Note.** Lemma 1, p.12, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04) is stated
without a class, and is false as printed: no bounded solution exists, and at `α = 1/2`, `η = 2` the
function `v + c` is a second solution. This class is the corrected setting. -/
def InClass (P : Params) (w : ℝ → ℝ≥0 → ℝ≥0 → ℝ) : Prop :=
  Measurable (fun x : ℝ × ℝ≥0 × ℝ≥0 => w x.1 x.2.1 x.2.2) ∧
    ∃ A : ℝ, ∀ (μ : ℝ) (s c : ℝ≥0), |w μ s c - μ / (1 - (P.α : ℝ))| ≤ A * (1 + (s : ℝ))

end LearnManip



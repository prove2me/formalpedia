-- Prove2me | Definitions.Def_LearnManip_GClass
-- name    : LearnManip_GClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:54:43.124112+00:00
-- url     : https://prove2.me/theorems/e90c5355-12b1-4dc9-a9de-26443a0d05b5
-- title:
--   Growth class of manipulation values
-- statement:
--   The class of measurable functions $g(s,c)$ with $|g(s,c)|\le A(1+s)$ for some constant $A$ and all $s,c\ge0$.
--
--   This class replaces the bounded functions of the printed proof of Lemma 1, which contain no solution of the dynamic program.
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 1, p.12, proof, pp.ec6–ec7 (PDF 45–46), corrected

import Mathlib

open scoped NNReal ENNReal
open MeasureTheory ProbabilityTheory

namespace LearnManip

/-- The growth class of manipulation values: measurable, with `|g(s, c)| ≤ A (1 + s)`.

**Formalization Note.** Lemma 1, p.12, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04) proves its
uniqueness on the bounded Borel functions (p.ec6), which contain no solution. This weighted class is
the corrected setting. -/
def GClass (g : ℝ≥0 → ℝ≥0 → ℝ) : Prop :=
  Measurable (fun x : ℝ≥0 × ℝ≥0 => g x.1 x.2) ∧
    ∃ A : ℝ, ∀ s c : ℝ≥0, |g s c| ≤ A * (1 + (s : ℝ))

end LearnManip



-- Prove2me | Definitions.Def_EffRobustLearn_MajClass
-- name    : EffRobustLearn_MajClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:32:30.955235+00:00
-- url     : https://prove2.me/theorems/4b07c5a3-d38c-4b2a-88ae-ba4e22c6900d
-- title:
--   The class $\mathrm{Maj}_k(C)$ of $k$-wise majorities (2.3)
-- statement:
--   For a concept class $C$ and $k\ge1$,
--   $$\mathrm{Maj}_k(C)=\Big\{x\mapsto\mathrm{sign}\Big(\frac1k\sum_{i=1}^k c_i(x)\Big):c_1,\dots,c_k\in C\Big\}.$$
--
--   The output of Algorithm 1 lies in the convex hull of this class, which is what Lemma C.5 controls.
--
--   **Formalization Note** The class is Boolean-valued, with value true exactly when the average is $\ge0$, the reading $\mathrm{sign}(0)=+1$.
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), eq. (2.3), p.11 (PDF p.12)

import Mathlib
import Definitions.Def_EffRobustLearn_toPM

namespace EffRobustLearn

/-- The class of `k`-wise majorities of concepts in `C`, (2.3), Klivans, Stavropoulos, Tikhonov, Vasilyan, *Efficient Robust Learning at the Information-Theoretic Limit*, arXiv:2609.17655 (held version, sha256 312a0857…), p.11:
`Maj_k(C) = { x ↦ sign((1/k) ∑_i c_i(x)) : c_1, …, c_k ∈ C }`.

**Formalization Note.** The class is Boolean-valued so that its VC dimension (Fact C.3 item 5) is the published
`UnderstandingML.vcDim`. `h x = true` exactly when the average is `≥ 0`, which is the reading `sign 0 = +1`, so
`toPM h x = signPM ((1/k) ∑_i toPM (c_i) x)`. -/
def MajClass {X : Type*} (k : ℕ) (C : Set (X → Bool)) : Set (X → Bool) :=
  {h | ∃ cs : Fin k → X → Bool, (∀ i, cs i ∈ C) ∧
    ∀ x, h x = decide (0 ≤ (1 / (k : ℝ)) * ∑ i, pm (cs i x))}

end EffRobustLearn



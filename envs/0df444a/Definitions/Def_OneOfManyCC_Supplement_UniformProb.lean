-- Prove2me | Definitions.Def_OneOfManyCC_Supplement_UniformProb
-- name    : OneOfManyCC_Supplement_UniformProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:21:10.090954+00:00
-- url     : https://prove2.me/theorems/714fe0fe-22c1-4bdf-996c-ed331d976fbf
-- title:
--   Probability over a uniformly random Boolean function $g:\{0,1\}^n\to\{0,1\}$
-- statement:
--   For an event $P$ on Boolean functions $g:\{0,1\}^n\to\{0,1\}$, its probability under a uniformly random $g$ is
--   $$\Pr_g[P]=\frac{|\{g: P(g)\}|}{2^{2^n}},$$
--   the fraction of all $2^{2^n}$ functions that satisfy $P$.
--
--   This is the sample space of Theorems 1.6 and 6.6 ("a uniformly random $g$").
--
--   **Formalization Note** The numerator is a `Finset.card` over the finite type of all functions `(Fin n → Bool) → Bool`; the denominator is that type's cardinality.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.6, p.3 (PDF p.4); Theorem 6.6, p.18 (PDF p.19)

import Mathlib

namespace OneOfManyCC.Supplement

open Classical in
/-- **Probability over a uniformly random Boolean function** `g : {0,1}ⁿ → {0,1}`.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorems 1.6, 6.6, p.3, p.18: "a uniformly random g: {0, 1}n → {0, 1}".

`probUniform n P` is the fraction of the `2^(2ⁿ)` functions `g` that satisfy `P`.

**Formalization Note.** The count is a `Finset.card` over the finite type of all functions; the
denominator is that type's cardinality, which is positive. -/
noncomputable def probUniform (n : ℕ) (P : ((Fin n → Bool) → Bool) → Prop) : ℝ :=
  ((Finset.univ.filter P).card : ℝ) / (Fintype.card ((Fin n → Bool) → Bool) : ℝ)

end OneOfManyCC.Supplement



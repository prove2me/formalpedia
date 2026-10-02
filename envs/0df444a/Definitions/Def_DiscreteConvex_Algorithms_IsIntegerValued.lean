-- Prove2me | Definitions.Def_DiscreteConvex_Algorithms_IsIntegerValued
-- name    : DiscreteConvex_Algorithms_IsIntegerValued
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-28T03:23:33.428192+00:00
-- url     : https://prove2.me/theorems/7fb7a54a-d66e-4a33-bed2-74da6261c181
-- title:
--   Integer-valuedness of a $\mathbb R\cup\{+\infty\}$-valued set function
-- statement:
--   A $\mathbb R \cup \{+\infty\}$-valued set function is **integer valued** if every finite value it takes is an integer.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.288

import Mathlib

namespace DiscreteConvex.Algorithms

/-- A `ℝ ∪ {+∞}`-valued set function is **integer valued** if every finite value it takes is an
integer. -/
def IsIntegerValued {V : Type*} (g : Finset V → WithTop ℝ) : Prop :=
  ∀ X : Finset V, ∀ r : ℝ, g X = (r : WithTop ℝ) → ∃ n : ℤ, (n : ℝ) = r

end DiscreteConvex.Algorithms



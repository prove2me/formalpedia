-- Prove2me | Definitions.Def_NatureSLT_Bounds_growthFunction
-- name    : NatureSLT_Bounds_growthFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:34.430576+00:00
-- url     : https://prove2.me/theorems/196b3a89-8820-4a1d-8b3f-50983b3c5e75
-- title:
--   Growth function $G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell)$
-- statement:
--   Let $Q(z, \alpha)$, $\alpha \in \Lambda$, be a set of indicator functions on a set $Z$, and $N^\Lambda(z_1, \dots, z_\ell)$ the number of different separations of a sample $z_1, \dots, z_\ell$ by the set. The **growth function** of the set is
--   $$G^\Lambda(\ell) = \ln \sup_{z_1, \dots, z_\ell} N^\Lambda(z_1, \dots, z_\ell),$$
--   the supremum taken over all samples of size $\ell$ from $Z$, and $\ln$ the natural logarithm.
--
--   Unlike the annealed entropy, the growth function does not depend on any probability measure; it bounds the annealed entropy from above for every distribution and yields the distribution-free bounds (3.3), (3.4), (3.10)–(3.12) and (3.14) of the book.
--
--   **Formalization Note** The supremum is the real supremum `⨆ z, (N^Λ(z) : ℝ)` over all functions $z : \{0, \dots, \ell-1\} \to Z$. For a $\{0, 1\}$-valued $Q$ (the only case in which the theorems of this mission apply it) the values are bounded by $2^\ell$, so the supremum is genuine.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 55, Section 2.7 (ii)

import Mathlib
import Definitions.Def_NatureSLT_Bounds_numSeparations

namespace NatureSLT.Bounds

/-- Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., p. 55, §2.7 (ii): the growth
function `G^Λ(ℓ) = ln sup_{z₁, …, z_ℓ} N^Λ(z₁, …, z_ℓ)`, the supremum over all samples of
size `ℓ`. For a `{0, 1}`-valued `Q` the values `N^Λ` are bounded by `2^ℓ`, so the supremum is
genuine. -/
noncomputable def growthFunction {Λ Z : Type*} (Q : Λ → Z → ℝ) (ℓ : ℕ) : ℝ :=
  Real.log (⨆ z : Fin ℓ → Z, (numSeparations Q z : ℝ))

end NatureSLT.Bounds



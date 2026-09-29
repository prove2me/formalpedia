-- Prove2me | Definitions.Def_Mathlib_RingTheory_Ideal_Quotient_Basic
-- name    : Mathlib_RingTheory_Ideal_Quotient_Basic
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/3c5be94c-4a9f-5a65-a065-b31de7cab786
-- title:
--   Quotient representatives differ from the original by an ideal element
-- statement:
--   The module records a single lemma about representatives of cosets in a quotient ring. The standing context is a ring $R$ (not assumed commutative) together with an ideal $I$ of $R$ that is two-sided, so that the quotient $R/I$ carries a ring structure. For the quotient ring $R \,/\, I$, Lean's choice function `Quotient.out` selects, for each class, some element of $R$ representing it. The lemma [`Ideal.Quotient.out_sub`](../def/Mathlib_RingTheory_Ideal_Quotient_Basic.html#L7) states that for every $x : R$, the chosen representative of the class of $x$, that is `(Ideal.Quotient.mk I x).out`, satisfies
--   $$(\text{mk}_I\,x).\mathrm{out} - x \in I.$$
--   In other words, the canonical representative of a coset and any given element of that coset differ by an element of $I$, which is exactly the statement that the two have the same image under the projection $R \to R/I$. The proof is the combination of the criterion that $a - b \in I$ iff $a$ and $b$ have equal images in $R/I$ with the fact that `out` is a section of the projection (`Ideal.Quotient.mk_out`). The lemma is the convenient form in which to pass between an element of $R$ and the representative produced by the choice function when computing in the quotient.
--
--   **Relation to Mathlib.** The declaration lives in Mathlib's `Ideal.Quotient` namespace and is a small addition to the Mathlib API for quotient rings, alongside `Ideal.Quotient.mk_out` and the criterion `Ideal.Quotient.eq`, from which it follows.
--
--   **Where it is used.** It is a general-purpose utility used at several places in the tree where one has to replace an element of a quotient ring by a chosen lift in $R$ and control the resulting error modulo the ideal.
--
--   *Attribution:* this file contains material adapted from third-party Apache-2.0 sources (whole file (100%): `FLT/Mathlib/RingTheory/Ideal/Quotient/Basic.lean` — © 2025 Salvatore Mercuri; authors: Salvatore Mercuri, Kevin Buzzard). See ATTRIBUTION.md and NOTICE in the source repository.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Mathlib_RingTheory_Ideal_Quotient_Basic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]

end



-- Prove2me | Definitions.Def_Diaz_Instantiation
-- name    : Diaz_Instantiation
-- status  : Definition
-- author  : @carlok
-- created : 2026-09-07T08:20:56.308985+00:00
-- url     : https://prove2.me/theorems/9aadbc99-cffa-47ee-9410-69fa01e3bca2
-- title:
--   $\bar{\mathbb{Q}}$, the algebraic numbers as a subfield of $\mathbb{C}$
-- statement:
--   Define
--
--   $$\bar{\mathbb{Q}} = \{\, z \in \mathbb{C} : z \text{ is algebraic over } \mathbb{Q} \,\},$$
--
--   as a subfield of $\mathbb{C}$ — concretely, the algebraic closure of $\mathbb{Q}$ inside $\mathbb{C}$ (`algebraicClosure ℚ ℂ`), coerced from an intermediate field to a `Subfield ℂ`.
--
--   Alongside it the file records the typeclass instance $\bar{\mathbb{Q}}$ *is algebraic over* $\mathbb{Q}$. That fact is already in Mathlib as `algebraicClosure.isAlgebraic`, but it does not fire through the `IntermediateField → Subfield` coercion on its own, so without this named instance every statement of the development quantified over a base field $L$ with `Algebra.IsAlgebraic ℚ L` would apply to nothing. The instance is named rather than anonymous so that it is visible in generated artefacts.
--
--   $\bar{\mathbb{Q}}$ is the base field Diaz's conjecture is actually about: the general results of the development are stated for an arbitrary conjugation-stable subfield $K \subseteq \mathbb{C}$, and this is the instantiation intended throughout.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Instantiation.lean#L25-L33

/-
# The intended base, worked out

Everything else is stated for an arbitrary conjugation-stable subfield
`K ⊆ ℂ`, which is all the arguments use. The base actually meant is the
algebraic numbers, and an adversarial audit observed that the repository
never exhibited it: the instance `Algebra.IsAlgebraic ℚ ↥L` failed to
synthesize for every candidate base, so `candidate_no_vanishing_coeff`,
though sound, applied to nothing.

This file supplies the base and the missing instance, and applies the
end-to-end theorem to it. The instance does exist in Mathlib
(`algebraicClosure.isAlgebraic`); what was missing is that it does not
fire through the `IntermediateField → Subfield` coercion on its own.
-/
import Mathlib

open ComplexConjugate

namespace Diaz

/-- The algebraic numbers, as a subfield of `ℂ`. -/
noncomputable def Qbar : Subfield ℂ := (algebraicClosure ℚ ℂ).toSubfield

/-- The instance that does not fire on its own.  Named rather than
anonymous so that it appears in the generated artefacts: an anonymous
instance has no identifier for the generator to match, and would be
invisible to the very document meant to expose the assumed surface. -/
noncomputable instance QbarIsAlgebraic : Algebra.IsAlgebraic ℚ (↥Qbar) :=
  algebraicClosure.isAlgebraic ℚ ℂ

/-! ## The closure theorem, end to end -/

end Diaz



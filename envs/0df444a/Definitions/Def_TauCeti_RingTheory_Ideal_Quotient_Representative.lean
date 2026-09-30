-- Prove2me | Definitions.Def_TauCeti_RingTheory_Ideal_Quotient_Representative
-- name    : TauCeti_RingTheory_Ideal_Quotient_Representative
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:39:49.006239+00:00
-- url     : https://prove2.me/theorems/c66f641e-d6f8-48cc-9cf0-46ac37eeb0e8
-- title:
--   Nonzero representatives of residue classes
-- statement:
--   Every residue class modulo a nonzero ideal has a nonzero representative. This allows residue calculations to retain representatives in the multiplicative group of the fraction field.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/Quotient/Representative.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/RingTheory/Ideal/Quotient/Representative.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.RingTheory.Ideal.Quotient.Defs

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Nonzero representatives of residue classes

`Ideal.Quotient.mk_surjective` produces *some* representative of a class in `R ⧸ I`, with no
control over it.  Modulo a nonzero two-sided ideal the representative can be chosen nonzero: a
representative that happens to vanish is corrected by a nonzero element of the ideal, which does
not change its class.  This is what a residue class needs before its representative can be
inverted in an appropriate fraction field.

## Main results

* `Ideal.Quotient.exists_ne_zero_mk_eq`: every residue class modulo a nonzero ideal is the class of
  a nonzero element.
-/

 section

namespace Ideal.Quotient

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-- **A nonzero ideal has a nonzero representative for every residue class.**  A representative
that happens to vanish can be corrected by a nonzero element of the ideal. -/
theorem exists_ne_zero_mk_eq (hI : I ≠ ⊥) (y : R ⧸ I) : ∃ a ≠ (0 : R), mk I a = y := by
  obtain ⟨a, rfl⟩ := mk_surjective y
  obtain ⟨m, hm, hm0⟩ := (Submodule.ne_bot_iff I).mp hI
  rcases eq_or_ne a 0 with rfl | ha
  · exact ⟨m, hm0, by rw [eq_zero_iff_mem.mpr hm, map_zero]⟩
  · exact ⟨a, ha, rfl⟩

end Ideal.Quotient

end

end



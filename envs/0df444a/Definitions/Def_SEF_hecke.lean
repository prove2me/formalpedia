-- Prove2me | Definitions.Def_SEF_hecke
-- name    : SEF_hecke
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-22T18:42:21.395469+00:00
-- url     : https://prove2.me/theorems/4ba5267e-3650-438c-966a-abc3057dba26
-- title:
--   The Hecke-family layer: characters of the Eisenstein integers and their normalized lattice L-functions
-- statement:
--   The second definition bundle of the mission: the Hecke-family layer transcribed verbatim from the source file. The definition carries: the cyclotomic field of the third roots of unity and its ring of integers, the Eisenstein integers, with the cyclotomic generator omega (the single disclosed adaptation: the source writes a toInteger projection on the Mathlib cyclotomic root specification, which does not exist; omega is defined as the Mathlib cyclotomic generator embedded into the ring of integers through its integrality witness, the polynomial X^3 - 1); the coordinate element x + y omega of the integer grid; the character structure: a modulus ideal (required to be nonzero), a residue multiplicative character on the quotient ring that is trivial on the units, and a positive period contained in the modulus; the coefficient functions elementCoeff and coefficients evaluating the character on the coordinate grid of the period; and the L-functions: the continued lattice L-function through the theta layer of the first bundle, normalized to the L-function LFunction chi s, the completed lattice L-function divided by 6.
-- source:
--   HeckeSevenEighths.lean.txt, user-supplied Lean 4 statement file (namespace OAI.SevenEighths.HeckeFamily), the Hecke-family layer transcribed verbatim with the disclosed omega adaptation.

import Mathlib
import Definitions.Def_SEF_theta

/-!
# SEF_hecke: characters of the Eisenstein integers and their lattice L-functions

The second of the two definition bundles of the mission on the $7/8$ zero-free
line. This module transcribes, verbatim, the Hecke-family layer of the
user-supplied Lean 4 statement file `HeckeSevenEighths.lean.txt` (namespace
`OAI.SevenEighths.HeckeFamily`): the cyclotomic field `K` $= \mathbb{Q}(\zeta_3)$
and its ring of integers `O` (the Eisenstein integers), the character
structure `Character` carrying a modulus ideal, a residue multiplicative
character on the quotient that is trivial on units, and a positive period
contained in the modulus, the coefficient functions `elementCoeff` and
`coefficients` on the period grid built from `coordinateElement`
($x + y\omega$), and the lattice L-function `continuedLattice` (through
`HeckeTheta.latticeL` of `Def_SEF_theta`) normalized to `LFunction`
($\Lambda(s)/6$).

Source: user-supplied Lean 4 statement file `HeckeSevenEighths.lean.txt`,
transcribed verbatim with the single disclosed adaptation of `omega`: the
source writes `(IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger`, and no
`toInteger` projection exists on the Mathlib lemma `zeta_spec` (which is a
proof of `IsPrimitiveRoot (zeta n A B) n`); `omega` is here the Mathlib
cyclotomic generator `IsCyclotomicExtension.zeta 3 ℚ K`, embedded into `O`
through its integrality witness ($X^3 - 1$). See the proposal description,
disclosure 4.
-/

namespace OAI

noncomputable section
open Polynomial

namespace SevenEighths.HeckeFamily

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

instance : IsCyclotomicExtension {3} ℚ K := CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  ⟨IsCyclotomicExtension.zeta 3 ℚ K,
    ⟨X ^ 3 - 1, monic_X_pow_sub_C 1 (by norm_num : (3 : ℕ) ≠ 0),
      by simp [IsCyclotomicExtension.zeta_pow]⟩⟩

def coordinateElement (x y : ℤ) : O := (x : O) + (y : O) * omega

structure Character where
  modulus : Ideal O
  modulus_ne_bot : modulus ≠ ⊥
  residue : MulChar (O ⧸ modulus) ℂ
  unit_trivial : ∀ u : Oˣ, residue (Ideal.Quotient.mk modulus (u : O)) = 1
  period : ℕ
  period_pos : 0 < period
  period_mem : (period : O) ∈ modulus

instance (χ : Character) : NeZero χ.period := ⟨Nat.ne_of_gt χ.period_pos⟩

def elementCoeff (χ : Character) (z : O) : ℂ := χ.residue (Ideal.Quotient.mk χ.modulus z)

def coefficients (χ : Character) (a : Fin χ.period × Fin χ.period) : ℂ :=
  elementCoeff χ (coordinateElement a.1 a.2)

def continuedLattice (χ : Character) : ℂ → ℂ := HeckeTheta.latticeL (coefficients χ)

def LFunction (χ : Character) (s : ℂ) : ℂ := continuedLattice χ s / 6

end SevenEighths.HeckeFamily

end

end OAI



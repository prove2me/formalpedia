-- Prove2me | Definitions.Def_TauCeti_GroupTheory_FiniteAbelian_CharacterOrthogonality
-- name    : TauCeti_GroupTheory_FiniteAbelian_CharacterOrthogonality
-- status  : Definition
-- author  : @riccardo.brasca
-- created : 2026-09-29T19:36:33.06005+00:00
-- url     : https://prove2.me/theorems/98a9b84d-48fb-4647-9250-07e2468f99b5
-- title:
--   Character orthogonality for finite commutative groups
-- statement:
--   For a finite left-cancellative monoid $G$ and an integral domain $R$, the multiplicative characters $G\to R^\times$ form a finite set. This supplies finite sums over characters for orthogonality arguments.
--
--   **Formalization Note.** These foundational declarations are transplanted from the Tau Ceti contributors' [original source](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/FiniteAbelian/CharacterOrthogonality.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`), with compatibility adaptations for Lean 4.33.1. Mathematical proofs requiring separate theorem nodes are published separately.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/GroupTheory/FiniteAbelian/CharacterOrthogonality.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Character orthogonality for finite commutative groups

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — in both its punctured and its normal form,
and shows that the commutativity it assumes is necessary: the column relation fails for every
finite non-commutative group whenever the number of characters is nonzero in `M`, as it is in
characteristic zero. The underlying group-theoretic fact, that homomorphisms into a
commutative monoid separate elements only in a commutative group, is
`TauCeti.isMulCommutative_of_forall_exists_monoidHom_apply_ne_one` in
`TauCeti.GroupTheory.Commutator`.

## Main results

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.sum_monoidHom_apply_eq_ite`: the same sum in normal form, `Nat.card G` at `g = 1`
  and `0` elsewhere. This is the shape an indicator-formula consumer wants, and it is the `simp`
  normal form for such a sum.
* `CommGroup.sum_monoidHom_apply_eq_ite`'s tagged form,
  `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite`: summing `(χ σ)⁻¹ * χ g` isolates the single
  element `σ`, giving `Nat.card G` when `g = σ` and `0` otherwise.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field
  sums to `-1` over the nonzero elements, even after multiplication by a unit.
* `TauCeti.sum_monoidHom_apply_eq_card_of_mem_commutator`: at an element of the commutator
  subgroup the character sum is the number of characters, every summand being `1`.
* `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`: **column orthogonality fails for every
  finite non-commutative group** whenever the number of characters is nonzero in `M`, as in
  characteristic zero: at the tag `1` and a nontrivial commutator the tagged sum is the number
  of characters, not `0`.

The file also registers `Fintype (G →* Mˣ)`, which Mathlib leaves at `Finite`; without it a
consumer's own character sum does not elaborate, and two ad-hoc `Fintype.ofFinite` introductions
give syntactically distinct sums. That instance needs only `LeftCancelMonoid G`, so it also serves
consumers indexing over the characters of a finite noncommutative group or monoid.

## Row orthogonality and punctured additive-character sums

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the analogous statement in the `MulChar`
vocabulary, for a multiplicative character of a finite commutative monoid valued in a domain.)

The theorem `AddChar.sum_units_mul_eq_neg_one` below is not a restatement of that full row
relation: it removes the zero term from a finite-field additive-character sum and reindexes the
remaining nonzero elements by `Fˣ`. This punctured form is what character computations over a
finite field consume directly.

The column relation genuinely is not in Mathlib in this generality. It appears there only in
specialisations: the `ZMod n` one, `DirichletCharacter.sum_characters_eq_zero` in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`, and the finite-additive-group one
over `ℂ`, `AddChar.sum_apply_eq_ite` in
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` (with
`AddChar.sum_apply_eq_zero_iff_ne_zero` beside it). Neither implies the statement below, which is
multiplicative and valued in an arbitrary domain with enough roots of unity rather than in `ℂ`
or over `ZMod n`.

## References

Two of the results are adapted from
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca).

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one` comes from `sum_char_apply_eq_zero_of_ne_one`
  in `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`, at commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`.
* `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` comes from the private
  `sum_galoisCharacter_mul_inv_eq` in `CebotarevDensity/Cyclotomic.lean`, at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7`, where the argument is attributed to Sharifi,
  *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The source writes the sum as
  `∑ χ, χ σ * (χ τ)⁻¹` with the inverse on the second argument and concludes `σ * τ⁻¹ = 1`; the
  statement here carries the inverse on the tag and concludes `g = σ`, which is the same identity
  read in the other orientation.
-/

 section

open scoped commutatorElement

namespace AddChar

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R] [IsDomain R]



end AddChar

variable {G : Type*} [Finite G] {M : Type*} [CommRing M] [IsDomain M]

/-- The characters of a finite left-cancellative monoid valued in a domain form a `Fintype`.
Mathlib registers only `Finite (G →* Mˣ)`, so a character sum written by a consumer has no
`Finset` to range over without this; it mirrors `AddChar.instFintype`. Neither commutativity nor
invertibility is needed: `Finite (G →* Mˣ)` already holds at `LeftCancelMonoid`, which is where
this is stated. -/
noncomputable instance instFintypeMonoidHomUnits [LeftCancelMonoid G] : Fintype (G →* Mˣ) :=
  Fintype.ofFinite _

namespace CommGroup

variable [CommGroup G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]







end CommGroup

namespace TauCeti

variable [Group G]





end TauCeti

end
end



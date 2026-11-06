-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Basic_f6b0b12617
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Basic_f6b0b12617
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T17:39:34.345363+00:00
-- url     : https://prove2.me/theorems/8959f408-d51e-42f5-b277-bfafa904e434
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / ReeG2 / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.ReeG2.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/ReeG2/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_G2_ShortRoot_PrimeField_SpecialIsogeny_1f3afd3c91
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeG2_Carrier_362eab4909
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_HalfFrobenius_6c06eef7da
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_OddPowerSteinberg_57a2f0b731
public import Definitions.Def_TC433_GroupTheory_FixedPointCandidate_c28335b059

/-!
# The Ree G2 Steinberg map and candidate group

The signed-minor construction gives the exceptional endomorphism of the characteristic-three
short-root carrier. Its odd power is the Steinberg map for a validated Ree G2 index. The candidate
is the derived subgroup of its fixed points modulo the centre of that derived subgroup.

The ambient group consists of algebraic-closure points of the explicit prime-field short-root
carrier. A comparison with the pinned simply connected G2 group scheme requires an isomorphism
preserving the root subgroups and exceptional endomorphism. No finiteness or simplicity is assumed
or proved here. The conventions follow Carter, *Simple Groups of Lie Type*, §12.4.
-/

/- Adapted from the family interface in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Suzuki/Basic.lean`. -/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.ReeG2LieIndex

noncomputable section

variable (d : ReeG2LieIndex)

/-- The exceptional endomorphism of the Ree G2 ambient carrier. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  G2ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius is the characteristic-three carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = G2ShortRoot.PrimeField.specialIsogeny d.1.Closure := by rfl

/-- The half-Frobenius squares to the prime-field Frobenius. -/
@[simp] theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius_def, primeFrobenius_def,
    G2ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    finCongr d.rank_eq_two (d.toSuzukiReeIndex.lengthPerm i) =
      Equiv.swap 0 1 (finCongr d.rank_eq_two i) := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  have hswap : lengthPermRankTwo = Equiv.swap 0 1 := by
    ext j
    rw [lengthPermRankTwo_apply]
    fin_cases j <;> decide
  simp [toSuzukiReeIndex, SuzukiReeIndex.lengthPerm_reeG2, Equiv.permCongr_def, hswap]

private theorem carrierExponent (i : Fin d.1.rank) :
    G2ShortRoot.PrimeField.specialIsogenyExponent (.inl (finCongr d.rank_eq_two i)) =
      d.toSuzukiReeIndex.exponent i := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  fin_cases i
  · have h := SuzukiReeIndex.exponent_of_not_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex
      ⟨0, by simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]⟩ (by
        rw [DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_reeG2 m),
          DynkinType.isLongSimpleRoot_G2]
        exact Nat.zero_ne_one)
    rw [(of m hvalid).characteristic_eq_three] at h
    simpa using h.symm
  · have h := SuzukiReeIndex.exponent_of_isLongSimpleRoot
      (of m hvalid).toSuzukiReeIndex
      ⟨1, by simp [ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]⟩ (by
        rw [DynkinType.isLongSimpleRoot_congr (LieTypeIndex.dynkinType_reeG2 m),
          DynkinType.isLongSimpleRoot_G2]
        exact finCongr_apply_coe _ _)
    simpa [Fin.ext_iff] using h.symm

/-- The half-Frobenius has the index's own root permutation and long/short exponents. -/
@[simp] theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  obtain ⟨t, rfl⟩ := Multiplicative.ofAdd.surjective u
  rw [halfFrobenius_def, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    G2ShortRoot.PrimeField.specialIsogenyRootIndex_inl,
    carrierNode_lengthPerm, ← carrierExponent]
  simp only [toAdd_ofAdd]

/-- The Steinberg endomorphism is the recorded odd power of the exceptional endomorphism. -/
def steinberg : d.AmbientGroup →* d.AmbientGroup :=
  HPow.hPow (α := Monoid.End d.AmbientGroup) d.halfFrobenius d.1.fieldExponent

/-- The Steinberg map is the recorded power in the monoid of endomorphisms. -/
theorem steinberg_def :
    d.steinberg = HPow.hPow (α := Monoid.End d.AmbientGroup)
      d.halfFrobenius d.1.fieldExponent := by rfl

/-- The square of the Steinberg endomorphism is the field-order Frobenius. -/
@[simp] theorem steinberg_steinberg (g : d.AmbientGroup) :
    d.steinberg (d.steinberg g) = d.frobenius g := by
  rw [d.frobenius_eq_primeFrobenius_pow]
  exact d.toSuzukiReeIndex.pow_fieldExponent_pow_fieldExponent d.halfFrobenius_halfFrobenius g

/-- The odd iterate exchanges the numbered roots with the prescribed parameter power. -/
@[simp] theorem steinberg_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.steinberg (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^
          (d.1.characteristic ^ d.toSuzukiReeIndex.halfExponent *
            d.toSuzukiReeIndex.exponent i))) :=
  d.toSuzukiReeIndex.pow_fieldExponent_apply_lengthPerm
    (x := fun j t => d.simpleRootSubgroup j t)
    (fun j t => d.halfFrobenius_simpleRootSubgroup j t)
    (fun j t => (d.halfFrobenius_halfFrobenius (d.simpleRootSubgroup j t)).trans
      ((d.primeFrobenius_simpleRootSubgroup j t).trans (by simp)))
    i u

/-- The fixed subgroup of the Ree G2 Steinberg endomorphism. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Ree G2 candidate: the derived subgroup of the Steinberg fixed points modulo its own
centre. This definition carries no assertion of finiteness, perfectness, or simplicity. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeG2LieIndex



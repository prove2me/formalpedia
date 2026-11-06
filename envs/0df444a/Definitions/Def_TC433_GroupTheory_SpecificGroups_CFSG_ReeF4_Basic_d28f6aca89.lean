-- Prove2me | Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Basic_d28f6aca89
-- name    : TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Basic_d28f6aca89
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:44:21.224205+00:00
-- url     : https://prove2.me/theorems/55331c42-3e6e-4f39-864b-f16fa0158d9d
-- title:
--   TauCeti: GroupTheory / SpecificGroups / CFSG / ReeF4 / Basic
-- statement:
--   Compatibility port of the definitions and proved supporting lemmas in TauCeti.GroupTheory.SpecificGroups.CFSG.ReeF4.Basic for the concrete CFSG catalog. This module does not assert the classification theorem.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/6e0c6acab5f4c6f42e5f5bab9bd5e4e84f74c380/TauCeti/GroupTheory/SpecificGroups/CFSG/ReeF4/Basic.lean

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Definitions.Def_TC433_Algebra_Lie_F4_ShortRoot_PrimeField_QuotientSpecialIsogeny_e7cb9f468d
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_ReeF4_Carrier_6657beb940
public import Definitions.Def_TC433_GroupTheory_SpecificGroups_CFSG_OddPowerSteinberg_57a2f0b731
public import Definitions.Def_TC433_GroupTheory_FixedPointCandidate_c28335b059

/-!
# The Ree F4 Steinberg map and candidate group

The represented quotient constructs the exceptional endomorphism of the characteristic-two
short-root carrier. Its odd power is the Steinberg map for a validated Ree F4 index. The candidate
is the derived subgroup of its fixed points modulo the centre of that derived subgroup.

The ambient group consists of algebraic-closure points of the explicit prime-field short-root
carrier. A comparison with the pinned simply connected F4 group scheme requires an isomorphism
preserving the root subgroups and exceptional endomorphism. No finiteness or simplicity is assumed
or proved here. The conventions follow Carter, *Simple Groups of Lie Type*, §14.
-/

/- Adapted from the family interface and odd-iterate construction in
`TauCeti/GroupTheory/SpecificGroups/CFSG/Suzuki/Basic.lean`. -/

public section
set_option backward.isDefEq.respectTransparency.types false

namespace TauCeti.ReeF4LieIndex

noncomputable section

variable (d : ReeF4LieIndex)

/-- The exceptional endomorphism of the Ree F4 ambient carrier. -/
def halfFrobenius : d.AmbientGroup →* d.AmbientGroup :=
  F4ShortRoot.PrimeField.specialIsogeny d.1.Closure

/-- The half-Frobenius is the characteristic-two carrier's special isogeny. -/
theorem halfFrobenius_def :
    d.halfFrobenius = F4ShortRoot.PrimeField.specialIsogeny d.1.Closure := by rfl

/-- The half-Frobenius squares to the prime-field Frobenius. -/
@[simp] theorem halfFrobenius_halfFrobenius (g : d.AmbientGroup) :
    d.halfFrobenius (d.halfFrobenius g) = d.primeFrobenius g := by
  rw [halfFrobenius_def, primeFrobenius_def,
    F4ShortRoot.PrimeField.specialIsogeny_specialIsogeny]

private theorem carrierNode_lengthPerm (i : Fin d.1.rank) :
    finCongr d.rank_eq_four (d.toSuzukiReeIndex.lengthPerm i) =
      Fin.revPerm (finCongr d.rank_eq_four i) := by
  obtain ⟨m, hvalid, rfl⟩ := d.exists_eq_of
  simp [toSuzukiReeIndex, SuzukiReeIndex.lengthPerm_reeF4, Equiv.permCongr_def,
    lengthPermF4_apply]

private theorem carrierExponent (i : Fin d.1.rank) :
    F4ShortRoot.isogenyExponent (.inl (finCongr d.rank_eq_four i)) =
      d.toSuzukiReeIndex.exponent i := by
  rw [exponent_eq]
  have h : ∀ j : Fin 4, F4ShortRoot.isogenyExponent (.inl j) =
      if (j : ℕ) < 2 then 1 else 2 := by decide
  exact h (finCongr d.rank_eq_four i)

/-- The half-Frobenius has the index's own root permutation and long/short exponents. -/
@[simp] theorem halfFrobenius_simpleRootSubgroup (i : Fin d.1.rank)
    (u : Multiplicative d.1.Closure) :
    d.halfFrobenius (d.simpleRootSubgroup i u) =
      d.simpleRootSubgroup (d.toSuzukiReeIndex.lengthPerm i)
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.toSuzukiReeIndex.exponent i)) := by
  rw [halfFrobenius_def, simpleRootSubgroup_def,
    F4ShortRoot.PrimeField.specialIsogeny_rootSubgroupPoints, simpleRootSubgroup_def,
    carrierNode_lengthPerm, ← carrierExponent]
  simp only [F4ShortRoot.isogenyReverse, Sum.map_inl]

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

/-- The fixed subgroup of the Ree F4 Steinberg endomorphism. -/
abbrev FixedPoints : Type := ↥(fixedSubgroup d.steinberg)

/-- The Ree F4 candidate: the derived subgroup of the Steinberg fixed points modulo its own
centre. This definition carries no assertion of finiteness, perfectness, or simplicity. -/
abbrev Group : Type := FixedPointCandidate d.steinberg

example : _root_.Group d.Group := inferInstance

end

end TauCeti.ReeF4LieIndex



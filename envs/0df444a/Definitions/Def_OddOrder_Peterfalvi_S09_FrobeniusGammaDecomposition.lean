-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition
-- name    : OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:23:21.298175+00:00
-- url     : https://prove2.me/theorems/918b4bef-27f0-4d06-b4ff-2638f7462c8b
-- title:
--   Frobenius-family Gamma decomposition (Peterfalvi 7.10)
-- statement:
--   This file constructs the coefficient relation used in Peterfalvi (7.10) to project the residual $\Gamma$ of a selected Frobenius-family member onto the weighted coherent sums of the other members (Peterfalvi, §7, pp. 41-43).
--
--   Main definitions: `weightedNuSumAt` (the weighted coherent sum of a family member), `betaAt`, `distinguishedNuAt` (the distinguished coherent image defining the integer cross-family coefficient), `gammaAt` (the $\Gamma$ residual of the proved beta decomposition) and `reverseCoefficientZeroIndices` (Peterfalvi's set $B$ for the selected index).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusGammaDecomposition.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalCoefficient

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Fintype ↥((F.H i).subgroupOf (F.L i))]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

noncomputable abbrev localH78_S09_FrobeniusGammaDecomposition :=
  F.hypothesis78 i hodd hnilp C hFrob

end LocalCoefficient

end FrobeniusFamily

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section FamilyRealization

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (hodd : Odd (Nat.card G))

variable (hnilp : ∀ j : Fin k,
  Group.IsNilpotent ↥((F.H j).subgroupOf (F.L j)))

variable (C : ∀ j : Fin k, Subgroup ↥(F.L j))

variable (hFrob : ∀ j : Fin k, OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L j) ((F.H j).subgroupOf (F.L j)) (C j))

/-- The weighted coherent sum belonging to the canonical (7.8) datum of a
family member. -/
noncomputable def weightedNuSumAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).weightedNuSum

/-- The beta class function of the canonical (7.8) datum at a family index. -/
noncomputable def betaAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  (F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)).beta

/-- The distinguished coherent image used to define the integer cross-family
coefficient. -/
noncomputable def distinguishedNuAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let H78 := F.hypothesis78 j hodd (hnilp j) (C j) (hFrob j)
  H78.nu (H78.hyp76.zeta 0)

/-- The Gamma residual of the proved beta decomposition at a family index. -/
noncomputable def gammaAt (j : Fin k) : ClassFunction G ℂ :=
  letI : Fintype ↥(F.L j) := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(F.L j) : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := F.L j)).ne')
  letI : Fintype ↥((F.H j).subgroupOf (F.L j)) := Fintype.ofFinite _
  letI : Invertible
      (Nat.card ↥((F.H j).subgroupOf (F.L j)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : ((F.H j).subgroupOf (F.L j)).Normal := (hFrob j).isNormal
  (F.hypothesis78_betaDecomp j hodd (hnilp j) (C j) (hFrob j)).Gamma

/-- Peterfalvi's set B for the selected index i: the other family members whose
reverse cross coefficient with the distinguished image at i vanishes. -/
noncomputable def reverseCoefficientZeroIndices (i : Fin k) :
    Finset (Fin k) := by
  classical
  exact Finset.univ.filter fun j =>
    i ≠ j ∧ ClassFunction.inner
      (F.betaAt hodd hnilp C hFrob j)
      (F.distinguishedNuAt hodd hnilp C hFrob i) = 0

end FamilyRealization

end FrobeniusFamily

end OddOrder.Peterfalvi.S09



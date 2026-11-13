-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate
-- name    : OddOrder_Peterfalvi_S09_FrobeniusSelectedEstimate
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:26:35.052216+00:00
-- url     : https://prove2.me/theorems/dda5289f-d23b-4b62-827e-61b6cd37e5c0
-- title:
--   Frobenius-family selected-character estimate (Peterfalvi 7.8.b)
-- statement:
--   This file proves the lower norm estimate for the canonical distinguished coherent image `distinguishedNuAt` of every member of a Frobenius family, the character whose reverse coefficients define the set $B$ in (7.10). It applies the abstract (7.8.b) identity to this canonical character.
--
--   The bundle's only definition is the local abbreviation `localH78`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusSelectedEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
import Definitions.Def_OddOrder_Peterfalvi_S09_NonexistenceCertain_FrobeniusFamily

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalSelectedEstimate

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

noncomputable abbrev localH78_S09_FrobeniusSelectedEstimate :=
  F.hypothesis78 i hodd hnilp C hFrob

end LocalSelectedEstimate

end FrobeniusFamily

end OddOrder.Peterfalvi.S09



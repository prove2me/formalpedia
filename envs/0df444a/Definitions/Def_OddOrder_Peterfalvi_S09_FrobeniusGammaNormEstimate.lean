-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
-- name    : OddOrder_Peterfalvi_S09_FrobeniusGammaNormEstimate
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:24:49.273318+00:00
-- url     : https://prove2.me/theorems/53351854-155f-4af6-8782-b245186b017d
-- title:
--   Frobenius-family Gamma norm estimate (Peterfalvi 7.8.b)
-- statement:
--   This file evaluates the norm of the concrete residual $\Gamma$ attached to a Frobenius-family member. The source norm of $\mathrm{Ind}\,1_H-\zeta$ gives $\|\beta\|^2=e+1$, the evaluated weighted coherent sum gives the orthogonal expansion of $\|\beta\|^2$, and Peterfalvi's quadratic argument yields $\|\Gamma\|^2\le e-1$ (Peterfalvi, §7, pp. 41-43).
--
--   The bundle's definitions are local abbreviations `localH78` and `localBD`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusGammaNormEstimate.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusGammaNormEstimate.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusGammaDecomposition

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

section LocalGammaNorm

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))

variable [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]

variable [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]

variable [((F.H i).subgroupOf (F.L i)).Normal]

variable (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))

variable (C : Subgroup ↥(F.L i))

variable (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
  ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C)

noncomputable abbrev localH78_S09_FrobeniusGammaNormEstimate :=
  F.hypothesis78 i hodd hnilp C hFrob

noncomputable abbrev localBD_S09_FrobeniusGammaNormEstimate :=
  F.hypothesis78_betaDecomp i hodd hnilp C hFrob

end LocalGammaNorm

end FrobeniusFamily

end OddOrder.Peterfalvi.S09



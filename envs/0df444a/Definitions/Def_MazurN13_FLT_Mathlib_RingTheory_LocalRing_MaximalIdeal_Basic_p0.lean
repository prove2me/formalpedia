-- Prove2me | Definitions.Def_MazurN13_FLT_Mathlib_RingTheory_LocalRing_MaximalIdeal_Basic_p0
-- name    : MazurN13_FLT_Mathlib_RingTheory_LocalRing_MaximalIdeal_Basic_p0
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T21:47:42.123279+00:00
-- url     : https://prove2.me/theorems/0374935e-e93f-4cbd-b357-ff726337a16b
-- title:
--   FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic source foundation
-- statement:
--   Definitions and supporting proofs for the order-thirteen exclusion, retained from the indicated source commands.
-- source:
--   https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580:FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/- Port source: https://github.com/xiangyazi24/FLT @ 51bbb4f191ad0d3753b87123635c100a638ae580
Module: FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
Original leading source comments and nonproject imports are retained below. -/
/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

set_option autoImplicit false




/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R



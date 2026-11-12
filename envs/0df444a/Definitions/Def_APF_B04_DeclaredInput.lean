-- Prove2me | Definitions.Def_APF_B04_DeclaredInput
-- name    : APF_B04_DeclaredInput
-- status  : Definition
-- author  : @FiniteUniverse
-- created : 2026-10-06T20:54:15.098812+00:00
-- url     : https://prove2.me/theorems/8c2b43e8-cb86-4ce8-80f4-ad40027bbce7
-- title:
--   Declared input — B04 — Finite capacity A1
-- statement:
--   Each physical context has finite available capacity, C_Gamma < infinity.
-- source:
--   APF Reconstruction Spine/FOUNDATION_INPUTS.json; revision 2026-10-04.1; SHA-256 bb3b59f6011dd70c5d34c9c830ab65aad0a224b11e26d4d438c4e1ab2ad445c4; declared input B04.

import Mathlib.Data.Real.Basic

/-! B04, revision 2026-10-04.1: capacity at EACH original physical context.
Context ranges over the original source contexts; C is their original capacity,
not a selected subfamily or a bound on every nominal protocol bill.
Finite real typing expresses finiteness, and the predicate retains nonnegativity.
Source: Supplement v9.27:1763-1776,1851-1860,2650-2652.
This defines the adopted input, not a derived capacity theorem; the bound of
record foundation_capacity_bound_infimal is unchanged and is not reproved here.
-/
set_option autoImplicit false
namespace APFB04

def B04FiniteCapacity {Context : Type*} (C : Context → ℝ) : Prop :=
  ∀ g, 0 ≤ C g

end APFB04



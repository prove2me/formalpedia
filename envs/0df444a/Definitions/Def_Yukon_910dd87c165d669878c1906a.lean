-- Prove2me | Definitions.Def_Yukon_910dd87c165d669878c1906a
-- name    : Yukon_910dd87c165d669878c1906a
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:03:50.814809+00:00
-- url     : https://prove2.me/theorems/a9f5039e-033c-487c-82ab-a4a1817fc834
-- title:
--   YukonModule.CompPoly.Fields.KoalaBear.Fast.part0
-- statement:
--   Source module CompPoly.Fields.KoalaBear.Fast.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Fast.lean
--
--   yukon-proof-operation:d2fc9b2ada9ea07bd62c060b26b8a599f8f93d6bfbe56e548e04558838230f6b
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246ZDJmYzliMmFkYTllYTA3YmQ2MmMwNjBiMjZiOGE1OTlmOGY5M2Q2YmZiZTU2ZTU0OGUwNDU1ODgzODIzMGY2YiIsImhhc2giOiJhZjUxNDgyYjNlYTRkZGY2ZTlmOWFmMDgyOTllYjQ4MmM4ZTA5NDJhZmE2YWY0MDVmZDg1ZTY5YTYxZjNhMzZjIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85MTBkZDg3YzE2NWQ2Njk4NzhjMTkwNmEiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Valerii Huhnin
-/
module

public import Definitions.Def_Yukon_db9e62887577419e408bc32c

public import Definitions.Def_Yukon_75117712fcefe5e9df83f473



public import Mathlib.Tactic.Linarith
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.ModEq
public import Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
meta import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_75117712fcefe5e9df83f473
set_option backward.isDefEq.respectTransparency.types false
/-!
# Fast KoalaBear Field

A native-word Montgomery implementation of KoalaBear arithmetic. The shared algorithms and
proofs live in `CompPoly.Fields.Montgomery.Native32Field`; this module supplies the KoalaBear
constants and its concrete API.
-/

@[expose] public section

namespace KoalaBear.Fast

open Montgomery.Native32 (Mont32Field FastField)
open Montgomery.Native32.FastField

/-! ## Parameters and carrier -/

/-- The per-field data realizing KoalaBear as a fast 32-bit-word Montgomery field. -/
instance instMont32Field : Mont32Field KoalaBear.fieldSize where
  prime := KoalaBear.is_prime
  modulus32 := 0x7F000001
  modulus64 := 0x7F000001
  rModModulus := 0x01FFFFFE
  r2ModModulus := 0x17F7EFE4
  montgomeryNegInv := 0x7EFFFFFF

/-- The fast native-word KoalaBear field carrier, stored as a Montgomery residue. -/
abbrev Field : Type := FastField KoalaBear.fieldSize

/-! ## Conversions -/

/-- Convert a 32-bit word into fast Montgomery representation. -/
@[inline]
def ofUInt32 (x : UInt32) : Field :=
  Montgomery.Native32.FastField.ofUInt32 KoalaBear.fieldSize x

/-- Convert from the canonical `ZMod` KoalaBear field into fast Montgomery form. -/
@[inline]
def ofField (x : KoalaBear.Field) : Field :=
  Montgomery.Native32.FastField.ofField x

/-! ## Canonical bridge -/

/-- Ring equivalence between the fast Montgomery representation and canonical `KoalaBear.Field`. -/
def ringEquiv : Field ≃+* KoalaBear.Field :=
  Montgomery.Native32.ringEquiv KoalaBear.fieldSize

/-! ## Two-adic roots -/

/-- Precomputed KoalaBear two-adic generators in Montgomery representation. -/
def twoAdicGenerators : List Field :=
  [
    ⟨0x01FFFFFE, by decide⟩,
    ⟨0x7D000003, by decide⟩,
    ⟨0x7B020407, by decide⟩,
    ⟨0x60F5EF4D, by decide⟩,
    ⟨0x6D249C01, by decide⟩,
    ⟨0x788529F3, by decide⟩,
    ⟨0x07F7373E, by decide⟩,
    ⟨0x6FE91D3C, by decide⟩,
    ⟨0x3FD49211, by decide⟩,
    ⟨0x1E056392, by decide⟩,
    ⟨0x6D969BAB, by decide⟩,
    ⟨0x439600CC, by decide⟩,
    ⟨0x150276FC, by decide⟩,
    ⟨0x68CACC36, by decide⟩,
    ⟨0x42336C40, by decide⟩,
    ⟨0x019B1972, by decide⟩,
    ⟨0x34E52F6D, by decide⟩,
    ⟨0x1C2EB437, by decide⟩,
    ⟨0x7CB65829, by decide⟩,
    ⟨0x29306FAE, by decide⟩,
    ⟨0x351C7FA7, by decide⟩,
    ⟨0x6E3E9A00, by decide⟩,
    ⟨0x47C2BDF7, by decide⟩,
    ⟨0x0C895820, by decide⟩,
    ⟨0x13C85195, by decide⟩
  ]

/-- The Montgomery root table represents the canonical KoalaBear roots. -/
theorem twoAdicGenerators_eq_map :
    twoAdicGenerators = KoalaBear.twoAdicGenerators.map ofField := by
  decide

end KoalaBear.Fast



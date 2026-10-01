-- Prove2me | Definitions.Def_Yukon_9e16b2bd8a44fd5b9c05fbe2
-- name    : Yukon_9e16b2bd8a44fd5b9c05fbe2
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:09:19.818947+00:00
-- url     : https://prove2.me/theorems/fda0468c-c41c-4d51-a523-b2a24ab7b73e
-- title:
--   YukonModule.CompPoly.Fields.KoalaBear.part0
-- statement:
--   Source module CompPoly.Fields.KoalaBear.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear.lean
--
--   yukon-proof-operation:04e2214b64cd9747c86e078264a4b94af43608677b17b7a742fbe371b7b183c9
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MDRlMjIxNGI2NGNkOTc0N2M4NmUwNzgyNjRhNGI5NGFmNDM2MDg2NzdiMTdiN2E3NDJmYmUzNzFiN2IxODNjOSIsImhhc2giOiI1MWFlYjFmNzQwYTBlNjBkMjZmNTlhNDEzZmQyMDJkOGQ1NjY4MjI3NmYyMGYyZDU3YjEyYTg1ZGU0NTY5M2I5Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl85ZTE2YjJiZDhhNDRmZDViOWMwNWZiZTIiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Valerii Huhnin
-/
module

public import Definitions.Def_Yukon_db9e62887577419e408bc32c

public import Definitions.Def_Yukon_910dd87c165d669878c1906a



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
meta import Definitions.Def_Yukon_910dd87c165d669878c1906a
set_option backward.isDefEq.respectTransparency.types false
/-!
# KoalaBear Field

Facade module for the KoalaBear field. It re-exports the canonical `ZMod` model
from `CompPoly.Fields.KoalaBear.Basic` and the native-word implementation from
`CompPoly.Fields.KoalaBear.Fast`.
-/

@[expose] public section



-- Prove2me | Definitions.Def_Yukon_cc5bf869a789ce66594ace6c
-- name    : Yukon_cc5bf869a789ce66594ace6c
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:21:26.087993+00:00
-- url     : https://prove2.me/theorems/cb9f150c-8a73-4ff3-8808-ff6b1078549a
-- title:
--   YukonModule.CompPoly.Fields.Extension.part0
-- statement:
--   Source module CompPoly.Fields.Extension.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/Extension.lean
--
--   yukon-proof-operation:7d0df6de047ef43da389b9aef323a419015d61c9e04ddc1f0ad7ff8b9edd3a5e
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246N2QwZGY2ZGUwNDdlZjQzZGEzODliOWFlZjMyM2E0MTkwMTVkNjFjOWUwNGRkYzFmMGFkN2ZmOGI5ZWRkM2E1ZSIsImhhc2giOiJjM2I3ZWI1OTc1NDdiODc3M2QyYjhiYTE4ZTY0ZTA2OGMwMWUyNzNlNjEyYTE3OWJlYzlhMGMxOTQ2N2I4NDdkIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl9jYzViZjg2OWE3ODljZTY2NTk0YWNlNmMiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Definitions.Def_Yukon_04b73565b72d377e4c48e6c0

public import Definitions.Def_Yukon_b64c002b9f6caec7014c6911

public import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752

public import Definitions.Def_Yukon_01021eded3220e2800cfca71



public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Init
public import Mathlib.RingTheory.Henselian
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Algebra.Order.Star.Basic
meta import Definitions.Def_Yukon_04b73565b72d377e4c48e6c0
meta import Definitions.Def_Yukon_b64c002b9f6caec7014c6911
meta import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
meta import Definitions.Def_Yukon_01021eded3220e2800cfca71
set_option backward.isDefEq.respectTransparency.types false
/-!
# Computable field extensions

Facade for the field-extension stack. Extensions are `F[X] / f` for an arbitrary monic modulus
`f`; the binomial case `f = X^d - W` is the special case `BinomialParams.toExtensionParams`. See the
individual modules for details:

* `CompPoly/Fields/Extension/Binomial.lean` — irreducibility of `X^d - W` over a finite field,
  via Rabin's test collapsed to two base-field exponentiations.
* `CompPoly/Fields/Extension/Defs.lean` — `ExtensionParams` (an arbitrary monic modulus) and the
  binomial front-end `BinomialParams`, plus the coefficient-vector carrier `Ext P` with its ring
  operations (`shiftReduce`, `monomialMod`, `mul`).
* `CompPoly/Fields/Extension/Bridge.lean` — `toQuot : Ext P → AdjoinRoot P.poly`, the
  multiply-by-`X` law `toQuot_shiftReduce`, and the `CommRing` structure.
* `CompPoly/Fields/Extension/Field.lean` — bijectivity, cardinality, and the `Field` structure.
-/

@[expose] public section



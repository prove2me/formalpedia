-- Prove2me | Definitions.Def_Yukon_7bdfb5c7976bc55dd3e2bf3e
-- name    : Yukon_7bdfb5c7976bc55dd3e2bf3e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:26:44.86736+00:00
-- url     : https://prove2.me/theorems/0e21cb09-567d-4cd5-9898-a51e8f1e6ccc
-- title:
--   YukonModule.CompPoly.Fields.KoalaBear.Ext6.part0
-- statement:
--   Source module CompPoly.Fields.KoalaBear.Ext6.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Ext6.lean
--
--   yukon-proof-operation:ce9a86fe40685c17635ecae8684af0a202fa8faaf576d371cae192b96f57b430
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMjBkOTNmZjczZjk2NDFjMzI4NDYyMzExMGJjYTNjOTJjMGQyOTBkZTFmOGE3YmRiZjY2YTJlNGY5MWQ2ZWQyZSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlOWE4NmZlNDA2ODVjMTc2MzVlY2FlODY4NGFmMGEyMDJmYThmYWFmNTc2ZDM3MWNhZTE5MmI5NmY1N2I0MzAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83YmRmYjVjNzk3NmJjNTVkZDNlMmJmM2UiLCJ2IjoyfQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Definitions.Def_Yukon_cc5bf869a789ce66594ace6c

public import Definitions.Def_Yukon_7863be5f7e3e09daa1620f08



public import Mathlib.Tactic.ComputeDegree
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.NumberTheory.LucasPrimality
public import Mathlib.Tactic.ReduceModChar
public import Init
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.Algebra.EuclideanDomain.Int
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
public import Mathlib.RingTheory.Henselian
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Data.NNReal.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.Regular
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
public import Definitions.Def_Yukon_01021eded3220e2800cfca71
public import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_cd1b61f69d8bf8bcce480752
meta import Definitions.Def_Yukon_01021eded3220e2800cfca71
meta import Definitions.Def_Yukon_cc5bf869a789ce66594ace6c
meta import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_7863be5f7e3e09daa1620f08
set_option backward.isDefEq.respectTransparency.types false
/-!
# The degree-6 extension of KoalaBear

`KoalaBear[X] / (X^6 + X^3 + 1)`, a field of `p^6 ≈ 2^186` elements. The modulus is `Φ₉`, the
ninth cyclotomic polynomial, so the adjoined root `θ` is a primitive 9th root of unity.

As at degree 5, the modulus is necessarily *not* a binomial, and for a stronger reason: since
`p - 1 = 2^24 · 127` we have `3 ∤ p - 1`, so `x ↦ x^3` is a bijection on KoalaBear and every `W`
is a cube `V^3`, whence `X^6 - W = (X^2 - V)(X^4 + V X^2 + V^2)` factors for *every* `W`. So no
degree-6 binomial extension of KoalaBear exists at all.

`Φ₉` is chosen among the irreducible sextics because every entry of its reduction table
`X^6 … X^10 mod f` is `±1` — reduction costs no base-field multiplications — and the same holds
for its Frobenius matrix, since `p ≡ 2 mod 9` makes Frobenius `θ ↦ θ^2`. It also carries the
`2`-then-`3` tower implicitly: `θ^3` is a primitive cube root of unity generating the `F_p²`
subfield, because `Y^2 + Y + 1` is irreducible over KoalaBear.

Irreducibility of `X^6 + X^3 + 1` is `KoalaBear.sexticPoly_irreducible`
(`CompPoly/Fields/KoalaBear/Ext6/SexticIrreducible.lean`), proved by Rabin's test at a degree with
two prime factors, with kernel-checked certificates for all three conditions. Supporting files
live under `KoalaBear/Ext6/`.

This sits alongside `KoalaBear.Ext5` rather than replacing it; the two are independent instances
of the same framework.

## Main definitions

* `KoalaBear.ext6Params`: the `ExtensionParams` for `X^6 + X^3 + 1`.
* `KoalaBear.Ext6`: the extension field itself.
-/

@[expose] public section

namespace KoalaBear

open CompPoly.Extension Polynomial

/-- The parameters of the sextic extension `KoalaBear[X] / (X^6 + X^3 + 1)`: the lower
coefficients of the monic modulus are `(1, 0, 0, 1, 0, 0)`. -/
def ext6Params : ExtensionParams Field where
  d := 6
  two_le := by norm_num
  lower := #v[1, 0, 0, 1, 0, 0]
  q := fieldSize
  card_eq := ZMod.card _

@[simp] theorem ext6Params_d : ext6Params.d = 6 := rfl
@[simp] theorem ext6Params_q : ext6Params.q = fieldSize := rfl

/-- The defining polynomial of the parameters is the sextic `X^6 + X^3 + 1`. -/
theorem ext6Params_poly : ext6Params.poly = sexticPoly := by
  have h0 : ext6Params.lowerCoeff ⟨0, by norm_num⟩ = 1 := rfl
  have h1 : ext6Params.lowerCoeff ⟨1, by norm_num⟩ = 0 := rfl
  have h2 : ext6Params.lowerCoeff ⟨2, by norm_num⟩ = 0 := rfl
  have h3 : ext6Params.lowerCoeff ⟨3, by norm_num⟩ = 1 := rfl
  have h4 : ext6Params.lowerCoeff ⟨4, by norm_num⟩ = 0 := rfl
  have h5 : ext6Params.lowerCoeff ⟨5, by norm_num⟩ = 0 := rfl
  rw [ExtensionParams.poly, sexticPoly]
  show X ^ 6 + (∑ i : Fin 6, C (ext6Params.lowerCoeff i) * X ^ (i : ℕ)) = X ^ 6 + X ^ 3 + C 1
  rw [Fin.sum_univ_six]
  rw [show ext6Params.lowerCoeff (0 : Fin 6) = 1 from h0,
    show ext6Params.lowerCoeff (1 : Fin 6) = 0 from h1,
    show ext6Params.lowerCoeff (2 : Fin 6) = 0 from h2,
    show ext6Params.lowerCoeff (3 : Fin 6) = 1 from h3,
    show ext6Params.lowerCoeff (4 : Fin 6) = 0 from h4,
    show ext6Params.lowerCoeff (5 : Fin 6) = 0 from h5]
  simp only [map_zero, map_one]
  rw [show ((0 : Fin 6) : ℕ) = 0 from rfl, show ((3 : Fin 6) : ℕ) = 3 from rfl]
  ring

/-- The irreducibility fact in the form the framework's `Field` instance consumes. -/
instance  _root_.KoalaBear.instFactIrreduciblePolynomialFieldPolyExt6Params : Fact (Irreducible ext6Params.poly) :=
  ⟨ext6Params_poly ▸ sexticPoly_irreducible⟩

/-- The degree-6 extension field of KoalaBear. -/
abbrev Ext6 : Type := CompPoly.Extension.Ext ext6Params

/-- The adjoined root of `X^6 + X^3 + 1`, a primitive 9th root of unity, as an element of
`Ext6`. -/
def ext6Gen : Ext6 := Ext.gen

/--
`ext6Gen` is the framework's `Ext.gen`.

Deliberately **not** `@[simp]`: as a rewrite it fires before `ext6Gen_pow_six` can match, which
would knock that lemma out of the simp set.
-/
theorem ext6Gen_eq_gen : ext6Gen = Ext.gen := rfl

/-- `ext6Gen` maps to the adjoined root of the specification. -/
@[simp] theorem toQuot_ext6Gen : Ext.toQuot ext6Gen = Ext.rt ext6Params := Ext.toQuot_gen

/-- `ext6Gen` is a root of `X^6 + X^3 + 1`, in the form `aeval` expects. -/
theorem aeval_ext6Gen : aeval ext6Gen ext6Params.poly = 0 := Ext.aeval_gen_poly

/-- **The defining relation**: the adjoined root satisfies `θ^6 = -θ^3 - 1`. Every coefficient is
`±1`, which is what makes reduction multiplication-free. -/
@[simp] theorem ext6Gen_pow_six :
    ext6Gen ^ 6 = -(ext6Gen ^ 3) - Ext.ofBase (1 : Field) := by
  have h := aeval_ext6Gen
  rw [ext6Params_poly, sexticPoly] at h
  simp only [map_add, map_pow, aeval_X, aeval_C, Ext.algebraMap_eq_ofBase] at h
  linear_combination h

/-- `θ^3` is a primitive cube root of unity: it satisfies `Y^2 + Y + 1 = 0`, which is irreducible
over KoalaBear because `3 ∤ p - 1`. So `F_p(θ^3)` is the `F_p²` subfield, and this is the
`2`-then-`3` tower `F_p ⊂ F_p² ⊂ F_p⁶` presented inside a single sextic. -/
theorem ext6Gen_cubed_is_primitive_cube_root :
    (ext6Gen ^ 3) ^ 2 + ext6Gen ^ 3 + Ext.ofBase (1 : Field) = 0 := by
  have h := ext6Gen_pow_six
  linear_combination h

/-- **`θ` is a primitive 9th root of unity**: `θ^9 = 1`. -/
@[simp] theorem ext6Gen_pow_nine : ext6Gen ^ 9 = 1 := by
  have h := ext6Gen_cubed_is_primitive_cube_root
  have hone : Ext.ofBase (1 : Field) = (1 : Ext6) := Ext.ofBase_one
  rw [hone] at h
  linear_combination (ext6Gen ^ 3 - 1) * h

@[simp] theorem card_ext6 : Fintype.card Ext6 = fieldSize ^ 6 := Ext.card_ext

end KoalaBear



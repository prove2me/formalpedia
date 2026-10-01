-- Prove2me | Definitions.Def_Yukon_766b34592bec7fcb9f69f5d5
-- name    : Yukon_766b34592bec7fcb9f69f5d5
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:45:15.316496+00:00
-- url     : https://prove2.me/theorems/6118d87f-8693-420b-9c0d-15f79b60c3cc
-- title:
--   YukonModule.ArkLib.Data.Polynomial.Trivariate.part0
-- statement:
--   Source module ArkLib.Data.Polynomial.Trivariate.
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Polynomial/Trivariate.lean
--
--   yukon-proof-operation:f72ef89b1b804bbc632658c4d5f19efe693428ce55b4a5288d0dd94ee1d1c95c
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNThhMTUzYTk3MDA1YzM2MjNiM2VlYTkwZGYzYTY2MjA4ZDQ2N2IzNTAyYzRhNThmODY1NGNlZjk2MzlhNGRkZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmY3MmVmODliMWI4MDRiYmM2MzI2NThjNGQ1ZjE5ZWZlNjkzNDI4Y2U1NWI0YTUyODhkMGRkOTRlZTFkMWM5NWMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83NjZiMzQ1OTJiZWM3ZmNiOWY2OWY1ZDUiLCJ2IjoyfQ]

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import Definitions.Def_Yukon_01ccec4dda453f6e2e78a73a

import Mathlib.FieldTheory.RatFunc.AsPolynomial


import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Algebra.Polynomial.Roots
import Aesop
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Cases
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.List.GetD
import Mathlib.Algebra.GroupWithZero.Nat
import Init
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Polynomial.Inductions
set_option backward.isDefEq.respectTransparency.types false
/-!
# Short interface on Trivariate Polynomials

We define trivariate polynomials to match their representation in statements and proofs
of [BCIKS20].

## Main Definitions

### Notation for trivariate polynomials and evaluation homomorphisms
- `eval_on_Z₀`: Evaluate a rational function on a point.
- `eval_on_Z`: Ring homomorphism evaluating the `Z` variable of a trivariate polynomial.
- `toRatFuncPoly`: Maps a trivariate polynomial to a bivariate polynomial over the rational
  function field.
- `D_Y`: The `Y`-degree of a trivariate polynomial.
- `D_YZ`: The `YZ`-degree of a trivariate polynomial.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/

namespace Trivariate

variable {F : Type} [Field F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate

/-- Evaluate a rational function on a point. -/
noncomputable def eval_on_Z₀ (p : (RatFunc F)) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p

notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial R))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

/-- A ring homomorphism mapping a trivariate polynomial with coefficients in `F` and variables
`Z, X, Y` to a bivariate polynomial with coefficients in `F` and variables in `X, Y` by evaluating
on a point `z ∈ F`. -/
noncomputable opaque eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

open Polynomial.Bivariate in
/-- A ring homomorphism mapping a trivariate polynomial to an element in the field of rational
functions of polynomial ring in two variables. -/
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

/-- Following [BCIKS20] this the `Y`-degree of a trivariate polynomial `Q`. -/
noncomputable def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q

/-- The `YZ`-degree of a trivariate polynomial: the total `(Y, Z)`-degree, i.e. the maximum of
`degY + degZ` over the monomials of `Q`.

Here `j` ranges over the `Y`-degrees of `Q` and `i` over the `X`-degrees occurring at `Y`-degree
`j`, so the coefficient of `X ^ i * Y ^ j` is `Bivariate.coeff Q i j` — note that
`Bivariate.coeff Q i j = (Q.coeff j).coeff i` takes the `X`-index first. -/
noncomputable def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun i => j + (Bivariate.coeff Q i j).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end Trivariate



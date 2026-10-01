-- Prove2me | Definitions.Def_Yukon_7863be5f7e3e09daa1620f08
-- name    : Yukon_7863be5f7e3e09daa1620f08
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T18:10:30.180804+00:00
-- url     : https://prove2.me/theorems/a78a8870-3ee6-407e-85d4-0b72149e6636
-- title:
--   YukonModule.CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible.part0
-- statement:
--   Source module CompPoly.Fields.KoalaBear.Ext6.SexticIrreducible.
-- source:
--   https://github.com/zksecurity/CompPoly/blob/641694629e4557520a1539b272ec338c9f3044c7/CompPoly/Fields/KoalaBear/Ext6/SexticIrreducible.lean
--
--   yukon-proof-operation:c567e2867e563fee21924e4793cf05bcd6bb5b468d8f3a320289270dec4b5cea
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246YzU2N2UyODY3ZTU2M2ZlZTIxOTI0ZTQ3OTNjZjA1YmNkNmJiNWI0NjhkOGYzYTMyMDI4OTI3MGRlYzRiNWNlYSIsImhhc2giOiI1MWNiZTQ0NWZhY2FkZmUwN2M1ZTE3YzYxMjU2NDlmZjA4MmNlZjYwZGRlYjYwYjEyMTNlNmVhZTVhNjBjZDAyIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl83ODYzYmU1ZjdlM2UwOWRhYTE2MjBmMDgiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 CompPoly Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Derek Sorensen
-/
module

public import Definitions.Def_Yukon_fd6496bbb3a6ffd84389acd4

public import Definitions.Def_Yukon_db9e62887577419e408bc32c

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
public import Definitions.Def_Yukon_4e69125b7cedd355ffb1d1c9
meta import Definitions.Def_Yukon_4e69125b7cedd355ffb1d1c9
meta import Definitions.Def_Yukon_db9e62887577419e408bc32c
meta import Definitions.Def_Yukon_fd6496bbb3a6ffd84389acd4
set_option backward.isDefEq.respectTransparency.types false
/-!
# Irreducibility of `X^6 + X^3 + 1` over KoalaBear

The sextic `X^6 + X^3 + 1` is the ninth cyclotomic polynomial `Φ₉`, so it is irreducible over
`KoalaBear.Field` exactly because `p` has multiplicative order 6 modulo 9 (`p ≡ 2 mod 9`); its
root is a primitive 9th root of unity. It is the defining polynomial of the degree-6 extension in
`CompPoly/Fields/KoalaBear/Ext6.lean`.

No degree-6 *binomial* does the job, for the same reason as at degree 5 but one step stronger:
`p - 1 = 2^24 · 127`, so `3 ∤ p - 1`, `x ↦ x^3` is a bijection on KoalaBear, and every `W` is a
cube `V^3` — whence `X^6 - W = (X^2 - V)(X^4 + V X^2 + V^2)` factors for *every* `W`.

`Φ₉` is chosen among the irreducible sextics for arithmetic reasons. Every entry of the reduction
table `X^6 … X^10 mod f` is `±1`, so reduction costs no base-field multiplications, and the same
holds for the Frobenius matrix (`θ ↦ θ^2`, since `p ≡ 2 mod 9`). It also exposes the `2`-then-`3`
tower for free: `θ^3` is a primitive cube root of unity, and `F_p(θ^3) = F_p²` because
`Y^2 + Y + 1` is irreducible over KoalaBear.

## Certificates

Degree 6 is *composite*, so Rabin's test needs the trace condition plus one coprimality check per
prime factor of 6 — at `p^3` (for `ℓ = 2`) and `p^2` (for `ℓ = 3`). The collapsed prime-degree
form is not just weaker but unsound here: `(X^3 + X + 4)(X^3 + X - 4)` divides `X^(p^6) - X` and
is coprime to `X^p - X`, so it would pass. The three conditions are discharged by kernel-checked
certificates from `CompPoly/Fields/KoalaBear/Ext6/SexticCertData.lean` (generated by
`scripts/gen_rabin_certificate.py`): a 258-step chain for the trace, 121 and 75 steps plus a
Bézout identity for the two coprimality checks. Each chain is verified by a single kernel
reduction of `CompPoly.RabinCert.runChain` — `Nat` arithmetic only, no `native_decide`.

## Main statements

* `KoalaBear.sexticPoly`: the polynomial `X^6 + X^3 + 1` over `KoalaBear.Field`.
* `KoalaBear.sexticPoly_irreducible`, and the `Fact` instance consumed by
  `CompPoly.Extension.Ext.instField`.
-/

@[expose] public section

namespace KoalaBear

open Polynomial CompPoly.RabinCert

/-- The defining sextic `X^6 + X^3 + 1 = Φ₉` of the degree-6 KoalaBear extension. -/
noncomputable def sexticPoly : Polynomial Field := X ^ 6 + X ^ 3 + C 1

/-- The sextic's little-endian `ℕ`-coefficient encoding. Every coefficient of `Φ₉` is `0` or `1`,
so unlike the quintic this needs no `p - 1` literal to spell a negative coefficient. -/
def sexticL : List ℕ := [1, 0, 0, 1, 0, 0, 1]

/-- The `ℕ`-coefficient encoding denotes the sextic. -/
theorem toPoly_sexticL : toPoly fieldSize sexticL = sexticPoly := by
  show toPoly fieldSize [1, 0, 0, 1, 0, 0, 1] = sexticPoly
  rw [sexticPoly, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons, toPoly_cons,
    toPoly_cons, toPoly_nil, Nat.cast_zero, Nat.cast_one, map_zero, map_one]
  ring

theorem sexticPoly_natDegree : sexticPoly.natDegree = 6 := by
  rw [sexticPoly]
  compute_degree!

theorem sexticPoly_ne_zero : sexticPoly ≠ 0 := by
  intro h
  have h6 := sexticPoly_natDegree
  rw [h, natDegree_zero] at h6
  exact absurd h6 (by norm_num)

/-!
### The kernel-checked certificates

Each theorem below is one kernel reduction: `runChain` re-verifies every step of the generated
chain (`cur² = q·f + r`, coefficientwise mod `p`), and `chainExp` recomputes the exponent the
chain reaches. `eqModP` checks the Bézout identities for coprimality.
-/

set_option maxRecDepth 60000 in
/-- The 258-step chain for `X^(p^6) mod f` verifies and ends at the residue `X`. -/
theorem sextic_trace_chain :
    runChain fieldSize sexticL [0, 1] SexticCert.traceSteps = some [0, 1] := by rfl

set_option maxRecDepth 60000 in
/-- The trace chain computes the exponent `p^6`. -/
theorem sextic_trace_exp : chainExp 1 SexticCert.traceSteps = fieldSize ^ 6 := by rfl

/-! #### Coprimality with `X^(p^3) - X`, the check for the prime factor `2` of `6` -/

set_option maxRecDepth 60000 in
/-- The 121-step chain for `X^(p^3) mod f` verifies and ends at the recorded residue. -/
theorem sextic_cop3_chain :
    runChain fieldSize sexticL [0, 1] SexticCert.cop3Steps = some SexticCert.cop3Rp := by rfl

set_option maxRecDepth 60000 in
/-- The chain computes the exponent `p^3`. -/
theorem sextic_cop3_exp : chainExp 1 SexticCert.cop3Steps = fieldSize ^ 3 := by rfl

/-- The recorded residue satisfies `cop3Rp = cop3W + X`. -/
theorem sextic_cop3_w_check :
    eqModP fieldSize SexticCert.cop3Rp (addNat SexticCert.cop3W [0, 1]) = true := by rfl

/-- The Bézout identity `cop3U·f + cop3V·cop3W = 1` verifies. -/
theorem sextic_cop3_bezout_check :
    eqModP fieldSize
      (addNat (mulNat SexticCert.cop3U sexticL) (mulNat SexticCert.cop3V SexticCert.cop3W)) [1]
      = true := by rfl

/-! #### Coprimality with `X^(p^2) - X`, the check for the prime factor `3` of `6` -/

set_option maxRecDepth 60000 in
/-- The 75-step chain for `X^(p^2) mod f` verifies and ends at the recorded residue. -/
theorem sextic_cop2_chain :
    runChain fieldSize sexticL [0, 1] SexticCert.cop2Steps = some SexticCert.cop2Rp := by rfl

set_option maxRecDepth 60000 in
/-- The chain computes the exponent `p^2`. -/
theorem sextic_cop2_exp : chainExp 1 SexticCert.cop2Steps = fieldSize ^ 2 := by rfl

/-- The recorded residue satisfies `cop2Rp = cop2W + X`. -/
theorem sextic_cop2_w_check :
    eqModP fieldSize SexticCert.cop2Rp (addNat SexticCert.cop2W [0, 1]) = true := by rfl

/-- The Bézout identity `cop2U·f + cop2V·cop2W = 1` verifies. -/
theorem sextic_cop2_bezout_check :
    eqModP fieldSize
      (addNat (mulNat SexticCert.cop2U sexticL) (mulNat SexticCert.cop2V SexticCert.cop2W)) [1]
      = true := by rfl

/-- **`X^6 + X^3 + 1` is irreducible over KoalaBear**, by Rabin's test at a degree with two prime
factors, with kernel-checked certificates for all three conditions. -/
theorem sexticPoly_irreducible : Irreducible sexticPoly := by
  have hcard : Fintype.card Field = fieldSize := ZMod.card _
  refine irreducible_of_rabin_degree_six_of_card fieldSize hcard sexticPoly_natDegree ?_ ?_ ?_
  · exact dvd_X_pow_sub_X_of_runChain toPoly_sexticL sexticPoly_ne_zero
      sextic_trace_chain sextic_trace_exp
  · exact isCoprime_X_pow_sub_X_of_runChain toPoly_sexticL sexticPoly_ne_zero
      sextic_cop3_chain sextic_cop3_exp sextic_cop3_w_check sextic_cop3_bezout_check
  · exact isCoprime_X_pow_sub_X_of_runChain toPoly_sexticL sexticPoly_ne_zero
      sextic_cop2_chain sextic_cop2_exp sextic_cop2_w_check sextic_cop2_bezout_check

instance  _root_.KoalaBear.instFactIrreduciblePolynomialFieldSexticPoly : Fact (Irreducible sexticPoly) := ⟨sexticPoly_irreducible⟩

end KoalaBear



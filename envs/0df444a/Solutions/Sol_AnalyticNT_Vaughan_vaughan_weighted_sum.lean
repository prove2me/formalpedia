-- Prove2me | solution 1 for AnalyticNT.Vaughan.vaughan_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T03:58:25.671184+00:00
-- url     : https://prove2.me/submissions/12a7dbc8-357f-489b-96d3-484ac52b3b44

import Definitions.Def_AnalyticNT_Vaughan
/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Vaughan's identity and finite weighted sums

## Statement

Vaughan's identity decomposes the von Mangoldt function into four
pieces controlled by truncation parameters `U, V ≥ 1`:

```
Λ(n) = Λ'(n) + S₁(n) − S₂(n) + S₃(n)
```

(The `+ S₃` sign is dictated by the chosen definition of `S₃` as the
positive bilinear convolution `Λ_{>V} * (μ_{>U} * ζ)`; the textbook form
`… − S₃` corresponds to negating this definition.)

where, schematically,

* `Λ'(n) = Λ(n) · 𝟙[n ≤ V]`              — small direct contribution,
* `S₁(n) = ∑_{d | n, d ≤ U} μ(d) · log(n / d)`        — Type-I, log-weighted,
* `S₂(n) = ∑_{d | n, d ≤ UV} (μ_{≤U} ∗ Λ_{≤V})(d)`   — Type-I, Λ-weighted,
* `S₃(n) = ∑_{k|n, V<k} Λ(k) ∑_{d|n/k, U<d} μ(d)` — Type-II tail.

The arithmetic-function-level proof is already in
`MathExtras/NumberTheory/Vinogradov/MinorArcVaughan.lean`
(`vaughan_identity_finite`).  This module exposes the package-side API:
explicit `U, V` truncation parameters, the four named pieces, and the
clean equality statement for use in summation-by-parts.

## References

* Vaughan, *An elementary method in prime number theory*, Acta Arith. 37 (1980), 111–115.
* Davenport, *Multiplicative Number Theory* (3rd ed., GTM 74), Ch. 24.
* Iwaniec & Kowalski, *Analytic Number Theory* (AMS Coll. 53, 2004), Ch. 13.
* Helfgott, *Minor arcs for Goldbach's problem*, arXiv:1205.5252v4, §3.
-/








/-!
Port of ext/analytic_nt/AnalyticNT/Vaughan/Identity.lean from
https://github.com/gersh/ternary-goldbach-lean at commit
27df23af6a712895f22204d0d81102baa74f0ebe.
Validated against Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
The original Apache-2.0 notice and declaration names are retained.
-/

namespace AnalyticNT
namespace Vaughan

open scoped ArithmeticFunction

/- The "small direct" piece `Λ'(n) = Λ(n) · 𝟙[n ≤ V]`. -/


/- Möbius coefficients truncated at `d ≤ U`, used as the Type-I cutoff. -/


/- The complementary Möbius tail `μ(n) · 𝟙[U < n]`. -/


/- The complementary von-Mangoldt tail `Λ(n) · 𝟙[V < n]`. -/


/- The first Type-I piece `S₁(n) = ∑_{d|n, d ≤ U} μ(d) · log(n/d)`,
realized as the Dirichlet convolution `μ_{≤U} * log`. -/


/- The second Type-I piece `S₂(n) = (μ_{≤U} * (ζ * Λ_{≤V}))(n)`,
i.e. the cross term that appears after expanding Vaughan's identity. -/


/- The Type-II piece `S₃ = Λ_{>V} * (μ_{>U} * ζ)`.
The inner coefficient retains its full Möbius divisor sum. -/


/-- **Vaughan's identity** (M1 statement form).

For any `U, V, n`,
`Λ(n) = Λ'(n) + S₁(n) − S₂(n) + S₃(n)`,
where the four pieces are defined above.  (The sign on `S₃` is positive
because `vaughanS3` is defined as the positive bilinear convolution
`Λ_{>V} * (μ_{>U} * ζ)`; the textbook form `… − S₃` would correspond to the
negation of this definition.)

The proof is an arithmetic-function-level identity in
`ArithmeticFunction ℝ`, mirroring `vaughan_identity_finite` from
`MathExtras/NumberTheory/Vinogradov/MinorArcVaughan.lean`. -/
theorem vaughan_identity
    (U V : ℕ) (_hU : 1 ≤ U) (_hV : 1 ≤ V) (n : ℕ) :
    (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n =
      vaughanLow V n + vaughanS1 U n - vaughanS2 U V n + vaughanS3 U V n := by
  -- Two helper partitions of `μ` and `Λ` into `≤` and `>` pieces.
  have hμ_split :
      muTruncated U + muHigh U =
        (ArithmeticFunction.moebius : ArithmeticFunction ℝ) := by
    ext k
    change (if k ≤ U then (ArithmeticFunction.moebius k : ℝ) else 0) +
      (if U < k then (ArithmeticFunction.moebius k : ℝ) else 0) =
        (ArithmeticFunction.moebius k : ℝ)
    by_cases hk : k ≤ U
    · have hnot : ¬ U < k := not_lt.mpr hk
      simp [hk, hnot]
    · have hlt : U < k := lt_of_not_ge hk
      simp [hk, hlt]
  have hΛ_split :
      vaughanLow V + lambdaHigh V =
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) := by
    ext k
    change (if k ≤ V then ArithmeticFunction.vonMangoldt k else 0) +
      (if V < k then ArithmeticFunction.vonMangoldt k else 0) =
        ArithmeticFunction.vonMangoldt k
    by_cases hk : k ≤ V
    · have hnot : ¬ V < k := not_lt.mpr hk
      simp [hk, hnot]
    · have hlt : V < k := lt_of_not_ge hk
      simp [hk, hlt]
  -- It suffices to prove the identity at the level of arithmetic functions.
  suffices hfun :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        vaughanLow V + vaughanS1 U - vaughanS2 U V + vaughanS3 U V from by
    have := congr_arg (fun f : ArithmeticFunction ℝ => f n) hfun
    simpa only [ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
      sub_eq_add_neg] using this
  -- Rewrite `vaughanS2` so the `Λ` factor becomes `vaughanLow V`.
  have hS2 :
      vaughanS2 U V =
        muTruncated U *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V) := by
    unfold vaughanS2
    have hΛsub :
        (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V =
          vaughanLow V := by
      have h := hΛ_split
      have : (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - lambdaHigh V =
          (vaughanLow V + lambdaHigh V) - lambdaHigh V := by rw [h]
      simpa using this
    rw [hΛsub]
  -- Now the algebra: expand `Λ = Λ' + Λ_{>V}` and rewrite `Λ_{>V}` using
  -- `1 = μ * ζ` and the splits.
  have hΛhigh :
      lambdaHigh V =
        vaughanS1 U - vaughanS2 U V + vaughanS3 U V := by
    have hμζ :
        (muTruncated U + muHigh U) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
          (1 : ArithmeticFunction ℝ) := by
      rw [hμ_split, ArithmeticFunction.coe_moebius_mul_coe_zeta]
    have hexpand :
        lambdaHigh V =
          lambdaHigh V *
            ((muTruncated U + muHigh U) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) := by
      rw [hμζ, mul_one]
    -- Distribute and re-associate.
    have hdist :
        lambdaHigh V *
            ((muTruncated U + muHigh U) *
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
          muTruncated U *
              ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V) +
            vaughanS3 U V := by
      unfold vaughanS3
      ring
    -- Express the first term using `Λ_{>V} = Λ - Λ_{≤V}`.
    have hΛhigh_eq :
        lambdaHigh V =
          (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - vaughanLow V := by
      have h := hΛ_split
      have : lambdaHigh V =
          (vaughanLow V + lambdaHigh V) - vaughanLow V := by abel
      rw [this, h]
    have hfirst :
        muTruncated U *
            ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * lambdaHigh V) =
          vaughanS1 U - vaughanS2 U V := by
      rw [hΛhigh_eq, hS2]
      unfold vaughanS1
      have hlog :
          (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) - vaughanLow V) =
            ArithmeticFunction.log -
              (ArithmeticFunction.zeta : ArithmeticFunction ℝ) * vaughanLow V := by
        rw [mul_sub, ArithmeticFunction.zeta_mul_vonMangoldt]
      rw [hlog, mul_sub]
    rw [hexpand, hdist, hfirst]
  -- Assemble.
  have hΛsplit_ext :
      (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) =
        vaughanLow V + lambdaHigh V := hΛ_split.symm
  rw [hΛsplit_ext, hΛhigh]
  abel

/-! ## V1 / V2: Vaughan-derived exponential sum identities

The package consumer (Helfgott minor-arc; cone) needs the identity applied to
the smoothed exponential sum
`S_η(α, x) = ∑_{n ≤ x} Λ(n) η(n / x) e(αn)`,
yielding the Type-I / Type-II decomposition. The proofs below apply the
arithmetic identity termwise and expand the Type-II convolution.
-/

/- Additive character `e(α · n) = exp(2πi α n)` on `ℕ`. -/


/- Exponential sum attached to an arithmetic function `F` up to `N`. -/


/-- **V1** — Vaughan-decomposed exponential sum.

Applying `vaughan_identity` term-by-term to the prime exponential sum
`expSum Λ N α`, we obtain the decomposition

```
expSum Λ N α = expSum Λ'_{≤V} N α
              + expSum S₁ N α
              − expSum S₂ N α
              + expSum S₃ N α
```

valid for all `U, V ≥ 1` (the identity holds term-by-term on `ℕ`). -/
theorem vaughan_exp_sum
    (U V N : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (α : ℝ) :
    expSum (ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) N α =
      expSum (vaughanLow V) N α
        + expSum (vaughanS1 U) N α
        - expSum (vaughanS2 U V) N α
        + expSum (vaughanS3 U V) N α := by
  -- Termwise: rewrite `Λ(n)` using `vaughan_identity` then split the sum.
  unfold expSum
  have hterm : ∀ n ∈ Finset.range (N + 1),
      ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n : ℂ) *
          addChar α n =
        (vaughanLow V n : ℂ) * addChar α n
          + (vaughanS1 U n : ℂ) * addChar α n
          - (vaughanS2 U V n : ℂ) * addChar α n
          + (vaughanS3 U V n : ℂ) * addChar α n := by
    intro n _
    have hid := vaughan_identity U V hU hV n
    -- Push the ℝ→ℂ coercion through `+` and `-`, then distribute.
    have hcoe : ((ArithmeticFunction.vonMangoldt : ArithmeticFunction ℝ) n : ℂ) =
        (vaughanLow V n : ℂ) + (vaughanS1 U n : ℂ)
          - (vaughanS2 U V n : ℂ) + (vaughanS3 U V n : ℂ) := by
      exact_mod_cast hid
    rw [hcoe]
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- **V2** — bilinear regrouping of the Type-II piece.

Unfolding the convolution `vaughanS3 U V = Λ_{>V} * (μ_{>U} * ζ)` term-by-term
gives the divisor-pair bilinear form

```
expSum S₃ N α = ∑_{n ≤ N} ∑_{(a,b) : a·b = n} Λ_{>V}(a) (μ_{>U} * ζ)(b) e(α n)
```

This is the divisor-antidiagonal bilinear regrouping consumed by the Type-II
bilinear bound (`Bilinear/TypeII.lean`); it mirrors the
`vaughanTypeIIBilinearSum` form from
`MathExtras/NumberTheory/Vinogradov/MinorArcVaughan.lean`.

Note: the textbook formulation `∑_{m > U} μ(m) ∑_{k > V, mk ≤ N} Λ(k) e(αmk)`
collapses an additional divisor sum (coming from `ζ` in the inner factor) and
therefore is *not* equal to the Lean convolution unless one keeps the `ζ`
factor or expands `(μ_{>U} * ζ)`.  The form below is the one that is true
on the nose at the arithmetic-function level.
-/
theorem vaughan_typeII_bilinear
    (U V N : ℕ) (_hU : 1 ≤ U) (_hV : 1 ≤ V) (α : ℝ) :
    expSum (vaughanS3 U V) N α =
      ∑ n ∈ Finset.range (N + 1),
        ∑ ab ∈ n.divisorsAntidiagonal,
          (lambdaHigh V ab.1 : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
                ab.2 : ℂ) *
            addChar α n := by
  unfold expSum vaughanS3
  refine Finset.sum_congr rfl ?_
  intro n _hn
  rw [show ((lambdaHigh V *
        (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))) n : ℂ) =
        ∑ ab ∈ n.divisorsAntidiagonal,
          (lambdaHigh V ab.1 : ℂ) *
            ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ))
                ab.2 : ℂ) from ?_]
  · rw [Finset.sum_mul]
  · rw [ArithmeticFunction.mul_apply]
    push_cast
    rfl

end Vaughan
end AnalyticNT

/--
info: 'AnalyticNT.Vaughan.vaughan_identity' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AnalyticNT.Vaughan.vaughan_identity

/--
info: 'AnalyticNT.Vaughan.vaughan_exp_sum' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AnalyticNT.Vaughan.vaughan_exp_sum

/--
info: 'AnalyticNT.Vaughan.vaughan_typeII_bilinear' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AnalyticNT.Vaughan.vaughan_typeII_bilinear

namespace AnalyticNT.Vaughan

/- A finite weighted arithmetic-function sum. Arbitrary complex weights permit
smooth cutoffs, coprimality restrictions, and additive characters simultaneously. -/


/-- Vaughan's identity after multiplying by any complex weight and summing over
any finite set. This includes both smoothed and coprimality-restricted sums. -/
theorem vaughan_weighted_sum_local (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : Finset ℕ) (w : ℕ → ℂ) :
    weightedSum ArithmeticFunction.vonMangoldt s w =
      weightedSum (vaughanLow V) s w + weightedSum (vaughanS1 U) s w -
        weightedSum (vaughanS2 U V) s w + weightedSum (vaughanS3 U V) s w := by
  unfold weightedSum
  have hterm (n : ℕ) : (ArithmeticFunction.vonMangoldt n : ℂ) * w n =
      (vaughanLow V n : ℂ) * w n + (vaughanS1 U n : ℂ) * w n -
        (vaughanS2 U V n : ℂ) * w n + (vaughanS3 U V n : ℂ) * w n := by
    have hid := congrArg (fun r : ℝ ↦ (r : ℂ)) (vaughan_identity U V hU hV n)
    push_cast at hid
    rw [hid]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The Type-II coefficient retains the additional divisor sum contributed by ζ. -/
theorem muHigh_zeta_apply (U n : ℕ) :
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n =
      ∑ d ∈ n.divisors, if U < d then (ArithmeticFunction.moebius d : ℝ) else 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  rfl

/-- The Type-II Möbius coefficient vanishes at arguments at most the cutoff. -/
theorem muHigh_zeta_apply_eq_zero_of_le (U n : ℕ) (hn : n ≤ U) :
    (muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) n = 0 := by
  rw [muHigh_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  simp [not_lt.mpr (hdn.trans hn)]

/-- Weighted divisor-antidiagonal form of the Type-II term, valid for every finite
index set and every complex weight. No positivity of the truncations is needed. -/
theorem vaughan_weighted_typeII (U V : ℕ) (s : Finset ℕ) (w : ℕ → ℂ) :
    weightedSum (vaughanS3 U V) s w =
      ∑ n ∈ s, ∑ ab ∈ n.divisorsAntidiagonal,
        (lambdaHigh V ab.1 : ℂ) *
          ((muHigh U * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) ab.2 : ℂ) *
            w n := by
  unfold weightedSum vaughanS3
  apply Finset.sum_congr rfl
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  push_cast
  rw [Finset.sum_mul]

/-- Explicit divisor-sum form of the logarithm-weighted Type-I term. -/
theorem vaughanS1_apply (U n : ℕ) :
    vaughanS1 U n = ∑ d ∈ n.divisors,
      if d ≤ U then (ArithmeticFunction.moebius d : ℝ) * Real.log (n / d) else 0 := by
  rw [vaughanS1, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d k ↦ muTruncated U d * ArithmeticFunction.log k)]
  apply Finset.sum_congr rfl
  intro d hd
  change (if d ≤ U then (ArithmeticFunction.moebius d : ℝ) else 0) *
    Real.log ((n / d : ℕ) : ℝ) = _
  rw [Nat.cast_div_charZero (Nat.mem_divisors.mp hd).1]
  split_ifs <;> simp

/--
info: 'AnalyticNT.Vaughan.vaughan_weighted_sum_local' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vaughan_weighted_sum_local

/--
info: 'AnalyticNT.Vaughan.muHigh_zeta_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms muHigh_zeta_apply

/--
info: 'AnalyticNT.Vaughan.muHigh_zeta_apply_eq_zero_of_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms muHigh_zeta_apply_eq_zero_of_le

/--
info: 'AnalyticNT.Vaughan.vaughan_weighted_typeII' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vaughan_weighted_typeII

/--
info: 'AnalyticNT.Vaughan.vaughanS1_apply' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vaughanS1_apply

end AnalyticNT.Vaughan

open AnalyticNT.Vaughan

theorem solution (U V : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s : Finset ℕ) (w : ℕ → ℂ) :
    weightedSum ArithmeticFunction.vonMangoldt s w =
      weightedSum (vaughanLow V) s w + weightedSum (vaughanS1 U) s w -
        weightedSum (vaughanS2 U V) s w + weightedSum (vaughanS3 U V) s w := by
  exact vaughan_weighted_sum_local U V hU hV s w

/--
info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms solution

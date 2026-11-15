-- Prove2me | Definitions.Def_RPLib_S4_KummerBridge
-- name    : RPLib_S4_KummerBridge
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-15T05:22:21.175812+00:00
-- url     : https://prove2.me/theorems/27051e30-e99d-4dc9-ae44-b28ba276ef36
-- title:
--   Divisible valuations give $N$-th-power ideal classes, and unramified Kummer roots
-- statement:
--   In a Dedekind domain with fraction field $L$, the file computes the count of a height-one prime $v$ in the principal fractional ideal $(a)$ as $-\log v(a)$, and proves that if $N \mid \log v(a)$ for every height-one prime $v$, then $$I^N \cdot (a) = (1)$$ for a fractional ideal $I$. Consequently, if $M$ is a finite Galois extension in $\overline{K}$ unramified over $A$, $0 \ne a \in M$ has $N$-divisible valuation at every prime of the integral closure of $A$ in $M$, and $N$ is invertible in $A$, then every $N$-th root of $a$ in $\overline{K}$ lies in $K_U$.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (etale fundamental groups, Kummer theory and tame ramification on affine curves over finite fields). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   J. Neukirch, Algebraic Number Theory, Grundlehren 322, Springer (1999), Chapter I, Sections 3 and 9; M. Rosen, Number Theory in Function Fields, GTM 210, Springer (2002), Chapter 10

import Mathlib
import Definitions.Def_RPLib_S4_KummerUnr
import Definitions.Def_RPLib_S4_PicDescentD2

/-!
# S4-Kummer, part K4a (bridge): divisible valuations give `N`-th-power ideal classes

* `count_spanSingleton`: `val_v((a)) = -log v(a)` for a nonzero `a` in the fraction field of a Dedekind domain.
* `exists_pow_mul_spanSingleton_eq_one`: if `N ∣ log v(a)` for every height-one prime `v`, then
  `I ^ N * (a) = 1` for a fractional ideal `I`.
* `root_mem_maxUnram_of_dvd`: `M ∈ unramSet A K`, `0 ≠ a ∈ M` with `N ∣ log v(a)` at every prime of the integral
  closure of `A` in `M`, `N` invertible in `A`: every `γ ∈ K̄` with `γ ^ N = a` lies in `maxUnram A K`
  (Galois conjugates handled by `PicDescent.valuation_pullH`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open IsDedekindDomain

namespace RamanujanPetersson
namespace Kummer

noncomputable section

section Bridge

variable {B M : Type*} [CommRing B] [IsDedekindDomain B] [Field M] [Algebra B M] [IsFractionRing B M]

/-- `val_v((a)) = -log v(a)`. -/
theorem count_spanSingleton (v : HeightOneSpectrum B) {a : M} (ha : a ≠ 0) :
    FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a) =
      -WithZero.log (v.valuation M a) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := B) a
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  have hspan : ∀ t : B, t ≠ 0 → Ideal.span {t} ≠ 0 := fun t ht => by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  have hM : ∀ t : B, t ≠ 0 → algebraMap B M t ≠ 0 := fun t ht =>
    (map_ne_zero_iff _ (IsFractionRing.injective B M)).2 ht
  rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton, ← FractionalIdeal.spanSingleton_inv,
    FractionalIdeal.count_mul M v ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM r hr0))
      (inv_ne_zero ((FractionalIdeal.spanSingleton_ne_zero_iff).2 (hM s hs0))),
    FractionalIdeal.count_inv, ← FractionalIdeal.coeIdeal_span_singleton,
    ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe M v (hspan r hr0),
    FractionalIdeal.count_coe M v (hspan s hs0), map_mul, map_inv₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_def,
    HeightOneSpectrum.intValuation_def, if_neg hr0, if_neg hs0, ← WithZero.exp_neg, ← WithZero.exp_add,
    WithZero.log_exp]
  ring

/-- **Divisible valuations give an `N`-th-power ideal class**: `I ^ N * (a) = 1`. -/
theorem exists_pow_mul_spanSingleton_eq_one {N : ℕ} [NeZero N] {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum B, (N : ℤ) ∣ WithZero.log (v.valuation M a)) :
    ∃ I : FractionalIdeal (nonZeroDivisors B) M,
      I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a = 1 := by
  classical
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).2 ha
  have hfin : (Function.support fun v : HeightOneSpectrum B =>
      -(FractionalIdeal.count M v (FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) / (N : ℤ)).Finite := by
    refine (Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors B) a))).subset ?_
    intro v hv h0
    apply hv
    simp only [h0, neg_zero, EuclideanDomain.zero_div]
  let e := Finsupp.ofSupportFinite _ hfin
  let I : FractionalIdeal (nonZeroDivisors B) M := e.prod (HeightOneSpectrum.asIdeal · ^ ·)
  have hI0 : I ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hJ0 : I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a ≠ 0 := mul_ne_zero (pow_ne_zero _ hI0) hspan
  have hcount : ∀ v : HeightOneSpectrum B,
      FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a) = 0 := by
    intro v
    rw [FractionalIdeal.count_mul M v (pow_ne_zero _ hI0) hspan, FractionalIdeal.count_pow,
      FractionalIdeal.count_finsuppProd, Finsupp.ofSupportFinite_coe, count_spanSingleton v ha]
    obtain ⟨k, hk⟩ := hdiv v
    rw [hk, neg_neg, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 (NeZero.ne N))]
    ring
  refine ⟨I, ?_⟩
  calc I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a
      = ∏ᶠ v : HeightOneSpectrum B, (v.asIdeal : FractionalIdeal (nonZeroDivisors B) M) ^
          (FractionalIdeal.count M v (I ^ N * FractionalIdeal.spanSingleton (nonZeroDivisors B) a)) :=
        (FractionalIdeal.finprod_heightOneSpectrum_factorization' M hJ0).symm
    _ = 1 := by simp only [hcount, zpow_zero, finprod_one]

end Bridge

section Assembly

variable {K : Type} [Field K] (A : Type) [CommRing A] [Algebra A K]

/-- **Kummer roots of elements with `N`-divisible valuations are unramified.** -/
theorem root_mem_maxUnram_of_dvd {M : IntermediateField K (AlgebraicClosure K)} (hM : M ∈ unramSet A K)
    [IsDedekindDomain (integralClosure A M)] [IsFractionRing (integralClosure A M) M] {N : ℕ} [NeZero N]
    (hN : IsUnit (N : A)) {a : M} (ha : a ≠ 0)
    (hdiv : ∀ v : HeightOneSpectrum (integralClosure A M), (N : ℤ) ∣ WithZero.log (v.valuation M a))
    {γ : AlgebraicClosure K} (hγ : γ ^ N = (a : AlgebraicClosure K)) : γ ∈ maxUnram A K := by
  refine root_mem_maxUnram A hM hN ha (fun τ => exists_pow_mul_spanSingleton_eq_one
    ((_root_.map_ne_zero τ).2 ha) (fun w => ?_)) hγ
  let σ : integralClosure A M ≃+* integralClosure A M := (τ.restrictScalars A).mapIntegralClosure.toRingEquiv
  have h : w.valuation M (τ a) = (PicDescent.pullH σ w).valuation M a :=
    (PicDescent.valuation_pullH σ τ.toRingEquiv (fun b => rfl) w a).symm
  rw [h]
  exact hdiv _

end Assembly

end

end Kummer
end RamanujanPetersson



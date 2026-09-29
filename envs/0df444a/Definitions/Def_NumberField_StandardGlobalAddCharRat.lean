-- Prove2me | Definitions.Def_NumberField_StandardGlobalAddCharRat
-- name    : NumberField_StandardGlobalAddCharRat
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/26123bc8-623f-5575-ac96-035d735b44c7
-- title:
--   Standard additive character of the adele ring of Q
-- statement:
--   For a prime $p$ the module first records that every $x \in \mathbb{Q}_p$ admits an approximant of the form $a/p^k$ with $a \in \mathbb{Z}$, $k \in \mathbb{N}$ and $\|x - a/p^k\| \le 1$, and that any two such approximants differ by a rational integer (the auxiliary divisibility statement being that $\|a/p^k\| \le 1$ forces $p^k \mid a$). `psiPadicFun` is then $x \mapsto \exp(-2\pi i\,(a/p^k))$ for a chosen approximant, and `psiPadicFun_eq` shows the value is the same for every approximant, so `psiPadic` is a well-defined element of `AddChar ℚ_[p] ℂ`. It equals $1$ on $\|x\| \le 1$, is constant on closed unit balls (hence continuous), and takes the value $\exp(-2\pi i/p) \neq 1$ at $p^{-1}$. For a height-one prime $v$ of $\mathbb{Z}$, `psiV v` is `psiPadic` composed with Mathlib's identification of $\mathbb{Q}_v$ with $\mathbb{Q}_{p}$, $p =$ `primesEquiv v`; it is continuous, trivial on the valuation ring, and nontrivial on the image of the inverse of the natural generator of $v$. `psiFin` is the character of the finite adeles given by the multipliable product $\prod_v \psi_v(x_v)$, the support being finite because an adele is integral outside a finite set; it is trivial on the integral adeles, continuous, and satisfies $\psi_f(q) = \exp(-2\pi i q)$ for $q \in \mathbb{Q}$, proved from the fact that a rational of $p$-adic norm at most $1$ for all $p$ is an integer. At the unique infinite place `psiArchPlace` is $x \mapsto \exp(+2\pi i x)$ through the real embedding of the completion, and `psiArch` their product over infinite places, with $\psi_\infty(q) = \exp(2\pi i q)$. Finally `psiQ` is $x \mapsto \psi_\infty(x_\infty)\psi_f(x_f)$ on $\mathbb{A}_{\mathbb{Q}}$; `isGlobalAddChar_psiQ` supplies the three fields of `IsGlobalAddChar ℚ`: triviality on the image of $\mathbb{Q}$ (the two reciprocity formulas cancel), continuity, and $\psi_{\mathbb{Q}} \neq 1$, witnessed at the archimedean component $1/2$, where the value is $-1$. A helper `singlePlaceAdele v r` is the finite adele with entry $r$ at $v$ and $0$ elsewhere, used to record nontriviality of $\psi_{\mathbb{Q}}$ at each finite place. With these signs ($e^{-2\pi i}$ at the finite places, $e^{+2\pi i}$ at the real place) the character is the complex conjugate of Tate's normalisation.
--
--   **Relation to Mathlib.** Mathlib supplies `AddChar`, the adele ring of a number field, and the identification of the $v$-adic completion of $\mathbb{Q}$ with $\mathbb{Q}_p$; it has no standard additive character of an adele ring, which is what is constructed here for $\mathbb{Q}$.
--
--   **Where it is used.** The character $\psi_{\mathbb{Q}}$ together with its `IsGlobalAddChar` certificate is the additive character entering the Whittaker coefficients of adelic automorphic forms on $\mathrm{GL}_2$ over $\mathbb{Q}$, and hence the Fourier expansions used on the automorphic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_StandardGlobalAddCharRat.lean

import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace NumberField.StandardAddChar

open scoped Real

variable {p : ℕ} [Fact p.Prime]

theorem pPow_dvd_of_norm_le_one (a : ℤ) (k : ℕ)
    (h : ‖((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)‖ ≤ 1) : (p : ℤ) ^ k ∣ a := by
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [norm_div, norm_pow, Padic.norm_p, div_le_one (by positivity)] at h
  have h' : ‖(a : ℚ_[p])‖ ≤ (p : ℝ) ^ (-k : ℤ) := by
    rwa [inv_pow, ← zpow_natCast ((p : ℝ)), ← zpow_neg] at h
  have := (Padic.norm_int_le_pow_iff_dvd a k).mp h'
  exact_mod_cast this

theorem exists_pPow_approx (x : ℚ_[p]) :
    ∃ (a : ℤ) (k : ℕ), ‖x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)‖ ≤ 1 := by
  have hp0 : ((p : ℝ)) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hx : ‖x‖ ≤ 1
  · exact ⟨0, 0, by simpa using hx⟩
  · push Not at hx
    have hx0 : x ≠ 0 := by
      intro h; rw [h, norm_zero] at hx; linarith
    have hvneg : x.valuation < 0 := by
      by_contra hge
      push Not at hge
      have h1 : ‖x‖ ≤ 1 := by
        rw [Padic.norm_eq_zpow_neg_valuation hx0]
        have hp1 : (1 : ℝ) < (p : ℝ) := by
          exact_mod_cast (Fact.out : p.Prime).one_lt
        exact zpow_le_one_of_nonpos₀ (le_of_lt hp1) (by omega)
      linarith
    set k : ℕ := (-x.valuation).toNat with hk
    have hkval : (k : ℤ) = -x.valuation := by
      rw [hk]; exact Int.toNat_of_nonneg (by omega)

    have hykmem : ‖x * (p : ℚ_[p]) ^ k‖ ≤ 1 := by
      rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← zpow_natCast ((p : ℝ)), ← zpow_neg,
        Padic.norm_eq_zpow_neg_valuation hx0, ← zpow_add₀ hp0, hkval]
      simp
    set y : ℤ_[p] := ⟨x * (p : ℚ_[p]) ^ k, hykmem⟩ with hy
    set a : ℤ := (PadicInt.appr y k : ℤ) with ha
    have hspec := PadicInt.appr_spec k y
    rw [Ideal.mem_span_singleton] at hspec
    obtain ⟨c, hc⟩ := hspec
    refine ⟨a, k, ?_⟩
    have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    have hpk : ((p : ℚ_[p]) ^ k) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    have hcoe : ((y - ((PadicInt.appr y k : ℕ) : ℤ_[p])) : ℚ_[p])
        = x * (p : ℚ_[p]) ^ k - ((a : ℚ_[p])) := by
      push_cast [hy, ha]
      ring
    have hxa : x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)
        = ((y - ((PadicInt.appr y k : ℕ) : ℤ_[p])) : ℚ_[p]) / (p : ℚ_[p]) ^ k := by
      rw [hcoe]
      field_simp
    rw [hxa, norm_div, norm_pow, Padic.norm_p, div_le_one (by positivity)]
    have hnormZ : ‖y - ((PadicInt.appr y k : ℕ) : ℤ_[p])‖ ≤ ((p : ℝ))⁻¹ ^ k := by
      rw [hc]
      calc ‖(p : ℤ_[p]) ^ k * c‖ = ‖(p : ℤ_[p]) ^ k‖ * ‖c‖ := norm_mul _ _
      _ ≤ ‖(p : ℤ_[p]) ^ k‖ * 1 :=
            mul_le_mul_of_nonneg_left c.norm_le_one (norm_nonneg _)
      _ = ((p : ℝ))⁻¹ ^ k := by rw [mul_one, norm_pow, PadicInt.norm_p]

    calc ‖((y - ((PadicInt.appr y k : ℕ) : ℤ_[p])) : ℚ_[p])‖
        = ‖y - ((PadicInt.appr y k : ℕ) : ℤ_[p])‖ :=
          PadicInt.padic_norm_e_of_padicInt (y - ((PadicInt.appr y k : ℕ) : ℤ_[p]))
    _ ≤ ((p : ℝ))⁻¹ ^ k := hnormZ

theorem pPow_approx_sub_int (a b : ℤ) (k j : ℕ) (x : ℚ_[p])
    (ha : ‖x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)‖ ≤ 1)
    (hb : ‖x - ((b : ℚ_[p]) / (p : ℚ_[p]) ^ j)‖ ≤ 1) :
    ∃ m : ℤ, (a : ℚ) / (p : ℚ) ^ k - (b : ℚ) / (p : ℚ) ^ j = m := by
  have hpQ : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpQQ : ((p : ℚ)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hd : ‖(((a * p ^ j - b * p ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + j))‖ ≤ 1 := by
    have heq : (((a * p ^ j - b * p ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + j))
        = (x - ((b : ℚ_[p]) / (p : ℚ_[p]) ^ j)) - (x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)) := by
      push_cast
      field_simp
      ring
    rw [heq, sub_eq_add_neg]
    refine le_trans (Padic.nonarchimedean _ _) (max_le hb ?_)
    rw [norm_neg]
    exact ha
  obtain ⟨m, hm⟩ := pPow_dvd_of_norm_le_one (a * p ^ j - b * p ^ k) (k + j) hd
  refine ⟨m, ?_⟩
  have hmQ : (a : ℚ) * (p : ℚ) ^ j - (b : ℚ) * (p : ℚ) ^ k = (p : ℚ) ^ (k + j) * (m : ℚ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℚ) hm
  field_simp
  linear_combination hmQ

def psiPadicFun (x : ℚ_[p]) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
    (((exists_pPow_approx x).choose : ℂ)
      / (p : ℂ) ^ ((exists_pPow_approx x).choose_spec.choose)))

theorem psiPadicFun_eq {x : ℚ_[p]} {a : ℤ} {k : ℕ}
    (h : ‖x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)‖ ≤ 1) :
    psiPadicFun x = Complex.exp (-(2 * Real.pi * Complex.I) * ((a : ℂ) / (p : ℂ) ^ k)) := by
  have hpC : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨m, hm⟩ := pPow_approx_sub_int ((exists_pPow_approx x).choose) a
    ((exists_pPow_approx x).choose_spec.choose) k x
    ((exists_pPow_approx x).choose_spec.choose_spec) h
  unfold psiPadicFun
  have hC : (((exists_pPow_approx x).choose : ℂ)
      / (p : ℂ) ^ ((exists_pPow_approx x).choose_spec.choose))
      = (a : ℂ) / (p : ℂ) ^ k + (m : ℂ) := by
    have hQ := congrArg (Rat.cast (K := ℂ)) hm
    push_cast at hQ
    linear_combination hQ
  rw [hC, mul_add, Complex.exp_add]
  have hone : Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ)) = 1 := by
    rw [show -(2 * Real.pi * Complex.I) * (m : ℂ)
        = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-m)
  rw [hone, mul_one]

theorem psiPadicFun_zero : psiPadicFun (0 : ℚ_[p]) = 1 := by
  rw [psiPadicFun_eq (a := 0) (k := 0) (by simp)]
  simp

theorem psiPadicFun_add (x y : ℚ_[p]) :
    psiPadicFun (x + y) = psiPadicFun x * psiPadicFun y := by
  have hpC : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpQ : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨a, k, ha⟩ := exists_pPow_approx x
  obtain ⟨b, j, hb⟩ := exists_pPow_approx y
  have hsum : ‖(x + y) - (((a * p ^ j + b * p ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + j))‖ ≤ 1 := by
    have heq : (((a * p ^ j + b * p ^ k : ℤ) : ℚ_[p]) / (p : ℚ_[p]) ^ (k + j))
        = ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k) + ((b : ℚ_[p]) / (p : ℚ_[p]) ^ j) := by
      push_cast
      field_simp
      ring
    rw [heq, show (x + y) - (((a : ℚ_[p]) / (p : ℚ_[p]) ^ k) + ((b : ℚ_[p]) / (p : ℚ_[p]) ^ j))
        = (x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)) + (y - ((b : ℚ_[p]) / (p : ℚ_[p]) ^ j)) by ring]
    exact le_trans (Padic.nonarchimedean _ _) (max_le ha hb)
  rw [psiPadicFun_eq hsum, psiPadicFun_eq ha, psiPadicFun_eq hb, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

def psiPadic : AddChar ℚ_[p] ℂ where
  toFun := psiPadicFun
  map_zero_eq_one' := psiPadicFun_zero
  map_add_eq_mul' := psiPadicFun_add

theorem psiPadic_apply (x : ℚ_[p]) : psiPadic x = psiPadicFun x := rfl

theorem psiPadic_eq_one_of_norm_le_one {x : ℚ_[p]} (hx : ‖x‖ ≤ 1) :
    psiPadic x = 1 := by
  rw [psiPadic_apply, psiPadicFun_eq (a := 0) (k := 0) (by simpa using hx)]
  simp

theorem psiPadicFun_eq_of_norm_sub_le_one {x y : ℚ_[p]} (h : ‖y - x‖ ≤ 1) :
    psiPadicFun y = psiPadicFun x := by
  obtain ⟨a, k, ha⟩ := exists_pPow_approx x
  have hy : ‖y - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)‖ ≤ 1 := by
    rw [show y - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)
        = (y - x) + (x - ((a : ℚ_[p]) / (p : ℚ_[p]) ^ k)) by ring]
    exact le_trans (Padic.nonarchimedean _ _) (max_le h ha)
  rw [psiPadicFun_eq hy, psiPadicFun_eq ha]

theorem continuous_psiPadic : Continuous (psiPadic (p := p)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hconst : (fun y : ℚ_[p] => psiPadicFun y) =ᶠ[nhds x] (fun _ => psiPadicFun x) := by
    filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
    exact psiPadicFun_eq_of_norm_sub_le_one (by simpa [dist_eq_norm] using hy)
  exact ContinuousAt.congr continuousAt_const hconst.symm

theorem psiPadic_inv_p :
    psiPadic ((p : ℚ_[p]))⁻¹ = Complex.exp (-(2 * Real.pi * Complex.I) / p) := by
  have hpQ : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [psiPadic_apply, psiPadicFun_eq (a := 1) (k := 1) (by simp [pow_one, one_div])]
  push_cast
  ring_nf

theorem psiPadic_inv_p_ne_one : psiPadic ((p : ℚ_[p]))⁻¹ ≠ 1 := by
  rw [psiPadic_inv_p]
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpC : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  field_simp at hn

  have hZ : (-1 : ℤ) = (p : ℤ) * n := by exact_mod_cast hn
  have hdvd : (p : ℤ) ∣ 1 := ⟨-n, by linear_combination -hZ⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  omega

section PlaceChar

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))

set_option synthInstance.maxHeartbeats 400000 in

def psiV : AddChar (v.adicCompletion ℚ) ℂ where
  toFun x := psiPadic (adicCompletion.padicEquiv v x)
  map_zero_eq_one' := by
    rw [map_zero]
    exact psiPadicFun_zero
  map_add_eq_mul' a b := by
    rw [map_add]
    exact psiPadicFun_add _ _

theorem psiV_apply (x : v.adicCompletion ℚ) :
    psiV v x = psiPadic (adicCompletion.padicEquiv v x) := rfl

theorem continuous_psiV : Continuous (psiV v) :=
  continuous_psiPadic.comp (adicCompletion.padicEquiv v).continuous

theorem psiV_eq_one_of_mem_integers {x : v.adicCompletion ℚ}
    (hx : x ∈ v.adicCompletionIntegers ℚ) : psiV v x = 1 := by
  rw [psiV_apply]
  have hco : adicCompletion.padicEquiv v x
      = ((adicCompletionIntegers.padicIntEquiv v ⟨x, hx⟩ : ℤ_[primesEquiv v]) : ℚ_[primesEquiv v]) := by
    rw [adicCompletionIntegers.coe_padicIntEquiv_apply]
  rw [hco]
  refine psiPadic_eq_one_of_norm_le_one ?_
  rw [PadicInt.padic_norm_e_of_padicInt]
  exact PadicInt.norm_le_one _

theorem psiV_algebraMap_inv_ne_one :
    psiV v (algebraMap ℚ (v.adicCompletion ℚ) ((natGenerator v : ℚ))⁻¹) ≠ 1 := by
  rw [psiV_apply]
  have hcomm : adicCompletion.padicEquiv v
      (algebraMap ℚ (v.adicCompletion ℚ) ((natGenerator v : ℚ))⁻¹)
      = algebraMap ℚ (ℚ_[primesEquiv v]) ((natGenerator v : ℚ))⁻¹ :=
    (adicCompletion.padicEquiv v).commutes _
  rw [hcomm]
  have hval : algebraMap ℚ (ℚ_[primesEquiv v]) ((natGenerator v : ℚ))⁻¹
      = ((primesEquiv v : ℕ) : ℚ_[primesEquiv v])⁻¹ := by
    rw [map_inv₀, eq_ratCast (algebraMap ℚ (ℚ_[primesEquiv v])) ((natGenerator v : ℚ)),
      Rat.cast_natCast]
    rfl
  rw [hval]
  exact psiPadic_inv_p_ne_one

end PlaceChar

section GlobalInt

theorem exists_int_of_forall_norm_le_one (D : ℚ)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ‖(D : ℚ_[ℓ])‖ ≤ 1) : ∃ m : ℤ, D = (m : ℚ) := by
  refine ⟨D.num, ?_⟩
  have hden : D.den = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro ℓ hℓ hdvd
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hD0 : D ≠ 0 := by
      rintro rfl
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp (by simpa using hdvd))

    have hnum : ¬ (ℓ : ℤ) ∣ D.num := by
      intro hc
      have hd1 : ℓ ∣ D.num.natAbs := by
        have := Int.natAbs_dvd_natAbs.mpr hc
        simpa using this
      have hgcd : ℓ ∣ 1 := D.reduced ▸ Nat.dvd_gcd hd1 hdvd
      exact hℓ.one_lt.ne' (Nat.dvd_one.mp hgcd)
    have hvalInt : padicValInt ℓ D.num = 0 := padicValInt.eq_zero_of_not_dvd hnum
    have hvalNat : 1 ≤ padicValNat ℓ D.den :=
      one_le_padicValNat_of_dvd D.den_nz hdvd
    have hvr : padicValRat ℓ D ≤ -1 := by
      rw [padicValRat_def, hvalInt]
      omega

    have hgt : (1 : ℚ) < padicNorm ℓ D := by
      rw [show padicNorm ℓ D = (ℓ : ℚ) ^ (-padicValRat ℓ D) from by
        simp [padicNorm, hD0]]
      refine one_lt_zpow₀ ?_ (by omega)
      exact_mod_cast hℓ.one_lt
    have hle : ((padicNorm ℓ D : ℚ) : ℝ) ≤ 1 := by
      rw [← Padic.eq_padicNorm]
      exact h ℓ
    have : ((padicNorm ℓ D : ℚ) : ℝ) > 1 := by exact_mod_cast hgt
    linarith
  rw [← Rat.num_div_den D, hden]
  simp

end GlobalInt

section FiniteChar

open IsDedekindDomain NumberField

theorem mulSupport_psiV_finite (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    (Function.mulSupport fun v => psiV v (x v)).Finite := by
  refine Set.Finite.subset (Filter.eventually_cofinite.mp x.eventually) ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  by_contra hmem
  simp only [Set.mem_setOf_eq, not_not] at hmem
  exact hv (psiV_eq_one_of_mem_integers v hmem)

def psiFin : AddChar (FiniteAdeleRing (𝓞 ℚ) ℚ) ℂ where
  toFun x := ∏ᶠ v, psiV v (x v)
  map_zero_eq_one' := by
    have h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
        psiV v ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = (1 : ℂ) := fun v => by
      rw [show ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 0 from rfl]
      exact AddChar.map_zero_eq_one _
    rw [finprod_congr h]
    exact finprod_one
  map_add_eq_mul' a b := by
    have h : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
        psiV v ((a + b) v) = psiV v (a v) * psiV v (b v) := fun v => by
      rw [show ((a + b) v) = a v + b v from rfl]
      exact AddChar.map_add_eq_mul _ _ _
    rw [finprod_congr h]
    exact finprod_mul_distrib (mulSupport_psiV_finite a) (mulSupport_psiV_finite b)

theorem psiFin_apply (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    psiFin x = ∏ᶠ v, psiV v (x v) := rfl

theorem psiFin_eq_one_of_forall_mem (x : FiniteAdeleRing (𝓞 ℚ) ℚ)
    (hx : ∀ v, x v ∈ v.adicCompletionIntegers ℚ) : psiFin x = 1 := by
  rw [psiFin_apply, finprod_congr (fun v => psiV_eq_one_of_mem_integers v (hx v))]
  exact finprod_one

theorem isOpen_forall_mem_integers :
    IsOpen {y : FiniteAdeleRing (𝓞 ℚ) ℚ | ∀ v, y v ∈ v.adicCompletionIntegers ℚ} := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (A := fun v : HeightOneSpectrum (𝓞 ℚ) => (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun _ => True)
  simp at h
  exact h

theorem continuous_psiFin : Continuous psiFin := by
  rw [continuous_iff_continuousAt]
  intro x
  have hsub : Continuous fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y - x :=
    continuous_id.sub continuous_const
  have hmem : x ∈ (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y - x) ⁻¹'
      {y | ∀ v, y v ∈ v.adicCompletionIntegers ℚ} := by
    simp only [Set.mem_preimage, sub_self, Set.mem_setOf_eq]
    intro v
    rw [show ((0 : FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 0 from rfl]
    exact zero_mem _
  have hnhds : (fun y : FiniteAdeleRing (𝓞 ℚ) ℚ => y - x) ⁻¹'
      {y | ∀ v, y v ∈ v.adicCompletionIntegers ℚ} ∈ nhds x :=
    (isOpen_forall_mem_integers.preimage hsub).mem_nhds hmem
  have hconst : (fun y => psiFin y) =ᶠ[nhds x] (fun _ => psiFin x) := by
    filter_upwards [hnhds] with y hy
    rw [show y = x + (y - x) by ring, AddChar.map_add_eq_mul,
      psiFin_eq_one_of_forall_mem _ hy, mul_one]
  exact ContinuousAt.congr continuousAt_const hconst.symm

end FiniteChar

section Reciprocity

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

theorem norm_pPow_ratCast_le_one {ℓ ℓ' : ℕ} [Fact ℓ.Prime] [Fact ℓ'.Prime] (hne : ℓ ≠ ℓ')
    (a : ℤ) (k : ℕ) : ‖((((a : ℚ) / (ℓ : ℚ) ^ k : ℚ)) : ℚ_[ℓ'])‖ ≤ 1 := by
  have hcast : ((((a : ℚ) / (ℓ : ℚ) ^ k : ℚ)) : ℚ_[ℓ'])
      = (a : ℚ_[ℓ']) / (ℓ : ℚ_[ℓ']) ^ k := by
    push_cast
    ring
  rw [hcast, norm_div, norm_pow]
  have hone : ‖((ℓ : ℚ_[ℓ']))‖ = 1 := by
    have hcop : Nat.Coprime ℓ' ℓ :=
      (Nat.coprime_primes (Fact.out : ℓ'.Prime) (Fact.out : ℓ.Prime)).mpr (Ne.symm hne)
    have h1 : ‖((ℓ : ℤ_[ℓ']))‖ = 1 := PadicInt.norm_natCast_eq_one_iff.mpr hcop
    calc ‖((ℓ : ℚ_[ℓ']))‖ = ‖(((ℓ : ℤ_[ℓ']) : ℚ_[ℓ']))‖ := by norm_cast
    _ = ‖((ℓ : ℤ_[ℓ']))‖ := PadicInt.padic_norm_e_of_padicInt _
    _ = 1 := h1
  rw [hone, one_pow, div_one]
  exact IsUltrametricDist.norm_intCast_le_one ℚ_[ℓ'] a

set_option maxHeartbeats 800000 in

theorem psiFin_algebraMap (q : ℚ) :
    psiFin (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q)
      = Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ)) := by
  classical
  have hstep1 : psiFin (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q)
      = ∏ᶠ ℓ : Nat.Primes, psiPadic ((q : ℚ_[ℓ.1])) := by
    rw [psiFin_apply]
    have hcong : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ),
        psiV v ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) v)
          = psiPadic ((q : ℚ_[(primesEquiv v).1])) := by
      intro v
      have hdiag : ((algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q) v)
          = algebraMap ℚ (v.adicCompletion ℚ) q := by
        rw [FiniteAdeleRing.algebraMap_apply]
        rfl
      have hcomm : (adicCompletion.padicEquiv v) (algebraMap ℚ (v.adicCompletion ℚ) q)
          = algebraMap ℚ (ℚ_[primesEquiv v]) q := (adicCompletion.padicEquiv v).commutes q
      rw [hdiag, psiV_apply, hcomm, eq_ratCast]
    rw [finprod_congr hcong]
    exact finprod_comp_equiv primesEquiv (f := fun ℓ : Nat.Primes => psiPadic ((q : ℚ_[ℓ.1])))
  rw [hstep1]
  set F : Nat.Primes → ℂ := fun ℓ => psiPadic ((q : ℚ_[ℓ.1])) with hF
  set S : Finset Nat.Primes := q.den.primeFactors.subtype Nat.Prime with hS
  have hSmem : ∀ ℓ' : ℕ, ∀ h : ℓ'.Prime, ((⟨ℓ', h⟩ : Nat.Primes) ∈ S ↔ ℓ' ∣ q.den) := by
    intro ℓ' h
    exact (Finset.mem_subtype).trans ⟨fun hm => (Nat.mem_primeFactors.mp hm).2.1,
      fun hd => Nat.mem_primeFactors.mpr ⟨h, hd, q.den_nz⟩⟩
  have hsupp : Function.mulSupport F ⊆ ↑S := by
    intro ℓ hℓ
    simp only [Function.mem_mulSupport, hF] at hℓ
    by_contra hmem
    apply hℓ
    apply psiPadic_eq_one_of_norm_le_one
    apply Padic.norm_rat_le_one
    intro hdvd
    exact hmem (by
      obtain ⟨ℓ1, h1⟩ := ℓ
      exact Finset.mem_coe.mpr ((hSmem ℓ1 h1).mpr hdvd))
  obtain ⟨c, hc_val, hc_near, hc_far⟩ :
      ∃ c : Nat.Primes → ℚ,
        (∀ ℓ : Nat.Primes, F ℓ = Complex.exp (-(2 * Real.pi * Complex.I) * ((c ℓ : ℚ) : ℂ)))
        ∧ (∀ ℓ : Nat.Primes, ‖((q : ℚ_[ℓ.1])) - (((c ℓ : ℚ)) : ℚ_[ℓ.1])‖ ≤ 1)
        ∧ (∀ (ℓ : Nat.Primes) (ℓ' : ℕ) [Fact ℓ'.Prime], ℓ.1 ≠ ℓ' →
            ‖(((c ℓ : ℚ)) : ℚ_[ℓ'])‖ ≤ 1) := by
    refine ⟨fun ℓ => ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose : ℚ)
      / (ℓ.1 : ℚ) ^ ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose_spec.choose), ?_, ?_, ?_⟩
    · intro ℓ
      show psiPadicFun ((q : ℚ_[ℓ.1])) = _
      rw [psiPadicFun_eq ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose_spec.choose_spec)]
      congr 1
      push_cast
      ring
    · intro ℓ
      have h := (exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose_spec.choose_spec
      have hcast : ((((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose : ℚ)
          / (ℓ.1 : ℚ) ^ ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose_spec.choose) : ℚ) : ℚ_[ℓ.1])
          = ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose : ℚ_[ℓ.1])
            / (ℓ.1 : ℚ_[ℓ.1]) ^ ((exists_pPow_approx ((q : ℚ_[ℓ.1]))).choose_spec.choose) := by
        push_cast
        ring
      rw [hcast]
      exact h
    · intro ℓ ℓ' hinst hne
      exact norm_pPow_ratCast_le_one hne _ _
  calc ∏ᶠ ℓ : Nat.Primes, F ℓ
      = ∏ ℓ ∈ S, F ℓ := finprod_eq_prod_of_mulSupport_subset F hsupp
  _ = ∏ ℓ ∈ S, Complex.exp (-(2 * Real.pi * Complex.I) * ((c ℓ : ℚ) : ℂ)) :=
      Finset.prod_congr rfl (fun ℓ _ => hc_val ℓ)
  _ = Complex.exp (∑ ℓ ∈ S, -(2 * Real.pi * Complex.I) * ((c ℓ : ℚ) : ℂ)) :=
      (Complex.exp_sum S _).symm
  _ = Complex.exp (-(2 * Real.pi * Complex.I) * (((∑ ℓ ∈ S, c ℓ : ℚ)) : ℂ)) := by
      rw [← Finset.mul_sum]
      congr 2
      push_cast
      rfl
  _ = Complex.exp (-(2 * Real.pi * Complex.I) * (q : ℂ)) := by
      have hnorm : ∀ (ℓ' : ℕ) [Fact ℓ'.Prime],
          ‖((q - ∑ ℓ ∈ S, c ℓ : ℚ) : ℚ_[ℓ'])‖ ≤ 1 := by
        intro ℓ' hinst
        have hcast : ((q - ∑ ℓ ∈ S, c ℓ : ℚ) : ℚ_[ℓ'])
            = ((q : ℚ_[ℓ'])) - ∑ ℓ ∈ S, (((c ℓ : ℚ)) : ℚ_[ℓ']) := by
          push_cast
          ring
        rw [hcast]
        have hsumbound : ∀ (T : Finset Nat.Primes), (∀ i ∈ T, (i : Nat.Primes).1 ≠ ℓ') →
            ‖∑ ℓ ∈ T, (((c ℓ : ℚ)) : ℚ_[ℓ'])‖ ≤ 1 := by
          intro T hT
          rcases Finset.eq_empty_or_nonempty T with he | hne
          · simp [he]
          · obtain ⟨i, hi, hle⟩ :=
              IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
                (fun ℓ => (((c ℓ : ℚ)) : ℚ_[ℓ']))
            exact le_trans hle (hc_far i ℓ' (hT i hi))
        by_cases hmem : (⟨ℓ', (Fact.out : ℓ'.Prime)⟩ : Nat.Primes) ∈ S
        · rw [← Finset.add_sum_erase S (fun ℓ => (((c ℓ : ℚ)) : ℚ_[ℓ'])) hmem]
          rw [show ((q : ℚ_[ℓ']))
              - ((((c ⟨ℓ', (Fact.out : ℓ'.Prime)⟩ : ℚ)) : ℚ_[ℓ'])
                + ∑ ℓ ∈ S.erase ⟨ℓ', (Fact.out : ℓ'.Prime)⟩, (((c ℓ : ℚ)) : ℚ_[ℓ']))
              = (((q : ℚ_[ℓ'])) - (((c ⟨ℓ', (Fact.out : ℓ'.Prime)⟩ : ℚ)) : ℚ_[ℓ']))
                + -(∑ ℓ ∈ S.erase ⟨ℓ', (Fact.out : ℓ'.Prime)⟩, (((c ℓ : ℚ)) : ℚ_[ℓ'])) by ring]
          refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
          · exact hc_near ⟨ℓ', (Fact.out : ℓ'.Prime)⟩
          · rw [norm_neg]
            refine hsumbound _ ?_
            intro i hi hcontra
            exact (Finset.mem_erase.mp hi).1 (Subtype.ext hcontra)
        · rw [sub_eq_add_neg]
          refine le_trans (Padic.nonarchimedean _ _) (max_le ?_ ?_)
          · apply Padic.norm_rat_le_one
            intro hdvd
            exact hmem ((hSmem ℓ' (Fact.out : ℓ'.Prime)).mpr hdvd)
          · rw [norm_neg]
            refine hsumbound _ ?_
            intro i hi hcontra
            have hieq : i = (⟨ℓ', (Fact.out : ℓ'.Prime)⟩ : Nat.Primes) :=
              Subtype.ext hcontra
            exact hmem (hieq ▸ hi)

      obtain ⟨m, hm⟩ := exists_int_of_forall_norm_le_one (q - ∑ ℓ ∈ S, c ℓ) hnorm
      have hsumQ : (∑ ℓ ∈ S, c ℓ : ℚ) = q - (m : ℚ) := by linarith [hm]
      have hsum : (((∑ ℓ ∈ S, c ℓ : ℚ)) : ℂ) = (q : ℂ) - (m : ℂ) := by
        rw [hsumQ]
        push_cast
        ring
      rw [hsum, mul_sub, Complex.exp_sub]
      rw [show -(2 * Real.pi * Complex.I) * (m : ℂ)
          = ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      rw [Complex.exp_int_mul_two_pi_mul_I]
      rw [div_one]

end Reciprocity

section ArchChar

open NumberField

def psiArchPlace (v : InfinitePlace ℚ) : AddChar v.Completion ℂ where
  toFun x := Complex.exp ((2 * Real.pi * Complex.I) *
    ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℂ))
  map_zero_eq_one' := by
    rw [map_zero]
    push_cast
    rw [mul_zero, Complex.exp_zero]
  map_add_eq_mul' a b := by
    rw [map_add]
    push_cast
    rw [mul_add, Complex.exp_add]

theorem psiArchPlace_apply (v : InfinitePlace ℚ) (x : v.Completion) :
    psiArchPlace v x = Complex.exp ((2 * Real.pi * Complex.I) *
      ((InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x : ℝ) : ℂ)) :=
  rfl

def psiArch : AddChar (InfiniteAdeleRing ℚ) ℂ where
  toFun x := ∏ᶠ v, psiArchPlace v (x v)
  map_zero_eq_one' := by
    have h : ∀ v : InfinitePlace ℚ, psiArchPlace v ((0 : InfiniteAdeleRing ℚ) v) = 1 := fun v => by
      rw [show ((0 : InfiniteAdeleRing ℚ) v) = 0 from rfl]
      exact AddChar.map_zero_eq_one _
    rw [finprod_congr h]
    exact finprod_one
  map_add_eq_mul' a b := by
    have h : ∀ v : InfinitePlace ℚ, psiArchPlace v ((a + b) v)
        = psiArchPlace v (a v) * psiArchPlace v (b v) := fun v => by
      rw [show ((a + b) v) = a v + b v from rfl]
      exact AddChar.map_add_eq_mul _ _ _
    rw [finprod_congr h]
    exact finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)

theorem psiArch_apply (x : InfiniteAdeleRing ℚ) :
    psiArch x = ∏ᶠ v, psiArchPlace v (x v) := rfl

theorem continuous_psiArch : Continuous psiArch := by
  show Continuous fun x : InfiniteAdeleRing ℚ => ∏ᶠ v, psiArchPlace v (x v)
  have heq : (fun x : InfiniteAdeleRing ℚ => ∏ᶠ v, psiArchPlace v (x v))
      = fun x => ∏ v : InfinitePlace ℚ, psiArchPlace v (x v) := by
    funext x
    exact finprod_eq_prod_of_fintype _
  rw [heq]
  refine continuous_finsetProd _ (fun v _ => ?_)
  have hemb : Continuous (InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal v)) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).continuous
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp (hemb.comp (continuous_apply v))))

theorem psiArch_algebraMap (q : ℚ) :
    psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) q)
      = Complex.exp ((2 * Real.pi * Complex.I) * (q : ℂ)) := by
  have h1 : psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) q)
      = psiArchPlace default ((algebraMap ℚ (InfiniteAdeleRing ℚ) q) default) := by
    rw [psiArch_apply]
    exact finprod_unique _
  have h2 : ((algebraMap ℚ (InfiniteAdeleRing ℚ) q) default)
      = algebraMap ℚ ((default : InfinitePlace ℚ).Completion) q := rfl
  rw [h1, h2, psiArchPlace_apply]
  have h3 : InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (IsTotallyReal.isReal (default : InfinitePlace ℚ))
      (algebraMap ℚ ((default : InfinitePlace ℚ).Completion) q) = (q : ℝ) := by
    simp
  rw [h3]
  push_cast
  ring_nf

end ArchChar

section FullChar

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

def psiQ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ where
  toFun x := psiArch x.1 * psiFin x.2
  map_zero_eq_one' := by
    rw [show ((0 : AdeleRing (𝓞 ℚ) ℚ).1) = 0 from rfl,
      show ((0 : AdeleRing (𝓞 ℚ) ℚ).2) = 0 from rfl,
      AddChar.map_zero_eq_one, AddChar.map_zero_eq_one, mul_one]
  map_add_eq_mul' a b := by
    rw [show ((a + b).1) = a.1 + b.1 from rfl,
      show ((a + b).2) = a.2 + b.2 from rfl,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    ring

theorem psiQ_apply (x : AdeleRing (𝓞 ℚ) ℚ) : psiQ x = psiArch x.1 * psiFin x.2 := rfl

theorem continuous_psiQ : Continuous psiQ := by
  show Continuous fun x : AdeleRing (𝓞 ℚ) ℚ => psiArch x.1 * psiFin x.2
  exact (continuous_psiArch.comp continuous_fst).mul (continuous_psiFin.comp continuous_snd)

theorem psiQ_algebraMap (q : ℚ) : psiQ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q) = 1 := by
  have h1 : ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).1)
      = algebraMap ℚ (InfiniteAdeleRing ℚ) q := rfl
  have h2 : ((algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ) q).2)
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q := rfl
  rw [psiQ_apply, h1, h2, psiArch_algebraMap, psiFin_algebraMap, ← Complex.exp_add]
  rw [show (2 * Real.pi * Complex.I) * (q : ℂ)
      + -(2 * Real.pi * Complex.I) * (q : ℂ) = 0 by ring]
  exact Complex.exp_zero

theorem psiQ_ne_one : psiQ ≠ 1 := by
  intro hcontra
  have h := congrArg (fun ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ =>
    ψ ((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2), 0))) hcontra
  simp only [AddChar.one_apply] at h
  rw [psiQ_apply] at h
  rw [show ((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2),
      (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : AdeleRing (𝓞 ℚ) ℚ).1
      = algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2) from rfl] at h
  rw [show ((algebraMap ℚ (InfiniteAdeleRing ℚ) ((1 : ℚ)/2),
      (0 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : AdeleRing (𝓞 ℚ) ℚ).2
      = (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) from rfl] at h
  rw [psiArch_algebraMap, AddChar.map_zero_eq_one, mul_one] at h
  rw [show (2 * Real.pi * Complex.I) * (((1 : ℚ)/2 : ℚ) : ℂ)
      = Real.pi * Complex.I by push_cast; ring] at h
  rw [Complex.exp_pi_mul_I] at h
  norm_num at h

open Classical in

def singlePlaceAdele (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    FiniteAdeleRing (𝓞 ℚ) ℚ :=
  ⟨fun w => if w = v then algebraMap ℚ (w.adicCompletion ℚ) r else 0, by
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton v) ?_
    intro w hw
    simp only [Set.mem_setOf_eq] at hw
    by_contra hne
    simp only [Set.mem_singleton_iff] at hne
    apply hw
    rw [if_neg hne]
    exact zero_mem _⟩

open Classical in
theorem singlePlaceAdele_apply (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (r : ℚ)
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    (singlePlaceAdele v r) w = if w = v then algebraMap ℚ (w.adicCompletion ℚ) r else 0 :=
  rfl

open Classical in

theorem psiFin_singlePlaceAdele (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    psiFin (singlePlaceAdele v r) = psiV v (algebraMap ℚ (v.adicCompletion ℚ) r) := by
  rw [psiFin_apply]
  have hsingle := finprod_eq_single
    (fun w => psiV w ((singlePlaceAdele v r) w)) v
    (fun w hw => by
      show psiV w ((singlePlaceAdele v r) w) = 1
      rw [singlePlaceAdele_apply, if_neg hw]
      exact AddChar.map_zero_eq_one _)
  rw [hsingle]
  show psiV v ((singlePlaceAdele v r) v) = _
  rw [singlePlaceAdele_apply, if_pos rfl]

theorem psiQ_singlePlaceAdele_ne_one (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    psiQ ((0 : InfiniteAdeleRing ℚ), singlePlaceAdele v ((natGenerator v : ℚ))⁻¹) ≠ 1 := by
  rw [psiQ_apply]
  rw [show (((0 : InfiniteAdeleRing ℚ),
      singlePlaceAdele v ((natGenerator v : ℚ))⁻¹) : AdeleRing (𝓞 ℚ) ℚ).1
      = (0 : InfiniteAdeleRing ℚ) from rfl]
  rw [show (((0 : InfiniteAdeleRing ℚ),
      singlePlaceAdele v ((natGenerator v : ℚ))⁻¹) : AdeleRing (𝓞 ℚ) ℚ).2
      = singlePlaceAdele v ((natGenerator v : ℚ))⁻¹ from rfl]
  rw [AddChar.map_zero_eq_one, one_mul, psiFin_singlePlaceAdele]
  exact psiV_algebraMap_inv_ne_one v

end FullChar

section InstanceLine

open AutomorphicForm

theorem isGlobalAddChar_psiQ : IsGlobalAddChar ℚ psiQ where
  principalInvariant := psiQ_algebraMap
  continuous := continuous_psiQ
  nontrivial := psiQ_ne_one

end InstanceLine

end NumberField.StandardAddChar

end



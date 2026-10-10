-- Prove2me | solution 1 for ArtinPrimitiveRoots.abs_card_specialLinearGroup_box_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:02:29.744507+00:00
-- url     : https://prove2.me/submissions/fa047866-16c4-4e9d-856e-6ed12963a8e7

import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Mathlib
import Theorems.Thm_ArtinPrimitiveRoots_abs_card_box_mul_sub_mod_le

section
/-! # L102K: the Kloosterman fourth moment ([21] Lemma 3.3, (3.24))

`K_m(h, k) = ∑_{y ∈ (ℤ/m)ˣ} e((h y + k y⁻¹)/m)`. Orthogonality gives
`∑_{h,k} |K_m(h,k)|⁴ = m² T_m`, where `T_m` counts unit quadruples with equal sums and equal
inverse sums, and `T_m ≤ 2 τ₃(m) m²`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

/-- `#{x ∈ ℤ/m : d ∣ x.val} = m/d` for `d ∣ m`. -/
lemma card_dvd_val (m d : ℕ) [NeZero m] (hd0 : 0 < d) (hd : d ∣ m) :
    #{x : ZMod m | d ∣ x.val} = m / d := by
  classical
  have him : (Finset.univ.filter fun x : ZMod m => d ∣ x.val).image ZMod.val =
      (Finset.range (m / d)).image (· * d) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨x, ⟨j, hj⟩, rfl⟩
      refine ⟨j, ?_, by rw [hj, mul_comm]⟩
      have hlt := ZMod.val_lt x
      rw [hj] at hlt
      rw [Nat.lt_div_iff_mul_lt' hd]
      linarith [mul_comm d j]
    · rintro ⟨j, hj, rfl⟩
      have hlt : j * d < m := by
        rw [Nat.lt_div_iff_mul_lt' hd] at hj; rw [mul_comm]; exact hj
      refine ⟨(j * d : ℕ), ?_, ?_⟩
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]; exact Dvd.intro_left j rfl
      · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  have h1 := congrArg Finset.card him
  rw [Finset.card_image_of_injective _ (ZMod.val_injective m),
    Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_right hd0 h),
    Finset.card_range] at h1
  exact h1

/-! ### The pointwise bound -/

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: completion of a box count in `(ℤ/m)²`

For a finite `Λ ⊆ (ℤ/m)²` and finite sets of integers `I, J`,
`#{(t, s) ∈ I × J : (t, s) mod m ∈ Λ} = m⁻² ∑_{h,k} Î(h) Ĵ(k) Λ̂(h,k)`, with
`Î(h) = ∑_{t ∈ I} e(ht/m)` and `Λ̂(h,k) = ∑_{(x,y) ∈ Λ} e(−(hx + ky)/m)`. For an integer
interval, `|Î(h)| ≤ m/(2 min(h, m − h))` for `h ≠ 0`. This replaces the smoothed-box
discrepancy (3.27) of [21]. -/

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

/-! ### The geometric sum -/

/-! ### The weighted sum `∑_{h ≠ 0} wt(h) (h, m)` -/

/-! ### The completion identity -/

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: Fourier coefficients of the residue hyperbola ([21] (3.28))

Modulo `m₁ = n S₁` (with `S₁ ∣ n`, `S₂` coprime to `m₁`, `a` a unit) the set
`Λ = {(t, s) : S₁ ∣ t, (x₀ + S₂ t)(y₀ + S₂ s) = a}` has Fourier coefficients
`S₁ Λ̂(h,k) = ∑_{j < S₁} e(c_j) K_{m₁}((jn − h)σ, −kσa)`, `σ = S₂⁻¹`, so
`|Λ̂(h,k)|⁴ ≤ 2 d(m₁)³ m₁³ S₁ (k, m₁)` and the same with `(h, m₁)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset

noncomputable section

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the number of points on the residue hyperbola ([21] (3.26))

`#Λ = ∑_{l ∣ n, (l, S) = 1} μ(l) n/l`, where `Λ = hyperSet n S₁ S₂ x₀ y₀ a`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- `∑_{l ∣ n, l ∣ z} μ(l) = 1[(z, n) = 1]`. -/
lemma sum_moebius_dvd (n : ℕ) (hn : 0 < n) (z : ℤ) :
    ∑ l ∈ n.divisors, (if (l : ℤ) ∣ z then μ l else 0) = if IsCoprime z (n : ℤ) then 1 else 0 := by
  have key : ∑ l ∈ n.divisors, (if (l : ℤ) ∣ z then μ l else 0) =
      ∑ l ∈ (Int.gcd z n).divisors, μ l := by
    rw [← Finset.sum_filter]
    congr 1
    ext l
    simp only [Finset.mem_filter, Nat.mem_divisors]
    have hg : Int.gcd z n ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hn.ne'))
    rw [Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hl, _⟩, hz⟩
      refine ⟨?_, hg⟩
      rw [Int.gcd, Int.natAbs_natCast]
      exact Nat.dvd_gcd hz hl
    · rintro ⟨hl, _⟩
      rw [Int.gcd, Int.natAbs_natCast] at hl
      exact ⟨⟨Nat.dvd_trans hl (Nat.gcd_dvd_right _ _), hn.ne'⟩,
        Nat.dvd_trans hl (Nat.gcd_dvd_left _ _)⟩
  rw [key, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  by_cases h : IsCoprime z (n : ℤ)
  · rw [if_pos h, if_pos (Int.isCoprime_iff_gcd_eq_one.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (Int.isCoprime_iff_gcd_eq_one.mpr h'))]

/-- `#{r < n : r ≡ c (mod l)} = n/l` for `l ∣ n`, `c < l`. -/
lemma card_range_mod_eq (n l c : ℕ) (hl : 0 < l) (hln : l ∣ n) (hc : c < l) :
    #((range n).filter (fun r => r % l = c)) = n / l := by
  obtain ⟨q, rfl⟩ := hln
  rw [Nat.mul_div_cancel_left _ hl]
  calc #((range (l * q)).filter (fun r => r % l = c)) = #(range q) := by
        refine Finset.card_nbij' (fun r => r / l) (fun i => c + l * i) ?_ ?_ ?_ ?_
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr ⊢
          rw [Nat.div_lt_iff_lt_mul hl]; linarith [mul_comm l q, hr.1]
        · intro i hi
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi ⊢
          refine ⟨?_, ?_⟩
          · have : i + 1 ≤ q := hi
            nlinarith
          · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
        · intro r hr
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hr
          rw [← hr.2]; exact Nat.mod_add_div r l
        · intro i _
          show (c + l * i) / l = i
          rw [Nat.add_mul_div_left _ _ hl, Nat.div_eq_of_lt hc, zero_add]
    _ = q := Finset.card_range q

/-- For `l ∣ n`: `#{r < n : l ∣ x₀ + S r}` is `n/l` if `(l, S) = 1` and `0` otherwise, provided
`x₀` is coprime to every prime dividing both `n` and `S`. -/
lemma card_range_dvd (n S l : ℕ) (hl : 0 < l) (hln : l ∣ n) (x₀ : ℤ)
    (hx₀ : IsCoprime x₀ (Nat.gcd n S : ℤ)) :
    #((range n).filter (fun r : ℕ => (l : ℤ) ∣ x₀ + S * r)) =
      if Nat.Coprime l S then n / l else 0 := by
  classical
  split_ifs with hcop
  · -- `S` is a unit mod `l`
    have : NeZero l := ⟨hl.ne'⟩
    set Su : (ZMod l)ˣ := ZMod.unitOfCoprime S hcop.symm
    set c : ZMod l := -(x₀ : ZMod l) * ((Su⁻¹ : (ZMod l)ˣ) : ZMod l)
    have hiff : ∀ r : ℕ, (l : ℤ) ∣ x₀ + S * r ↔ r % l = c.val := by
      intro r
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      have hSu : ((Su : (ZMod l)ˣ) : ZMod l) = (S : ZMod l) := ZMod.coe_unitOfCoprime _ _
      constructor
      · intro h
        have : (r : ZMod l) = c := by
          simp only [c]
          rw [← hSu] at h
          have h2 := congrArg (· * ((Su⁻¹ : (ZMod l)ˣ) : ZMod l)) h
          simp only [zero_mul] at h2
          rw [add_mul, mul_assoc, mul_comm (r : ZMod l), ← mul_assoc, Units.mul_inv, one_mul] at h2
          linear_combination h2
        rw [← this, ZMod.val_natCast]
      · intro h
        have : (r : ZMod l) = c := by
          rw [← ZMod.natCast_zmod_val c, ← h, ZMod.natCast_mod]
        rw [this]
        simp only [c]
        rw [← hSu]
        have := Su.mul_inv
        linear_combination (-(x₀ : ZMod l)) * this
    rw [Finset.filter_congr fun r _ => hiff r]
    exact card_range_mod_eq n l c.val hl hln (ZMod.val_lt c)
  · -- a common prime `p ∣ l, S` divides `x₀ + S r` only if it divides `x₀`
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro r _ hdiv
    obtain ⟨p, hp, hpl, hpS⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hpg : p ∣ Nat.gcd n S := Nat.dvd_gcd (hpl.trans hln) hpS
    have hpx : (p : ℤ) ∣ x₀ := by
      have h1 : (p : ℤ) ∣ x₀ + S * r := (Int.natCast_dvd_natCast.mpr hpl).trans hdiv
      have h2 : (p : ℤ) ∣ (S : ℤ) * r := (Int.natCast_dvd_natCast.mpr hpS).mul_right _
      have := dvd_sub h1 h2
      simpa using this
    have hpu : IsUnit (p : ℤ) := by
      have hpg' : (p : ℤ) ∣ (Nat.gcd n S : ℤ) := Int.natCast_dvd_natCast.mpr hpg
      exact hx₀.isUnit_of_dvd' hpx hpg'
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hpu
    exact hp.one_lt.ne' hpu

/-- `#{r < n : (x₀ + S r, n) = 1} = ∑_{l ∣ n, (l,S) = 1} μ(l) n/l`. -/
lemma card_range_coprime (n S : ℕ) (hn : 0 < n) (x₀ : ℤ) (hx₀ : IsCoprime x₀ (Nat.gcd n S : ℤ)) :
    ((#((range n).filter (fun r : ℕ => IsCoprime (x₀ + S * r) (n : ℤ))) : ℕ) : ℤ) =
      ∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ) := by
  classical
  rw [Finset.card_filter, Nat.cast_sum]
  have h1 : ∀ r ∈ range n, (((if IsCoprime (x₀ + S * r) (n : ℤ) then 1 else 0 : ℕ)) : ℤ) =
      ∑ l ∈ n.divisors, (if (l : ℤ) ∣ x₀ + S * r then μ l else 0) := by
    intro r _
    rw [sum_moebius_dvd n hn]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hln : l ∣ n := Nat.dvd_of_mem_divisors hl
  have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hln hn
  rw [← Finset.sum_filter, Finset.sum_const, card_range_dvd n S l hl0 hln x₀ hx₀, nsmul_eq_mul]
  split_ifs <;> simp [mul_comm]

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the fibre count ([21] (3.25)–(3.27))

For `n ≥ 1`, squarefree `S`, `a` coprime to `n` with `a ≡ x₀y₀ (S)`, and integer intervals
`[A₁, B₁)`, `[A₂, B₂)`:

`#{(x, y) : x ≡ x₀, y ≡ y₀ (S), nS ∣ xy − a} = (B₁−A₁)(B₂−A₂) M(n)/(nS)² + O(error)`,

`M(n) = ∑_{l ∣ n, (l,S)=1} μ(l) n/l`. The proof splits `S = S₁S₂` with `S₁ = (S, n)`, substitutes
`x = x₀ + S₂t`, `y = y₀ + S₂s`, and applies the completion bound to `hyperSet` modulo `nS₁`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The arithmetic of `S = S₁ S₂` -/

/-! ### The substituted interval -/

/-! ### The substitution is a bijection -/

end

end ArtinPrimitiveRoots.L102K

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

noncomputable section

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the Euler-factor average and the constant `1/ζ(2)`

`P(S) = ∑_{(l,S)=1} μ(l)/l²` and `J(S) = ∑_{d ∣ S} μ(d)/d²` satisfy `J(S) P(S) = 6/π²`, and
`∑_{A ≤ u < B, u ≡ u₀ (S)} ∑_{l ∣ u, (l,S)=1} μ(l)/l = (B − A)/S · P(S) + O(1 + log B)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- `μ(n)/n²`. -/
def mu2 (n : ℕ) : ℝ := (μ n : ℝ) / (n : ℝ) ^ 2

/-- `P(S) = ∑_{(l,S)=1} μ(l)/l²`. -/
def PS (S : ℕ) : ℝ := ∑' n : ℕ, if Nat.Coprime n S then mu2 n else 0

/-- `J(S) = ∑_{d ∣ S} μ(d)/d²`. -/
def JS (S : ℕ) : ℝ := ∑ d ∈ S.divisors, mu2 d

lemma abs_moebius_real_le (n : ℕ) : |(μ n : ℝ)| ≤ 1 := by
  have := abs_moebius_le_one (n := n)
  rw [← Int.cast_abs]
  exact_mod_cast this

lemma abs_mu2_le (n : ℕ) : |mu2 n| ≤ 1 / (n : ℝ) ^ 2 := by
  rw [mu2, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)]
  exact div_le_div_of_nonneg_right (abs_moebius_real_le n) (by positivity)

lemma summable_inv_sq : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr one_lt_two

lemma summable_of_le_mu2 {f : ℕ → ℝ} (h : ∀ n, |f n| ≤ |mu2 n|) : Summable f :=
  Summable.of_norm_bounded summable_inv_sq fun n => by
    rw [Real.norm_eq_abs]; exact (h n).trans (abs_mu2_le n)

lemma mu2_zero : mu2 0 = 0 := by simp [mu2]

/-- `∑ μ(n)/n² = 6/π²`. -/
theorem tsum_mu2 : ∑' n : ℕ, mu2 n = 6 / π ^ 2 := by
  have h := LSeries_zeta_mul_Lseries_moebius (s := 2) (by norm_num)
  rw [LSeries_zeta_eq_riemannZeta (by norm_num), riemannZeta_two] at h
  have hL : LSeries (fun n => ((μ n : ℤ) : ℂ)) 2 = ((∑' n : ℕ, mu2 n : ℝ) : ℂ) := by
    rw [LSeries, Complex.ofReal_tsum]
    congr 1
    ext n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [mu2]
    · rw [LSeries.term_of_ne_zero hn.ne', mu2]
      have : ((n : ℂ) ^ (2 : ℂ)) = ((n : ℝ) ^ 2 : ℝ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
      rw [this]; push_cast; ring
  rw [hL] at h
  have hpi0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h3 : ((∑' n : ℕ, mu2 n : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by
    field_simp
    linear_combination 6 * h
  have h4 : ((6 / π ^ 2 : ℝ) : ℂ) = 6 / (π : ℂ) ^ 2 := by push_cast; ring
  exact_mod_cast h3.trans h4.symm

/-- For squarefree `n ≠ 0` and `d ∣ S`: `d ∣ n ∧ (n/d, S) = 1 ↔ d = (n, S)`. -/
lemma dvd_coprime_iff (n S d : ℕ) (hn : Squarefree n) (hn0 : n ≠ 0) (hdS : d ∣ S) :
    (d ∣ n ∧ Nat.Coprime (n / d) S) ↔ d = Nat.gcd n S := by
  constructor
  · rintro ⟨hdn, hcop⟩
    have hdg : d ∣ Nat.gcd n S := Nat.dvd_gcd hdn hdS
    obtain ⟨e, he⟩ := hdg
    have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at hdn; exact hn0 hdn)
    have hen : e ∣ n / d := by
      have hgn : Nat.gcd n S ∣ n := Nat.gcd_dvd_left n S
      rw [he] at hgn
      obtain ⟨k, hk⟩ := hgn
      rw [hk, mul_assoc, Nat.mul_div_cancel_left _ hd0]
      exact Dvd.intro k rfl
    have heS : e ∣ S := by
      have : e ∣ Nat.gcd n S := by rw [he]; exact Dvd.intro_left d rfl
      exact this.trans (Nat.gcd_dvd_right n S)
    have he1 : e = 1 := Nat.eq_one_of_dvd_coprimes hcop hen heS
    rw [he, he1, mul_one]
  · rintro rfl
    refine ⟨Nat.gcd_dvd_left n S, ?_⟩
    apply Nat.coprime_of_dvd
    intro p hp hpn hpS
    have hg0 : 0 < Nat.gcd n S := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    have hpn' : p ∣ n := hpn.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left n S))
    have hpg : p ∣ Nat.gcd n S := Nat.dvd_gcd hpn' hpS
    have hsq : p * p ∣ n := by
      have := Nat.mul_dvd_mul hpn hpg
      rwa [Nat.div_mul_cancel (Nat.gcd_dvd_left n S)] at this
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hn p hsq))

/-- **`J(S) P(S) = 6/π²`.** -/
theorem JS_mul_PS (S : ℕ) (hS : 0 < S) : JS S * PS S = 6 / π ^ 2 := by
  classical
  set c : ℕ → ℝ := fun n => if Nat.Coprime n S then mu2 n else 0 with hc
  have hcs : Summable c := summable_of_le_mu2 fun n => by
    simp only [c]; split_ifs <;> simp
  let F : ℕ → ℕ → ℝ := fun d n => if d ∣ n ∧ Nat.Coprime (n / d) S then mu2 n else 0
  have hFs : ∀ d, Summable (F d) := fun d => summable_of_le_mu2 fun n => by
    simp only [F]; split_ifs <;> simp
  have hstep : ∀ d ∈ S.divisors, mu2 d * PS S = ∑' n, F d n := by
    intro d hd
    have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdS hS
    rw [PS, ← tsum_mul_left]
    have hinj : Function.Injective (fun l : ℕ => d * l) := fun a b h =>
      Nat.eq_of_mul_eq_mul_left hd0 h
    have hsupp : Function.support (F d) ⊆ Set.range (fun l : ℕ => d * l) := by
      intro n hn
      simp only [Function.mem_support, F] at hn
      split_ifs at hn with h
      · exact ⟨n / d, Nat.mul_div_cancel' h.1⟩
      · exact absurd rfl hn
    symm
    rw [← hinj.tsum_eq (f := F d) hsupp]
    · refine tsum_congr fun l => ?_
      simp only [F, Nat.mul_div_cancel_left _ hd0, dvd_mul_right, true_and]
      split_ifs with hl
      · have hdl : Nat.Coprime d l := Nat.Coprime.coprime_dvd_left hdS hl.symm
        simp only [mu2]
        rw [isMultiplicative_moebius.map_mul_of_coprime hdl]
        push_cast; ring
      · ring
  have hsum : ∀ n, ∑ d ∈ S.divisors, F d n = mu2 n := by
    intro n
    by_cases hmu : μ n = 0
    · have : mu2 n = 0 := by simp [mu2, hmu]
      rw [this]
      exact Finset.sum_eq_zero fun d _ => by simp only [F]; split_ifs <;> simp [this]
    · have hsq : Squarefree n := moebius_ne_zero_iff_squarefree.mp hmu
      have hn0 : n ≠ 0 := by rintro rfl; simp at hmu
      rw [Finset.sum_eq_single (Nat.gcd n S)]
      · simp only [F]
        rw [if_pos ((dvd_coprime_iff n S _ hsq hn0 (Nat.gcd_dvd_right n S)).mpr rfl)]
      · intro d hd hne
        simp only [F]
        rw [if_neg]
        intro h
        exact hne ((dvd_coprime_iff n S d hsq hn0 (Nat.dvd_of_mem_divisors hd)).mp h)
      · intro h
        exact absurd (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n S, hS.ne'⟩) h
  calc JS S * PS S = ∑ d ∈ S.divisors, mu2 d * PS S := by rw [JS, Finset.sum_mul]
    _ = ∑ d ∈ S.divisors, ∑' n, F d n := Finset.sum_congr rfl hstep
    _ = ∑' n, ∑ d ∈ S.divisors, F d n := (Summable.tsum_finsetSum fun d _ => hFs d).symm
    _ = ∑' n, mu2 n := tsum_congr hsum
    _ = 6 / π ^ 2 := tsum_mu2

/-- `∑_{i ≥ 0} 1/(i + B)² ≤ 2/B`. -/
lemma tsum_inv_sq_shift_le (B : ℕ) (hB : 1 ≤ B) :
    ∑' i : ℕ, 1 / ((i + B : ℕ) : ℝ) ^ 2 ≤ 2 / (B : ℝ) := by
  refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N => ?_
  have h1 : ∑ i ∈ range N, 1 / ((i + B : ℕ) : ℝ) ^ 2 =
      ∑ j ∈ Finset.Ioo (B - 1) (B + N), ((j : ℝ) ^ 2)⁻¹ := by
    have hIoo : Finset.Ioo (B - 1) (B + N) = Finset.Ico B (B + N) := by
      ext j; simp only [Finset.mem_Ioo, Finset.mem_Ico]; omega
    rw [hIoo, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun i _ => ?_
    rw [one_div, add_comm i B]
  rw [h1]
  have h2 := sum_Ioo_inv_sq_le (α := ℝ) (B - 1) (B + N)
  have h3 : ((B - 1 : ℕ) : ℝ) + 1 = B := by
    rw [Nat.cast_sub hB]; push_cast; ring
  rw [h3] at h2
  exact h2

/-- **The tail of `P(S)`**: `|∑_{l < B, (l,S)=1} μ(l)/l² − P(S)| ≤ 2/B`. -/
theorem abs_partial_PS_sub_le (S B : ℕ) (hB : 1 ≤ B) :
    |∑ l ∈ range B, (if Nat.Coprime l S then mu2 l else 0) - PS S| ≤ 2 / (B : ℝ) := by
  set c : ℕ → ℝ := fun n => if Nat.Coprime n S then mu2 n else 0 with hc
  have hcs : Summable c := summable_of_le_mu2 fun n => by
    simp only [c]; split_ifs <;> simp
  have hsplit := hcs.sum_add_tsum_nat_add B
  have hPS : PS S = ∑' n, c n := rfl
  have e : ∑ l ∈ range B, c l - PS S = -∑' i, c (i + B) := by
    rw [hPS, ← hsplit]; ring
  rw [e, abs_neg]
  have hs2 : Summable (fun i => ‖c (i + B)‖) :=
    (summable_nat_add_iff (f := fun n => ‖c n‖) B).mpr hcs.norm
  calc |∑' i, c (i + B)| = ‖∑' i, c (i + B)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' i, ‖c (i + B)‖ := norm_tsum_le_tsum_norm hs2
    _ ≤ ∑' i : ℕ, 1 / ((i + B : ℕ) : ℝ) ^ 2 := by
        refine Summable.tsum_le_tsum (fun i => ?_) hs2 ?_
        · rw [Real.norm_eq_abs]
          simp only [c]
          split_ifs
          · exact abs_mu2_le _
          · simp only [abs_zero]; positivity
        · have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) B).mpr summable_inv_sq
          simpa using this
    _ ≤ 2 / (B : ℝ) := tsum_inv_sq_shift_le B hB

/-- CRT: for `(l, S) = 1`, `S ∣ u − u₀ ∧ l ∣ u` is one residue class mod `lS`. -/
lemma exists_crt (l S : ℕ) (hcop : Nat.Coprime l S) (u₀ : ℤ) :
    ∃ w : ℤ, ∀ u : ℤ, ((S : ℤ) ∣ u - u₀ ∧ (l : ℤ) ∣ u) ↔ u ≡ w [ZMOD (l * S : ℕ)] := by
  have hc : IsCoprime (l : ℤ) (S : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨x, y, hxy⟩ := hc
  refine ⟨u₀ * x * l, fun u => ?_⟩
  rw [Int.modEq_iff_dvd]
  push_cast
  constructor
  · rintro ⟨h1, h2⟩
    have hl : (l : ℤ) ∣ u₀ * x * l - u := dvd_sub (Dvd.intro_left _ rfl) h2
    have hS : (S : ℤ) ∣ u₀ * x * l - u := by
      have : u₀ * x * l - u = -(u - u₀) - u₀ * y * S := by linear_combination u₀ * hxy
      rw [this]
      exact dvd_sub (dvd_neg.mpr h1) (Dvd.intro_left _ rfl)
    exact (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd hl hS
  · intro h
    have hl : (l : ℤ) ∣ u₀ * x * l - u := (Dvd.intro _ rfl).trans h
    have hS : (S : ℤ) ∣ u₀ * x * l - u := (Dvd.intro_left _ rfl).trans h
    refine ⟨?_, ?_⟩
    · have : u - u₀ = -(u₀ * x * l - u) - u₀ * y * S := by linear_combination u₀ * hxy
      rw [this]
      exact dvd_sub (dvd_neg.mpr hS) (Dvd.intro_left _ rfl)
    · have : u = u₀ * x * l - (u₀ * x * l - u) := by ring
      rw [this]
      exact dvd_sub (Dvd.intro_left _ rfl) hl

/-- `#{A ≤ u < B : S ∣ u − u₀, l ∣ u} = (B − A)/(lS) + O(1)` for `(l, S) = 1`. -/
lemma abs_card_progression_sub_le (l S : ℕ) (hl : 0 < l) (hS : 0 < S) (hcop : Nat.Coprime l S)
    (u₀ A B : ℤ) (hAB : A ≤ B) :
    |((#((Finset.Ico A B).filter (fun u => (S : ℤ) ∣ u - u₀ ∧ (l : ℤ) ∣ u)) : ℕ) : ℝ) -
        ((B - A : ℤ) : ℝ) / ((l : ℝ) * S)| ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_crt l S hcop u₀
  have hr : (0 : ℤ) < ((l * S : ℕ) : ℤ) := by exact_mod_cast Nat.mul_pos hl hS
  rw [Finset.filter_congr fun u _ => hw u]
  have hcard : ((#((Finset.Ico A B).filter (fun u => u ≡ w [ZMOD ((l * S : ℕ) : ℤ)])) : ℕ) : ℤ) =
      max (⌈(B - w) / (((l * S : ℕ) : ℤ) : ℚ)⌉ - ⌈(A - w) / (((l * S : ℕ) : ℤ) : ℚ)⌉) 0 := by
    convert Int.Ico_filter_modEq_card A B hr w
  have hcardR : ((#((Finset.Ico A B).filter (fun u => u ≡ w [ZMOD ((l * S : ℕ) : ℤ)])) : ℕ) : ℝ) =
      (((#((Finset.Ico A B).filter (fun u => u ≡ w [ZMOD ((l * S : ℕ) : ℤ)])) : ℕ) : ℤ) : ℝ) := by
    norm_cast
  rw [hcardR, hcard]
  set β : ℚ := (B - w) / (((l * S : ℕ) : ℤ) : ℚ)
  set α : ℚ := (A - w) / (((l * S : ℕ) : ℤ) : ℚ)
  have hrq : (0 : ℚ) < (((l * S : ℕ) : ℤ) : ℚ) := by exact_mod_cast hr
  have hab : α ≤ β := by
    apply div_le_div_of_nonneg_right _ hrq.le
    have : (A : ℚ) ≤ B := by exact_mod_cast hAB
    linarith
  have hce : ⌈α⌉ ≤ ⌈β⌉ := Int.ceil_mono hab
  rw [max_eq_left (by linarith)]
  have h1 := Int.le_ceil α
  have h2 := Int.ceil_lt_add_one α
  have h3 := Int.le_ceil β
  have h4 := Int.ceil_lt_add_one β
  have hdiff : β - α = ((B - A : ℤ) : ℚ) / (((l * S : ℕ) : ℤ) : ℚ) := by
    simp only [β, α]; push_cast; field_simp; ring
  have hq : |((⌈β⌉ - ⌈α⌉ : ℤ) : ℚ) - ((B - A : ℤ) : ℚ) / (((l * S : ℕ) : ℤ) : ℚ)| ≤ 1 := by
    rw [← hdiff, abs_le]; push_cast; constructor <;> linarith
  have : ((((⌈β⌉ - ⌈α⌉ : ℤ) : ℚ) - ((B - A : ℤ) : ℚ) / (((l * S : ℕ) : ℤ) : ℚ) : ℚ) : ℝ) =
      ((⌈β⌉ - ⌈α⌉ : ℤ) : ℝ) - ((B - A : ℤ) : ℝ) / ((l : ℝ) * S) := by
    push_cast; ring
  have hq' := (Rat.cast_le (K := ℝ)).mpr hq
  rw [Rat.cast_abs, this, Rat.cast_one] at hq'
  exact hq'

/-- **The Euler-factor average** ([21] p. 16):
`∑_{A ≤ u < B, u ≡ u₀ (S)} ∑_{l ∣ u, (l,S)=1} μ(l)/l = (B − A)/S · P(S) + O(3 + log B)`. -/
theorem euler_average (S : ℕ) (hS : 0 < S) (u₀ A B : ℤ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    |∑ u ∈ (Finset.Ico A B).filter (fun u => (S : ℤ) ∣ u - u₀),
        ∑ l ∈ u.toNat.divisors.filter (fun l => Nat.Coprime l S), (μ l : ℝ) / l -
      ((B - A : ℤ) : ℝ) / S * PS S| ≤ 3 + Real.log B := by
  classical
  set U := (Finset.Ico A B).filter (fun u => (S : ℤ) ∣ u - u₀) with hU
  set Bn := B.toNat with hBn
  have hB1 : 1 ≤ B := le_trans hA hAB
  have hBn1 : 1 ≤ Bn := by omega
  have hBR : ((Bn : ℕ) : ℝ) = (B : ℝ) := by
    have : ((Bn : ℕ) : ℤ) = B := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  -- (1) swap the sums
  have hswap : ∑ u ∈ U, ∑ l ∈ u.toNat.divisors.filter (fun l => Nat.Coprime l S), (μ l : ℝ) / l =
      ∑ l ∈ range Bn, (if Nat.Coprime l S then (μ l : ℝ) / l else 0) *
        (#((Finset.Ico A B).filter (fun u => (S : ℤ) ∣ u - u₀ ∧ (l : ℤ) ∣ u)) : ℝ) := by
    have h1 : ∀ u ∈ U, ∑ l ∈ u.toNat.divisors.filter (fun l => Nat.Coprime l S), (μ l : ℝ) / l =
        ∑ l ∈ range Bn, if (l : ℤ) ∣ u then (if Nat.Coprime l S then (μ l : ℝ) / l else 0)
          else 0 := by
      intro u hu
      simp only [hU, Finset.mem_filter, Finset.mem_Ico] at hu
      have hu0 : 0 < u.toNat := by omega
      have hset : (range Bn).filter (fun l : ℕ => (l : ℤ) ∣ u) = u.toNat.divisors := by
        ext l
        simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
        constructor
        · rintro ⟨_, hd⟩
          have : (l : ℤ) ∣ (u.toNat : ℤ) := by rwa [Int.toNat_of_nonneg (by omega)]
          exact ⟨Int.natCast_dvd_natCast.mp this, hu0.ne'⟩
        · rintro ⟨hd, _⟩
          refine ⟨?_, ?_⟩
          · have := Nat.le_of_dvd hu0 hd
            omega
          · have : (l : ℤ) ∣ (u.toNat : ℤ) := Int.natCast_dvd_natCast.mpr hd
            rwa [Int.toNat_of_nonneg (by omega)] at this
      conv_rhs => rw [← Finset.sum_filter, hset]
      rw [Finset.sum_filter]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 2
    rw [hU, Finset.filter_filter]
  rw [hswap]
  -- (2) the main term and the error
  set f : ℕ → ℝ := fun l => if Nat.Coprime l S then (μ l : ℝ) / l else 0 with hf
  set N : ℕ → ℝ := fun l =>
    (#((Finset.Ico A B).filter (fun u => (S : ℤ) ∣ u - u₀ ∧ (l : ℤ) ∣ u)) : ℝ) with hN
  set D := ((B - A : ℤ) : ℝ) with hD
  have hD0 : 0 ≤ D := by rw [hD]; exact_mod_cast (by omega : (0 : ℤ) ≤ B - A)
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hterm : ∀ l ∈ range Bn, |f l * N l - D / S * (if Nat.Coprime l S then mu2 l else 0)| ≤
      (if l = 0 then 0 else 1 / (l : ℝ)) := by
    intro l _
    simp only [f, N]
    by_cases hcop : Nat.Coprime l S
    · rw [if_pos hcop, if_pos hcop]
      rcases Nat.eq_zero_or_pos l with hl0 | hl0
      · subst hl0; simp [mu2]
      · rw [if_neg hl0.ne']
        have hlR : (0 : ℝ) < l := by exact_mod_cast hl0
        have e : (μ l : ℝ) / l * N l - D / S * mu2 l =
            (μ l : ℝ) / l * (N l - D / ((l : ℝ) * S)) := by
          simp only [mu2]; field_simp
        simp only [N] at e
        rw [e, abs_mul, abs_div, abs_of_pos hlR]
        have h1 := abs_card_progression_sub_le l S hl0 hS hcop u₀ A B hAB
        have h2 := abs_moebius_real_le l
        calc |(μ l : ℝ)| / l * |(#((Finset.Ico A B).filter
              (fun u => (S : ℤ) ∣ u - u₀ ∧ (l : ℤ) ∣ u)) : ℝ) - D / ((l : ℝ) * S)|
            ≤ 1 / l * 1 := by
              apply mul_le_mul (div_le_div_of_nonneg_right h2 hlR.le) h1 (abs_nonneg _)
                (by positivity)
          _ = 1 / l := mul_one _
    · rw [if_neg hcop, if_neg hcop]
      split_ifs <;> simp
  have hharm : ∑ l ∈ range Bn, (if l = 0 then (0 : ℝ) else 1 / (l : ℝ)) ≤ 1 + Real.log B := by
    have : ∑ l ∈ range Bn, (if l = 0 then (0 : ℝ) else 1 / (l : ℝ)) ≤
        ∑ i ∈ Finset.Icc 1 Bn, (1 / (i : ℝ)) := by
      have e : ∀ l ∈ range Bn, (if l = 0 then (0 : ℝ) else 1 / (l : ℝ)) =
          if l ≠ 0 then 1 / (l : ℝ) else 0 := fun l _ => by split_ifs <;> simp_all
      rw [Finset.sum_congr rfl e, ← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
      intro l hl
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hl ⊢
      omega
    refine this.trans ?_
    have h := harmonic_le_one_add_log Bn
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    rw [← hBR]
    simpa [one_div] using h
  have hmain : |∑ l ∈ range Bn, f l * N l - D / S * ∑ l ∈ range Bn,
      (if Nat.Coprime l S then mu2 l else 0)| ≤ 1 + Real.log B := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans hharm)
  have htail := abs_partial_PS_sub_le S Bn hBn1
  have htail' : |D / S * ∑ l ∈ range Bn, (if Nat.Coprime l S then mu2 l else 0) -
      D / S * PS S| ≤ 2 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
    calc D / S * |∑ l ∈ range Bn, (if Nat.Coprime l S then mu2 l else 0) - PS S|
        ≤ D / S * (2 / Bn) := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ 2 := by
          rw [hBR]
          have hDB : D ≤ B := by rw [hD]; push_cast; linarith [(by exact_mod_cast hA : (1 : ℝ) ≤ A)]
          have hB0 : (0 : ℝ) < B := by exact_mod_cast (by omega : (0 : ℤ) < B)
          rw [div_mul_div_comm, div_le_iff₀ (by positivity)]
          nlinarith
  calc |∑ l ∈ range Bn, f l * N l - D / S * PS S|
      = |(∑ l ∈ range Bn, f l * N l - D / S * ∑ l ∈ range Bn,
            (if Nat.Coprime l S then mu2 l else 0)) +
          (D / S * ∑ l ∈ range Bn, (if Nat.Coprime l S then mu2 l else 0) - D / S * PS S)| := by
        ring_nf
    _ ≤ (1 + Real.log B) + 2 := (abs_add_le _ _).trans (add_le_add hmain htail')
    _ = 3 + Real.log B := by ring

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: summing the fibre counts ([21] p. 16)

`∑_{A ≤ n < B, n ≡ n₀ (S)} #{(x, y) : x ∈ [X₁(n), X₂(n)), y ∈ [Y₁, Y₂), x ≡ x₀, y ≡ y₀ (S),
nS ∣ xy − (n e₀ + t)} = θ (Y₂ − Y₁)(B − A) P(S)/S³ + error`, when `X₂(n) − X₁(n) = θ n + O(1)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction Real
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The divisor bound -/

/-- **The divisor bound** `d(n) ≤ C n^ε`. -/
theorem card_divisors_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε :=
  by
  try haveI := ε; try haveI := hε; first
    | exact BlockCycleRotation.exists_card_divisors_le hε
    | exact BlockCycleRotation.exists_card_divisors_le
    | exact BlockCycleRotation.exists_card_divisors_le ..
    | (apply BlockCycleRotation.exists_card_divisors_le <;> first | assumption | infer_instance)
    | simpa using BlockCycleRotation.exists_card_divisors_le

/-- `(d(m)(1 + log m))³ ≤ K m^{1/8}`. -/
theorem exists_T_cube_le :
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8) := by
  obtain ⟨C, hC, hCd⟩ := card_divisors_le_rpow (1 / 48) (by norm_num)
  refine ⟨(C * 49) ^ 3, by positivity, fun m hm => ?_⟩
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : 1 + Real.log m ≤ 49 * (m : ℝ) ^ ((1 : ℝ) / 48) := by
    have h1 := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 1 / 48)
    have h2 : (1 : ℝ) ≤ (m : ℝ) ^ ((1 : ℝ) / 48) := Real.one_le_rpow hm1 (by norm_num)
    have : (m : ℝ) ^ ((1 : ℝ) / 48) / (1 / 48) = 48 * (m : ℝ) ^ ((1 : ℝ) / 48) := by ring
    linarith
  have hT : (m.divisors.card : ℝ) * (1 + Real.log m) ≤
      C * 49 * (m : ℝ) ^ ((1 : ℝ) / 24) := by
    have hd := hCd m (by omega)
    have hpow : (m : ℝ) ^ ((1 : ℝ) / 48) * (m : ℝ) ^ ((1 : ℝ) / 48) =
        (m : ℝ) ^ ((1 : ℝ) / 24) := by
      rw [← Real.rpow_add hm0]; norm_num
    have hlog0 : 0 ≤ 1 + Real.log m := by linarith [Real.log_nonneg hm1]
    calc (m.divisors.card : ℝ) * (1 + Real.log m)
        ≤ (C * (m : ℝ) ^ ((1 : ℝ) / 48)) * (49 * (m : ℝ) ^ ((1 : ℝ) / 48)) :=
          mul_le_mul hd hlog hlog0 (by positivity)
      _ = C * 49 * (m : ℝ) ^ ((1 : ℝ) / 24) := by rw [← hpow]; ring
  have h3 : ((m : ℝ) ^ ((1 : ℝ) / 24)) ^ 3 = (m : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]; norm_num
  calc ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3
      ≤ (C * 49 * (m : ℝ) ^ ((1 : ℝ) / 24)) ^ 3 := pow_le_pow_left₀ (by positivity) hT 3
    _ = (C * 49) ^ 3 * (m : ℝ) ^ ((1 : ℝ) / 8) := by rw [mul_pow, h3]

/-! ### `M(n)` -/

/-- `M(n) = ∑_{l ∣ n, (l,S)=1} μ(l) n/l`. -/
def Mfun (n S : ℕ) : ℤ := ∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), μ l * ((n / l : ℕ) : ℤ)

lemma Mfun_bounds (n S : ℕ) (hn : 0 < n) : 0 ≤ Mfun n S ∧ Mfun n S ≤ n := by
  have h := card_range_coprime n S hn 1 isCoprime_one_left
  rw [← Mfun] at h
  rw [← h]
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have := Finset.card_filter_le (range n)
    (fun r : ℕ => IsCoprime ((1 : ℤ) + (S : ℤ) * (r : ℤ)) ((n : ℕ) : ℤ))
  rw [Finset.card_range] at this
  exact_mod_cast this

lemma Mfun_div (n S : ℕ) (hn : 0 < n) :
    (Mfun n S : ℝ) / n = ∑ l ∈ n.divisors.filter (fun l => Nat.Coprime l S), (μ l : ℝ) / l := by
  rw [Mfun, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Int.cast_mul, Int.cast_natCast]
  have hln : l ∣ n := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hl).1
  have hl0 : (0 : ℝ) < l := by exact_mod_cast Nat.pos_of_dvd_of_pos hln hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nat.cast_div hln hl0.ne']
  field_simp

/-! ### Summing the fibres -/

/-- Replacing `X` by `θ n` in the main term. -/
lemma main_replace {X θ n Y M S A : ℝ} (hn : 0 < n) (hS : 1 ≤ S) (hA : 0 < A) (hAn : A ≤ n)
    (hY : 0 ≤ Y) (hM0 : 0 ≤ M) (hMn : M ≤ n) (hX : |X - θ * n| ≤ 2) :
    |X * Y * M / (n * S) ^ 2 - θ * Y / S ^ 2 * (M / n)| ≤ 2 * Y / A := by
  have hS0 : 0 < S := by linarith
  have hnS0 : 0 < n * S := mul_pos hn hS0
  have hW0 : 0 ≤ Y * M / (n * S) ^ 2 := div_nonneg (mul_nonneg hY hM0) (sq_nonneg _)
  have e : X * Y * M / (n * S) ^ 2 - θ * Y / S ^ 2 * (M / n) =
      (X - θ * n) * (Y * M / (n * S) ^ 2) := by
    field_simp
  rw [e, abs_mul, abs_of_nonneg hW0]
  have h1 : Y * M / (n * S) ^ 2 ≤ Y / A := by
    rw [div_le_div_iff₀ (pow_pos hnS0 2) hA]
    have h2 : M * A ≤ n * n := mul_le_mul hMn hAn hA.le hn.le
    have h3 : n * n ≤ (n * S) ^ 2 := by
      calc n * n = n ^ 2 * 1 := by ring
        _ ≤ n ^ 2 * S ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hS) (sq_nonneg _)
        _ = (n * S) ^ 2 := by ring
    calc Y * M * A = Y * (M * A) := by ring
      _ ≤ Y * (n * S) ^ 2 := mul_le_mul_of_nonneg_left (h2.trans h3) hY
  calc |X - θ * n| * (Y * M / (n * S) ^ 2) ≤ 2 * (Y / A) := mul_le_mul hX h1 hW0 (by norm_num)
    _ = 2 * Y / A := by ring

/-- The per-`n` estimate in `sum_fibers`. -/
lemma fiber_term_bound (S : ℕ) (hS0 : 0 < S) (hS : Squarefree S) (n₀ x₀ y₀ e₀ t : ℤ)
    (ht : t = 1 ∨ t = -1) (hcong : (S : ℤ) ∣ n₀ * e₀ + t - x₀ * y₀)
    (A B Y₁ Y₂ : ℤ) (hA : 1 ≤ A) (hY : Y₁ ≤ Y₂)
    (X₁ X₂ : ℤ → ℤ) (θ : ℝ) (hθ2 : θ ≤ 2)
    (hX : ∀ n, A ≤ n → n < B → X₁ n ≤ X₂ n ∧ |((X₂ n - X₁ n : ℤ) : ℝ) - θ * n| ≤ 2)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8))
    (n : ℤ) (hn : n ∈ (Finset.Ico A B).filter (fun n => (S : ℤ) ∣ n - n₀)) :
    |((#((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ n * S ∣ p.1 * p.2 - (n * e₀ + t))) : ℕ) : ℝ) -
      θ * ((Y₂ - Y₁ : ℤ) : ℝ) / (S : ℝ) ^ 2 * ((Mfun n.toNat S : ℝ) / n)| ≤
      3 * K * S * ((B : ℝ) * S) ^ ((7 : ℝ) / 8) * (8 + ((Y₂ - Y₁ : ℤ) : ℝ) / A) +
        2 * ((Y₂ - Y₁ : ℤ) : ℝ) / A := by
  classical
  set Y : ℝ := ((Y₂ - Y₁ : ℤ) : ℝ) with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact_mod_cast (by omega : (0 : ℤ) ≤ Y₂ - Y₁)
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS0
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  set E₁ : ℝ := 3 * K * S * ((B : ℝ) * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) with hE₁
  simp only [Finset.mem_filter, Finset.mem_Ico] at hn
  obtain ⟨⟨hAn, hnB⟩, hSn⟩ := hn
  have hn1 : 1 ≤ n := le_trans hA hAn
  set nn := n.toNat with hnn
  have hnnZ : (nn : ℤ) = n := Int.toNat_of_nonneg (by omega)
  have hnn0 : 0 < nn := by omega
  have hnR : ((nn : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hnnZ
  have hn0R : (0 : ℝ) < n := by exact_mod_cast (by omega : (0 : ℤ) < n)
  have hnAR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hnBR : (n : ℝ) ≤ B := by exact_mod_cast hnB.le
  -- hypotheses of `fiber_count`
  have ha : IsCoprime (n * e₀ + t) (nn : ℤ) := by
    rw [hnnZ]
    have ht' : IsCoprime t n := by
      rcases ht with rfl | rfl
      · exact isCoprime_one_left
      · exact isCoprime_one_left.neg_left
    have e : n * e₀ + t = t + n * e₀ := by ring
    rw [e]
    exact ht'.add_mul_left_left e₀
  have hax : (S : ℤ) ∣ (n * e₀ + t) - x₀ * y₀ := by
    have : (n * e₀ + t) - x₀ * y₀ = (n - n₀) * e₀ + (n₀ * e₀ + t - x₀ * y₀) := by ring
    rw [this]
    exact dvd_add (hSn.mul_right _) hcong
  obtain ⟨hX12, hXθ⟩ := hX n hAn hnB
  have hfc := ArtinPrimitiveRoots.abs_card_box_mul_sub_mod_le nn S hnn0 hS0 hS x₀ y₀ (n * e₀ + t) ha hax (X₁ n) (X₂ n) Y₁ Y₂ hX12 hY
  have hfilter : ((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ n * S ∣ p.1 * p.2 - (n * e₀ + t))) =
      ((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧
          ((nn * S : ℕ) : ℤ) ∣ p.1 * p.2 - (n * e₀ + t))) := by
    congr 1; ext p; push_cast; rw [hnnZ]
  rw [hfilter]
  set F := ((#((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
        (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧
          ((nn * S : ℕ) : ℤ) ∣ p.1 * p.2 - (n * e₀ + t))) : ℕ) : ℝ) with hF
  have hMeq : (((∑ l ∈ nn.divisors.filter (fun l => Nat.Coprime l S),
      μ l * ((nn / l : ℕ) : ℤ)) : ℤ) : ℝ) = (Mfun nn S : ℝ) := rfl
  rw [hMeq] at hfc
  set M := (Mfun nn S : ℝ) with hM
  obtain ⟨hM0, hMn⟩ := Mfun_bounds nn S hnn0
  have hM0R : 0 ≤ M := by rw [hM]; exact_mod_cast hM0
  have hMnR : M ≤ n := by rw [hM, ← hnR]; exact_mod_cast hMn
  set X : ℝ := ((X₂ n - X₁ n : ℤ) : ℝ) with hXdef
  -- (a) the fibre error
  have hTn := hK (nn * S) (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos hnn0 hS0).ne')
  have hnSR : ((nn * S : ℕ) : ℝ) = (n : ℝ) * S := by push_cast; rw [hnR]
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hnS1 : (1 : ℝ) ≤ (n : ℝ) * S := one_le_mul_of_one_le_of_one_le hn1R hSR
  have hpow : ((nn * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) * ((nn * S : ℕ) : ℝ) ^ ((1 : ℝ) / 8) ≤
      ((B : ℝ) * S) ^ ((7 : ℝ) / 8) := by
    rw [← Real.rpow_add (by rw [hnSR]; linarith), hnSR]
    norm_num
    exact Real.rpow_le_rpow (by linarith) (mul_le_mul_of_nonneg_right hnBR (by linarith))
      (by norm_num)
  have hbrack : (X + Y + 2) / (nn : ℝ) + 1 ≤ 8 + Y / A := by
    rw [hnR]
    have hXle : X ≤ θ * n + 2 := by linarith [(abs_le.mp hXθ).2]
    have h1 : (X + Y + 2) / (n : ℝ) ≤ (2 * n + 4) / n + Y / n := by
      rw [← add_div]
      have hθn : θ * n ≤ 2 * n := mul_le_mul_of_nonneg_right hθ2 hn0R.le
      exact div_le_div_of_nonneg_right (by linarith) hn0R.le
    have h2 : (2 * (n : ℝ) + 4) / n ≤ 6 := by
      rw [div_le_iff₀ hn0R]; linarith
    have h3 : Y / (n : ℝ) ≤ Y / A := div_le_div_of_nonneg_left hY0 (by linarith) hnAR
    linarith
  have herr1 : 3 * S * ((nn * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
      (((nn * S).divisors.card : ℝ) * (1 + Real.log ((nn * S : ℕ) : ℝ))) ^ 3 *
      ((X + Y + 2) / nn + 1) ≤ E₁ := by
    rw [hE₁]
    have h0 : 0 ≤ (X + Y + 2) / (nn : ℝ) + 1 := by
      have : 0 ≤ X := by rw [hXdef]; exact_mod_cast (by omega : (0 : ℤ) ≤ X₂ n - X₁ n)
      positivity
    calc 3 * S * ((nn * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
          (((nn * S).divisors.card : ℝ) * (1 + Real.log ((nn * S : ℕ) : ℝ))) ^ 3 *
          ((X + Y + 2) / nn + 1)
        ≤ 3 * S * ((nn * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
            (K * ((nn * S : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) * ((X + Y + 2) / nn + 1) := by
          gcongr
      _ = 3 * K * S * (((nn * S : ℕ) : ℝ) ^ ((3 : ℝ) / 4) *
            ((nn * S : ℕ) : ℝ) ^ ((1 : ℝ) / 8)) * ((X + Y + 2) / nn + 1) := by ring
      _ ≤ 3 * K * S * ((B : ℝ) * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) := by
          have hc0 : 0 ≤ 3 * K * S := mul_nonneg (mul_nonneg (by norm_num) hK0) (by positivity)
          have hB0 : (0 : ℝ) ≤ (B : ℝ) * S := by
            have : (0 : ℝ) ≤ B := le_trans hn0R.le hnBR
            positivity
          exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hc0) hbrack h0
            (mul_nonneg hc0 (Real.rpow_nonneg hB0 _))
  -- (b) the main term
  have hmain : |X * Y * M / ((nn : ℝ) * S) ^ 2 - θ * Y / (S : ℝ) ^ 2 * (M / n)| ≤ 2 * Y / A := by
    rw [hnR]
    exact main_replace hn0R hSR (by linarith) hnAR hY0 hM0R hMnR hXθ
  have hfc' : |F - X * Y * M / ((nn : ℝ) * S) ^ 2| ≤ E₁ := by
    have := hfc.trans herr1
    rw [hYdef]
    exact this
  exact (abs_sub_le _ _ _).trans (add_le_add hfc' hmain)

/-- **The sum of the fibre counts.** -/
theorem sum_fibers (S : ℕ) (hS0 : 0 < S) (hS : Squarefree S) (n₀ x₀ y₀ e₀ t : ℤ)
    (ht : t = 1 ∨ t = -1) (hcong : (S : ℤ) ∣ n₀ * e₀ + t - x₀ * y₀)
    (A B Y₁ Y₂ : ℤ) (hA : 1 ≤ A) (hAB : A ≤ B) (hY : Y₁ ≤ Y₂)
    (X₁ X₂ : ℤ → ℤ) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ2 : θ ≤ 2)
    (hX : ∀ n, A ≤ n → n < B → X₁ n ≤ X₂ n ∧ |((X₂ n - X₁ n : ℤ) : ℝ) - θ * n| ≤ 2)
    (K : ℝ) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8)) :
    |∑ n ∈ (Finset.Ico A B).filter (fun n => (S : ℤ) ∣ n - n₀),
        ((#((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
          (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ n * S ∣ p.1 * p.2 - (n * e₀ + t))) : ℕ) : ℝ) -
      θ * ((Y₂ - Y₁ : ℤ) : ℝ) * ((B - A : ℤ) : ℝ) * PS S / (S : ℝ) ^ 3| ≤
      ((B - A : ℤ) : ℝ) * (3 * K * S * ((B : ℝ) * S) ^ ((7 : ℝ) / 8) *
          (8 + ((Y₂ - Y₁ : ℤ) : ℝ) / A) + 2 * ((Y₂ - Y₁ : ℤ) : ℝ) / A) +
        θ * ((Y₂ - Y₁ : ℤ) : ℝ) * (3 + Real.log B) / (S : ℝ) ^ 2 := by
  classical
  set Nset := (Finset.Ico A B).filter (fun n => (S : ℤ) ∣ n - n₀) with hNset
  set Y : ℝ := ((Y₂ - Y₁ : ℤ) : ℝ) with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact_mod_cast (by omega : (0 : ℤ) ≤ Y₂ - Y₁)
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS0
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hBR : (A : ℝ) ≤ B := by exact_mod_cast hAB
  have hK0 : 0 ≤ K := by
    have := hK 1 le_rfl
    simp at this
    linarith
  set E₁ : ℝ := 3 * K * S * ((B : ℝ) * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) with hE₁
  have hper : ∀ n ∈ Nset,
      |((#((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
          (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ n * S ∣ p.1 * p.2 - (n * e₀ + t))) : ℕ) : ℝ) -
        θ * Y / (S : ℝ) ^ 2 * ((Mfun n.toNat S : ℝ) / n)| ≤ E₁ + 2 * Y / A :=
    fun n hn => fiber_term_bound S hS0 hS n₀ x₀ y₀ e₀ t ht hcong A B Y₁ Y₂ hA hY X₁ X₂ θ hθ2
      hX K hK0 hK n hn
  -- sum over `n`
  have hcard : (#Nset : ℝ) ≤ ((B - A : ℤ) : ℝ) := by
    have h1 : #Nset ≤ #(Finset.Ico A B) := Finset.card_filter_le _ _
    rw [Int.card_Ico] at h1
    have h2 : (((B - A).toNat : ℕ) : ℝ) = ((B - A : ℤ) : ℝ) := by
      have : (((B - A).toNat : ℕ) : ℤ) = B - A := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    calc (#Nset : ℝ) ≤ (((B - A).toNat : ℕ) : ℝ) := by exact_mod_cast h1
      _ = _ := h2
  have hsum1 : |∑ n ∈ Nset,
      ((#((Finset.Ico (X₁ n) (X₂ n) ×ˢ Finset.Ico Y₁ Y₂).filter (fun p : ℤ × ℤ =>
          (S : ℤ) ∣ p.1 - x₀ ∧ (S : ℤ) ∣ p.2 - y₀ ∧ n * S ∣ p.1 * p.2 - (n * e₀ + t))) : ℕ) : ℝ) -
      θ * Y / (S : ℝ) ^ 2 * ∑ n ∈ Nset, ((Mfun n.toNat S : ℝ) / n)| ≤
      ((B - A : ℤ) : ℝ) * (E₁ + 2 * Y / A) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hper).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hA0 : (0 : ℝ) < A := by linarith
    have hB0 : (0 : ℝ) ≤ (B : ℝ) * S := mul_nonneg (by linarith) (by positivity)
    have hE0 : 0 ≤ E₁ := by
      rw [hE₁]
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK0) (by positivity))
        (Real.rpow_nonneg hB0 _)) (by have := div_nonneg hY0 hA0.le; linarith)
    have : 0 ≤ E₁ + 2 * Y / A := add_nonneg hE0 (div_nonneg (by linarith) hA0.le)
    exact mul_le_mul_of_nonneg_right hcard this
  -- the Euler average
  have heul := euler_average S hS0 n₀ A B hA hAB
  have hMsum : ∑ n ∈ Nset, ((Mfun n.toNat S : ℝ) / n) =
      ∑ u ∈ Nset, ∑ l ∈ u.toNat.divisors.filter (fun l => Nat.Coprime l S), (μ l : ℝ) / l := by
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hNset, Finset.mem_filter, Finset.mem_Ico] at hn
    have hn0 : 0 < n.toNat := by omega
    rw [← Mfun_div n.toNat S hn0]
    congr 1
    exact_mod_cast (Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n)).symm
  have hsum2 : |θ * Y / (S : ℝ) ^ 2 * ∑ n ∈ Nset, ((Mfun n.toNat S : ℝ) / n) -
      θ * Y * ((B - A : ℤ) : ℝ) * PS S / (S : ℝ) ^ 3| ≤ θ * Y * (3 + Real.log B) / (S : ℝ) ^ 2 := by
    rw [hMsum]
    have e : θ * Y / (S : ℝ) ^ 2 * ∑ u ∈ Nset, ∑ l ∈ u.toNat.divisors.filter
        (fun l => Nat.Coprime l S), (μ l : ℝ) / l - θ * Y * ((B - A : ℤ) : ℝ) * PS S / (S : ℝ) ^ 3 =
        θ * Y / (S : ℝ) ^ 2 * (∑ u ∈ Nset, ∑ l ∈ u.toNat.divisors.filter
          (fun l => Nat.Coprime l S), (μ l : ℝ) / l - ((B - A : ℤ) : ℝ) / S * PS S) := by
      field_simp
    rw [e, abs_mul, abs_of_nonneg (div_nonneg (mul_nonneg hθ0 hY0) (by positivity))]
    calc θ * Y / (S : ℝ) ^ 2 * |∑ u ∈ Nset, ∑ l ∈ u.toNat.divisors.filter
          (fun l => Nat.Coprime l S), (μ l : ℝ) / l - ((B - A : ℤ) : ℝ) / S * PS S|
        ≤ θ * Y / (S : ℝ) ^ 2 * (3 + Real.log B) := mul_le_mul_of_nonneg_left heul (by positivity)
      _ = θ * Y * (3 + Real.log B) / (S : ℝ) ^ 2 := by ring
  have := (abs_sub_le _ _ _).trans (add_le_add hsum1 hsum2)
  refine this.trans (le_of_eq ?_)
  rw [hE₁]

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: from matrices in `SL₂(ℤ)` to fibre counts

A matrix `g = (u c; v d) ∈ SL₂(ℤ)` is determined by `(u, c, v)` when `u ≠ 0`, and by `(v, d, u)`
when `v ≠ 0`. With `g ≡ g₀ (mod S)` this turns the count of Lemma 3.3 into a sum, over `u` (or
over `v`), of the residue-hyperbola counts of `fiber_count`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset Matrix

noncomputable section

/-- The congruence `g ≡ g₀ (mod S)` entrywise. -/
lemma map_eq_iff (S : ℕ) [NeZero S] (g : SpecialLinearGroup (Fin 2) ℤ)
    (g₀ : SpecialLinearGroup (Fin 2) (ZMod S)) :
    SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀ ↔
      ((S : ℤ) ∣ g 0 0 - ((g₀ 0 0).val : ℤ) ∧ (S : ℤ) ∣ g 0 1 - ((g₀ 0 1).val : ℤ) ∧
        (S : ℤ) ∣ g 1 0 - ((g₀ 1 0).val : ℤ) ∧ (S : ℤ) ∣ g 1 1 - ((g₀ 1 1).val : ℤ)) := by
  have key : ∀ (a : ℤ) (b : ZMod S), (a : ZMod S) = b ↔ (S : ℤ) ∣ a - (b.val : ℤ) := by
    intro a b
    have hb : (((b.val : ℤ)) : ZMod S) = b := by push_cast; exact ZMod.natCast_zmod_val b
    conv_lhs => rw [← hb]
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub, dvd_sub_comm]
  constructor
  · intro h
    subst h
    simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      eq_intCast]
    exact ⟨(key _ _).mp rfl, (key _ _).mp rfl, (key _ _).mp rfl, (key _ _).mp rfl⟩
  · rintro ⟨h1, h2, h3, h4⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
        eq_intCast, Fin.zero_eta, Fin.mk_one] <;>
      first
      | exact (key _ _).mpr h1
      | exact (key _ _).mpr h2
      | exact (key _ _).mpr h3
      | exact (key _ _).mpr h4

lemma det_eq (g : SpecialLinearGroup (Fin 2) ℤ) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := g.2
  rw [Matrix.det_fin_two] at this
  exact this

/-- `det g₀ = 1` gives `S ∣ u₀d₀ − c₀v₀ − 1` for the representatives. -/
lemma det_rep (S : ℕ) [NeZero S] (g₀ : SpecialLinearGroup (Fin 2) (ZMod S)) :
    (S : ℤ) ∣ ((g₀ 0 0).val : ℤ) * ((g₀ 1 1).val : ℤ) - ((g₀ 0 1).val : ℤ) * ((g₀ 1 0).val : ℤ)
      - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_zmod_val]
  have := g₀.2
  rw [Matrix.det_fin_two] at this
  rw [this, sub_self]

/-- Build a matrix from `(u, c, v)` with `u ∣ 1 + cv`. -/
def mkU (u c v : ℤ) (h : u ∣ 1 + c * v) : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![u, c; v, (1 + c * v) / u], by
    rw [Matrix.det_fin_two_of]
    rw [Int.mul_ediv_cancel' h]; ring⟩

/-- Build a matrix from `(v, d, u)` with `v ∣ ud − 1`. -/
def mkV (u d v : ℤ) (h : v ∣ u * d - 1) : SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![u, (u * d - 1) / v; v, d], by
    rw [Matrix.det_fin_two_of]
    rw [mul_comm ((u * d - 1) / v) v, Int.mul_ediv_cancel' h]; ring⟩

variable (S : ℕ) [NeZero S] (g₀ : SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ)
  (I₁ I₂ I₃ : Set ℝ)

/-- The predicate of Lemma 3.3. -/
def RootPred (g : SpecialLinearGroup (Fin 2) ℤ) : Prop :=
  (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
    (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧ SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀

/-- The fibre over `u` (case `U ≤ V`): pairs `(c, v)`. -/
def fiberU (A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (u : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico (X₁ u) (X₂ u)) ×ˢ (Finset.Ico A₂ B₂)).filter (fun p : ℤ × ℤ =>
    (S : ℤ) ∣ p.1 - ((g₀ 0 1).val : ℤ) ∧ (S : ℤ) ∣ p.2 - ((g₀ 1 0).val : ℤ) ∧
      u * S ∣ p.1 * p.2 - (u * ((g₀ 1 1).val : ℤ) + -1))

/-- The fibre over `v` (case `V < U`): pairs `(d, u)`. -/
def fiberV (A₁ B₁ : ℤ) (X₁ X₂ : ℤ → ℤ) (v : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Ico (X₁ v) (X₂ v)) ×ˢ (Finset.Ico A₁ B₁)).filter (fun p : ℤ × ℤ =>
    (S : ℤ) ∣ p.1 - ((g₀ 1 1).val : ℤ) ∧ (S : ℤ) ∣ p.2 - ((g₀ 0 0).val : ℤ) ∧
      v * S ∣ p.1 * p.2 - (v * ((g₀ 0 1).val : ℤ) + 1))

/-- The sigma set over `u`. -/
def sigmaU (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) : Finset (Σ _ : ℤ, ℤ × ℤ) :=
  ((Finset.Ico A₁ B₁).filter (fun u => (S : ℤ) ∣ u - ((g₀ 0 0).val : ℤ))).sigma
    (fiberU S g₀ A₂ B₂ X₁ X₂)

/-- The sigma set over `v`. -/
def sigmaV (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) : Finset (Σ _ : ℤ, ℤ × ℤ) :=
  ((Finset.Ico A₂ B₂).filter (fun v => (S : ℤ) ∣ v - ((g₀ 1 0).val : ℤ))).sigma
    (fiberV S g₀ A₁ B₁ X₁ X₂)

/-- **Upper bound, case `U ≤ V`.** -/
theorem count_le_sigmaU (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (hA₁ : 1 ≤ A₁)
    (h1 : ∀ u : ℤ, (u : ℝ) / U ∈ I₁ → A₁ ≤ u ∧ u < B₁)
    (h2 : ∀ v : ℤ, (v : ℝ) / V ∈ I₂ → A₂ ≤ v ∧ v < B₂)
    (h3 : ∀ u c : ℤ, A₁ ≤ u → 0 ≤ c → c < u → (c : ℝ) / u ∈ I₃ → X₁ u ≤ c ∧ c < X₂ u) :
    Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g} ∧
      Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} ≤ #(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) := by
  classical
  let f : {g // RootPred S g₀ U V I₁ I₂ I₃ g} → {x // x ∈ sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂} :=
    fun g => ⟨⟨g.1 0 0, (g.1 0 1, g.1 1 0)⟩, by
      obtain ⟨g, hu, hv, hc0, hcu, hr, hm⟩ := g
      obtain ⟨m1, m2, m3, m4⟩ := (map_eq_iff S g g₀).mp hm
      obtain ⟨hA, hB⟩ := h1 _ hu
      obtain ⟨hA2, hB2⟩ := h2 _ hv
      obtain ⟨hX1, hX2⟩ := h3 _ _ hA hc0 hcu hr
      simp only [sigmaU, fiberU, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_filter,
        Finset.mem_product]
      refine ⟨⟨⟨hA, hB⟩, m1⟩, ⟨⟨hX1, hX2⟩, hA2, hB2⟩, m2, m3, ?_⟩
      have hdet := det_eq g
      have : g 0 1 * g 1 0 - (g 0 0 * ((g₀ 1 1).val : ℤ) + -1) =
          g 0 0 * (g 1 1 - ((g₀ 1 1).val : ℤ)) := by linear_combination -hdet
      rw [this]
      exact mul_dvd_mul_left _ m4⟩
  have hf : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [f, Subtype.mk.injEq, Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq] at h
    obtain ⟨e1, e2, e3⟩ := h
    have hu : g 0 0 ≠ 0 := by
      have := (h1 _ hg.1).1; omega
    have e4 : g 1 1 = g' 1 1 := by
      have d1 := det_eq g
      have d2 := det_eq g'
      rw [← e1, ← e2, ← e3] at d2
      have : g 0 0 * (g 1 1 - g' 1 1) = 0 := by linear_combination d1 - d2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hu
      · linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have hfin : Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g} := Finite.of_injective f hf
  refine ⟨hfin, ?_⟩
  calc Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g}
      ≤ Nat.card {x // x ∈ sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂} := Nat.card_le_card_of_injective f hf
    _ = #(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) :=
        Nat.card_eq_fintype_card.trans (Fintype.card_coe _)

/-- **Lower bound, case `U ≤ V`.** -/
theorem sigmaU_le_count (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ)
    (hfin : Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g})
    (h1 : ∀ u : ℤ, A₁ ≤ u → u < B₁ → (u : ℝ) / U ∈ I₁)
    (h2 : ∀ v : ℤ, A₂ ≤ v → v < B₂ → (v : ℝ) / V ∈ I₂)
    (h3 : ∀ u c : ℤ, A₁ ≤ u → X₁ u ≤ c → c < X₂ u → 0 ≤ c ∧ c < u ∧ (c : ℝ) / u ∈ I₃) :
    #(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) ≤ Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} := by
  classical
  have hdiv : ∀ x ∈ sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂, x.1 ∣ 1 + x.2.1 * x.2.2 := by
    intro x hx
    simp only [sigmaU, fiberU, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_product] at hx
    obtain ⟨_, _, _, _, h⟩ := hx
    have : x.1 ∣ x.2.1 * x.2.2 - (x.1 * ((g₀ 1 1).val : ℤ) + -1) :=
      (Dvd.intro _ rfl).trans h
    have e : 1 + x.2.1 * x.2.2 = (x.2.1 * x.2.2 - (x.1 * ((g₀ 1 1).val : ℤ) + -1)) +
        x.1 * ((g₀ 1 1).val : ℤ) := by ring
    rw [e]
    exact dvd_add this (Dvd.intro _ rfl)
  let f : {x // x ∈ sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂} → {g // RootPred S g₀ U V I₁ I₂ I₃ g} :=
    fun x => ⟨mkU x.1.1 x.1.2.1 x.1.2.2 (hdiv x.1 x.2), by
      obtain ⟨⟨u, c, v⟩, hx⟩ := x
      have hx' := hx
      simp only [sigmaU, fiberU, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_filter,
        Finset.mem_product] at hx'
      obtain ⟨⟨⟨hA, hB⟩, m1⟩, ⟨⟨hX1, hX2⟩, hA2, hB2⟩, m2, m3, m4⟩ := hx'
      obtain ⟨hc0, hcu, hr⟩ := h3 u c hA hX1 hX2
      have hu0 : u ≠ 0 := by omega
      have huv : u ∣ 1 + c * v := hdiv _ hx
      refine ⟨h1 u hA hB, h2 v hA2 hB2, hc0, hcu, hr, ?_⟩
      rw [map_eq_iff]
      refine ⟨m1, m2, m3, ?_⟩
      show (S : ℤ) ∣ (1 + c * v) / u - ((g₀ 1 1).val : ℤ)
      obtain ⟨k, hk⟩ := huv
      rw [hk, Int.mul_ediv_cancel_left _ hu0]
      have : u * S ∣ u * (k - ((g₀ 1 1).val : ℤ)) := by
        have e : u * (k - ((g₀ 1 1).val : ℤ)) = c * v - (u * ((g₀ 1 1).val : ℤ) + -1) := by
          linear_combination -hk
        rw [e]; exact m4
      exact (mul_dvd_mul_iff_left hu0).mp this⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨u, c, v⟩, hx⟩ ⟨⟨u', c', v'⟩, hx'⟩ h
    simp only [f, Subtype.mk.injEq] at h
    have e1 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 0 0) h
    have e2 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 0 1) h
    have e3 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 1 0) h
    simp only [mkU] at e1 e2 e3
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e2 e3
    subst e1; subst e2; subst e3
    rfl
  calc #(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) = Nat.card {x // x ∈ sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂} :=
        (Nat.card_eq_fintype_card.trans (Fintype.card_coe _)).symm
    _ ≤ Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} := Nat.card_le_card_of_injective f hf

/-- **Upper bound, case `V < U`.** -/
theorem count_le_sigmaV (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (hA₂ : 1 ≤ A₂)
    (h1 : ∀ u : ℤ, (u : ℝ) / U ∈ I₁ → A₁ ≤ u ∧ u < B₁)
    (h2 : ∀ v : ℤ, (v : ℝ) / V ∈ I₂ → A₂ ≤ v ∧ v < B₂)
    (h3 : ∀ u v c d : ℤ, A₁ ≤ u → A₂ ≤ v → u * d - c * v = 1 → 0 ≤ c → c < u →
      (c : ℝ) / u ∈ I₃ → X₁ v ≤ d ∧ d < X₂ v) :
    Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g} ∧
      Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} ≤ #(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) := by
  classical
  let f : {g // RootPred S g₀ U V I₁ I₂ I₃ g} → {x // x ∈ sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂} :=
    fun g => ⟨⟨g.1 1 0, (g.1 1 1, g.1 0 0)⟩, by
      obtain ⟨g, hu, hv, hc0, hcu, hr, hm⟩ := g
      obtain ⟨m1, m2, m3, m4⟩ := (map_eq_iff S g g₀).mp hm
      obtain ⟨hA, hB⟩ := h1 _ hu
      obtain ⟨hA2, hB2⟩ := h2 _ hv
      have hdet := det_eq g
      obtain ⟨hX1, hX2⟩ := h3 _ _ _ _ hA hA2 hdet hc0 hcu hr
      simp only [sigmaV, fiberV, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_filter,
        Finset.mem_product]
      refine ⟨⟨⟨hA2, hB2⟩, m3⟩, ⟨⟨hX1, hX2⟩, hA, hB⟩, m4, m1, ?_⟩
      have : g 1 1 * g 0 0 - (g 1 0 * ((g₀ 0 1).val : ℤ) + 1) =
          g 1 0 * (g 0 1 - ((g₀ 0 1).val : ℤ)) := by linear_combination hdet
      rw [this]
      exact mul_dvd_mul_left _ m2⟩
  have hf : Function.Injective f := by
    rintro ⟨g, hg⟩ ⟨g', hg'⟩ h
    simp only [f, Subtype.mk.injEq, Sigma.mk.inj_iff, Prod.mk.injEq, heq_eq_eq] at h
    obtain ⟨e3, e4, e1⟩ := h
    have hv : g 1 0 ≠ 0 := by
      have := (h2 _ hg.2.1).1; omega
    have e2 : g 0 1 = g' 0 1 := by
      have d1 := det_eq g
      have d2 := det_eq g'
      rw [← e1, ← e3, ← e4] at d2
      have : g 1 0 * (g 0 1 - g' 0 1) = 0 := by linear_combination d2 - d1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hv
      · linarith
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact e1
    · exact e2
    · exact e3
    · exact e4
  have hfin : Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g} := Finite.of_injective f hf
  refine ⟨hfin, ?_⟩
  calc Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g}
      ≤ Nat.card {x // x ∈ sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂} := Nat.card_le_card_of_injective f hf
    _ = #(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) :=
        Nat.card_eq_fintype_card.trans (Fintype.card_coe _)

/-- **Lower bound, case `V < U`.** -/
theorem sigmaV_le_count (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (hA₂ : 1 ≤ A₂)
    (hfin : Finite {g // RootPred S g₀ U V I₁ I₂ I₃ g})
    (h1 : ∀ u : ℤ, A₁ ≤ u → u < B₁ → (u : ℝ) / U ∈ I₁)
    (h2 : ∀ v : ℤ, A₂ ≤ v → v < B₂ → (v : ℝ) / V ∈ I₂)
    (h3 : ∀ u v d : ℤ, A₁ ≤ u → u < B₁ → A₂ ≤ v → v < B₂ → X₁ v ≤ d → d < X₂ v →
      v ∣ u * d - 1 →
      0 ≤ (u * d - 1) / v ∧ (u * d - 1) / v < u ∧ (((u * d - 1) / v : ℤ) : ℝ) / u ∈ I₃) :
    #(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) ≤ Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} := by
  classical
  have hdiv : ∀ x ∈ sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂, x.1 ∣ x.2.2 * x.2.1 - 1 := by
    intro x hx
    simp only [sigmaV, fiberV, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Ico,
      Finset.mem_product] at hx
    obtain ⟨_, _, _, _, h⟩ := hx
    have : x.1 ∣ x.2.1 * x.2.2 - (x.1 * ((g₀ 0 1).val : ℤ) + 1) :=
      (Dvd.intro _ rfl).trans h
    have e : x.2.2 * x.2.1 - 1 = (x.2.1 * x.2.2 - (x.1 * ((g₀ 0 1).val : ℤ) + 1)) +
        x.1 * ((g₀ 0 1).val : ℤ) := by ring
    rw [e]
    exact dvd_add this (Dvd.intro _ rfl)
  let f : {x // x ∈ sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂} → {g // RootPred S g₀ U V I₁ I₂ I₃ g} :=
    fun x => ⟨mkV x.1.2.2 x.1.2.1 x.1.1 (hdiv x.1 x.2), by
      obtain ⟨⟨v, d, u⟩, hx⟩ := x
      have hx' := hx
      simp only [sigmaV, fiberV, Finset.mem_sigma, Finset.mem_Ico, Finset.mem_filter,
        Finset.mem_product] at hx'
      obtain ⟨⟨⟨hA2, hB2⟩, m3⟩, ⟨⟨hX1, hX2⟩, hA, hB⟩, m4, m1, m2⟩ := hx'
      have hv0 : v ≠ 0 := by omega
      have hvd : v ∣ u * d - 1 := hdiv _ hx
      obtain ⟨hc0, hcu, hr⟩ := h3 u v d hA hB hA2 hB2 hX1 hX2 hvd
      refine ⟨h1 u hA hB, h2 v hA2 hB2, hc0, hcu, hr, ?_⟩
      rw [map_eq_iff]
      refine ⟨m1, ?_, m3, m4⟩
      show (S : ℤ) ∣ (u * d - 1) / v - ((g₀ 0 1).val : ℤ)
      obtain ⟨k, hk⟩ := hvd
      rw [hk, Int.mul_ediv_cancel_left _ hv0]
      have : v * S ∣ v * (k - ((g₀ 0 1).val : ℤ)) := by
        have e : v * (k - ((g₀ 0 1).val : ℤ)) = d * u - (v * ((g₀ 0 1).val : ℤ) + 1) := by
          linear_combination -hk
        rw [e]; exact m2
      exact (mul_dvd_mul_iff_left hv0).mp this⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨v, d, u⟩, hx⟩ ⟨⟨v', d', u'⟩, hx'⟩ h
    simp only [f, Subtype.mk.injEq] at h
    have e1 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 0 0) h
    have e3 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 1 0) h
    have e4 := congrArg (fun g : SpecialLinearGroup (Fin 2) ℤ => g 1 1) h
    simp only [mkV] at e1 e3 e4
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one] at e1 e3 e4
    subst e1; subst e3; subst e4
    rfl
  calc #(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) = Nat.card {x // x ∈ sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂} :=
        (Nat.card_eq_fintype_card.trans (Fintype.card_coe _)).symm
    _ ≤ Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} := Nat.card_le_card_of_injective f hf

omit [NeZero S] in
lemma card_sigmaU (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) :
    #(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) =
      ∑ u ∈ (Finset.Ico A₁ B₁).filter (fun u => (S : ℤ) ∣ u - ((g₀ 0 0).val : ℤ)),
        #(((Finset.Ico (X₁ u) (X₂ u)) ×ˢ (Finset.Ico A₂ B₂)).filter (fun p : ℤ × ℤ =>
          (S : ℤ) ∣ p.1 - ((g₀ 0 1).val : ℤ) ∧ (S : ℤ) ∣ p.2 - ((g₀ 1 0).val : ℤ) ∧
            u * S ∣ p.1 * p.2 - (u * ((g₀ 1 1).val : ℤ) + -1))) := by
  rw [sigmaU, Finset.card_sigma]; rfl

omit [NeZero S] in
lemma card_sigmaV (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) :
    #(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) =
      ∑ v ∈ (Finset.Ico A₂ B₂).filter (fun v => (S : ℤ) ∣ v - ((g₀ 1 0).val : ℤ)),
        #(((Finset.Ico (X₁ v) (X₂ v)) ×ˢ (Finset.Ico A₁ B₁)).filter (fun p : ℤ × ℤ =>
          (S : ℤ) ∣ p.1 - ((g₀ 1 1).val : ℤ) ∧ (S : ℤ) ∣ p.2 - ((g₀ 0 0).val : ℤ) ∧
            v * S ∣ p.1 * p.2 - (v * ((g₀ 0 1).val : ℤ) + 1))) := by
  rw [sigmaV, Finset.card_sigma]; rfl

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: integer ranges for real intervals, and small real lemmas for the assembly -/

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

/-- The outer range `⌈aU⌉ ≤ u < ⌊bU⌋ + 1` of `aU ≤ u ≤ bU`. -/
lemma outer_range (a b U : ℝ) (hab : a * U ≤ b * U) :
    ⌈a * U⌉ ≤ ⌊b * U⌋ + 1 ∧
      |((⌊b * U⌋ + 1 - ⌈a * U⌉ : ℤ) : ℝ) - (b * U - a * U)| ≤ 1 ∧
      ∀ u : ℤ, a * U ≤ u → (u : ℝ) ≤ b * U → ⌈a * U⌉ ≤ u ∧ u < ⌊b * U⌋ + 1 := by
  have h1 := Int.le_ceil (a * U)
  have h2 := Int.ceil_lt_add_one (a * U)
  have h3 := Int.floor_le (b * U)
  have h4 := Int.lt_floor_add_one (b * U)
  refine ⟨?_, ?_, ?_⟩
  · have : (⌈a * U⌉ : ℝ) < ⌊b * U⌋ + 2 := by linarith
    have : ⌈a * U⌉ < ⌊b * U⌋ + 2 := by exact_mod_cast this
    omega
  · push_cast; rw [abs_le]; constructor <;> linarith
  · intro u hu1 hu2
    exact ⟨Int.ceil_le.mpr hu1, Int.lt_add_one_iff.mpr (Int.le_floor.mpr hu2)⟩

/-- The inner range `⌊aU⌋ + 1 ≤ u < max ⌈bU⌉ (⌊aU⌋ + 1)` of `aU < u < bU`. -/
lemma inner_range (a b U : ℝ) (hab : a * U ≤ b * U) :
    ⌊a * U⌋ + 1 ≤ max ⌈b * U⌉ (⌊a * U⌋ + 1) ∧
      |((max ⌈b * U⌉ (⌊a * U⌋ + 1) - (⌊a * U⌋ + 1) : ℤ) : ℝ) - (b * U - a * U)| ≤ 1 ∧
      ∀ u : ℤ, ⌊a * U⌋ + 1 ≤ u → u < max ⌈b * U⌉ (⌊a * U⌋ + 1) → a * U < u ∧ (u : ℝ) < b * U := by
  have h1 := Int.le_ceil (b * U)
  have h2 := Int.ceil_lt_add_one (b * U)
  have h3 := Int.floor_le (a * U)
  have h4 := Int.lt_floor_add_one (a * U)
  refine ⟨le_max_right _ _, ?_, ?_⟩
  · rcases le_total ⌈b * U⌉ (⌊a * U⌋ + 1) with h | h
    · rw [max_eq_right h, sub_self, Int.cast_zero, zero_sub, abs_neg, abs_le]
      have : (⌈b * U⌉ : ℝ) ≤ ⌊a * U⌋ + 1 := by exact_mod_cast h
      constructor <;> linarith
    · rw [max_eq_left h]; push_cast; rw [abs_le]; constructor <;> linarith
  · intro u hu1 hu2
    have hu3 : u < ⌈b * U⌉ := by
      rcases le_total ⌈b * U⌉ (⌊a * U⌋ + 1) with h | h
      · rw [max_eq_right h] at hu2; omega
      · rwa [max_eq_left h] at hu2
    refine ⟨?_, Int.lt_ceil.mp hu3⟩
    have : (⌊a * U⌋ : ℝ) + 1 ≤ u := by exact_mod_cast hu1
    linarith

/-- The outer `x`-range `⌈αn⌉ ≤ x < min (⌊β'n⌋ + 1) n`. -/
lemma outer_X (α β β' : ℝ) (n : ℤ) (hn : 1 ≤ n) (hαβ : α ≤ β) (hββ' : β ≤ β')
    (hβ1 : β ≤ 1) :
    ⌈α * n⌉ ≤ min (⌊β' * n⌋ + 1) n ∧
      (β - α) * n - 1 ≤ ((min (⌊β' * n⌋ + 1) n - ⌈α * n⌉ : ℤ) : ℝ) ∧
      ((min (⌊β' * n⌋ + 1) n - ⌈α * n⌉ : ℤ) : ℝ) ≤ (β' - α) * n + 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Int.le_ceil (α * n)
  have h2 := Int.ceil_lt_add_one (α * n)
  have h3 := Int.floor_le (β' * n)
  have h4 := Int.lt_floor_add_one (β' * n)
  have hαn : α * n ≤ β' * n := mul_le_mul_of_nonneg_right (hαβ.trans hββ') (by linarith)
  have hβn : β * n ≤ n := mul_le_of_le_one_left (by linarith) hβ1
  have hαn' : α * n ≤ n := mul_le_of_le_one_left (by linarith) (by linarith)
  refine ⟨le_min ?_ ?_, ?_, ?_⟩
  · have : (⌈α * n⌉ : ℝ) < ⌊β' * n⌋ + 2 := by linarith
    have : ⌈α * n⌉ < ⌊β' * n⌋ + 2 := by exact_mod_cast this
    omega
  · exact Int.ceil_le.mpr hαn'
  · rcases le_total (⌊β' * n⌋ + 1) n with h | h
    · rw [min_eq_left h]; push_cast
      have : β * n ≤ β' * n := mul_le_mul_of_nonneg_right hββ' (by linarith)
      linarith
    · rw [min_eq_right h]; push_cast
      have e : (β - α) * n = β * n - α * n := by ring
      linarith
  · have : ((min (⌊β' * n⌋ + 1) n - ⌈α * n⌉ : ℤ) : ℝ) ≤ ((⌊β' * n⌋ + 1 - ⌈α * n⌉ : ℤ) : ℝ) := by
      exact_mod_cast (by omega : min (⌊β' * n⌋ + 1) n - ⌈α * n⌉ ≤ ⌊β' * n⌋ + 1 - ⌈α * n⌉)
    refine this.trans ?_
    push_cast; linarith

/-- The inner `x`-range `⌊α'n⌋ + 1 ≤ x < max ⌈βn⌉ (⌊α'n⌋ + 1)`. -/
lemma inner_X (α α' β : ℝ) (n : ℤ) (hn : 1 ≤ n) (hαα' : α ≤ α') (hαβ : α ≤ β) :
    ⌊α' * n⌋ + 1 ≤ max ⌈β * n⌉ (⌊α' * n⌋ + 1) ∧
      (β - α') * n - 1 ≤ ((max ⌈β * n⌉ (⌊α' * n⌋ + 1) - (⌊α' * n⌋ + 1) : ℤ) : ℝ) ∧
      ((max ⌈β * n⌉ (⌊α' * n⌋ + 1) - (⌊α' * n⌋ + 1) : ℤ) : ℝ) ≤ (β - α) * n + 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 := Int.le_ceil (β * n)
  have h2 := Int.ceil_lt_add_one (β * n)
  have h3 := Int.floor_le (α' * n)
  have h4 := Int.lt_floor_add_one (α' * n)
  have hαα'n : α * n ≤ α' * n := mul_le_mul_of_nonneg_right hαα' (by linarith)
  have hαβn : α * n ≤ β * n := mul_le_mul_of_nonneg_right hαβ (by linarith)
  refine ⟨le_max_right _ _, ?_, ?_⟩
  · rcases le_total ⌈β * n⌉ (⌊α' * n⌋ + 1) with h | h
    · rw [max_eq_right h, sub_self, Int.cast_zero]
      have : (⌈β * n⌉ : ℝ) ≤ ⌊α' * n⌋ + 1 := by exact_mod_cast h
      linarith
    · rw [max_eq_left h]; push_cast; linarith
  · rcases le_total ⌈β * n⌉ (⌊α' * n⌋ + 1) with h | h
    · rw [max_eq_right h, sub_self, Int.cast_zero]
      have e : (β - α) * n = β * n - α * n := by ring
      linarith
    · rw [max_eq_left h]; push_cast; linarith

/-- Comparing main terms. -/
lemma main_compare {θ P S X Y X' Y' : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hP : |P| ≤ 2)
    (hS : 1 ≤ S) (hX : |X - X'| ≤ 1) (hY : |Y - Y'| ≤ 1) (hX'0 : 0 ≤ X') (hY0 : 0 ≤ Y) :
    |θ * Y * X * P / S ^ 3 - θ * Y' * X' * P / S ^ 3| ≤ 2 * (Y + X') := by
  have hS3 : 1 ≤ S ^ 3 := one_le_pow₀ hS
  have e : θ * Y * X * P / S ^ 3 - θ * Y' * X' * P / S ^ 3 =
      θ * P / S ^ 3 * (Y * (X - X') + X' * (Y - Y')) := by ring
  rw [e, abs_mul]
  have hS3pos : 0 < S ^ 3 := by linarith
  have h1 : |θ * P / S ^ 3| ≤ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hθ0, abs_of_pos hS3pos]
    rw [div_le_iff₀ hS3pos]
    have : θ * |P| ≤ 1 * 2 := mul_le_mul hθ1 hP (abs_nonneg _) (by norm_num)
    linarith
  have h2 : |Y * (X - X') + X' * (Y - Y')| ≤ Y + X' := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hY0, abs_of_nonneg hX'0]
    have h1 := mul_le_of_le_one_right hY0 hX
    have h2 := mul_le_of_le_one_right hX'0 hY
    linarith
  calc |θ * P / S ^ 3| * |Y * (X - X') + X' * (Y - Y')| ≤ 2 * (Y + X') :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)

lemma abs_PS_le (S : ℕ) : |PS S| ≤ 2 := by
  have := abs_partial_PS_sub_le S 1 le_rfl
  simp only [Finset.range_one, Finset.sum_singleton, mu2_zero, ite_self, zero_sub, abs_neg,
    Nat.cast_one, div_one] at this
  exact this

end

end ArtinPrimitiveRoots.L102K

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

/-- `(BS)^{7/8} ≤ 17 w^{7/8} S` for `B ≤ 17w`. -/
lemma rpow_78_le {B w S : ℝ} (hB : 0 ≤ B) (hBw : B ≤ 17 * w) (hS : 1 ≤ S) :
    (B * S) ^ ((7 : ℝ) / 8) ≤ 17 * w ^ ((7 : ℝ) / 8) * S := by
  have hw : 0 ≤ w := by linarith
  have hS0 : 0 ≤ S := by linarith
  calc (B * S) ^ ((7 : ℝ) / 8) ≤ (17 * w * S) ^ ((7 : ℝ) / 8) :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_right hBw hS0) (by norm_num)
    _ = (17 : ℝ) ^ ((7 : ℝ) / 8) * w ^ ((7 : ℝ) / 8) * S ^ ((7 : ℝ) / 8) := by
        rw [Real.mul_rpow (by positivity) hS0, Real.mul_rpow (by norm_num) hw]
    _ ≤ 17 * w ^ ((7 : ℝ) / 8) * S := by
        have h1 : (17 : ℝ) ^ ((7 : ℝ) / 8) ≤ 17 := by
          calc (17 : ℝ) ^ ((7 : ℝ) / 8) ≤ (17 : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 17 := Real.rpow_one 17
        have h2 : S ^ ((7 : ℝ) / 8) ≤ S := by
          calc S ^ ((7 : ℝ) / 8) ≤ S ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hS (by norm_num)
            _ = S := Real.rpow_one S
        have h3 : 0 ≤ w ^ ((7 : ℝ) / 8) := by positivity
        have h4 : 0 ≤ S ^ ((7 : ℝ) / 8) := by positivity
        calc (17 : ℝ) ^ ((7 : ℝ) / 8) * w ^ ((7 : ℝ) / 8) * S ^ ((7 : ℝ) / 8)
            ≤ 17 * w ^ ((7 : ℝ) / 8) * S ^ ((7 : ℝ) / 8) := by gcongr
          _ ≤ 17 * w ^ ((7 : ℝ) / 8) * S := by gcongr

/-- `1 + log(17w) ≤ 10 √w`-type bound in the form `(39 + log(17w)) ≤ 49 w^{1/2}`. -/
lemma log_bound {w : ℝ} (hw : 1 ≤ w) : 39 + Real.log (17 * w) ≤ 49 * w ^ ((1 : ℝ) / 2) := by
  have h17 : 0 < 17 * w := by linarith
  have h1 := Real.log_le_rpow_div h17.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (17 * w) ^ ((1 : ℝ) / 2) = (17 : ℝ) ^ ((1 : ℝ) / 2) * w ^ ((1 : ℝ) / 2) :=
    Real.mul_rpow (by norm_num) (by linarith)
  have h3 : (17 : ℝ) ^ ((1 : ℝ) / 2) ≤ 5 := by
    rw [show (5 : ℝ) = (25 : ℝ) ^ ((1 : ℝ) / 2) by
      rw [show (25 : ℝ) = 5 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  have hw1 : 1 ≤ w ^ ((1 : ℝ) / 2) := Real.one_le_rpow hw (by norm_num)
  have h4 : Real.log (17 * w) ≤ 10 * w ^ ((1 : ℝ) / 2) := by
    calc Real.log (17 * w) ≤ (17 * w) ^ ((1 : ℝ) / 2) / (1 / 2) := h1
      _ = 2 * ((17 : ℝ) ^ ((1 : ℝ) / 2) * w ^ ((1 : ℝ) / 2)) := by rw [h2]; ring
      _ ≤ 2 * (5 * w ^ ((1 : ℝ) / 2)) := by gcongr
      _ = 10 * w ^ ((1 : ℝ) / 2) := by ring
  linarith

/-- **The error budget** of one case: everything is `≤ 20000 (K+1) S² w^{-1/8} w W`. -/
lemma error_budget {K S w W A B X Y θ F : ℝ} (hK : 0 ≤ K) (hS : 1 ≤ S) (hw : 1 ≤ w)
    (hwW : w ≤ W) (hA : w ≤ A) (hB1 : 1 ≤ B) (hB : B ≤ 17 * w) (hX : X ≤ 16 * w)
    (hY0 : 0 ≤ Y) (hY : Y ≤ 16 * W) (hθ1 : θ ≤ 1) (hF : F ≤ 64 * W) :
    X * (3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) + 2 * Y / A) +
        θ * Y * (3 + Real.log B) / S ^ 2 + F ≤
      20000 * (K + 1) * S ^ 2 * w ^ (-(1 : ℝ) / 8) * (w * W) := by
  have hw0 : 0 < w := by linarith
  have hA0 : 0 < A := by linarith
  have hS2 : 1 ≤ S ^ 2 := one_le_pow₀ hS
  have hW0 : 0 < W := by linarith
  -- pieces
  have hYA : Y / A ≤ 16 * W / w := by
    calc Y / A ≤ Y / w := div_le_div_of_nonneg_left hY0 hw0 hA
      _ ≤ 16 * W / w := div_le_div_of_nonneg_right hY hw0.le
  have hWw : 1 ≤ W / w := by rw [le_div_iff₀ hw0]; linarith
  have h8 : 8 + Y / A ≤ 24 * (W / w) := by
    have : 16 * W / w = 16 * (W / w) := by ring
    linarith
  have hBS := rpow_78_le (by linarith) hB hS
  have hw78 : w ^ ((7 : ℝ) / 8) = w * w ^ (-(1 : ℝ) / 8) := by
    rw [show ((7 : ℝ) / 8) = 1 + (-(1 : ℝ) / 8) by norm_num, Real.rpow_add hw0, Real.rpow_one]
  have hwneg : 0 < w ^ (-(1 : ℝ) / 8) := Real.rpow_pos_of_pos hw0 _
  set q := w ^ (-(1 : ℝ) / 8) with hq
  -- the first term
  have hT1 : X * (3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A)) ≤
      19584 * K * S ^ 2 * q * (w * W) := by
    have e1 : 3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) ≤
        3 * K * S * (17 * (w * q) * S) * (24 * (W / w)) := by
      rw [← hw78]
      have hKS : 0 ≤ 3 * K * S := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hBS hKS) h8 (by positivity) (by positivity)
    have e2 : 3 * K * S * (17 * (w * q) * S) * (24 * (W / w)) = 1224 * K * S ^ 2 * q * W := by
      field_simp; ring
    rw [e2] at e1
    calc X * (3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A))
        ≤ (16 * w) * (1224 * K * S ^ 2 * q * W) :=
          mul_le_mul hX e1 (by positivity) (by positivity)
      _ = 19584 * K * S ^ 2 * q * (w * W) := by ring
  -- the second term
  have hT2 : X * (2 * Y / A) ≤ 512 * W := by
    have : 2 * Y / A ≤ 32 * W / w := by
      have := hYA; rw [mul_div_assoc] at this ⊢
      calc 2 * (Y / A) ≤ 2 * (16 * W / w) := by linarith
        _ = 32 * (W / w) := by ring
        _ = 32 * W / w := by ring
    calc X * (2 * Y / A) ≤ (16 * w) * (32 * W / w) :=
          mul_le_mul hX this (by positivity) (by positivity)
      _ = 512 * W := by field_simp; ring
  -- the third term
  have hlogB : Real.log B ≤ Real.log (17 * w) := Real.log_le_log (by linarith) hB
  have hT3 : θ * Y * (3 + Real.log B) / S ^ 2 ≤ 16 * W * (3 + Real.log (17 * w)) := by
    have hlog0 : 0 ≤ 3 + Real.log B := by linarith [Real.log_nonneg hB1]
    rw [div_le_iff₀ (by positivity)]
    have h1 : θ * Y ≤ 16 * W := le_trans (mul_le_of_le_one_left hY0 hθ1) hY
    have h2 : θ * Y * (3 + Real.log B) ≤ 16 * W * (3 + Real.log (17 * w)) :=
      mul_le_mul h1 (by linarith) hlog0 (by positivity)
    have h3 : 0 ≤ 16 * W * (3 + Real.log (17 * w)) := by
      have : 0 ≤ Real.log (17 * w) := Real.log_nonneg (by linarith)
      positivity
    have h4 := le_mul_of_one_le_right h3 hS2
    linarith
  have hT4 : F ≤ 64 * W := hF
  -- the logarithmic terms are `≤ 784 q w W`
  have hlog := log_bound hw
  have hsqrt : w ^ ((1 : ℝ) / 2) ≤ w * q := by
    rw [hq, ← Real.rpow_one_add' hw0.le (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le hw (by norm_num)
  have hrest : 512 * W + 16 * W * (3 + Real.log (17 * w)) + 64 * W ≤ 784 * q * (w * W) := by
    have h1 : 512 * W + 16 * W * (3 + Real.log (17 * w)) + 64 * W =
        16 * W * (39 + Real.log (17 * w)) := by ring
    rw [h1]
    calc 16 * W * (39 + Real.log (17 * w)) ≤ 16 * W * (49 * w ^ ((1 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 16 * W * (49 * (w * q)) := by gcongr
      _ = 784 * q * (w * W) := by ring
  have hfinal : 19584 * K * S ^ 2 * q * (w * W) + 784 * q * (w * W) ≤
      20000 * (K + 1) * S ^ 2 * q * (w * W) := by
    have hqw : 0 ≤ q * (w * W) := by positivity
    have h784 : 784 ≤ 20000 * S ^ 2 := by linarith
    have hKS : 0 ≤ K * S ^ 2 * (q * (w * W)) := by positivity
    have h2 : 784 * (q * (w * W)) ≤ 20000 * S ^ 2 * (q * (w * W)) :=
      mul_le_mul_of_nonneg_right h784 hqw
    have e : 20000 * (K + 1) * S ^ 2 * q * (w * W) =
        20000 * (K * S ^ 2 * (q * (w * W))) + 20000 * S ^ 2 * (q * (w * W)) := by ring
    have e2 : 19584 * K * S ^ 2 * q * (w * W) = 19584 * (K * S ^ 2 * (q * (w * W))) := by ring
    have e3 : 784 * q * (w * W) = 784 * (q * (w * W)) := by ring
    rw [e, e2, e3]
    linarith
  calc X * (3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A) + 2 * Y / A) +
        θ * Y * (3 + Real.log B) / S ^ 2 + F
      = X * (3 * K * S * (B * S) ^ ((7 : ℝ) / 8) * (8 + Y / A)) + X * (2 * Y / A) +
          θ * Y * (3 + Real.log B) / S ^ 2 + F := by ring
    _ ≤ 19584 * K * S ^ 2 * q * (w * W) + 512 * W + 16 * W * (3 + Real.log (17 * w)) +
          64 * W := by linarith
    _ ≤ 19584 * K * S ^ 2 * q * (w * W) + 784 * q * (w * W) := by linarith
    _ ≤ 20000 * (K + 1) * S ^ 2 * q * (w * W) := hfinal

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: `|SL₂(ℤ/S)| = S³ ∑_{d ∣ S} μ(d)/d²` ([21] (3.29))

Unimodular columns are counted by Möbius inversion (`#{d ∣ u, d ∣ v} = (S/d)²`), and each
unimodular column has exactly `S` completions. -/

namespace ArtinPrimitiveRoots.L102K

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

/-- A column `(u, v)` is unimodular iff `(u, v, S) = 1`. -/
lemma exists_completion_iff (S : ℕ) [NeZero S] (u v : ZMod S) :
    (∃ c d : ZMod S, u * d - c * v = 1) ↔ Nat.gcd (Nat.gcd u.val v.val) S = 1 := by
  set g := Nat.gcd (Nat.gcd u.val v.val) S with hg
  constructor
  · rintro ⟨c, d, h⟩
    have hgS : g ∣ S := Nat.gcd_dvd_right _ _
    let π := ZMod.castHom hgS (ZMod g)
    have hu : π u = 0 := by
      have : π u = ((u.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val u]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    have hv : π v = 0 := by
      have : π v = ((v.val : ℕ) : ZMod g) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val v]
        rw [map_natCast]
      rw [this, ZMod.natCast_eq_zero_iff]
      exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    have h1 := congrArg π h
    rw [map_sub, map_mul, map_mul, hu, hv, map_one] at h1
    simp only [zero_mul, mul_zero, sub_zero] at h1
    have h01 : (0 : ZMod g) = 1 := h1
    have := ZMod.natCast_self g
    by_contra hne
    have hg1 : 1 < g ∨ g = 0 := by omega
    rcases hg1 with hg1 | hg0
    · have : Fact (1 < g) := ⟨hg1⟩
      exact zero_ne_one h01
    · have h0 : Nat.gcd (Nat.gcd u.val v.val) S = 0 := hg0
      exact NeZero.ne S (Nat.gcd_eq_zero_iff.mp h0).2
  · intro h1
    -- Bezout in `ℤ`
    have hcop : IsCoprime ((Nat.gcd u.val v.val : ℕ) : ℤ) (S : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]; exact h1
    obtain ⟨a, b, hab⟩ := hcop
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, ((Nat.gcd u.val v.val : ℕ) : ℤ) = x * u.val + y * v.val := by
      refine ⟨Nat.gcdA u.val v.val, Nat.gcdB u.val v.val, ?_⟩
      rw [Nat.gcd_eq_gcd_ab]; ring
    refine ⟨-((a * y : ℤ) : ZMod S), ((a * x : ℤ) : ZMod S), ?_⟩
    have h2 : (((a * (x * u.val + y * v.val) + b * S : ℤ)) : ZMod S) = 1 := by
      rw [← hxy, hab]; simp
    push_cast at h2
    rw [ZMod.natCast_self, mul_zero, add_zero, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2
    rw [← h2]; push_cast; ring

/-- A unimodular column has exactly `S` completions. -/
lemma card_completions (S : ℕ) [NeZero S] (u v : ZMod S) (c₀ d₀ : ZMod S)
    (h₀ : u * d₀ - c₀ * v = 1) :
    #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) = S := by
  classical
  suffices h : #(univ : Finset (ZMod S)) =
      #((univ : Finset (ZMod S × ZMod S)).filter (fun q => u * q.2 - q.1 * v = 1)) by
    rw [← h, Finset.card_univ, ZMod.card]
  refine Finset.card_bij (fun t _ => (c₀ + t * u, d₀ + t * v)) ?_ ?_ ?_
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    linear_combination h₀
  · intro t _ t' _ h
    simp only [Prod.mk.injEq] at h
    have e1 : (t - t') * u = 0 := by linear_combination h.1
    have e2 : (t - t') * v = 0 := by linear_combination h.2
    have : t - t' = 0 := by
      have : (t - t') * (u * d₀ - c₀ * v) = 0 := by linear_combination d₀ * e1 - c₀ * e2
      rwa [h₀, mul_one] at this
    exact sub_eq_zero.mp this
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    refine ⟨d₀ * (q.1 - c₀) - c₀ * (q.2 - d₀), Finset.mem_univ _, ?_⟩
    ext
    · simp only
      linear_combination q.1 * h₀ - c₀ * hq
    · simp only
      linear_combination q.2 * h₀ - d₀ * hq

/-- `#{(u, v) : (u, v, S) = 1} = ∑_{d ∣ S} μ(d) (S/d)²`. -/
lemma card_unimodular (S : ℕ) [NeZero S] :
    ((#((univ : Finset (ZMod S × ZMod S)).filter
        (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) : ℕ) : ℤ) =
      ∑ d ∈ S.divisors, μ d * (((S / d) ^ 2 : ℕ) : ℤ) := by
  classical
  have hS : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  rw [Finset.card_filter, Nat.cast_sum]
  have h1 : ∀ p : ZMod S × ZMod S, (((if Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1 then 1 else 0 :
      ℕ)) : ℤ) = ∑ d ∈ S.divisors, if d ∣ p.1.val ∧ d ∣ p.2.val then μ d else 0 := by
    intro p
    have hg0 : Nat.gcd (Nat.gcd p.1.val p.2.val) S ≠ 0 := (Nat.gcd_pos_of_pos_right _ hS).ne'
    rw [← Finset.sum_filter]
    have hset : S.divisors.filter (fun d => d ∣ p.1.val ∧ d ∣ p.2.val) =
        (Nat.gcd (Nat.gcd p.1.val p.2.val) S).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hdS, _⟩, h1, h2⟩; exact ⟨⟨⟨h1, h2⟩, hdS⟩, hg0⟩
      · rintro ⟨⟨⟨h1, h2⟩, hdS⟩, _⟩; exact ⟨⟨hdS, hS.ne'⟩, h1, h2⟩
    rw [hset, ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun p _ => h1 p, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdS hS
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  congr 1
  have : (univ : Finset (ZMod S × ZMod S)).filter (fun p => d ∣ p.1.val ∧ d ∣ p.2.val) =
      (univ.filter fun x : ZMod S => d ∣ x.val) ×ˢ (univ.filter fun x : ZMod S => d ∣ x.val) := by
    ext p; simp
  rw [this, Finset.card_product, card_dvd_val S d hd0 hdS]
  push_cast; ring

/-- The matrix entries `((a, c), (b, d))` of `!![a, b; c, d]`. -/
def matPairs (R : Type*) : Matrix (Fin 2) (Fin 2) R ≃ (R × R) × (R × R) where
  toFun M := ((M 0 0, M 1 0), (M 0 1, M 1 1))
  invFun x := !![x.1.1, x.2.1; x.1.2, x.2.2]
  left_inv M := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  right_inv x := rfl

/-- **(3.29)**: `|SL₂(ℤ/S)| = S³ ∑_{d ∣ S} μ(d)/d²`. -/
theorem card_SL2 (S : ℕ) (hS : 0 < S) :
    (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) = (S : ℝ) ^ 3 * JS S := by
  classical
  have : NeZero S := ⟨hS.ne'⟩
  -- `SL₂` as quadruples
  have h1 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) =
      #((univ : Finset ((ZMod S × ZMod S) × (ZMod S × ZMod S))).filter
        (fun x => x.1.1 * x.2.2 - x.2.1 * x.1.2 = 1)) := by
    rw [Nat.card_eq_fintype_card]
    rw [show Fintype.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) =
      Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod S) // M.det = 1} from rfl]
    rw [Fintype.card_subtype]
    refine Finset.card_bij (fun M _ => matPairs (ZMod S) M) ?_ ?_ ?_
    · intro M hM
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
      simp only [matPairs]
      rw [Matrix.det_fin_two] at hM
      linear_combination hM
    · intro M _ M' _ h; exact (matPairs (ZMod S)).injective h
    · intro x hx
      refine ⟨(matPairs (ZMod S)).symm x, ?_, (matPairs (ZMod S)).apply_symm_apply x⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hm : (matPairs (ZMod S)).symm x = !![x.1.1, x.2.1; x.1.2, x.2.2] := rfl
      rw [hm, Matrix.det_fin_two_of]
      linear_combination hx
  -- fibre over the first column
  have h2 : #((univ : Finset ((ZMod S × ZMod S) × (ZMod S × ZMod S))).filter
        (fun x => x.1.1 * x.2.2 - x.2.1 * x.1.2 = 1)) =
      S * #((univ : Finset (ZMod S × ZMod S)).filter
        (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) := by
    rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product, Finset.card_filter,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.card_filter]
    by_cases hp : Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1
    · rw [if_pos hp, mul_one]
      obtain ⟨c₀, d₀, h₀⟩ := (exists_completion_iff S p.1 p.2).mpr hp
      exact card_completions S p.1 p.2 c₀ d₀ h₀
    · rw [if_neg hp, mul_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q _ hq
      exact hp ((exists_completion_iff S p.1 p.2).mp ⟨q.1, q.2, hq⟩)
  rw [h1, h2]
  have h3 := card_unimodular S
  have h4 : ((#((univ : Finset (ZMod S × ZMod S)).filter
      (fun p => Nat.gcd (Nat.gcd p.1.val p.2.val) S = 1)) : ℕ) : ℝ) =
      ∑ d ∈ S.divisors, (μ d : ℝ) * (((S / d) ^ 2 : ℕ) : ℝ) := by
    have := congrArg (Int.cast : ℤ → ℝ) h3
    push_cast at this ⊢
    exact this
  push_cast
  rw [h4, JS, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdS : d ∣ S := Nat.dvd_of_mem_divisors hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_dvd_of_pos hdS hS
  rw [mu2, Nat.cast_pow, Nat.cast_div hdS hd0.ne']
  field_simp

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: the two cases of Lemma 3.3

Case `U ≤ V`: sum over `u = g₀₀`. Case `V < U`: sum over `v = g₁₀`, using `d/v = c/u + 1/(uv)`.
Each gives `|N − θ V|I₂| U|I₁| P(S)/S³| ≤ 20000 (K+1) S² w^{-1/8} UV`, `w = min(U, V)`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

lemma mem_Icc_div {x U a b : ℝ} (hU : 0 < U) (h : x / U ∈ Set.Icc a b) :
    a * U ≤ x ∧ x ≤ b * U :=
  ⟨(le_div_iff₀ hU).mp h.1, (div_le_iff₀ hU).mp h.2⟩

lemma mem_Ioo_div {x U a b : ℝ} (hU : 0 < U) (h1 : a * U < x) (h2 : x < b * U) :
    x / U ∈ Set.Ioo a b :=
  ⟨(lt_div_iff₀ hU).mpr h1, (div_lt_iff₀ hU).mpr h2⟩

lemma sandwich' {N N₁ N₂ M E : ℝ} (h1 : N₁ ≤ N) (h2 : N ≤ N₂) (hb1 : |N₁ - M| ≤ E)
    (hb2 : |N₂ - M| ≤ E) : |N - M| ≤ E := by
  rw [abs_le] at hb1 hb2 ⊢
  constructor <;> linarith

/-- The sigma count over `u`, for generic ranges. -/
theorem sigma_count_U (S : ℕ) [NeZero S] (hS : Squarefree S)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V θ X' Y' : ℝ) (hU : 1 ≤ U) (hUV : U ≤ V)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hX'0 : 0 ≤ X') (hX'15 : X' ≤ 15 * U) (hY'V : Y' ≤ V)
    (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (hUA : U ≤ A₁) (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂)
    (hB17 : (B₁ : ℝ) ≤ 17 * U)
    (hlen₁ : |((B₁ - A₁ : ℤ) : ℝ) - X'| ≤ 1) (hlen₂ : |((B₂ - A₂ : ℤ) : ℝ) - Y'| ≤ 1)
    (hX : ∀ n, A₁ ≤ n → n < B₁ → X₁ n ≤ X₂ n ∧ |((X₂ n - X₁ n : ℤ) : ℝ) - θ * n| ≤ 2)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8)) :
    |((#(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y' * X' * PS S / (S : ℝ) ^ 3| ≤
      20000 * (K + 1) * (S : ℝ) ^ 2 * U ^ (-(1 : ℝ) / 8) * (U * V) := by
  have hS0 : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS0
  have hA₁ : 1 ≤ A₁ := by
    have : (1 : ℝ) ≤ A₁ := le_trans hU hUA
    exact_mod_cast this
  have hcong : (S : ℤ) ∣ ((g₀ 0 0).val : ℤ) * ((g₀ 1 1).val : ℤ) + -1 -
      ((g₀ 0 1).val : ℤ) * ((g₀ 1 0).val : ℤ) := by
    have := det_rep S g₀
    have e : ((g₀ 0 0).val : ℤ) * ((g₀ 1 1).val : ℤ) + -1 -
        ((g₀ 0 1).val : ℤ) * ((g₀ 1 0).val : ℤ) = ((g₀ 0 0).val : ℤ) * ((g₀ 1 1).val : ℤ) -
          ((g₀ 0 1).val : ℤ) * ((g₀ 1 0).val : ℤ) - 1 := by ring
    rw [e]; exact this
  have hsum := sum_fibers S hS0 hS ((g₀ 0 0).val : ℤ) ((g₀ 0 1).val : ℤ) ((g₀ 1 0).val : ℤ)
    ((g₀ 1 1).val : ℤ) (-1) (Or.inr rfl) hcong A₁ B₁ A₂ B₂ hA₁ hAB₁ hAB₂ X₁ X₂ θ hθ0
    (by linarith) hX K hK
  have hcard := card_sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂
  rw [← Nat.cast_sum, ← hcard] at hsum
  have hP := abs_PS_le S
  set X := ((B₁ - A₁ : ℤ) : ℝ) with hXdef
  set Y := ((B₂ - A₂ : ℤ) : ℝ) with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact_mod_cast (by omega : (0 : ℤ) ≤ B₂ - A₂)
  have hm := main_compare hθ0 hθ1 hP hSR hlen₁ hlen₂ hX'0 hY0
  have hYle : Y ≤ Y' + 1 := by linarith [(abs_le.mp hlen₂).2]
  have hXle : X ≤ X' + 1 := by linarith [(abs_le.mp hlen₁).2]
  have hB1 : (1 : ℝ) ≤ B₁ := by
    have : (A₁ : ℝ) ≤ B₁ := by exact_mod_cast hAB₁
    linarith
  have hbud := error_budget (K := K) (S := S) (w := U) (W := V) (A := (A₁ : ℝ)) (B := (B₁ : ℝ))
    (X := X) (Y := Y) (θ := θ) (F := 2 * (Y + X')) hK0 hSR hU hUV hUA hB1 hB17 (by linarith)
    hY0 (by linarith) hθ1 (by linarith)
  calc |((#(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y' * X' * PS S / (S : ℝ) ^ 3|
      ≤ |((#(sigmaU S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y * X * PS S / (S : ℝ) ^ 3| +
          |θ * Y * X * PS S / (S : ℝ) ^ 3 - θ * Y' * X' * PS S / (S : ℝ) ^ 3| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsum hm
    _ ≤ _ := by linarith [hbud]

/-- The sigma count over `v`, for generic ranges. -/
theorem sigma_count_V (S : ℕ) [NeZero S] (hS : Squarefree S)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V θ X' Y' : ℝ) (hV : 1 ≤ V) (hVU : V ≤ U)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hX'0 : 0 ≤ X') (hX'V : X' ≤ V) (hY'15 : Y' ≤ 15 * U)
    (A₁ B₁ A₂ B₂ : ℤ) (X₁ X₂ : ℤ → ℤ) (hVA : V ≤ A₂) (hAB₁ : A₁ ≤ B₁) (hAB₂ : A₂ ≤ B₂)
    (hB17 : (B₂ : ℝ) ≤ 17 * V)
    (hlen₂ : |((B₂ - A₂ : ℤ) : ℝ) - X'| ≤ 1) (hlen₁ : |((B₁ - A₁ : ℤ) : ℝ) - Y'| ≤ 1)
    (hX : ∀ n, A₂ ≤ n → n < B₂ → X₁ n ≤ X₂ n ∧ |((X₂ n - X₁ n : ℤ) : ℝ) - θ * n| ≤ 2)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8)) :
    |((#(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y' * X' * PS S / (S : ℝ) ^ 3| ≤
      20000 * (K + 1) * (S : ℝ) ^ 2 * V ^ (-(1 : ℝ) / 8) * (V * U) := by
  have hS0 : 0 < S := Nat.pos_of_ne_zero (NeZero.ne S)
  have hSR : (1 : ℝ) ≤ S := by exact_mod_cast hS0
  have hA₂ : 1 ≤ A₂ := by
    have : (1 : ℝ) ≤ A₂ := le_trans hV hVA
    exact_mod_cast this
  have hcong : (S : ℤ) ∣ ((g₀ 1 0).val : ℤ) * ((g₀ 0 1).val : ℤ) + 1 -
      ((g₀ 1 1).val : ℤ) * ((g₀ 0 0).val : ℤ) := by
    have := det_rep S g₀
    have e : ((g₀ 1 0).val : ℤ) * ((g₀ 0 1).val : ℤ) + 1 -
        ((g₀ 1 1).val : ℤ) * ((g₀ 0 0).val : ℤ) = -(((g₀ 0 0).val : ℤ) * ((g₀ 1 1).val : ℤ) -
          ((g₀ 0 1).val : ℤ) * ((g₀ 1 0).val : ℤ) - 1) := by ring
    rw [e]; exact dvd_neg.mpr this
  have hsum := sum_fibers S hS0 hS ((g₀ 1 0).val : ℤ) ((g₀ 1 1).val : ℤ) ((g₀ 0 0).val : ℤ)
    ((g₀ 0 1).val : ℤ) 1 (Or.inl rfl) hcong A₂ B₂ A₁ B₁ hA₂ hAB₂ hAB₁ X₁ X₂ θ hθ0
    (by linarith) hX K hK
  have hcard := card_sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂
  rw [← Nat.cast_sum, ← hcard] at hsum
  have hP := abs_PS_le S
  set X := ((B₂ - A₂ : ℤ) : ℝ) with hXdef
  set Y := ((B₁ - A₁ : ℤ) : ℝ) with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef]; exact_mod_cast (by omega : (0 : ℤ) ≤ B₁ - A₁)
  have hm := main_compare hθ0 hθ1 hP hSR hlen₂ hlen₁ hX'0 hY0
  have hYle : Y ≤ Y' + 1 := by linarith [(abs_le.mp hlen₁).2]
  have hXle : X ≤ X' + 1 := by linarith [(abs_le.mp hlen₂).2]
  have hB1 : (1 : ℝ) ≤ B₂ := by
    have : (A₂ : ℝ) ≤ B₂ := by exact_mod_cast hAB₂
    linarith
  have hbud := error_budget (K := K) (S := S) (w := V) (W := U) (A := (A₂ : ℝ)) (B := (B₂ : ℝ))
    (X := X) (Y := Y) (θ := θ) (F := 2 * (Y + X')) hK0 hSR hV hVU hVA hB1 hB17 (by linarith)
    hY0 (by linarith) hθ1 (by linarith)
  calc |((#(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y' * X' * PS S / (S : ℝ) ^ 3|
      ≤ |((#(sigmaV S g₀ A₁ B₁ A₂ B₂ X₁ X₂) : ℕ) : ℝ) - θ * Y * X * PS S / (S : ℝ) ^ 3| +
          |θ * Y * X * PS S / (S : ℝ) ^ 3 - θ * Y' * X' * PS S / (S : ℝ) ^ 3| := abs_sub_le _ _ _
    _ ≤ _ := add_le_add hsum hm
    _ ≤ _ := by linarith [hbud]

/-- **Case `U ≤ V`.** -/
theorem case_U (S : ℕ) [NeZero S] (hS : Squarefree S)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ) (hU : 3 ≤ U) (hUV : U ≤ V)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) (ha₁ : 1 ≤ a₁) (hab₁ : a₁ ≤ b₁) (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂)
    (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2) (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1)
    (I₁ I₂ I₃ : Set ℝ) (hI₁ : Set.Ioo a₁ b₁ ⊆ I₁) (hI₁' : I₁ ⊆ Set.Icc a₁ b₁)
    (hI₂ : Set.Ioo a₂ b₂ ⊆ I₂) (hI₂' : I₂ ⊆ Set.Icc a₂ b₂)
    (hI₃ : Set.Ioo a₃ b₃ ⊆ I₃) (hI₃' : I₃ ⊆ Set.Icc a₃ b₃)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8)) :
    |(Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} : ℝ) -
        (b₃ - a₃) * (V * (b₂ - a₂)) * (U * (b₁ - a₁)) * PS S / (S : ℝ) ^ 3| ≤
      20000 * (K + 1) * (S : ℝ) ^ 2 * U ^ (-(1 : ℝ) / 8) * (U * V) := by
  classical
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hθ0 : 0 ≤ b₃ - a₃ := by linarith
  have hθ1 : b₃ - a₃ ≤ 1 := by linarith
  have haU : a₁ * U ≤ b₁ * U := mul_le_mul_of_nonneg_right hab₁ hU0.le
  have haV : a₂ * V ≤ b₂ * V := mul_le_mul_of_nonneg_right hab₂ hV0.le
  obtain ⟨hAB₁, hlen₁, hmem₁⟩ := outer_range a₁ b₁ U haU
  obtain ⟨hAB₂, hlen₂, hmem₂⟩ := outer_range a₂ b₂ V haV
  obtain ⟨hAB₁', hlen₁', hmem₁'⟩ := inner_range a₁ b₁ U haU
  obtain ⟨hAB₂', hlen₂', hmem₂'⟩ := inner_range a₂ b₂ V haV
  have hUa : U ≤ a₁ * U := le_mul_of_one_le_left hU0.le ha₁
  have hbU : b₁ * U ≤ 16 * U := mul_le_mul_of_nonneg_right hb₁ hU0.le
  have hUA : U ≤ (⌈a₁ * U⌉ : ℝ) := le_trans hUa (Int.le_ceil _)
  have hUA' : U ≤ ((⌊a₁ * U⌋ + 1 : ℤ) : ℝ) := by
    push_cast; linarith [Int.lt_floor_add_one (a₁ * U)]
  have hA₁ : 1 ≤ ⌈a₁ * U⌉ := by
    have : (1 : ℝ) ≤ ⌈a₁ * U⌉ := by linarith
    exact_mod_cast this
  have hA₁' : 1 ≤ ⌊a₁ * U⌋ + 1 := by
    have : (1 : ℝ) ≤ ((⌊a₁ * U⌋ + 1 : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  have hX'0 : 0 ≤ U * (b₁ - a₁) := mul_nonneg hU0.le (by linarith)
  have hX'15 : U * (b₁ - a₁) ≤ 15 * U := by
    rw [mul_comm 15 U]; exact mul_le_mul_of_nonneg_left (by linarith) hU0.le
  have hY'V : V * (b₂ - a₂) ≤ V := mul_le_of_le_one_right hV0.le (by linarith)
  -- upper bound
  obtain ⟨hfin, hN_le⟩ := count_le_sigmaU S g₀ U V I₁ I₂ I₃ ⌈a₁ * U⌉ (⌊b₁ * U⌋ + 1) ⌈a₂ * V⌉
    (⌊b₂ * V⌋ + 1) (fun u => ⌈a₃ * u⌉) (fun u => min (⌊b₃ * u⌋ + 1) u) hA₁
    (fun u hu => by obtain ⟨h1, h2⟩ := mem_Icc_div hU0 (hI₁' hu); exact hmem₁ u h1 h2)
    (fun v hv => by obtain ⟨h1, h2⟩ := mem_Icc_div hV0 (hI₂' hv); exact hmem₂ v h1 h2)
    (fun u c hu hc0 hcu hr => by
      have hu0 : (0 : ℝ) < u := by
        have : (1 : ℤ) ≤ u := le_trans hA₁ hu
        exact_mod_cast (by omega : (0 : ℤ) < u)
      obtain ⟨h1, h2⟩ := mem_Icc_div hu0 (hI₃' hr)
      exact ⟨Int.ceil_le.mpr h1, lt_min (Int.lt_add_one_iff.mpr (Int.le_floor.mpr h2)) hcu⟩)
  -- lower bound
  have hN_ge := sigmaU_le_count S g₀ U V I₁ I₂ I₃ (⌊a₁ * U⌋ + 1) (max ⌈b₁ * U⌉ (⌊a₁ * U⌋ + 1))
    (⌊a₂ * V⌋ + 1) (max ⌈b₂ * V⌉ (⌊a₂ * V⌋ + 1)) (fun u => ⌊a₃ * u⌋ + 1)
    (fun u => max ⌈b₃ * u⌉ (⌊a₃ * u⌋ + 1)) hfin
    (fun u h1 h2 => hI₁ (mem_Ioo_div hU0 (hmem₁' u h1 h2).1 (hmem₁' u h1 h2).2))
    (fun v h1 h2 => hI₂ (mem_Ioo_div hV0 (hmem₂' v h1 h2).1 (hmem₂' v h1 h2).2))
    (fun u c hu h1 h2 => by
      have hu1 : (1 : ℤ) ≤ u := le_trans hA₁' hu
      have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : (0 : ℤ) < u)
      obtain ⟨-, -, hm⟩ := inner_range a₃ b₃ (u : ℝ)
        (mul_le_mul_of_nonneg_right hab₃ hu0.le)
      obtain ⟨hc1, hc2⟩ := hm c h1 h2
      have hc0 : (0 : ℝ) < c := lt_of_le_of_lt (by positivity) hc1
      have hcu : (c : ℝ) < u := lt_of_lt_of_le hc2 (mul_le_of_le_one_left hu0.le hb₃)
      refine ⟨by exact_mod_cast hc0.le, by exact_mod_cast hcu, hI₃ (mem_Ioo_div hu0 hc1 hc2)⟩)
  -- the two sigma counts
  have hout := sigma_count_U S hS g₀ U V (b₃ - a₃) (U * (b₁ - a₁)) (V * (b₂ - a₂)) (by linarith)
    hUV hθ0 hθ1 hX'0 hX'15 hY'V ⌈a₁ * U⌉ (⌊b₁ * U⌋ + 1) ⌈a₂ * V⌉ (⌊b₂ * V⌋ + 1)
    (fun u => ⌈a₃ * u⌉) (fun u => min (⌊b₃ * u⌋ + 1) u) hUA hAB₁ hAB₂
    (by push_cast; linarith [Int.floor_le (b₁ * U)])
    (by convert hlen₁ using 2; ring) (by convert hlen₂ using 2; ring)
    (fun n hn _ => by
      obtain ⟨h1, h2, h3⟩ := outer_X a₃ b₃ b₃ n (le_trans hA₁ hn) hab₃ le_rfl hb₃
      exact ⟨h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩) K hK0 hK
  have hin := sigma_count_U S hS g₀ U V (b₃ - a₃) (U * (b₁ - a₁)) (V * (b₂ - a₂)) (by linarith)
    hUV hθ0 hθ1 hX'0 hX'15 hY'V (⌊a₁ * U⌋ + 1) (max ⌈b₁ * U⌉ (⌊a₁ * U⌋ + 1)) (⌊a₂ * V⌋ + 1)
    (max ⌈b₂ * V⌉ (⌊a₂ * V⌋ + 1)) (fun u => ⌊a₃ * u⌋ + 1)
    (fun u => max ⌈b₃ * u⌉ (⌊a₃ * u⌋ + 1)) hUA' hAB₁' hAB₂'
    (by
      have h1 := Int.ceil_lt_add_one (b₁ * U)
      have h2 := Int.floor_le (a₁ * U)
      push_cast
      exact max_le (by linarith) (by linarith))
    (by convert hlen₁' using 2; ring) (by convert hlen₂' using 2; ring)
    (fun n hn _ => by
      obtain ⟨h1, h2, h3⟩ := inner_X a₃ a₃ b₃ n (le_trans hA₁' hn) le_rfl hab₃
      exact ⟨h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩) K hK0 hK
  exact sandwich' (by exact_mod_cast hN_ge) (by exact_mod_cast hN_le) hin hout

lemma d_lt_v {u v c d : ℝ} (hv : 1 < v) (hu0 : 0 < u) (hdet : u * d = 1 + c * v)
    (hc : c ≤ u - 1) (hv0 : 0 ≤ v) : d < v := by
  have h1 : c * v ≤ (u - 1) * v := mul_le_mul_of_nonneg_right hc hv0
  have h2 : u * d < u * v := by rw [hdet]; nlinarith
  exact lt_of_mul_lt_mul_left h2 hu0.le

lemma c_low {u v c d a ε : ℝ} (hu0 : 0 < u) (hv0 : 0 < v) (hcR : u * d - 1 = v * c)
    (hd : (a + ε) * v < d) (hε : 1 < ε * (u * v)) : a * u < c := by
  have h1 : u * ((a + ε) * v) < u * d := mul_lt_mul_of_pos_left hd hu0
  have h2 : v * (a * u) < v * c := by rw [← hcR]; nlinarith
  exact lt_of_mul_lt_mul_left h2 hv0.le

lemma c_high {u v c d b : ℝ} (hu0 : 0 < u) (hv0 : 0 < v) (hcR : u * d - 1 = v * c)
    (hd : d < b * v) : c < b * u := by
  have h1 : u * d < u * (b * v) := mul_lt_mul_of_pos_left hd hu0
  have h2 : v * c < v * (b * u) := by rw [← hcR]; nlinarith
  exact lt_of_mul_lt_mul_left h2 hv0.le

/-- The outer `d`-range in case `V < U`. -/
lemma caseV_outer (U V a₃ b₃ : ℝ) (hU0 : 0 < U) (hV3 : 3 ≤ V) (u v c d : ℤ) (huR : U ≤ u)
    (hvR : V ≤ v) (hdet : u * d - c * v = 1) (hcu : c < u) (h1 : a₃ * u ≤ c)
    (h2 : (c : ℝ) ≤ b₃ * u) :
    ⌈a₃ * (v : ℝ)⌉ ≤ d ∧ d < min (⌊(b₃ + 1 / (U * V)) * (v : ℝ)⌋ + 1) v := by
  have hV0 : 0 < V := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hdetR : (u : ℝ) * d = 1 + c * v := by
    have : (u * d : ℤ) = 1 + c * v := by linarith
    exact_mod_cast this
  refine ⟨Int.ceil_le.mpr ?_, lt_min (Int.lt_add_one_iff.mpr (Int.le_floor.mpr ?_)) ?_⟩
  · have : (u : ℝ) * (a₃ * v) ≤ u * d := by rw [hdetR]; nlinarith
    exact le_of_mul_le_mul_left this hu0
  · have huv : U * V ≤ (u : ℝ) * v := mul_le_mul huR hvR hV0.le hu0.le
    have h1u : 1 ≤ (u : ℝ) * (1 / (U * V) * v) := by
      rw [show (u : ℝ) * (1 / (U * V) * v) = (u * v) / (U * V) by ring,
        le_div_iff₀ (by positivity)]
      linarith
    have : (u : ℝ) * d ≤ u * ((b₃ + 1 / (U * V)) * v) := by
      rw [hdetR]; nlinarith
    exact le_of_mul_le_mul_left this hu0
  · have hcu' : (c : ℝ) ≤ u - 1 := by
      have : c ≤ u - 1 := by omega
      exact_mod_cast this
    have := d_lt_v (by linarith) hu0 hdetR hcu' hv0.le
    exact_mod_cast this

/-- The inner `d`-range in case `V < U`. -/
lemma caseV_inner (U V a₃ b₃ : ℝ) (hU0 : 0 < U) (hV0 : 0 < V) (ha₃ : 0 ≤ a₃) (hb₃ : b₃ ≤ 1)
    (u v d : ℤ) (huR : U < u) (hvR : V < v) (hd1 : ⌊(a₃ + 1 / (U * V)) * (v : ℝ)⌋ + 1 ≤ d)
    (hd2 : d < max ⌈b₃ * (v : ℝ)⌉ (⌊(a₃ + 1 / (U * V)) * (v : ℝ)⌋ + 1)) (hvd : v ∣ u * d - 1) :
    0 ≤ (u * d - 1) / v ∧ (u * d - 1) / v < u ∧
      ((((u * d - 1) / v : ℤ)) : ℝ) / u ∈ Set.Ioo a₃ b₃ := by
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < v := by linarith
  have hd1' : (a₃ + 1 / (U * V)) * v < d := by
    have := Int.lt_floor_add_one ((a₃ + 1 / (U * V)) * (v : ℝ))
    have h' : ((⌊(a₃ + 1 / (U * V)) * (v : ℝ)⌋ + 1 : ℤ) : ℝ) ≤ d := by exact_mod_cast hd1
    push_cast at h'
    linarith
  have hd2' : (d : ℝ) < b₃ * v := by
    have : d < ⌈b₃ * (v : ℝ)⌉ := by
      rcases le_total ⌈b₃ * (v : ℝ)⌉ (⌊(a₃ + 1 / (U * V)) * (v : ℝ)⌋ + 1) with h | h
      · rw [max_eq_right h] at hd2; omega
      · rwa [max_eq_left h] at hd2
    exact Int.lt_ceil.mp this
  obtain ⟨c, hc⟩ := hvd
  have hv0' : v ≠ 0 := by
    intro h; rw [h] at hv0; simp at hv0
  rw [hc, Int.mul_ediv_cancel_left _ hv0']
  have hcR : (u : ℝ) * d - 1 = v * c := by exact_mod_cast hc
  have huv : U * V < (u : ℝ) * v := mul_lt_mul'' huR hvR hU0.le hV0.le
  have hεuv : 1 < 1 / (U * V) * ((u : ℝ) * v) := by
    rw [div_mul_eq_mul_div, one_mul, one_lt_div (by positivity)]
    exact huv
  have hlow : a₃ * u < c := c_low hu0 hv0 hcR hd1' hεuv
  have hhigh : (c : ℝ) < b₃ * u := c_high hu0 hv0 hcR hd2'
  have hc0 : (0 : ℝ) < c := lt_of_le_of_lt (by positivity) hlow
  have hcu : (c : ℝ) < u := lt_of_lt_of_le hhigh (mul_le_of_le_one_left hu0.le hb₃)
  exact ⟨by exact_mod_cast hc0.le, by exact_mod_cast hcu, mem_Ioo_div hu0 hlow hhigh⟩

/-- **Case `V < U`.** -/
theorem case_V (S : ℕ) [NeZero S] (hS : Squarefree S)
    (g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) (U V : ℝ) (hV : 3 ≤ V) (hVU : V ≤ U)
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℝ) (ha₁ : 1 ≤ a₁) (hab₁ : a₁ ≤ b₁) (hb₁ : b₁ ≤ 16) (ha₂ : 1 ≤ a₂)
    (hab₂ : a₂ ≤ b₂) (hb₂ : b₂ ≤ 2) (ha₃ : 0 ≤ a₃) (hab₃ : a₃ ≤ b₃) (hb₃ : b₃ ≤ 1)
    (I₁ I₂ I₃ : Set ℝ) (hI₁ : Set.Ioo a₁ b₁ ⊆ I₁) (hI₁' : I₁ ⊆ Set.Icc a₁ b₁)
    (hI₂ : Set.Ioo a₂ b₂ ⊆ I₂) (hI₂' : I₂ ⊆ Set.Icc a₂ b₂)
    (hI₃ : Set.Ioo a₃ b₃ ⊆ I₃) (hI₃' : I₃ ⊆ Set.Icc a₃ b₃)
    (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ m : ℕ, 1 ≤ m →
      ((m.divisors.card : ℝ) * (1 + Real.log m)) ^ 3 ≤ K * (m : ℝ) ^ ((1 : ℝ) / 8)) :
    |(Nat.card {g // RootPred S g₀ U V I₁ I₂ I₃ g} : ℝ) -
        (b₃ - a₃) * (U * (b₁ - a₁)) * (V * (b₂ - a₂)) * PS S / (S : ℝ) ^ 3| ≤
      20000 * (K + 1) * (S : ℝ) ^ 2 * V ^ (-(1 : ℝ) / 8) * (V * U) := by
  classical
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hθ0 : 0 ≤ b₃ - a₃ := by linarith
  have hθ1 : b₃ - a₃ ≤ 1 := by linarith
  have hε0 : 0 ≤ 1 / (U * V) := by positivity
  have haU : a₁ * U ≤ b₁ * U := mul_le_mul_of_nonneg_right hab₁ hU0.le
  have haV : a₂ * V ≤ b₂ * V := mul_le_mul_of_nonneg_right hab₂ hV0.le
  obtain ⟨hAB₁, hlen₁, hmem₁⟩ := outer_range a₁ b₁ U haU
  obtain ⟨hAB₂, hlen₂, hmem₂⟩ := outer_range a₂ b₂ V haV
  obtain ⟨hAB₁', hlen₁', hmem₁'⟩ := inner_range a₁ b₁ U haU
  obtain ⟨hAB₂', hlen₂', hmem₂'⟩ := inner_range a₂ b₂ V haV
  have hUa : U ≤ a₁ * U := le_mul_of_one_le_left hU0.le ha₁
  have hVa : V ≤ a₂ * V := le_mul_of_one_le_left hV0.le ha₂
  have hbV : b₂ * V ≤ 2 * V := mul_le_mul_of_nonneg_right hb₂ hV0.le
  have hVA : V ≤ (⌈a₂ * V⌉ : ℝ) := le_trans hVa (Int.le_ceil _)
  have hVA' : V ≤ ((⌊a₂ * V⌋ + 1 : ℤ) : ℝ) := by
    push_cast; linarith [Int.lt_floor_add_one (a₂ * V)]
  have hA₂ : 1 ≤ ⌈a₂ * V⌉ := by
    have : (1 : ℝ) ≤ ⌈a₂ * V⌉ := by linarith
    exact_mod_cast this
  have hA₂' : 1 ≤ ⌊a₂ * V⌋ + 1 := by
    have : (1 : ℝ) ≤ ((⌊a₂ * V⌋ + 1 : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  have hX'0 : 0 ≤ V * (b₂ - a₂) := mul_nonneg hV0.le (by linarith)
  have hX'V : V * (b₂ - a₂) ≤ V := mul_le_of_le_one_right hV0.le (by linarith)
  have hY'15 : U * (b₁ - a₁) ≤ 15 * U := by
    rw [mul_comm 15 U]; exact mul_le_mul_of_nonneg_left (by linarith) hU0.le
  -- `ε n ≤ 1` on the `v`-range
  have hεn : ∀ n : ℤ, (n : ℝ) ≤ 3 * V → 1 / (U * V) * n ≤ 1 := by
    intro n hn
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    calc (n : ℝ) ≤ 3 * V := hn
      _ ≤ U * V := mul_le_mul_of_nonneg_right (by linarith) hV0.le
  -- upper bound
  obtain ⟨hfin, hN_le⟩ := count_le_sigmaV S g₀ U V I₁ I₂ I₃ ⌈a₁ * U⌉ (⌊b₁ * U⌋ + 1) ⌈a₂ * V⌉
    (⌊b₂ * V⌋ + 1) (fun v => ⌈a₃ * v⌉) (fun v => min (⌊(b₃ + 1 / (U * V)) * v⌋ + 1) v) hA₂
    (fun u hu => by obtain ⟨h1, h2⟩ := mem_Icc_div hU0 (hI₁' hu); exact hmem₁ u h1 h2)
    (fun v hv => by obtain ⟨h1, h2⟩ := mem_Icc_div hV0 (hI₂' hv); exact hmem₂ v h1 h2)
    (fun u v c d hu hv hdet hc0 hcu hr => by
      have huR : U ≤ (u : ℝ) := le_trans (le_trans hUa (Int.le_ceil _)) (by exact_mod_cast hu)
      have hvR : V ≤ (v : ℝ) := le_trans hVA (by exact_mod_cast hv)
      have hu0 : (0 : ℝ) < u := by linarith
      obtain ⟨h1, h2⟩ := mem_Icc_div hu0 (hI₃' hr)
      exact caseV_outer U V a₃ b₃ hU0 hV u v c d huR hvR hdet hcu h1 h2)
  -- lower bound
  have hN_ge := sigmaV_le_count S g₀ U V I₁ I₂ I₃ (⌊a₁ * U⌋ + 1) (max ⌈b₁ * U⌉ (⌊a₁ * U⌋ + 1))
    (⌊a₂ * V⌋ + 1) (max ⌈b₂ * V⌉ (⌊a₂ * V⌋ + 1)) (fun v => ⌊(a₃ + 1 / (U * V)) * v⌋ + 1)
    (fun v => max ⌈b₃ * v⌉ (⌊(a₃ + 1 / (U * V)) * v⌋ + 1)) hA₂' hfin
    (fun u h1 h2 => hI₁ (mem_Ioo_div hU0 (hmem₁' u h1 h2).1 (hmem₁' u h1 h2).2))
    (fun v h1 h2 => hI₂ (mem_Ioo_div hV0 (hmem₂' v h1 h2).1 (hmem₂' v h1 h2).2))
    (fun u v d hu1 hu2 hv1 hv2 hd1 hd2 hvd => by
      obtain ⟨hua, -⟩ := hmem₁' u hu1 hu2
      obtain ⟨hva, -⟩ := hmem₂' v hv1 hv2
      obtain ⟨h1, h2, h3⟩ := caseV_inner U V a₃ b₃ hU0 hV0 ha₃ hb₃ u v d (by linarith)
        (by linarith) hd1 hd2 hvd
      exact ⟨h1, h2, hI₃ h3⟩)
  -- the two sigma counts
  have hout := sigma_count_V S hS g₀ U V (b₃ - a₃) (V * (b₂ - a₂)) (U * (b₁ - a₁)) (by linarith)
    hVU hθ0 hθ1 hX'0 hX'V hY'15 ⌈a₁ * U⌉ (⌊b₁ * U⌋ + 1) ⌈a₂ * V⌉ (⌊b₂ * V⌋ + 1)
    (fun v => ⌈a₃ * v⌉) (fun v => min (⌊(b₃ + 1 / (U * V)) * v⌋ + 1) v) hVA hAB₁ hAB₂
    (by push_cast; linarith [Int.floor_le (b₂ * V)])
    (by convert hlen₂ using 2; ring) (by convert hlen₁ using 2; ring)
    (fun n hn hnB => by
      have hn1 : 1 ≤ n := le_trans hA₂ hn
      obtain ⟨h1, h2, h3⟩ := outer_X a₃ b₃ (b₃ + 1 / (U * V)) n hn1 hab₃ (by linarith) hb₃
      have hnB' : (n : ℝ) ≤ 3 * V := by
        have : (n : ℝ) < ⌊b₂ * V⌋ + 1 := by exact_mod_cast hnB
        linarith [Int.floor_le (b₂ * V)]
      have := hεn n hnB'
      have e : (b₃ + 1 / (U * V) - a₃) * n = (b₃ - a₃) * n + 1 / (U * V) * n := by ring
      exact ⟨h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩) K hK0 hK
  have hin := sigma_count_V S hS g₀ U V (b₃ - a₃) (V * (b₂ - a₂)) (U * (b₁ - a₁)) (by linarith)
    hVU hθ0 hθ1 hX'0 hX'V hY'15 (⌊a₁ * U⌋ + 1) (max ⌈b₁ * U⌉ (⌊a₁ * U⌋ + 1)) (⌊a₂ * V⌋ + 1)
    (max ⌈b₂ * V⌉ (⌊a₂ * V⌋ + 1)) (fun v => ⌊(a₃ + 1 / (U * V)) * v⌋ + 1)
    (fun v => max ⌈b₃ * v⌉ (⌊(a₃ + 1 / (U * V)) * v⌋ + 1)) hVA' hAB₁' hAB₂'
    (by
      have h1 := Int.ceil_lt_add_one (b₂ * V)
      have h2 := Int.floor_le (a₂ * V)
      push_cast
      exact max_le (by linarith) (by linarith))
    (by convert hlen₂' using 2; ring) (by convert hlen₁' using 2; ring)
    (fun n hn hnB => by
      have hn1 : 1 ≤ n := le_trans hA₂' hn
      obtain ⟨h1, h2, h3⟩ := inner_X a₃ (a₃ + 1 / (U * V)) b₃ n hn1 (by linarith) hab₃
      have hnB' : (n : ℝ) ≤ 3 * V := by
        have : (n : ℝ) < ((max ⌈b₂ * V⌉ (⌊a₂ * V⌋ + 1) : ℤ) : ℝ) := by exact_mod_cast hnB
        push_cast at this
        have h1 := Int.ceil_lt_add_one (b₂ * V)
        have h2 := Int.floor_le (a₂ * V)
        have : max (⌈b₂ * V⌉ : ℝ) (⌊a₂ * V⌋ + 1) ≤ 3 * V := max_le (by linarith) (by linarith)
        linarith
      have := hεn n hnB'
      have e : (b₃ - (a₃ + 1 / (U * V))) * n = (b₃ - a₃) * n - 1 / (U * V) * n := by ring
      exact ⟨h1, abs_le.mpr ⟨by linarith, by linarith⟩⟩) K hK0 hK
  exact sandwich' (by exact_mod_cast hN_ge) (by exact_mod_cast hN_le) hin hout

end

end ArtinPrimitiveRoots.L102K
end

section
/-! # L102K: [21] Lemma 3.3 (root residues)

For `δ > 0` and any `C`, for all large `x`, all `U, V ≥ x^δ`, squarefree `S ≤ exp(C (log x)^{0.98})`,
`g₀ ∈ SL₂(ℤ/S)` and intervals `I₁ ⊆ [1,16]`, `I₂ ⊆ [1,2]`, `I₃ ⊆ [0,1]`:

`#{g = (u c; v d) ∈ SL₂(ℤ) : u/U ∈ I₁, v/V ∈ I₂, 0 ≤ c < u, c/u ∈ I₃, g ≡ g₀ (S)}`
`  = (6/π²) UV|I₁||I₂||I₃| / |SL₂(ℤ/S)| + O(UV x^{-δ/16})`,

with implied constant `1`. An interval `I` with endpoints `a ≤ b` is any set with
`(a, b) ⊆ I ⊆ [a, b]`. -/

namespace ArtinPrimitiveRoots.L102K

open Finset Real

noncomputable section

/-- The thresholds on `x`. -/
lemma eventually_bounds (δ C K : ℝ) (hδ : 0 < δ) (hK : 0 ≤ K) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, 0 < x ∧ 3 ≤ x ^ δ ∧ 20000 * (K + 1) ≤ x ^ (δ / 32) ∧
      Real.exp (2 * C * Real.log x ^ (0.98 : ℝ)) ≤ x ^ (δ / 32) := by
  set L₀ := (64 * |C| / δ) ^ (50 : ℝ) + 1 with hL₀
  refine ⟨max (max (Real.exp L₀) ((3 : ℝ) ^ (1 / δ))) ((20000 * (K + 1)) ^ (32 / δ)),
    fun x hx => ?_⟩
  have hx1 : Real.exp L₀ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : (3 : ℝ) ^ (1 / δ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : (20000 * (K + 1)) ^ (32 / δ) ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx1
  have hL : L₀ ≤ Real.log x := by
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) hx1
  have hpos : (0 : ℝ) ≤ (64 * |C| / δ) ^ (50 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hL1 : 1 ≤ Real.log x := by rw [hL₀] at hL; linarith
  refine ⟨hx0, ?_, ?_, ?_⟩
  · calc (3 : ℝ) = ((3 : ℝ) ^ (1 / δ)) ^ δ := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hδ.ne', Real.rpow_one]
      _ ≤ x ^ δ := Real.rpow_le_rpow (by positivity) hx2 hδ.le
  · calc 20000 * (K + 1) = ((20000 * (K + 1)) ^ (32 / δ)) ^ (δ / 32) := by
          rw [← Real.rpow_mul (by positivity)]
          rw [show 32 / δ * (δ / 32) = 1 by field_simp, Real.rpow_one]
      _ ≤ x ^ (δ / 32) := Real.rpow_le_rpow (by positivity) hx3 (by positivity)
  · rw [Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    set L := Real.log x with hLdef
    have hL0 : 0 < L := by linarith
    -- `L^{0.02} ≥ 64|C|/δ`
    have h1 : 64 * |C| / δ ≤ L ^ (0.02 : ℝ) := by
      have h2 : (64 * |C| / δ) ^ (50 : ℝ) ≤ L := by rw [hL₀] at hL; linarith
      calc 64 * |C| / δ = ((64 * |C| / δ) ^ (50 : ℝ)) ^ (0.02 : ℝ) := by
            rw [← Real.rpow_mul (by positivity)]; norm_num
        _ ≤ L ^ (0.02 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
    have h3 : L ^ (0.98 : ℝ) * L ^ (0.02 : ℝ) = L := by
      rw [← Real.rpow_add hL0]; norm_num
    have h4 : 0 ≤ L ^ (0.98 : ℝ) := by positivity
    have h5 : 2 * C * L ^ (0.98 : ℝ) ≤ 2 * |C| * L ^ (0.98 : ℝ) := by
      have := le_abs_self C
      nlinarith
    have h6 : 2 * |C| * L ^ (0.98 : ℝ) ≤ δ / 32 * L := by
      have h7 : 2 * |C| * L ^ (0.98 : ℝ) = δ / 32 * (64 * |C| / δ) * L ^ (0.98 : ℝ) := by
        field_simp; ring
      rw [h7]
      have : 0 ≤ δ / 32 := by positivity
      calc δ / 32 * (64 * |C| / δ) * L ^ (0.98 : ℝ)
          ≤ δ / 32 * L ^ (0.02 : ℝ) * L ^ (0.98 : ℝ) := by gcongr
        _ = δ / 32 * (L ^ (0.98 : ℝ) * L ^ (0.02 : ℝ)) := by ring
        _ = δ / 32 * L := by rw [h3]
    calc 2 * C * L ^ (0.98 : ℝ) ≤ δ / 32 * L := h5.trans h6
      _ = L * (δ / 32) := by ring

/-- `w ≥ x^δ` gives `w^{-1/8} ≤ x^{-δ/8}`. -/
lemma rpow_neg_le {x w δ : ℝ} (hx : 0 < x) (hw : x ^ δ ≤ w) :
    w ^ (-(1 : ℝ) / 8) ≤ x ^ (-δ / 8) := by
  have hxδ : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  calc w ^ (-(1 : ℝ) / 8) ≤ (x ^ δ) ^ (-(1 : ℝ) / 8) :=
        Real.rpow_le_rpow_of_nonpos hxδ hw (by norm_num)
    _ = x ^ (-δ / 8) := by rw [← Real.rpow_mul hx.le]; ring_nf

/-- **[21] Lemma 3.3 (root residues).** -/
theorem root_residues (δ C : ℝ) (hδ : 0 < δ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ, x ^ δ ≤ U → x ^ δ ≤ V →
      ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ Real.exp (C * Real.log x ^ (0.98 : ℝ)) →
      ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
        0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
      ∀ I₁ I₂ I₃ : Set ℝ, Set.Ioo a₁ b₁ ⊆ I₁ → I₁ ⊆ Set.Icc a₁ b₁ →
        Set.Ioo a₂ b₂ ⊆ I₂ → I₂ ⊆ Set.Icc a₂ b₂ → Set.Ioo a₃ b₃ ⊆ I₃ → I₃ ⊆ Set.Icc a₃ b₃ →
      |(Nat.card {g : Matrix.SpecialLinearGroup (Fin 2) ℤ //
          (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
          (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀} : ℝ) -
        6 / π ^ 2 * (U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) /
          (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)| ≤
        U * V * x ^ (-δ / 16) := by
  obtain ⟨K, hK0, hK⟩ := exists_T_cube_le
  obtain ⟨x₀, hx₀⟩ := eventually_bounds δ C K hδ hK0.le
  refine ⟨x₀, fun x hx U V hU hV S hS0 hS hSx g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂
    ha₃ hab₃ hb₃ I₁ I₂ I₃ hI₁ hI₁' hI₂ hI₂' hI₃ hI₃' => ?_⟩
  obtain ⟨hx0, hx3, hxK, hxS⟩ := hx₀ x hx
  have : NeZero S := ⟨hS0.ne'⟩
  have hU3 : 3 ≤ U := le_trans hx3 hU
  have hV3 : 3 ≤ V := le_trans hx3 hV
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  -- the constant
  have hSL := card_SL2 S hS0
  have hJP := JS_mul_PS S hS0
  have hSLpos : (0 : ℝ) < (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hSR : (0 : ℝ) < S := by exact_mod_cast hS0
  have hJS : 0 < JS S := by
    rw [hSL] at hSLpos
    exact pos_of_mul_pos_right hSLpos (by positivity)
  have hmain : 6 / π ^ 2 * (U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) /
      (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) =
      (b₃ - a₃) * (V * (b₂ - a₂)) * (U * (b₁ - a₁)) * PS S / (S : ℝ) ^ 3 := by
    rw [hSL, ← hJP]
    field_simp
  -- `S² ≤ x^{δ/32}`
  have hS2 : (S : ℝ) ^ 2 ≤ x ^ (δ / 32) := by
    refine le_trans ?_ hxS
    calc (S : ℝ) ^ 2 ≤ (Real.exp (C * Real.log x ^ (0.98 : ℝ))) ^ 2 :=
          pow_le_pow_left₀ hSR.le hSx 2
      _ = Real.exp (2 * C * Real.log x ^ (0.98 : ℝ)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  -- the final bound from either case
  have hfinal : ∀ w : ℝ, x ^ δ ≤ w →
      20000 * (K + 1) * (S : ℝ) ^ 2 * w ^ (-(1 : ℝ) / 8) * (U * V) ≤ U * V * x ^ (-δ / 16) := by
    intro w hw
    have h1 := rpow_neg_le hx0 hw
    have hw0' : 0 < w := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hw
    have hw0 : 0 ≤ w ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos hw0' _).le
    have hS2' : 0 ≤ (S : ℝ) ^ 2 := by positivity
    have hK1 : 0 ≤ 20000 * (K + 1) := by linarith
    have hx32 : 0 ≤ x ^ (δ / 32) := (Real.rpow_pos_of_pos hx0 _).le
    have h2 : 20000 * (K + 1) * (S : ℝ) ^ 2 * w ^ (-(1 : ℝ) / 8) ≤
        x ^ (δ / 32) * x ^ (δ / 32) * x ^ (-δ / 8) :=
      mul_le_mul (mul_le_mul hxK hS2 hS2' hx32) h1 hw0 (mul_nonneg hx32 hx32)
    have h3 : x ^ (δ / 32) * x ^ (δ / 32) * x ^ (-δ / 8) = x ^ (-δ / 16) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; ring_nf
    rw [h3] at h2
    have hUV0 : 0 ≤ U * V := by positivity
    have := mul_le_mul_of_nonneg_right h2 hUV0
    linarith
  rw [hmain]
  rcases le_total U V with hUV | hVU
  · have := case_U S hS g₀ U V hU3 hUV a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃
      I₁ I₂ I₃ hI₁ hI₁' hI₂ hI₂' hI₃ hI₃' K hK0.le hK
    exact this.trans (hfinal U hU)
  · have := case_V S hS g₀ U V hV3 hVU a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂ ha₃ hab₃ hb₃
      I₁ I₂ I₃ hI₁ hI₁' hI₂ hI₂' hI₃ hI₃' K hK0.le hK
    have e : (b₃ - a₃) * (U * (b₁ - a₁)) * (V * (b₂ - a₂)) * PS S / (S : ℝ) ^ 3 =
        (b₃ - a₃) * (V * (b₂ - a₂)) * (U * (b₁ - a₁)) * PS S / (S : ℝ) ^ 3 := by ring
    rw [e] at this
    refine this.trans ?_
    have := hfinal V hV
    calc 20000 * (K + 1) * (S : ℝ) ^ 2 * V ^ (-(1 : ℝ) / 8) * (V * U)
        = 20000 * (K + 1) * (S : ℝ) ^ 2 * V ^ (-(1 : ℝ) / 8) * (U * V) := by ring
      _ ≤ U * V * x ^ (-δ / 16) := this

/-- **D3 of `L102D.md`** ([21] Lemma 3.3, root residues) as a proposition: there is `c_δ > 0` such
that for every `C`, for `x` large, `U, V ≥ x^δ`, squarefree `S ≤ exp(C (log x)^{0.98})`,
`g₀ ∈ SL₂(ℤ/S)` and intervals `I₁ ⊆ [1,16]`, `I₂ ⊆ [1,2]`, `I₃ ⊆ [0,1]` (given by endpoints
`a ≤ b` with `(a,b) ⊆ I ⊆ [a,b]`), the number of `g = (u c; v d) ∈ SL₂(ℤ)` with `u/U ∈ I₁`,
`v/V ∈ I₂`, `0 ≤ c < u`, `c/u ∈ I₃`, `g ≡ g₀ (mod S)` is
`UV|I₁||I₂||I₃|/(ζ(2)|SL₂(ℤ/S)|) + O(UV x^{-c_δ})` (here with implied constant `1`). -/
def RootResiduesStmt : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ,
    x ^ δ ≤ U → x ^ δ ≤ V →
    ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ Real.exp (C * Real.log x ^ (0.98 : ℝ)) →
    ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
    ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
      0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
    ∀ I₁ I₂ I₃ : Set ℝ, Set.Ioo a₁ b₁ ⊆ I₁ → I₁ ⊆ Set.Icc a₁ b₁ →
      Set.Ioo a₂ b₂ ⊆ I₂ → I₂ ⊆ Set.Icc a₂ b₂ → Set.Ioo a₃ b₃ ⊆ I₃ → I₃ ⊆ Set.Icc a₃ b₃ →
    |(Nat.card {g : Matrix.SpecialLinearGroup (Fin 2) ℤ //
        (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
        (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀} : ℝ) -
      U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
        ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
      U * V * x ^ (-c)

/-- **[21] Lemma 3.3 holds** (`c_δ = δ/16`). -/
theorem rootResidues : RootResiduesStmt := by
  intro δ hδ
  refine ⟨δ / 16, by positivity, fun C => ?_⟩
  obtain ⟨x₀, hx₀⟩ := root_residues δ C hδ
  refine ⟨x₀, fun x hx U V hU hV S hS0 hS hSx g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂
    ha₃ hab₃ hb₃ I₁ I₂ I₃ hI₁ hI₁' hI₂ hI₂' hI₃ hI₃' => ?_⟩
  have h := hx₀ x hx U V hU hV S hS0 hS hSx g₀ a₁ b₁ a₂ b₂ a₃ b₃ ha₁ hab₁ hb₁ ha₂ hab₂ hb₂
    ha₃ hab₃ hb₃ I₁ I₂ I₃ hI₁ hI₁' hI₂ hI₂' hI₃ hI₃'
  have hz : (riemannZeta 2).re = π ^ 2 / 6 := by
    rw [riemannZeta_two]
    rw [show (π : ℂ) ^ 2 / 6 = ((π ^ 2 / 6 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  have he : U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
      ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ)) =
      6 / π ^ 2 * (U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃)) /
        (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ) := by
    rw [hz]
    have : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [he, show -(δ / 16) = -δ / 16 by ring]
  exact h

end

end ArtinPrimitiveRoots.L102K
end

section
/-! Check module: `chk_abs_card_specialLinearGroup_box_sub_le`, the published statement `abs_card_specialLinearGroup_box_sub_le` verbatim, proved from the
development and the cuts `abs_card_box_mul_sub_mod_le`. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution :
    ∀ δ : ℝ, 0 < δ → ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, ∃ x₀ : ℝ, ∀ x ≥ x₀, ∀ U V : ℝ,
      x ^ δ ≤ U → x ^ δ ≤ V →
      ∀ S : ℕ, 0 < S → Squarefree S → (S : ℝ) ≤ Real.exp (C * Real.log x ^ (0.98 : ℝ)) →
      ∀ g₀ : Matrix.SpecialLinearGroup (Fin 2) (ZMod S),
      ∀ a₁ b₁ a₂ b₂ a₃ b₃ : ℝ, 1 ≤ a₁ → a₁ ≤ b₁ → b₁ ≤ 16 → 1 ≤ a₂ → a₂ ≤ b₂ → b₂ ≤ 2 →
        0 ≤ a₃ → a₃ ≤ b₃ → b₃ ≤ 1 →
      ∀ I₁ I₂ I₃ : Set ℝ, Set.Ioo a₁ b₁ ⊆ I₁ → I₁ ⊆ Set.Icc a₁ b₁ →
        Set.Ioo a₂ b₂ ⊆ I₂ → I₂ ⊆ Set.Icc a₂ b₂ → Set.Ioo a₃ b₃ ⊆ I₃ → I₃ ⊆ Set.Icc a₃ b₃ →
      |(Nat.card {g : Matrix.SpecialLinearGroup (Fin 2) ℤ //
          (g 0 0 : ℝ) / U ∈ I₁ ∧ (g 1 0 : ℝ) / V ∈ I₂ ∧ 0 ≤ g 0 1 ∧ g 0 1 < g 0 0 ∧
          (g 0 1 : ℝ) / (g 0 0 : ℝ) ∈ I₃ ∧
          Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod S)) g = g₀} : ℝ) -
        U * V * (b₁ - a₁) * (b₂ - a₂) * (b₃ - a₃) /
          ((riemannZeta 2).re * (Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod S)) : ℝ))| ≤
        U * V * x ^ (-c) :=
  L102K.rootResidues
end

-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_minorSquare_sub_sum_dyadPairingSTS_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:13:20.226115+00:00
-- url     : https://prove2.me/submissions/2ee36b30-db57-4398-a6f4-a3c705f1e176

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

/-- The product of all labels of a list. -/
def listProd {K J : ℕ} (ℓ : Fin K → Fin (J + 1) → ℕ) : ℕ := ∏ i, ∏ j, ℓ i j

end ArtinPrimitiveRoots
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- **D8bc** ([21] §4.9, (4.58)–(4.63)): the pads are independent harmonic draws, so the dyadic
sum of the unprojected pairings reproduces `Q^min` up to pad collisions. -/
def PadLiftStmt (δ C c₁ c₂ : ℝ) : Prop :=
  ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    ∀ A : ℝ, 0 < A →
    ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
      ∀ α β : ℕ → ℂ,
        (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
          ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
        (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
        (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
        ∀ Y : ℝ, 1 ≤ Y →
          ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
              ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
            c * (Hm * Hn * Y * log x ^ (-A))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the spectral Hölder step of [21] §3.3, (3.20), in abstract form

For a finite-dimensional complex inner product space `E`, an operator `A` and `B = A A†`:

* `re_inner_pow_eq_sum`: `re ⟪v, Tᵏ v⟫ = ∑ λᵢᵏ ‖cᵢ‖²` in an eigenbasis of a symmetric `T`;
* `re_inner_le_pow` (spectral Hölder): `re ⟪f, B f⟫ ≤ ‖f‖^{2(1-1/R)} (re ⟪f, Bᴿ f⟫)^{1/R}`
  for a positive symmetric `B`;
* `norm_inner_apply_le_moment`: `‖⟪f, A g⟫‖ ≤ ‖g‖ ‖f‖^{1-1/R} (re ⟪f, (A A†)ᴿ f⟫)^{1/(2R)}`;
* `re_inner_sum_le_trace` (largest eigenvalue ≤ trace): for `f = ∑ cₚ uₚ` and a positive `C`,
  `re ⟪f, C f⟫ ≤ (∑ |cₚ|²) (∑ re ⟪uₚ, C uₚ⟫)`;
* `norm_sum_inner_le_moment` (the localized Hölder step): for blocks `j`,
  `‖∑ⱼ ⟪fⱼ, A gⱼ⟫‖ ≤ (∑ ‖gⱼ‖²)^{1/2} (∑ ‖fⱼ‖²)^{(1-1/R)/2} (∑ⱼ re ⟪fⱼ, (A A†)ᴿ fⱼ⟫)^{1/(2R)}`.

These are exactly the inequalities used between (3.19) and (3.20) of [21]; the concrete inputs
(the slope-interval partition with `O(H)` primitive positions per interval, and the norm bounds
(3.18)) are separate. -/

namespace ArtinPrimitiveRoots.L102D

open RCLike Finset
open scoped InnerProductSpace ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the localized spectral Hölder step of (3.20) for matrices

For a matrix `A` on a finite index set of states with positions `pos : ι → P`, a vector `f`
constant on positions, and a block index `blk : P → ℤ` such that `A` only connects blocks at
distance `≤ W` and each block has `≤ κ` positions,
`|⟨f, A f⟩| ≤ ((2W+1)‖f‖²)^{1/2} (‖f‖²)^{(1-1/R)/2} (κ F² M)^{1/(2R)}`,
`M = ∑_P ⟨u_P, (AA*)^R u_P⟩`, `F = sup |f|`. -/

namespace ArtinPrimitiveRoots.L102D

open Finset Matrix WithLp
open scoped InnerProductSpace ComplexConjugate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end ArtinPrimitiveRoots.L102D
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

/-- The harmonic sum over `(0, X]`. -/
theorem harm_le (X : ℕ) : ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) ≤ 1 + Real.log X := by
  have h := harmonic_le_one_add_log X
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have : Icc 1 X = Ioc 0 X := by ext i; simp; omega
  rw [this] at h
  simpa [one_div] using h

theorem harmonic_partial_sum_nonneg (X : ℕ) : 0 ≤ ∑ i ∈ Ioc 0 X, (1 / (i : ℝ)) :=
  Finset.sum_nonneg fun i _ => by positivity

/-- `∑_{a,b ≤ X} gcd(a,b)/(ab) ≤ H_X^3`. -/
theorem sum_gcd_div_le (X : ℕ) :
    ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, ((Nat.gcd a b : ℝ) / (a * b)) ≤
      (∑ i ∈ Ioc 0 X, (1 / (i : ℝ))) ^ 3 := by
  rw [← Finset.sum_product']
  set φ : ℕ × ℕ → ℕ × ℕ × ℕ := fun p => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2,
    p.2 / Nat.gcd p.1 p.2) with hφ
  have hinj : Set.InjOn φ ↑(Ioc 0 X ×ˢ Ioc 0 X) := by
    rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ h
    simp only [hφ, Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have ea : a = Nat.gcd a b * (a / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : b = Nat.gcd a b * (b / Nat.gcd a b) := (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ea' : a' = Nat.gcd a' b' * (a' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left a' b')).symm
    have eb' : b' = Nat.gcd a' b' * (b' / Nat.gcd a' b') :=
      (Nat.mul_div_cancel' (Nat.gcd_dvd_right a' b')).symm
    simp only [Prod.mk.injEq]
    constructor
    · rw [ea, ea']; exact congrArg₂ (· * ·) h1 h2
    · rw [eb, eb']; exact congrArg₂ (· * ·) h1 h3
  have hval : ∀ p ∈ Ioc 0 X ×ˢ Ioc 0 X, ((Nat.gcd p.1 p.2 : ℝ) / (p.1 * p.2)) =
      (fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) (φ p) := by
    rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, Finset.mem_Ioc] at hp
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ hp.1.1
    have ea : (a : ℝ) = Nat.gcd a b * ((a / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
    have eb : (b : ℝ) = Nat.gcd a b * ((b / Nat.gcd a b : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
    have ha0 : ((a / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at ea; exact (Nat.pos_iff_ne_zero.mp hp.1.1) (by exact_mod_cast ea)
    have hb0 : ((b / Nat.gcd a b : ℕ) : ℝ) ≠ 0 := by
      intro h; rw [h, mul_zero] at eb; exact (Nat.pos_iff_ne_zero.mp hp.2.1) (by exact_mod_cast eb)
    have hg0 : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
    rw [ea, eb]
    field_simp
  rw [Finset.sum_congr rfl hval,
    ← Finset.sum_image (f := fun t : ℕ × ℕ × ℕ => 1 / ((t.1 : ℝ) * t.2.1 * t.2.2)) hinj]
  have hsub : (Ioc 0 X ×ˢ Ioc 0 X).image φ ⊆ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X := by
    intro t ht
    simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Ioc] at ht ⊢
    obtain ⟨⟨a, b⟩, ⟨⟨ha, haX⟩, hb, hbX⟩, rfl⟩ := ht
    simp only [hφ]
    have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
    refine ⟨⟨hg, (Nat.gcd_le_left _ ha).trans haX⟩, ⟨?_, (Nat.div_le_self _ _).trans haX⟩, ?_,
      (Nat.div_le_self _ _).trans hbX⟩
    · exact Nat.div_pos (Nat.gcd_le_left _ ha) hg
    · exact Nat.div_pos (Nat.gcd_le_right _ hb) hg
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => by positivity)).trans
    (le_of_eq ?_)
  have : ∀ t ∈ Ioc 0 X ×ˢ Ioc 0 X ×ˢ Ioc 0 X, 1 / ((t.1 : ℝ) * t.2.1 * t.2.2) =
      (1 / (t.1 : ℝ)) * ((1 / (t.2.1 : ℝ)) * (1 / (t.2.2 : ℝ))) := by
    intro t _; rw [one_div_mul_one_div, one_div_mul_one_div, mul_assoc]
  rw [Finset.sum_congr rfl this, Finset.sum_product]
  simp_rw [Finset.sum_product, ← Finset.mul_sum]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring

/-- **Second moment of the divisor function**: `∑_{n ≤ X} d(n)^2 ≤ X (1 + log X)^3`. -/
theorem sum_card_divisors_sq_le (X : ℕ) :
    ∑ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 ≤ X * (1 + Real.log X) ^ 3 := by
  have hdiv : ∀ n ∈ Ioc 0 X, ((n.divisors.card : ℝ)) ^ 2 =
      ∑ a ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hd : n.divisors = (Ioc 0 X).filter (· ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨h, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos h hn.1, (Nat.le_of_dvd hn.1 h).trans hn.2⟩, h⟩
      · rintro ⟨-, h⟩
        exact ⟨h, hn.1.ne'⟩
    rw [hd, sq, Finset.card_filter, Nat.cast_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases ha : a ∣ n <;> by_cases hb : b ∣ n <;> simp [ha, hb]
  rw [Finset.sum_congr rfl hdiv, Finset.sum_comm]
  have hinner : ∀ a ∈ Ioc 0 X, ∑ n ∈ Ioc 0 X, ∑ b ∈ Ioc 0 X,
      (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) ≤
        ∑ b ∈ Ioc 0 X, (X : ℝ) * (Nat.gcd a b / (a * b)) := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun b hb => ?_
    rw [Finset.mem_Ioc] at ha hb
    have hcount : ∑ n ∈ Ioc 0 X, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) =
        ((X / Nat.lcm a b : ℕ) : ℝ) := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div, Finset.card_filter, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [Nat.lcm_dvd_iff]
      split_ifs <;> simp
    rw [hcount]
    have hl : 0 < Nat.lcm a b := Nat.lcm_pos ha.1 hb.1
    have h1 : ((X / Nat.lcm a b : ℕ) : ℝ) ≤ (X : ℝ) / Nat.lcm a b := Nat.cast_div_le
    have h2 : (X : ℝ) / Nat.lcm a b = X * (Nat.gcd a b / (a * b)) := by
      have := Nat.gcd_mul_lcm a b
      have hab : (a : ℝ) * b = Nat.gcd a b * Nat.lcm a b := by exact_mod_cast this.symm
      rw [hab]
      have : (Nat.gcd a b : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ ha.1).ne'
      have : (Nat.lcm a b : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
      field_simp
    linarith
  refine (Finset.sum_le_sum hinner).trans ?_
  simp_rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((sum_gcd_div_le X).trans ?_) (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (harmonic_partial_sum_nonneg X) (harm_le X) 3

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

open Classical in
/-- The raw inner sum of `expandedSquare` at the label products `a, b`. -/
noncomputable def rawInner (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
  ∑ r ∈ range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ range (⌊2 * Hn⌋₊ + 1),
    if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β else 0

/-- The inner sum of `majorSquare` at the label products `a, b`. -/
noncomputable def majInner (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ) : ℂ :=
  ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
  ∑ r ∈ range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ range (⌊2 * Hn⌋₊ + 1),
    sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b

/-! ## Elementary inputs -/

/-- `∫_{[0,1)} e(θ n) dθ = 1_{n = 0}`. -/
lemma integral_Ico_exp_int (n : ℤ) :
    ∫ θ in Set.Ico (0 : ℝ) 1, Complex.exp (2 * π * Complex.I * ((θ * n : ℝ) : ℂ)) =
      if n = 0 then 1 else 0 := by
  split_ifs with hn
  · subst hn; simp
  · rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    have hc : (2 * π * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have := integral_exp_mul_complex (a := 0) (b := 1) hc
    simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
    rw [show (fun θ : ℝ => Complex.exp (2 * π * Complex.I * ((θ : ℂ) * n))) =
        fun θ : ℝ => Complex.exp (2 * π * Complex.I * n * θ) by
      funext θ; ring_nf]
    rw [this]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.ofReal_one, mul_one,
        show (2 * π * Complex.I * n : ℂ) = n * (2 * π * Complex.I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp

lemma majorArcs_subset (x A₀ Y : ℝ) : majorArcs x A₀ Y ⊆ Set.Ico 0 1 :=
  fun _ h => ⟨h.1, h.2.1⟩

lemma measurableSet_majorArcs (x A₀ Y : ℝ) : MeasurableSet (majorArcs x A₀ Y) := by
  have : majorArcs x A₀ Y = Set.Ico 0 1 ∩ ⋃ k : ℕ, ⋃ c : ℤ,
      {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
    ext θ
    simp only [majorArcs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ico, Set.mem_iUnion]
    constructor
    · rintro ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩; exact ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩
    · rintro ⟨⟨h0, h1⟩, k, c, hk1, hk2, hc, hd⟩; exact ⟨h0, h1, k, hk1, hk2, c, hc, hd⟩
  rw [this]
  refine measurableSet_Ico.inter (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun c => ?_)
  by_cases hP : 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = {θ : ℝ | |θ - c / k| ≤ 2 * log x ^ A₀ / Y} := by
      ext θ; simp only [Set.mem_ofPred_eq]; tauto
    rw [this]
    exact measurableSet_le (by fun_prop) measurable_const
  · have : {θ : ℝ | 1 ≤ k ∧ (k : ℝ) ≤ log x ^ A₀ ∧ Int.gcd c k = 1 ∧
        |θ - c / k| ≤ 2 * log x ^ A₀ / Y} = ∅ := by
      ext θ; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]; tauto
    rw [this]; exact MeasurableSet.empty

/-- `H_𝔪 = ψ(t/Y) 1_{t = b − a} − H_𝔐`. -/
lemma minorKernel_eq (x A₀ Y : ℝ) (t a b : ℤ) :
    minorKernel x A₀ Y t a b =
      (arcCutoff (t / Y) : ℂ) * (if t - b + a = 0 then 1 else 0) - majorKernel x A₀ Y t a b := by
  unfold minorKernel majorKernel
  have hint : IntegrableOn (fun θ : ℝ =>
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))) (Set.Ico 0 1) :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Set.Ico_subset_Icc_self
  rw [setIntegral_sdiff (measurableSet_majorArcs x A₀ Y) hint (majorArcs_subset x A₀ Y), mul_sub]
  congr 2
  have := integral_Ico_exp_int (t - b + a)
  push_cast at this ⊢
  rw [this]

lemma dyadicBump_ne_zero {u : ℝ} (h : dyadicBump u ≠ 0) : 1 < u ∧ u < 4 := by
  unfold dyadicBump at h
  constructor
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]
    simp
  · by_contra hu
    push Not at hu
    apply h
    rw [Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    simp

lemma arcCutoff_eq_one {u : ℝ} (h : |u| ≤ 4) : arcCutoff u = 1 := by
  unfold arcCutoff
  rw [abs_le] at h
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

/-- [21] (3.10): for coprime `a, b > 0` and `mn, rs ≥ 1`, a common `h` exists iff
`b m n − a r s = b − a`. -/
lemma exists_common_iff {a b m n r s : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (hmn : 1 ≤ m * n) (hrs : 1 ≤ r * s) :
    (∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h) ↔ sqDet a b m n r s - b + a = 0 := by
  unfold sqDet
  constructor
  · rintro ⟨h, h1, h2⟩
    have e1 : ((m * n : ℕ) : ℤ) = 1 + a * h := by
      rw [← Nat.sub_add_cancel hmn, h1]; push_cast; ring
    have e2 : ((r * s : ℕ) : ℤ) = 1 + b * h := by
      rw [← Nat.sub_add_cancel hrs, h2]; push_cast; ring
    push_cast at e1 e2
    linear_combination (b : ℤ) * e1 - (a : ℤ) * e2
  · intro heq
    obtain ⟨u, hu⟩ : ∃ u, m * n = u + 1 := ⟨m * n - 1, by omega⟩
    obtain ⟨v, hv⟩ : ∃ v, r * s = v + 1 := ⟨r * s - 1, by omega⟩
    have key : b * u = a * v := by
      have : (b : ℤ) * (u : ℤ) = (a : ℤ) * (v : ℤ) := by
        have e1 : ((m : ℤ) * n) = u + 1 := by exact_mod_cast hu
        have e2 : ((r : ℤ) * s) = v + 1 := by exact_mod_cast hv
        linear_combination heq + (-(b : ℤ)) * e1 + (a : ℤ) * e2
      exact_mod_cast this
    have hdvd : a ∣ u := by
      have : a ∣ u * b := ⟨v, by rw [mul_comm u b, key]⟩
      exact hab.dvd_of_dvd_mul_right this
    obtain ⟨h, rfl⟩ := hdvd
    refine ⟨h, by omega, ?_⟩
    have : a * v = a * (b * h) := by rw [← key]; ring
    have := Nat.eq_of_mul_eq_mul_left ha this
    omega

/-- The termwise identity on a coprime pair. -/
lemma term_identity (x A₀ Y : ℝ) (α β : ℕ → ℂ) (hα : α 0 = 0) (hβ : β 0 = 0)
    {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) (m n r s : ℕ) [Decidable
      (∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h)] :
    (if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β else 0) -
        sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b =
      sqWeight Y a b m n r s α β * minorKernel x A₀ Y (sqDet a b m n r s) a b := by
  by_cases hw : sqWeight Y a b m n r s α β = 0
  · simp [hw]
  have hm : m ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hα]
  have hn : n ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hβ]
  have hr : r ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hα]
  have hs : s ≠ 0 := by rintro rfl; apply hw; simp [sqWeight, hβ]
  have hηa : dyadicBump ((a : ℝ) / Y) ≠ 0 := by
    intro h0; apply hw; simp [sqWeight, h0]
  have hηb : dyadicBump ((b : ℝ) / Y) ≠ 0 := by
    intro h0; apply hw; simp [sqWeight, h0]
  have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm hn)
  have hrs : 1 ≤ r * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr hs)
  rw [minorKernel_eq, mul_sub, sub_left_inj]
  have hiff := exists_common_iff ha hab hmn hrs
  by_cases hE : ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h
  · have h0 : sqDet a b m n r s - b + a = 0 := hiff.1 hE
    rw [if_pos hE, if_pos h0]
    obtain ⟨ha1, ha4⟩ := dyadicBump_ne_zero hηa
    obtain ⟨hb1, hb4⟩ := dyadicBump_ne_zero hηb
    have hY : 0 < Y := by
      by_contra hY; push Not at hY
      have : (a : ℝ) / Y ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by positivity) hY
      linarith
    have ht : (sqDet a b m n r s : ℝ) = b - a := by
      have : sqDet a b m n r s = (b : ℤ) - a := by linarith
      rw [this]; push_cast; ring
    have hψ : arcCutoff ((sqDet a b m n r s : ℝ) / Y) = 1 := by
      apply arcCutoff_eq_one
      rw [ht, sub_div, abs_le]
      constructor <;> linarith
    rw [hψ]; simp
  · have h0 : ¬ (sqDet a b m n r s - b + a = 0) := fun h => hE (hiff.2 h)
    rw [if_neg hE, if_neg h0]; simp

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

lemma circNorm_eq_norm (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

/-- For a nonzero integer `n`, `{r ∈ (0,1] : ‖n r‖ ≤ ε}` has measure at most `2ε`
(multiplication by `n` preserves Haar measure on `ℝ/ℤ`). -/
lemma volume_circNorm_le (n : ℤ) (hn : n ≠ 0) (ε : ℝ) :
    volume ({r : ℝ | circNorm (n * r) ≤ ε} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * ε) := by
  set f : ℝ → UnitAddCircle := fun r => n • (r : UnitAddCircle)
  have hf : MeasurePreserving f (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    have := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn).comp
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
    simpa [f, Function.comp_def] using this
  have hset : {r : ℝ | circNorm (n * r) ≤ ε} = f ⁻¹' Metric.closedBall 0 ε := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, f]
    rw [circNorm_eq_norm, ← AddCircle.coe_zsmul]
    simp
  have hmeas : MeasurableSet (f ⁻¹' Metric.closedBall 0 ε) :=
    hf.measurable measurableSet_closedBall
  rw [hset, ← Measure.restrict_apply hmeas, hf.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

lemma pos_of_mem_primeGroup {x b : ℝ} {p : ℕ} (h : p ∈ primeGroup x b) : 0 < p := by
  unfold primeGroup at h
  exact (Finset.mem_filter.1 h).2.1.pos

/-! ## Counting and asymptotics -/

/-- `C log L + D ≤ ε L^a` eventually, for `a, ε > 0`. -/
lemma eventually_log_le_rpow {a : ℝ} (ha : 0 < a) (C D : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, C * log L + D ≤ ε * L ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := ε / (2 * (|C| + 1))) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (2 * |D| / ε)
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with L hL1 hL2 hL3
  have hpos : 0 ≤ L ^ a := by positivity
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos] at hL1
  have hlog : 0 ≤ log L := log_nonneg hL3
  rw [abs_of_nonneg hlog] at hL1
  have hC : C * log L ≤ |C| * log L := mul_le_mul_of_nonneg_right (le_abs_self C) hlog
  have hC2 : |C| * log L ≤ |C| * (ε / (2 * (|C| + 1)) * L ^ a) :=
    mul_le_mul_of_nonneg_left hL1 (abs_nonneg C)
  have hC3 : |C| * (ε / (2 * (|C| + 1)) * L ^ a) ≤ ε / 2 * L ^ a := by
    have : |C| / (|C| + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc |C| * (ε / (2 * (|C| + 1)) * L ^ a) = (|C| / (|C| + 1)) * (ε / 2 * L ^ a) := by
          field_simp
      _ ≤ 1 * (ε / 2 * L ^ a) := by gcongr
      _ = ε / 2 * L ^ a := one_mul _
  have hD : D ≤ ε / 2 * L ^ a := by
    have : 2 * |D| / ε * ε = 2 * |D| := by field_simp
    have h' : 2 * |D| ≤ ε * L ^ a := by
      calc 2 * |D| = 2 * |D| / ε * ε := this.symm
        _ ≤ L ^ a * ε := by gcongr
        _ = ε * L ^ a := mul_comm _ _
    linarith [le_abs_self D]
  linarith

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- One of four positive integers with product `m³` has fourth power at most `m³`. -/
lemma exists_pow_four_le {a b c d m : ℕ} (h : a * b * c * d = m ^ 3) :
    a ^ 4 ≤ m ^ 3 ∨ b ^ 4 ≤ m ^ 3 ∨ c ^ 4 ≤ m ^ 3 ∨ d ^ 4 ≤ m ^ 3 := by
  by_contra hc
  simp only [not_or, not_le] at hc
  obtain ⟨ha, hb, hc', hd⟩ := hc
  have h1 := mul_lt_mul'' (mul_lt_mul'' (mul_lt_mul'' ha hb (Nat.zero_le _) (Nat.zero_le _)) hc'
    (Nat.zero_le _) (Nat.zero_le _)) hd (Nat.zero_le _) (Nat.zero_le _)
  have h2 : a ^ 4 * b ^ 4 * c ^ 4 * d ^ 4 = (m ^ 3) ^ 4 := by
    rw [← h]; ring
  rw [h2] at h1
  have : m ^ 3 * m ^ 3 * m ^ 3 * m ^ 3 = (m ^ 3) ^ 4 := by ring
  omega

/-- For divisors `d₁, d₂` of `n > 0`, one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)`
has `lcm⁴ ≤ n³`. -/
lemma exists_flip_lcm_le {n d₁ d₂ : ℕ} (hn : 0 < n) (h₁ : d₁ ∣ n) (h₂ : d₂ ∣ n) :
    Nat.lcm d₁ d₂ ^ 4 ≤ n ^ 3 ∨ Nat.lcm (n / d₁) (n / d₂) ^ 4 ≤ n ^ 3 ∨
      Nat.lcm d₁ (n / d₂) ^ 4 ≤ n ^ 3 ∨ Nat.lcm (n / d₁) d₂ ^ 4 ≤ n ^ 3 := by
  have hd₁ : 0 < d₁ := Nat.pos_of_dvd_of_pos h₁ hn
  have hd₂ : 0 < d₂ := Nat.pos_of_dvd_of_pos h₂ hn
  set g := Nat.gcd d₁ d₂ with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd₁
  obtain ⟨u, hu⟩ : g ∣ d₁ := Nat.gcd_dvd_left _ _
  obtain ⟨v, hv⟩ : g ∣ d₂ := Nat.gcd_dvd_right _ _
  have hlcm : Nat.lcm d₁ d₂ = g * u * v := by
    have h := Nat.gcd_mul_lcm d₁ d₂
    rw [← hg] at h
    have : g * Nat.lcm d₁ d₂ = g * (g * u * v) := by
      rw [h]; nth_rewrite 1 [hu]; nth_rewrite 1 [hv]; ring
    exact Nat.eq_of_mul_eq_mul_left hg0 this
  obtain ⟨w, hw⟩ : Nat.lcm d₁ d₂ ∣ n := Nat.lcm_dvd h₁ h₂
  rw [hlcm] at hw
  have hu0 : 0 < u := by rcases Nat.eq_zero_or_pos u with h | h
                         · rw [h, mul_zero] at hu; omega
                         · exact h
  have hv0 : 0 < v := by rcases Nat.eq_zero_or_pos v with h | h
                         · rw [h, mul_zero] at hv; omega
                         · exact h
  have hw0 : 0 < w := by rcases Nat.eq_zero_or_pos w with h | h
                         · rw [h, mul_zero] at hw; omega
                         · exact h
  have hn1 : n / d₁ = v * w := by
    rw [hw, hu]; exact Nat.div_eq_of_eq_mul_right (by positivity) (by ring)
  have hn2 : n / d₂ = u * w := by
    rw [hw, hv]; exact Nat.div_eq_of_eq_mul_right (by positivity) (by ring)
  rw [hn1, hn2, hlcm, hu, hv]
  have b2 : Nat.lcm (v * w) (u * w) ≤ u * v * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨u, by ring⟩ ⟨v, by ring⟩)
  have b3 : Nat.lcm (g * u) (u * w) ≤ g * u * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨w, by ring⟩ ⟨g, by ring⟩)
  have b4 : Nat.lcm (v * w) (g * v) ≤ g * v * w :=
    Nat.le_of_dvd (by positivity) (Nat.lcm_dvd ⟨g, by ring⟩ ⟨w, by ring⟩)
  have hprod : (g * u * v) * (u * v * w) * (g * u * w) * (g * v * w) = n ^ 3 := by
    rw [hw]; ring
  rcases exists_pow_four_le hprod with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ((Nat.pow_le_pow_left b2 4).trans h))
  · exact Or.inr (Or.inr (Or.inl ((Nat.pow_le_pow_left b3 4).trans h)))
  · exact Or.inr (Or.inr (Or.inr ((Nat.pow_le_pow_left b4 4).trans h)))

/-- The four flips of a divisor pair. -/
def flip4 (n : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, q => q
  | 1, q => (n / q.1, n / q.2)
  | 2, q => (q.1, n / q.2)
  | _, q => (n / q.1, q.2)

lemma flip4_mem {n : ℕ} (k : ℕ) {q : ℕ × ℕ} (hq : q ∈ n.divisors ×ˢ n.divisors) :
    flip4 n k q ∈ n.divisors ×ˢ n.divisors := by
  simp only [mem_product, Nat.mem_divisors] at hq ⊢
  obtain ⟨⟨h1, hn⟩, h2, -⟩ := hq
  match k with
  | 0 => exact ⟨⟨h1, hn⟩, h2, hn⟩
  | 1 => exact ⟨⟨Nat.div_dvd_of_dvd h1, hn⟩, Nat.div_dvd_of_dvd h2, hn⟩
  | 2 => exact ⟨⟨h1, hn⟩, Nat.div_dvd_of_dvd h2, hn⟩
  | k + 3 => exact ⟨⟨Nat.div_dvd_of_dvd h1, hn⟩, h2, hn⟩

lemma flip4_flip4 {n : ℕ} (k : ℕ) {q : ℕ × ℕ} (hq : q ∈ n.divisors ×ˢ n.divisors) :
    flip4 n k (flip4 n k q) = q := by
  simp only [mem_product, Nat.mem_divisors] at hq
  obtain ⟨⟨h1, hn⟩, h2, -⟩ := hq
  obtain ⟨q1, q2⟩ := q
  match k with
  | 0 => rfl
  | 1 => simp [flip4, Nat.div_div_self h1 hn, Nat.div_div_self h2 hn]
  | 2 => simp [flip4, Nat.div_div_self h2 hn]
  | k + 3 => simp [flip4, Nat.div_div_self h1 hn]

/-- `τ(n)² ≤ 4 #{(e₁, e₂) : e₁, e₂ ∣ n, lcm(e₁, e₂)⁴ ≤ n³}`. -/
lemma card_divisors_sq_le (n : ℕ) (hn : 0 < n) :
    (n.divisors ×ˢ n.divisors).card ≤
      4 * ((n.divisors ×ˢ n.divisors).filter fun q => Nat.lcm q.1 q.2 ^ 4 ≤ n ^ 3).card := by
  set D := n.divisors ×ˢ n.divisors
  set good : ℕ × ℕ → Prop := fun q => Nat.lcm q.1 q.2 ^ 4 ≤ n ^ 3
  have hsub : D ⊆ (range 4).biUnion fun k => D.filter fun q => good (flip4 n k q) := by
    intro q hq
    have hq' := hq
    simp only [D, mem_product, Nat.mem_divisors] at hq'
    obtain ⟨⟨h1, -⟩, h2, -⟩ := hq'
    simp only [mem_biUnion, mem_range, mem_filter]
    rcases exists_flip_lcm_le hn h1 h2 with h | h | h | h
    · exact ⟨0, by norm_num, hq, h⟩
    · exact ⟨1, by norm_num, hq, h⟩
    · exact ⟨2, by norm_num, hq, h⟩
    · exact ⟨3, by norm_num, hq, h⟩
  have heq : ∀ k, (D.filter fun q => good (flip4 n k q)).card = (D.filter good).card := by
    intro k
    refine Finset.card_nbij' (flip4 n k) (flip4 n k) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq ⊢
      exact ⟨flip4_mem k hq.1, hq.2⟩
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq ⊢
      exact ⟨flip4_mem k hq.1, by rw [flip4_flip4 k hq.1]; exact hq.2⟩
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq
      exact flip4_flip4 k hq.1
    · intro q hq
      simp only [coe_filter, Set.mem_ofPred_eq] at hq
      exact flip4_flip4 k hq.1
  calc D.card ≤ ((range 4).biUnion fun k => D.filter fun q => good (flip4 n k q)).card :=
        card_le_card hsub
    _ ≤ ∑ k ∈ range 4, (D.filter fun q => good (flip4 n k q)).card := card_biUnion_le
    _ = 4 * (D.filter good).card := by simp [heq]

/-- The solutions `h ≤ Z` of `e ∣ 1 + l h` form at most one residue class modulo `e`. -/
lemma card_filter_dvd_le (e l Z : ℕ) (_he : 0 < e) :
    ((range (Z + 1)).filter fun h => e ∣ 1 + l * h).card ≤ Z / e + 1 := by
  set S := (range (Z + 1)).filter fun h => e ∣ 1 + l * h
  rcases S.eq_empty_or_nonempty with hS | ⟨h₀, hh₀⟩
  · rw [hS]; simp
  have hcop : Nat.Coprime e l := by
    have h0 := (mem_filter.1 hh₀).2
    have hd : Nat.gcd e l ∣ 1 :=
      (Nat.dvd_add_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right e l) h₀)).1
        ((Nat.gcd_dvd_left e l).trans h0)
    exact Nat.eq_one_of_dvd_one hd
  have hmod : ∀ h ∈ S, ∀ h' ∈ S, h % e = h' % e := by
    intro h hh h' hh'
    have e1 := (Nat.modEq_zero_iff_dvd.2 (mem_filter.1 hh).2)
    have e2 := (Nat.modEq_zero_iff_dvd.2 (mem_filter.1 hh').2)
    have e3 : 1 + l * h ≡ 1 + l * h' [MOD e] := e1.trans e2.symm
    have e4 : l * h ≡ l * h' [MOD e] := Nat.ModEq.add_left_cancel' 1 e3
    exact Nat.ModEq.cancel_left_of_coprime (hcop : Nat.gcd e l = 1) e4
  have hinj : Set.InjOn (fun h => h / e) S := by
    intro h hh h' hh' hq
    simp only at hq
    rw [← Nat.div_add_mod h e, ← Nat.div_add_mod h' e, hq, hmod h hh h' hh']
  have hmaps : Set.MapsTo (fun h => h / e) S (range (Z / e + 1)) := by
    intro h hh
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, S] at hh
    simp only [coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
  have := card_le_card_of_injOn _ hmaps hinj
  simpa using this

/-- **[21] (3.9).** If every `m` with `m⁴ ≤ (1 + lZ)³` is at most `T`, then
`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³`. -/
theorem sum_card_divisors_sq_progression (l Z T : ℕ)
    (hT : ∀ m : ℕ, m ^ 4 ≤ (1 + l * Z) ^ 3 → m ≤ T) :
    ∑ h ∈ range (Z + 1), (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * ((Z : ℝ) + T) * (1 + Real.log T) ^ 3 := by
  set P := Ioc 0 T ×ˢ Ioc 0 T
  -- pointwise: `τ(n)² ≤ 4 #{(e₁,e₂) ∈ [1,T]² : lcm ≤ T, lcm ∣ n}`
  have hpt : ∀ h ∈ range (Z + 1), (((1 + l * h).divisors.card : ℕ) : ℝ) ^ 2 ≤
      4 * ∑ q ∈ P, if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0 := by
    intro h hh
    have hn : 0 < 1 + l * h := by omega
    have hhZ : h ≤ Z := Nat.lt_succ_iff.1 (mem_range.1 hh)
    have h1 := card_divisors_sq_le (1 + l * h) hn
    rw [card_product] at h1
    have h2 : ((((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
        fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3).card : ℝ) ≤
        ∑ q ∈ P, if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0 := by
      rw [sum_boole]
      have hmaps : Set.MapsTo id
          (↑(((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
            fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3) : Set (ℕ × ℕ))
          ↑(P.filter fun q => Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h) := by
        intro q hq
        rw [mem_coe, mem_filter, mem_product, Nat.mem_divisors, Nat.mem_divisors] at hq
        obtain ⟨⟨⟨hq1, -⟩, hq2, -⟩, hq4⟩ := hq
        have hpow : (1 + l * h) ^ 3 ≤ (1 + l * Z) ^ 3 :=
          Nat.pow_le_pow_left (by have := Nat.mul_le_mul_left l hhZ; omega) 3
        have hlt : Nat.lcm q.1 q.2 ≤ T := hT _ (hq4.trans hpow)
        have hq1' : 0 < q.1 := Nat.pos_of_dvd_of_pos hq1 hn
        have hq2' : 0 < q.2 := Nat.pos_of_dvd_of_pos hq2 hn
        have hl1 : q.1 ≤ Nat.lcm q.1 q.2 :=
          Nat.le_of_dvd (Nat.lcm_pos hq1' hq2') (Nat.dvd_lcm_left _ _)
        have hl2 : q.2 ≤ Nat.lcm q.1 q.2 :=
          Nat.le_of_dvd (Nat.lcm_pos hq1' hq2') (Nat.dvd_lcm_right _ _)
        rw [id, mem_coe, mem_filter, mem_product, mem_Ioc, mem_Ioc]
        exact ⟨⟨⟨hq1', hl1.trans hlt⟩, hq2', hl2.trans hlt⟩, hlt, Nat.lcm_dvd hq1 hq2⟩
      exact_mod_cast card_le_card_of_injOn id hmaps (Set.injOn_id _)
    have h1' : ((((1 + l * h).divisors.card * (1 + l * h).divisors.card : ℕ)) : ℝ) ≤
        4 * ((((1 + l * h).divisors ×ˢ (1 + l * h).divisors).filter
          fun q => Nat.lcm q.1 q.2 ^ 4 ≤ (1 + l * h) ^ 3).card : ℝ) := by exact_mod_cast h1
    push_cast at h1'
    nlinarith
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, sum_comm]
  -- count `h` in one residue class
  have hcount : ∀ q ∈ P, ∑ h ∈ range (Z + 1),
      (if Nat.lcm q.1 q.2 ≤ T ∧ Nat.lcm q.1 q.2 ∣ 1 + l * h then (1 : ℝ) else 0) ≤
      ((Z : ℝ) + T) * ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) := by
    intro q hq
    simp only [P, mem_product, mem_Ioc] at hq
    obtain ⟨⟨hq1, -⟩, hq2, -⟩ := hq
    have hl0 : 0 < Nat.lcm q.1 q.2 := Nat.lcm_pos hq1 hq2
    have hgl : ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) = 1 / (Nat.lcm q.1 q.2 : ℝ) := by
      have := Nat.gcd_mul_lcm q.1 q.2
      have h' : ((q.1 : ℝ) * q.2) = Nat.gcd q.1 q.2 * Nat.lcm q.1 q.2 := by exact_mod_cast this.symm
      have hg0 : (Nat.gcd q.1 q.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.gcd_pos_of_pos_left _ hq1).ne'
      rw [h']; field_simp
    rw [hgl]
    by_cases hlT : Nat.lcm q.1 q.2 ≤ T
    · simp only [hlT, true_and]
      rw [sum_boole]
      have hc := card_filter_dvd_le (Nat.lcm q.1 q.2) l Z hl0
      have hc' : (((range (Z + 1)).filter fun h => Nat.lcm q.1 q.2 ∣ 1 + l * h).card : ℝ) ≤
          (Z / Nat.lcm q.1 q.2 : ℕ) + 1 := by exact_mod_cast hc
      have hdiv : ((Z / Nat.lcm q.1 q.2 : ℕ) : ℝ) ≤ (Z : ℝ) / Nat.lcm q.1 q.2 := Nat.cast_div_le
      have hlr : (0 : ℝ) < Nat.lcm q.1 q.2 := by exact_mod_cast hl0
      have h1 : (1 : ℝ) ≤ (T : ℝ) / Nat.lcm q.1 q.2 := by
        rw [le_div_iff₀ hlr]; exact_mod_cast (by simpa using hlT)
      calc _ ≤ ((Z / Nat.lcm q.1 q.2 : ℕ) : ℝ) + 1 := hc'
        _ ≤ (Z : ℝ) / Nat.lcm q.1 q.2 + (T : ℝ) / Nat.lcm q.1 q.2 := by linarith
        _ = ((Z : ℝ) + T) * (1 / (Nat.lcm q.1 q.2 : ℝ)) := by ring
    · simp only [hlT, false_and, if_false, sum_const_zero]
      positivity
  refine (mul_le_mul_of_nonneg_left (sum_le_sum hcount) (by norm_num)).trans ?_
  rw [← mul_sum, ← mul_assoc]
  have hP : ∑ q ∈ P, ((Nat.gcd q.1 q.2 : ℝ) / (q.1 * q.2)) ≤ (1 + Real.log T) ^ 3 := by
    rw [sum_product]
    refine (ArtinBV.sum_gcd_div_le T).trans ?_
    exact pow_le_pow_left₀ (ArtinBV.harmonic_partial_sum_nonneg T) (ArtinBV.harm_le T) 3
  have h0 : (0 : ℝ) ≤ 4 * ((Z : ℝ) + T) := by positivity
  exact mul_le_mul_of_nonneg_left hP h0

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

lemma dyadicBump_nonneg (u : ℝ) : 0 ≤ dyadicBump u := by
  unfold dyadicBump
  rcases le_or_gt u 0 with hu | hu
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith),
      Real.smoothTransition.zero_of_nonpos (by linarith)]; simp
  · exact sub_nonneg.2 (Real.smoothTransition.monotone (by linarith))

lemma dyadicBump_le_one (u : ℝ) : dyadicBump u ≤ 1 := by
  unfold dyadicBump
  linarith [Real.smoothTransition.le_one (u - 1), Real.smoothTransition.nonneg (u / 2 - 1)]

lemma abs_dyadicBump_le_one (u : ℝ) : |dyadicBump u| ≤ 1 := by
  rw [abs_of_nonneg (dyadicBump_nonneg u)]; exact dyadicBump_le_one u

lemma abs_arcCutoff_le (u : ℝ) : |arcCutoff u| ≤ if |u| < 5 then 1 else 0 := by
  unfold arcCutoff
  have h1 := Real.smoothTransition.nonneg (5 - u)
  have h2 := Real.smoothTransition.nonneg (5 + u)
  have h3 := Real.smoothTransition.le_one (5 - u)
  have h4 := Real.smoothTransition.le_one (5 + u)
  rw [abs_of_nonneg (mul_nonneg h1 h2)]
  split_ifs with hu
  · nlinarith
  · rw [abs_lt] at hu
    push Not at hu
    by_cases hu' : u ≤ -5
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith : 5 + u ≤ 0), mul_zero]
    · rw [Real.smoothTransition.zero_of_nonpos (by linarith [hu (not_le.1 hu')] : 5 - u ≤ 0),
        zero_mul]

/-- The number of factorizations `m n = k` with `m, n` in given finite sets is at most `τ(k)`. -/
lemma card_mul_eq_le (A B : Finset ℕ) (k : ℕ) (hk : 0 < k) :
    ((A ×ˢ B).filter fun q => q.1 * q.2 = k).card ≤ k.divisors.card := by
  refine card_le_card_of_injOn Prod.fst (fun q hq => ?_) (fun q hq q' hq' h => ?_)
  · simp only [coe_filter, Set.mem_ofPred_eq] at hq
    rw [mem_coe, Nat.mem_divisors]
    exact ⟨⟨q.2, hq.2.symm⟩, hk.ne'⟩
  · simp only [coe_filter, Set.mem_ofPred_eq] at hq hq'
    have h1 := hq.2
    have h2 := hq'.2
    have hq1 : 0 < q.1 := Nat.pos_of_ne_zero (by rintro h0; rw [h0, zero_mul] at h1; omega)
    have : q.2 = q'.2 := by
      rw [h] at h1
      exact Nat.eq_of_mul_eq_mul_left (h ▸ hq1) (h1.trans h2.symm)
    exact Prod.ext h this

/-- Regrouping a sum over pairs `(m, n)` by the product `k = m n`. -/
lemma sum_prod_le_sum_tau (A B : Finset ℕ) (N : ℕ) (G : ℕ → ℝ) (hG : ∀ k, 0 ≤ G k)
    (hA : ∀ m ∈ A, 0 < m) (hB : ∀ n ∈ B, 0 < n) (hN : ∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) :
    ∑ m ∈ A, ∑ n ∈ B, G (m * n) ≤ ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) * G k := by
  rw [← sum_product']
  rw [← sum_fiberwise_of_maps_to (s := A ×ˢ B) (t := Ioc 0 N) (g := fun q => q.1 * q.2)
    (fun q hq => by
      rw [mem_product] at hq
      exact mem_Ioc.2 ⟨Nat.mul_pos (hA _ hq.1) (hB _ hq.2), hN _ hq.1 _ hq.2⟩)]
  refine sum_le_sum fun k hk => ?_
  have hk0 : 0 < k := (mem_Ioc.1 hk).1
  rw [sum_congr rfl (fun q hq => by rw [(mem_filter.1 hq).2]), sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_mul_eq_le A B k hk0) (hG k)

/-- An open window of length `< 10 a` contains at most `10` multiples-indices: if `Y < a` then
`#{l ∈ S : |c − a l| < 5Y} ≤ 10`. -/
lemma card_window_le (S : Finset ℕ) (a : ℕ) (Y c : ℝ) (hY : 0 < Y) (ha : Y < a) :
    (S.filter fun l : ℕ => |c - a * (l : ℝ)| < 5 * Y).card ≤ 10 := by
  set F := S.filter fun l : ℕ => |c - a * (l : ℝ)| < 5 * Y
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF]; simp
  set l₀ := F.min' hF
  have hl₀ : l₀ ∈ F := F.min'_mem hF
  have hsub : F ⊆ Icc l₀ (l₀ + 9) := by
    intro l hl
    rw [mem_Icc]
    refine ⟨F.min'_le l hl, ?_⟩
    have h1 := (mem_filter.1 hl).2
    have h2 := (mem_filter.1 hl₀).2
    rw [abs_lt] at h1 h2
    have hapos : (0 : ℝ) < a := hY.trans ha
    have : (a : ℝ) * ((l : ℝ) - l₀) < 10 * a := by nlinarith
    have : (l : ℝ) - l₀ < 10 := by nlinarith
    have : (l : ℝ) < l₀ + 10 := by linarith
    have : l < l₀ + 10 := by exact_mod_cast this
    omega
  calc F.card ≤ (Icc l₀ (l₀ + 9)).card := card_le_card hsub
    _ = 10 := by simp only [Nat.card_Icc]; omega

/-- `|α m| ≤ L^C · 1_{m ≠ 0}` when `α₀ = 0`. -/
lemma norm_coeff_le (α : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (m : ℕ) :
    ‖α m‖ ≤ B * (if m ≠ 0 then 1 else 0) := by
  by_cases hm : m = 0
  · subst hm; simp [hα0]
  · simp [hm, hαB m]

/-! ## The measure of the major arcs -/

/-- `vol 𝔐 ≤ 4 L^{3A₀}/Y` (`L = log x ≥ 1`, `A₀ ≥ 0`, `Y > 0`). -/
lemma volume_majorArcs_le (x A₀ Y : ℝ) (hL : 1 ≤ log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    volume (majorArcs x A₀ Y) ≤ ENNReal.ofReal (4 * log x ^ (3 * A₀) / Y) := by
  set Q := log x ^ A₀
  set K₀ := ⌊Q⌋₊
  set ρ := 2 * Q / Y
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL hA₀
  have hsub : majorArcs x A₀ Y ⊆ {0} ∪ ⋃ k ∈ Icc 1 K₀,
      ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩ Set.Ioc 0 1) := by
    rintro θ ⟨h0, h1, k, hk1, hkQ, c, -, hc⟩
    rcases h0.lt_or_eq with h0 | h0
    · right
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨k, ⟨hk1, Nat.le_floor hkQ⟩, ?_, h0, h1.le⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc circNorm (((k : ℤ) : ℝ) * θ) ≤ |((k : ℤ) : ℝ) * θ - c| := round_le _ c
        _ = k * |θ - c / k| := by
            have e : ((k : ℤ) : ℝ) * θ - c = k * (θ - c / k) := by
              push_cast; field_simp
            rw [e, abs_mul, abs_of_pos hk0]
        _ ≤ k * ρ := by gcongr
    · left; exact h0.symm
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ k ∈ Icc 1 K₀, volume ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩
      Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (k * ρ)) := fun k hk =>
    volume_circNorm_le k (by have := (mem_Icc.1 hk).1; omega) _
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK₀ : (K₀ : ℝ) ≤ Q := Nat.floor_le (by positivity)
  have hsum : ∑ k ∈ Icc 1 K₀, 2 * ((k : ℝ) * ρ) ≤ ∑ _k ∈ Icc 1 K₀, 2 * (Q * ρ) := by
    refine sum_le_sum fun k hk => ?_
    have : (k : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hk).2).trans hK₀
    gcongr
  refine hsum.trans ?_
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  have h3 : log x ^ (3 * A₀) = Q * Q * Q := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  rw [h3]
  have hρ : 0 ≤ ρ := by positivity
  calc (K₀ : ℝ) * (2 * (Q * ρ)) ≤ Q * (2 * (Q * ρ)) := by gcongr
    _ = 4 * (Q * Q * Q) / Y := by simp only [ρ]; ring

/-! ## The raw inner sum at one pair of label products -/

lemma norm_sqWeight_le (Y : ℝ) (a b m n r s : ℕ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) :
    ‖sqWeight Y a b m n r s α β‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      ((if m ≠ 0 then 1 else 0) * (if n ≠ 0 then 1 else 0) * (if r ≠ 0 then 1 else 0) *
        (if s ≠ 0 then 1 else 0)) := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  unfold sqWeight
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
  have h1 := norm_coeff_le α B hα0 hαB m
  have h2 := norm_coeff_le α B hα0 hαB r
  have h3 := norm_coeff_le β B hβ0 hβB n
  have h4 := norm_coeff_le β B hβ0 hβB s
  rw [abs_mul]
  have hη : 0 ≤ |dyadicBump (a / Y)| * |dyadicBump (b / Y)| := by positivity
  calc |dyadicBump (a / Y)| * |dyadicBump (b / Y)| * ‖α m‖ * ‖α r‖ * ‖β n‖ * ‖β s‖
      ≤ |dyadicBump (a / Y)| * |dyadicBump (b / Y)| * (B * (if m ≠ 0 then 1 else 0)) *
          (B * (if r ≠ 0 then 1 else 0)) * (B * (if n ≠ 0 then 1 else 0)) *
          (B * (if s ≠ 0 then 1 else 0)) := by gcongr
    _ = _ := by ring

/-- **The raw inner sum** at label products `Y < a, b`: `‖rawInner‖ ≤ |η η| B⁴ · 4(Z + T)(1 + log T)³`
with `Z = ⌊4 H_m H_n / Y⌋`, by `∑_h τ(1+ah) τ(1+bh)` and (3.9). -/
lemma norm_rawInner_le (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (hY : 0 < Y)
    (a b : ℕ) (ha : Y < a) (_hb : Y < b) (T : ℕ)
    (hTa : ∀ m : ℕ, m ^ 4 ≤ (1 + a * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ T)
    (hTb : ∀ m : ℕ, m ^ 4 ≤ (1 + b * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ T) :
    ‖rawInner Y Hm Hn α β a b‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      (4 * ((⌊4 * Hm * Hn / Y⌋₊ : ℝ) + T) * (1 + log T) ^ 3) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  set Z := ⌊4 * Hm * Hn / Y⌋₊
  set E := |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4
  have hE : 0 ≤ E := by positivity
  set R1 := range (⌊2 * Hm⌋₊ + 1)
  set R2 := range (⌊2 * Hn⌋₊ + 1)
  set f : ℕ → ℕ → ℕ → ℝ := fun m n h => if m * n = 1 + a * h then 1 else 0
  set g : ℕ → ℕ → ℕ → ℝ := fun r s h => if r * s = 1 + b * h then 1 else 0
  have hapos : (0 : ℝ) < a := hY.trans ha
  -- pointwise
  have hpt : ∀ m ∈ R1, ∀ n ∈ R2, ∀ r ∈ R1, ∀ s ∈ R2,
      ‖(if ∃ h : ℕ, m * n - 1 = a * h ∧ r * s - 1 = b * h then sqWeight Y a b m n r s α β
        else 0)‖ ≤ E * ∑ h ∈ range (Z + 1), f m n h * g r s h := by
    intro m hm n hn r hr s hs
    have hsum0 : 0 ≤ ∑ h ∈ range (Z + 1), f m n h * g r s h :=
      sum_nonneg fun h _ => by simp only [f, g]; split_ifs <;> norm_num
    split_ifs with hE'
    · obtain ⟨h₀, hh1, hh2⟩ := hE'
      have hw := norm_sqWeight_le Y a b m n r s α β B hα0 hβ0 hαB hβB
      by_cases hz : m ≠ 0 ∧ n ≠ 0 ∧ r ≠ 0 ∧ s ≠ 0
      · obtain ⟨hm0, hn0, hr0, hs0⟩ := hz
        simp only [hm0, hn0, hr0, hs0, ne_eq, not_false_eq_true, if_true, mul_one] at hw
        have hmn : 1 ≤ m * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hm0 hn0)
        have hrs : 1 ≤ r * s := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hr0 hs0)
        have e1 : m * n = 1 + a * h₀ := by omega
        have e2 : r * s = 1 + b * h₀ := by omega
        have hh₀ : h₀ ∈ range (Z + 1) := by
          rw [mem_range, Nat.lt_succ_iff]
          apply Nat.le_floor
          have hm' : (m : ℝ) ≤ 2 * Hm :=
            (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hm))).trans (Nat.floor_le (by positivity))
          have hn' : (n : ℝ) ≤ 2 * Hn :=
            (Nat.cast_le.2 (Nat.lt_succ_iff.1 (mem_range.1 hn))).trans (Nat.floor_le (by positivity))
          have hprod : (a : ℝ) * h₀ < 4 * Hm * Hn := by
            have : ((m * n : ℕ) : ℝ) = 1 + a * h₀ := by exact_mod_cast e1
            push_cast at this
            have : (m : ℝ) * n ≤ 2 * Hm * (2 * Hn) :=
              mul_le_mul hm' hn' (Nat.cast_nonneg _) (by positivity)
            linarith
          rw [le_div_iff₀ hY]
          have : (h₀ : ℝ) * Y ≤ h₀ * a := by gcongr
          linarith [mul_comm (a : ℝ) h₀]
        have h1 : 1 ≤ ∑ h ∈ range (Z + 1), f m n h * g r s h := by
          have hle := single_le_sum (f := fun h => f m n h * g r s h)
            (fun h _ => by simp only [f, g]; split_ifs <;> norm_num) hh₀
          have hval : f m n h₀ * g r s h₀ = 1 := by simp only [f, g, e1, e2, if_true, mul_one]
          calc (1 : ℝ) = f m n h₀ * g r s h₀ := hval.symm
            _ ≤ _ := hle
        calc ‖sqWeight Y a b m n r s α β‖ ≤ E := hw
          _ = E * 1 := (mul_one E).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left h1 hE
      · have hzero : (if m ≠ 0 then (1 : ℝ) else 0) * (if n ≠ 0 then 1 else 0) *
            (if r ≠ 0 then 1 else 0) * (if s ≠ 0 then 1 else 0) = 0 := by
          simp only [not_and_or, not_not] at hz
          rcases hz with h | h | h | h <;> simp [h]
        rw [hzero, mul_zero] at hw
        exact hw.trans (mul_nonneg hE hsum0)
    · rw [norm_zero]; exact mul_nonneg hE hsum0
  -- sum the pointwise bound
  have hstep1 : ‖rawInner Y Hm Hn α β a b‖ ≤
      ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, E * ∑ h ∈ range (Z + 1), f m n h * g r s h := by
    unfold rawInner
    refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun r hr => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun s hs => ?_)
    exact hpt m hm n hn r hr s hs
  have hstep2 : ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2,
      E * ∑ h ∈ range (Z + 1), f m n h * g r s h =
      E * ∑ h ∈ range (Z + 1), (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h) := by
    set H := range (Z + 1)
    have hprod : ∀ h, (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h) =
        ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h := by
      intro h
      rw [sum_mul]; refine sum_congr rfl fun m _ => ?_
      rw [sum_mul]; refine sum_congr rfl fun n _ => ?_
      rw [mul_sum]; refine sum_congr rfl fun r _ => ?_
      rw [mul_sum]
    have hcomm : ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, ∑ h ∈ H, f m n h * g r s h =
        ∑ h ∈ H, ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h := by
      calc _ = ∑ m ∈ R1, ∑ n ∈ R2, ∑ r ∈ R1, ∑ h ∈ H, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ => sum_comm
        _ = ∑ m ∈ R1, ∑ n ∈ R2, ∑ h ∈ H, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_comm
        _ = ∑ m ∈ R1, ∑ h ∈ H, ∑ n ∈ R2, ∑ r ∈ R1, ∑ s ∈ R2, f m n h * g r s h :=
            sum_congr rfl fun m _ => sum_comm
        _ = _ := sum_comm
    simp only [← mul_sum]
    rw [hcomm]
    simp only [hprod]
  have hfib : ∀ (c : ℕ), ∀ k : ℕ, 0 < k → ∀ (A' B' : Finset ℕ),
      ∑ m ∈ A', ∑ n ∈ B', (if m * n = k then (1 : ℝ) else 0) ≤ (k.divisors.card : ℝ) := by
    intro _ k hk A' B'
    rw [← sum_product', sum_boole]
    exact_mod_cast card_mul_eq_le A' B' k hk
  have hstep3 : ∑ h ∈ range (Z + 1), (∑ m ∈ R1, ∑ n ∈ R2, f m n h) * (∑ r ∈ R1, ∑ s ∈ R2, g r s h)
      ≤ ∑ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
          (((1 + b * h).divisors.card : ℕ) : ℝ) := by
    refine sum_le_sum fun h _ => mul_le_mul (hfib 0 _ (by omega) R1 R2) (hfib 0 _ (by omega) R1 R2)
      (sum_nonneg fun r _ => sum_nonneg fun s _ => by simp only [g]; split_ifs <;> norm_num)
      (Nat.cast_nonneg _)
  have hstep4 : ∑ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
      (((1 + b * h).divisors.card : ℕ) : ℝ) ≤ 4 * ((Z : ℝ) + T) * (1 + log T) ^ 3 := by
    have ha3 := sum_card_divisors_sq_progression a Z T hTa
    have hb3 := sum_card_divisors_sq_progression b Z T hTb
    have : ∀ h ∈ range (Z + 1), (((1 + a * h).divisors.card : ℕ) : ℝ) *
        (((1 + b * h).divisors.card : ℕ) : ℝ) ≤ ((((1 + a * h).divisors.card : ℕ) : ℝ) ^ 2 +
          (((1 + b * h).divisors.card : ℕ) : ℝ) ^ 2) / 2 := fun h _ => by
      nlinarith [sq_nonneg ((((1 + a * h).divisors.card : ℕ) : ℝ) -
        (((1 + b * h).divisors.card : ℕ) : ℝ))]
    refine (sum_le_sum this).trans ?_
    rw [← sum_div, sum_add_distrib]
    linarith
  calc ‖rawInner Y Hm Hn α β a b‖ ≤ _ := hstep1
    _ = _ := hstep2
    _ ≤ E * (4 * ((Z : ℝ) + T) * (1 + log T) ^ 3) :=
        mul_le_mul_of_nonneg_left (hstep3.trans hstep4) hE

/-! ## The major inner sum at one pair of label products -/

lemma norm_majorKernel_le (x A₀ Y : ℝ) (t a b : ℤ) :
    ‖majorKernel x A₀ Y t a b‖ ≤
      (if |(t : ℝ) / Y| < 5 then 1 else 0) * (volume (majorArcs x A₀ Y)).toReal := by
  unfold majorKernel
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hfin : volume (majorArcs x A₀ Y) < ⊤ :=
    (measure_mono (majorArcs_subset x A₀ Y)).trans_lt (by simp)
  have hint : ‖∫ θ in majorArcs x A₀ Y,
      Complex.exp (2 * π * Complex.I * ((θ * (t - b + a) : ℝ) : ℂ))‖ ≤
      1 * volume.real (majorArcs x A₀ Y) := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun θ _ => ?_
    rw [Complex.norm_exp]
    simp
  rw [one_mul] at hint
  exact mul_le_mul (abs_arcCutoff_le _) hint (norm_nonneg _) (by split_ifs <;> norm_num)

/-- `∑_{k,l ≤ N} τ(k)τ(l) 1_{|bk − al| < 5Y} ≤ 10 ∑_{k ≤ N} τ(k)²` for `Y < a, b`. -/
lemma sum_tau_window_le (N a b : ℕ) (Y : ℝ) (hY : 0 < Y) (ha : Y < a) (hb : Y < b) :
    ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) * ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) *
      (if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0) ≤
      10 * ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) ^ 2 := by
  set W : ℕ → ℕ → ℝ := fun k l => if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0
  have hW0 : ∀ k l, 0 ≤ W k l := fun k l => by simp only [W]; split_ifs <;> norm_num
  have hWiff : ∀ k l : ℕ, |((b : ℝ) * k - a * l) / Y| < 5 ↔ |(b : ℝ) * k - a * l| < 5 * Y := by
    intro k l; rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY]
  have hrow : ∀ k, ∑ l ∈ Ioc 0 N, W k l ≤ 10 := by
    intro k
    simp only [W]
    rw [sum_boole]
    have := card_window_le (Ioc 0 N) a Y (b * k) hY ha
    have heq : ((Ioc 0 N).filter fun l : ℕ => |((b : ℝ) * k - a * l) / Y| < 5) =
        (Ioc 0 N).filter fun l : ℕ => |(b : ℝ) * k - a * (l : ℝ)| < 5 * Y := by
      ext l; simp only [mem_filter, hWiff]
    rw [heq]; exact_mod_cast this
  have hcol : ∀ l, ∑ k ∈ Ioc 0 N, W k l ≤ 10 := by
    intro l
    simp only [W]
    rw [sum_boole]
    have := card_window_le (Ioc 0 N) b Y (a * l) hY hb
    have heq : ((Ioc 0 N).filter fun k : ℕ => |((b : ℝ) * k - a * l) / Y| < 5) =
        (Ioc 0 N).filter fun k : ℕ => |(a : ℝ) * l - b * (k : ℝ)| < 5 * Y := by
      ext k; simp only [mem_filter, hWiff, abs_sub_comm]
    rw [heq]; exact_mod_cast this
  set τ : ℕ → ℝ := fun k => (k.divisors.card : ℝ)
  have hpt : ∀ k l, τ k * (τ l * W k l) ≤ (τ k ^ 2 * W k l + τ l ^ 2 * W k l) / 2 := by
    intro k l
    have := hW0 k l
    nlinarith [sq_nonneg (τ k - τ l), mul_nonneg this (sq_nonneg (τ k - τ l))]
  calc ∑ k ∈ Ioc 0 N, τ k * ∑ l ∈ Ioc 0 N, τ l * W k l
      = ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ k * (τ l * W k l) := by simp only [mul_sum]
    _ ≤ ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, (τ k ^ 2 * W k l + τ l ^ 2 * W k l) / 2 :=
        sum_le_sum fun k _ => sum_le_sum fun l _ => hpt k l
    _ = (∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ k ^ 2 * W k l +
          ∑ k ∈ Ioc 0 N, ∑ l ∈ Ioc 0 N, τ l ^ 2 * W k l) / 2 := by
        simp only [add_div, sum_add_distrib, sum_div]
    _ = (∑ k ∈ Ioc 0 N, τ k ^ 2 * ∑ l ∈ Ioc 0 N, W k l +
          ∑ l ∈ Ioc 0 N, τ l ^ 2 * ∑ k ∈ Ioc 0 N, W k l) / 2 := by
        congr 2
        · simp only [mul_sum]
        · rw [sum_comm]; simp only [mul_sum]
    _ ≤ (∑ k ∈ Ioc 0 N, τ k ^ 2 * 10 + ∑ l ∈ Ioc 0 N, τ l ^ 2 * 10) / 2 := by
        gcongr with k _ l _
        · exact hrow k
        · exact hcol l
    _ = 10 * ∑ k ∈ Ioc 0 N, τ k ^ 2 := by
        rw [← sum_mul, mul_comm]; ring

/-- **The major inner sum** at label products `Y < a, b`:
`‖majInner‖ ≤ |η η| B⁴ vol(𝔐) · 10 N (1 + log N)³`, `N = ⌊2H_m⌋ ⌊2H_n⌋` ((4.61)). -/
lemma norm_majInner_le (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (B : ℝ) (hα0 : α 0 = 0)
    (hβ0 : β 0 = 0) (hαB : ∀ m, ‖α m‖ ≤ B) (hβB : ∀ n, ‖β n‖ ≤ B) (hY : 0 < Y)
    (a b : ℕ) (ha : Y < a) (hb : Y < b) :
    ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4 *
      (volume (majorArcs x A₀ Y)).toReal *
        (10 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) *
          (1 + log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ^ 3) := by
  classical
  have hB : 0 ≤ B := (norm_nonneg _).trans (hαB 0)
  set N := ⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊
  set E := |dyadicBump (a / Y) * dyadicBump (b / Y)| * B ^ 4
  set μ := (volume (majorArcs x A₀ Y)).toReal
  have hE : 0 ≤ E := by positivity
  have hμ : 0 ≤ μ := ENNReal.toReal_nonneg
  set R1 := range (⌊2 * Hm⌋₊ + 1)
  set R2 := range (⌊2 * Hn⌋₊ + 1)
  set W : ℕ → ℕ → ℝ := fun k l => if |((b : ℝ) * k - a * l) / Y| < 5 then 1 else 0
  have hW0 : ∀ k l, 0 ≤ W k l := fun k l => by simp only [W]; split_ifs <;> norm_num
  set χ : ℕ → ℝ := fun m => if m ≠ 0 then 1 else 0
  -- pointwise
  have hpt : ∀ m n r s, ‖sqWeight Y a b m n r s α β * majorKernel x A₀ Y (sqDet a b m n r s) a b‖
      ≤ E * μ * (χ m * (χ n * (χ r * (χ s * W (m * n) (r * s))))) := by
    intro m n r s
    rw [norm_mul]
    have h1 := norm_sqWeight_le Y a b m n r s α β B hα0 hβ0 hαB hβB
    have h2 := norm_majorKernel_le x A₀ Y (sqDet a b m n r s) a b
    have hdet : ((sqDet a b m n r s : ℤ) : ℝ) = (b : ℝ) * ((m * n : ℕ) : ℝ) - a * ((r * s : ℕ) : ℝ) := by
      unfold sqDet; push_cast; ring
    rw [hdet] at h2
    have hχ : 0 ≤ χ m * χ n * χ r * χ s := by simp only [χ]; split_ifs <;> norm_num
    calc _ ≤ (E * (χ m * χ n * χ r * χ s)) * (W (m * n) (r * s) * μ) :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hE hχ)
      _ = _ := by ring
  have hstep1 : ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ E * μ *
      ∑ m ∈ R1, χ m * ∑ n ∈ R2, χ n * ∑ r ∈ R1, χ r * ∑ s ∈ R2, χ s * W (m * n) (r * s) := by
    unfold majInner
    simp only [mul_sum]
    refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    refine (norm_sum_le _ _).trans (sum_le_sum fun s _ => ?_)
    exact hpt m n r s
  -- restrict to nonzero variables
  set A := R1.filter (· ≠ 0)
  set B' := R2.filter (· ≠ 0)
  have hχsum : ∀ (S : Finset ℕ) (F : ℕ → ℝ), ∑ m ∈ S, χ m * F m = ∑ m ∈ S.filter (· ≠ 0), F m := by
    intro S F
    rw [sum_filter]
    refine sum_congr rfl fun m _ => ?_
    simp only [χ]; split_ifs <;> simp
  have hstep2 : ∑ m ∈ R1, χ m * ∑ n ∈ R2, χ n * ∑ r ∈ R1, χ r * ∑ s ∈ R2, χ s * W (m * n) (r * s)
      = ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) := by
    rw [hχsum]
    refine sum_congr rfl fun m _ => ?_
    rw [hχsum]
    refine sum_congr rfl fun n _ => ?_
    rw [hχsum]
    refine sum_congr rfl fun r _ => ?_
    rw [hχsum]
  have hApos : ∀ m ∈ A, 0 < m := fun m hm => Nat.pos_of_ne_zero (mem_filter.1 hm).2
  have hBpos : ∀ n ∈ B', 0 < n := fun n hn => Nat.pos_of_ne_zero (mem_filter.1 hn).2
  have hAB : ∀ m ∈ A, ∀ n ∈ B', m * n ≤ N := by
    intro m hm n hn
    exact Nat.mul_le_mul (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hm).1))
      (Nat.lt_succ_iff.1 (mem_range.1 (mem_filter.1 hn).1))
  have hstep3 : ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) ≤
      ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) *
        ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W k l := by
    calc ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s)
        ≤ ∑ m ∈ A, ∑ n ∈ B', ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W (m * n) l :=
          sum_le_sum fun m _ => sum_le_sum fun n _ =>
            sum_prod_le_sum_tau A B' N (W (m * n)) (hW0 _) hApos hBpos hAB
      _ ≤ _ := sum_prod_le_sum_tau A B' N
          (fun k => ∑ l ∈ Ioc 0 N, (l.divisors.card : ℝ) * W k l)
          (fun k => sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (hW0 _ _))
          hApos hBpos hAB
  have hstep4 := sum_tau_window_le N a b Y hY ha hb
  have hstep5 := ArtinBV.sum_card_divisors_sq_le N
  calc ‖majInner x A₀ Y Hm Hn α β a b‖ ≤ _ := hstep1
    _ = E * μ * ∑ m ∈ A, ∑ n ∈ B', ∑ r ∈ A, ∑ s ∈ B', W (m * n) (r * s) := by rw [hstep2]
    _ ≤ E * μ * (10 * ∑ k ∈ Ioc 0 N, (k.divisors.card : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (hstep3.trans hstep4) (mul_nonneg hE hμ)
    _ ≤ E * μ * (10 * ((N : ℝ) * (1 + log N) ^ 3)) := by gcongr
    _ = _ := by ring

/-! ## The mass of label pairs with a common prime -/

/-- The harmonic weight `∏ᵢ 1/(pᵢ Vᵢ)` of a label tuple. -/
noncomputable def labelWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) : ℝ :=
  ∏ i, 1 / ((p i : ℝ) * groupReciprocalSum x (a i))

lemma groupReciprocalSum_nonneg (x b : ℝ) : 0 ≤ groupReciprocalSum x b :=
  sum_nonneg fun p _ => by positivity

lemma labelWeight_nonneg (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (p : Fin K → ℕ) :
    0 ≤ labelWeight x a p :=
  prod_nonneg fun i _ => by have := groupReciprocalSum_nonneg x (a i); positivity

lemma sum_inv_mul_groupReciprocalSum_le (x b : ℝ) :
    ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) ≤ 1 := by
  have hV : groupReciprocalSum x b = ∑ q ∈ primeGroup x b, 1 / (q : ℝ) := rfl
  rw [show ∑ q ∈ primeGroup x b, 1 / ((q : ℝ) * groupReciprocalSum x b) =
      (∑ q ∈ primeGroup x b, 1 / (q : ℝ)) / groupReciprocalSum x b by
    rw [sum_div]; exact sum_congr rfl fun q _ => by rw [div_div], ← hV]
  exact div_self_le_one _

lemma sum_labelWeight_le_one (x : ℝ) {K : ℕ} (a : Fin K → ℝ) :
    ∑ p ∈ labelTuples x a, labelWeight x a p ≤ 1 := by
  unfold labelTuples labelWeight
  rw [← Finset.prod_univ_sum (fun i => primeGroup x (a i))
    (fun i (q : ℕ) => 1 / ((q : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_le_one (fun i _ => sum_nonneg fun q _ => ?_) fun i _ =>
    sum_inv_mul_groupReciprocalSum_le x (a i)
  have := groupReciprocalSum_nonneg x (a i); positivity

/-- Label products with a common prime share a label. -/
lemma exists_eq_of_not_coprime {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p p' : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) (hp' : p' ∈ labelTuples x a)
    (h : ¬ Nat.Coprime (∏ i, p i) (∏ i, p' i)) : ∃ i j, p i = p' j := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
  have hpr : ∀ (r : Fin K → ℕ), r ∈ labelTuples x a → ∀ i, (r i).Prime := by
    intro r hr i
    have := (Fintype.mem_piFinset.1 hr) i
    unfold primeGroup at this
    exact (mem_filter.1 this).2.1
  obtain ⟨i, -, hi⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h1
  obtain ⟨j, -, hj⟩ := (Nat.prime_iff.1 hq).dvd_finsetProd_iff _ |>.1 h2
  exact ⟨i, j, ((Nat.prime_dvd_prime_iff_eq hq (hpr p hp i)).1 hi).symm.trans
    ((Nat.prime_dvd_prime_iff_eq hq (hpr p' hp' j)).1 hj)⟩

lemma abs_dyadicBump_le_div (u : ℕ) (Y : ℝ) (hY : 0 < Y) (hu : 0 < u) :
    |dyadicBump (u / Y)| ≤ 4 * Y / u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  by_cases h : dyadicBump (u / Y) = 0
  · rw [h, abs_zero]; positivity
  · have := (dyadicBump_ne_zero h).2
    rw [div_lt_iff₀ hY] at this
    rw [le_div_iff₀ hu']
    have := mul_le_of_le_one_left hu'.le (abs_dyadicBump_le_one (u / Y))
    linarith

/-! ## Inputs about the groups for large `x` -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

lemma prod_le_of_mem_labelTuples {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {p : Fin K → ℕ}
    (hp : p ∈ labelTuples x a) : ((∏ i, p i : ℕ) : ℝ) ≤ ∏ i, exp (2 * log x ^ a i) := by
  push_cast
  exact prod_le_prod (fun i _ => Nat.cast_nonneg _)
    fun i _ => (le_of_mem_primeGroup ((Fintype.mem_piFinset.1 hp) i)).2

lemma dyadicBump_eq_zero_of_le_one {u : ℝ} (hu : u ≤ 1) : dyadicBump u = 0 := by
  by_contra h
  linarith [(dyadicBump_ne_zero h).1]

lemma rawInner_eq_zero (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ)
    (h : dyadicBump (a / Y) * dyadicBump (b / Y) = 0) : rawInner Y Hm Hn α β a b = 0 := by
  unfold rawInner sqWeight
  rcases mul_eq_zero.1 h with h | h <;> simp [h]

lemma majInner_eq_zero (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a b : ℕ)
    (h : dyadicBump (a / Y) * dyadicBump (b / Y) = 0) : majInner x A₀ Y Hm Hn α β a b = 0 := by
  unfold majInner sqWeight
  rcases mul_eq_zero.1 h with h | h <;> simp [h]

/-! ## Numerics -/

lemma rpow_combine {L : ℝ} (hL : 0 < L) (D : ℝ) (hD : 0 < D) (s t : ℝ)
    (h : log D + s * log L ≤ t) : D * L ^ s ≤ exp t := by
  rw [Real.rpow_def_of_pos hL, ← exp_log hD, ← exp_add]
  exact exp_le_exp.2 (by linarith)

lemma numeric_raw (K : ℕ) (hK : 1 ≤ K) (L X Y C A Z T : ℝ) (hL : 1 ≤ L) (hX : 0 < X)
    (hY : 0 < Y) (_hZ : 0 ≤ Z) (hZX : Z ≤ 4 * X / Y) (_hT0 : 0 ≤ T) (hTX : T ≤ X / Y)
    (hlogT : 0 ≤ 1 + log T) (hlogT2 : 1 + log T ≤ 2 * L)
    (hE : log (5120 * K ^ 2) + (4 * C + 3 + A) * log L ≤ L ^ (0.1 : ℝ)) :
    32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
      (4 * (Z + T) * (1 + log T) ^ 3)) ≤ 1 * (X * Y * L ^ (-A)) := by
  have hL0 : 0 < L := by linarith
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hZT : Z + T ≤ 5 * X / Y := by
    have : 4 * X / Y + X / Y = 5 * X / Y := by ring
    linarith
  have h3 : (1 + log T) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hlogT hlogT2 3
  have hcomb := rpow_combine hL0 (5120 * K ^ 2) (by positivity) (4 * C + 3 + A) _ hE
  have hpow : (L ^ C) ^ 4 * L ^ 3 * L ^ A = L ^ (4 * C + 3 + A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 3,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num; ring_nf
  have hLA : L ^ (-A) * L ^ A = 1 := by
    rw [← Real.rpow_add hL0]; simp
  have hLAp : 0 < L ^ A := by positivity
  have hP : 0 < exp (L ^ (0.1 : ℝ)) := exp_pos _
  have hLC : 0 ≤ (L ^ C) ^ 4 := by positivity
  calc 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
        (4 * (Z + T) * (1 + log T) ^ 3))
      ≤ 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 *
        (4 * (5 * X / Y) * (2 * L) ^ 3)) := by gcongr
    _ = (5120 * K ^ 2 * ((L ^ C) ^ 4 * L ^ 3 * L ^ A)) / exp (L ^ (0.1 : ℝ)) *
          (X * Y * L ^ (-A)) := by
        field_simp
        rw [show L ^ (-A) = (L ^ A)⁻¹ by rw [Real.rpow_neg hL0.le]]
        field_simp
        ring
    _ ≤ 1 * (X * Y * L ^ (-A)) := by
        gcongr
        rw [div_le_one hP, hpow]
        exact hcomb

lemma numeric_major (K : ℕ) (hK : 1 ≤ K) (L X Y C A A₀ μ N : ℝ) (hL : 1 ≤ L) (hX : 0 < X)
    (hY : 0 < Y) (_hμ0 : 0 ≤ μ) (hμ : μ ≤ 4 * L ^ (3 * A₀) / Y) (hN0 : 0 ≤ N) (hN : N ≤ 4 * X)
    (hlogN : 0 ≤ 1 + log N) (hlogN2 : 1 + log N ≤ 2 * L)
    (hE : log (40960 * K ^ 2) + (4 * C + 3 * A₀ + 3 + A) * log L ≤ L ^ (0.1 : ℝ)) :
    32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * μ *
      (10 * N * (1 + log N) ^ 3)) ≤ 1 * (X * Y * L ^ (-A)) := by
  have hL0 : 0 < L := by linarith
  have h3 : (1 + log N) ^ 3 ≤ (2 * L) ^ 3 := pow_le_pow_left₀ hlogN hlogN2 3
  have hcomb := rpow_combine hL0 (40960 * K ^ 2) (by positivity) (4 * C + 3 * A₀ + 3 + A) _ hE
  have hpow : (L ^ C) ^ 4 * L ^ (3 * A₀) * L ^ 3 * L ^ A = L ^ (4 * C + 3 * A₀ + 3 + A) := by
    rw [← Real.rpow_natCast (L ^ C), ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 3,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    norm_num; ring_nf
  have hP : 0 < exp (L ^ (0.1 : ℝ)) := exp_pos _
  have hLAp : 0 < L ^ A := by positivity
  calc 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * μ *
        (10 * N * (1 + log N) ^ 3))
      ≤ 32 * K ^ 2 * Y ^ 2 / exp (L ^ (0.1 : ℝ)) * ((L ^ C) ^ 4 * (4 * L ^ (3 * A₀) / Y) *
        (10 * (4 * X) * (2 * L) ^ 3)) := by gcongr
    _ = (40960 * K ^ 2 * ((L ^ C) ^ 4 * L ^ (3 * A₀) * L ^ 3 * L ^ A)) /
          exp (L ^ (0.1 : ℝ)) * (X * Y * L ^ (-A)) := by
        field_simp
        rw [show L ^ (-A) = (L ^ A)⁻¹ by rw [Real.rpow_neg hL0.le]]
        field_simp
        ring
    _ ≤ 1 * (X * Y * L ^ (-A)) := by
        gcongr
        rw [div_le_one hP, hpow]
        exact hcomb


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D5, the pairing from the moment ([21] §3.3, (3.20)), for the operator model

The concrete inputs to `norm_qform_le_blocks`: `A` only connects slope blocks at distance `≤ 12`,
a slope block of length `H/U²` holds `≤ 17(512H + 1)` primitive positions, `f` depends only on the
position, `|f| ≤ L^{2C}`, and `σ ∑ |f|² ≤ 32 U V L^{4C}` ((3.18)). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section Geometry

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

lemma mem_posBox_of_state (s : PhysState x a J U V) : s.1.1 ∈ posBox U V :=
  (mem_product.1 (mem_filter.1 s.2).1).1

lemma state_pos_bounds (hU : 0 < U) (hV : 0 < V) (s : PhysState x a J U V) :
    U ≤ s.1.1.1 ∧ (s.1.1.1 : ℝ) ≤ 16 * U ∧ Nat.Coprime s.1.1.1 s.1.1.2 ∧
      V ≤ s.1.1.2 ∧ (s.1.1.2 : ℝ) ≤ 2 * V := by
  have h := mem_posBox_of_state s
  simp only [posBox, mem_filter, mem_product, mem_Icc] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := h
  exact ⟨(Nat.le_ceil U).trans (by exact_mod_cast h1),
    (Nat.cast_le.2 h2).trans (Nat.floor_le (by linarith)), h5,
    (Nat.le_ceil V).trans (by exact_mod_cast h3), (Nat.cast_le.2 h4).trans (Nat.floor_le (by linarith))⟩

/-- A nonzero entry of the row operation has `|det(P, Q)| < (5Y + 1) · 2d₀`. -/
lemma rowOp_ne_zero {A₀ Y : ℝ} {d₀ : ℕ} {s s' : PhysState x a J U V}
    (h : rowOp x a A₀ Y J d₀ U V s s' ≠ 0) :
    |((s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1 : ℤ)| < (5 * Y + 1) * (2 * d₀) ∧
      d₀ ≤ padProd s.1.2 ∧ dyadicBump ((lastProd s.1.2 : ℝ) / Y) ≠ 0 := by
  unfold rowOp at h
  split_ifs at h with hc
  · obtain ⟨-, -, hd1, hd2⟩ := hc
    set det : ℤ := (s.1.1.1 : ℤ) * s'.1.1.2 - (s.1.1.2 : ℤ) * s'.1.1.1
    set D := padProd s.1.2
    have hk := (mul_ne_zero_iff.1 h).2
    have hr := Complex.ofReal_ne_zero.1 (mul_ne_zero_iff.1 h).1
    have hψ : arcCutoff (((det / (D : ℤ) : ℤ) : ℝ) / Y) ≠ 0 := by
      intro h0; apply hk; unfold minorKernel; rw [h0]; simp
    have ht : |(((det / (D : ℤ) : ℤ) : ℝ) / Y)| < 5 := by
      by_contra hge
      have := abs_arcCutoff_le (((det / (D : ℤ) : ℤ) : ℝ) / Y)
      rw [if_neg hge] at this
      exact hψ (abs_nonpos_iff.1 this)
    have hD0 : (0 : ℤ) < D := by
      have : 0 < d₀ ∨ d₀ = 0 := (Nat.eq_zero_or_pos d₀).symm
      rcases this with h0 | h0
      · exact_mod_cast lt_of_lt_of_le h0 hd1
      · omega
    have hη2 : dyadicBump ((lastProd s.1.2 : ℝ) / Y) ≠ 0 :=
      (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 (mul_ne_zero_iff.1 hr).1).1).2
    have hY : 0 < Y := by
      by_contra hY; push Not at hY
      apply hη2
      apply dyadicBump_eq_zero_of_le_one
      exact (div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hY).trans zero_le_one
    refine ⟨?_, hd1, hη2⟩
    have hq := Int.mul_ediv_add_emod det D
    have hr0 := Int.emod_nonneg det hD0.ne'
    have hr1 := Int.emod_lt_of_pos det hD0
    rw [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at ht
    have hDr : (D : ℝ) < 2 * d₀ := by exact_mod_cast hd2
    have hdet : (det : ℝ) = D * ((det / (D : ℤ) : ℤ) : ℝ) + ((det % D : ℤ) : ℝ) := by
      exact_mod_cast hq.symm
    have hr0' : (0 : ℝ) ≤ ((det % D : ℤ) : ℝ) := by exact_mod_cast hr0
    have hr1' : ((det % D : ℤ) : ℝ) < D := by exact_mod_cast hr1
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hD0
    have habs : |(det : ℝ)| ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := by
      rw [hdet]
      calc |(D : ℝ) * ((det / (D : ℤ) : ℤ) : ℝ) + ((det % D : ℤ) : ℝ)|
          ≤ |(D : ℝ) * ((det / (D : ℤ) : ℤ) : ℝ)| + |((det % D : ℤ) : ℝ)| := abs_add_le _ _
        _ ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := by
            rw [abs_mul, abs_of_pos hDpos, abs_of_nonneg hr0']; linarith
    rw [Int.cast_abs]
    calc |(det : ℝ)| ≤ D * |((det / (D : ℤ) : ℤ) : ℝ)| + D := habs
      _ ≤ D * (5 * Y) + D := by gcongr
      _ = D * (5 * Y + 1) := by ring
      _ < 2 * d₀ * (5 * Y + 1) := by gcongr
      _ = (5 * Y + 1) * (2 * d₀) := by ring
  · exact absurd rfl h

lemma slotSym_ne_zero {s s' : PhysState x a J U V} (h : slotSym x a J U V s s' ≠ 0) :
    s.1.1 = s'.1.1 := by
  unfold slotSym at h
  split_ifs at h with hc
  · exact hc.1
  · exact absurd rfl h

end Geometry

/-! ## Slope blocks -/

/-! ## The endpoint norm (3.18) -/

section Norm

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

/-- Disjoint groups: entries of a list of a state are pairwise distinct primes, so their product
divides `P₁`. -/
lemma listProd_dvd_of_disjoint {J : ℕ} {U V : ℝ}
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (s : PhysState x a J U V) : listProd s.1.2 ∣ s.1.1.1 := by
  have hs := mem_filter.1 s.2
  obtain ⟨hmem, hinj, hdvd⟩ := hs
  have hcand := (mem_product.1 hmem).2
  have hgrp : ∀ i j, s.1.2 i j ∈ primeGroup x (a i) := fun i j =>
    Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hcand i) j
  have hprime : ∀ i j, (s.1.2 i j).Prime := fun i j => by
    have := hgrp i j; unfold primeGroup at this; exact (mem_filter.1 this).2.1
  have hne : ∀ q q' : Fin K × Fin (J + 1), q ≠ q' → s.1.2 q.1 q.2 ≠ s.1.2 q'.1 q'.2 := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hq heq
    by_cases hi : i = i'
    · subst hi
      have : j = j' := hinj i heq
      exact hq (by rw [this])
    · exact Finset.disjoint_left.1 (hdisj i i' hi) (hgrp i j) (heq ▸ hgrp i' j')
  have hZ : (∏ q : Fin K × Fin (J + 1), ((s.1.2 q.1 q.2 : ℕ) : ℤ)) ∣ (s.1.1.1 : ℤ) := by
    refine Fintype.prod_dvd_of_coprime (fun q q' hqq => ?_) fun q => ?_
    · simp only [Function.onFun]
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_natCast_natCast]
      exact (Nat.coprime_primes (hprime q.1 q.2) (hprime q'.1 q'.2)).2 (hne q q' hqq)
    · exact_mod_cast hdvd q.1 q.2
  have : ((listProd s.1.2 : ℕ) : ℤ) ∣ (s.1.1.1 : ℤ) := by
    unfold listProd; push_cast
    have e := Fintype.prod_prod_type' (fun (i : Fin K) (j : Fin (J + 1)) => ((s.1.2 i j : ℕ) : ℤ))
    rw [e] at hZ
    exact hZ
  exact_mod_cast this

end Norm


/-! ## D5 at one `x` -/


/-! ## Large-`x` inputs and D5 -/

/-- For large `x` the prime groups are pairwise disjoint. -/
lemma eventually_disjoint_groups {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a)
    (_hpos : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup hp).2
    have h2 := (le_of_mem_primeGroup hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D8bc, the pad lift ([21] §4.9, (4.58)–(4.63))

The dyadic sum of the unprojected pairings `2^{-k} ⟨f, S T S f⟩_σ` reproduces `Q^min` up to the pad
configurations that collide. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section GroupPart

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

lemma prime_of_mem_groupPrimes {p : ℕ} (hp : p ∈ groupPrimes x a) : p.Prime := by
  unfold groupPrimes at hp
  obtain ⟨i, -, hi⟩ := mem_biUnion.1 hp
  unfold primeGroup at hi
  exact (mem_filter.1 hi).2.1

lemma mem_groupPrimes_of {i : Fin K} {p : ℕ} (hp : p ∈ primeGroup x (a i)) :
    p ∈ groupPrimes x a :=
  mem_biUnion.2 ⟨i, mem_univ _, hp⟩

lemma groupPart_mul {u v : ℕ} (hu : u ≠ 0) (hv : v ≠ 0) :
    groupPart x a (u * v) = groupPart x a u * groupPart x a v := by
  unfold groupPart
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun p _ => ?_
  rw [Nat.factorization_mul hu hv, Finsupp.add_apply, pow_add]

lemma groupPart_eq_one_of {m : ℕ} (h : ∀ p ∈ groupPrimes x a, ¬ p ∣ m) :
    groupPart x a m = 1 := by
  unfold groupPart
  refine prod_eq_one fun p hp => ?_
  rw [Nat.factorization_eq_zero_of_not_dvd (h p hp), pow_zero]

lemma dvd_groupPart_of {m p : ℕ} (hm : m ≠ 0) (hp : p ∈ groupPrimes x a) (hpm : p ∣ m) :
    p ∣ groupPart x a m := by
  unfold groupPart
  have hpr := prime_of_mem_groupPrimes hp
  have hv : 0 < m.factorization p := hpr.factorization_pos_of_dvd hm hpm
  exact (dvd_pow_self p hv.ne').trans (dvd_prod_of_mem _ hp)

lemma groupPart_ne_one_of {m p : ℕ} (hm : m ≠ 0) (hp : p ∈ groupPrimes x a) (hpm : p ∣ m) :
    groupPart x a m ≠ 1 := by
  intro h
  have := dvd_groupPart_of hm hp hpm
  rw [h] at this
  exact (prime_of_mem_groupPrimes hp).one_lt.ne' (Nat.dvd_one.1 this)

lemma factorization_prod_primes {S : Finset ℕ} (hpr : ∀ p ∈ S, p.Prime) (q : ℕ) :
    (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
  rw [Nat.factorization_prod (fun p hp => (hpr p hp).ne_zero), Finsupp.finsetSum_apply]
  rw [sum_congr rfl (fun p hp => by
    rw [(hpr p hp).factorization, Finsupp.single_apply] :
    ∀ p ∈ S, p.factorization q = if p = q then 1 else 0)]
  rw [sum_ite_eq']

lemma squarefree_prod_primes {S : Finset ℕ} (hpr : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  rw [Nat.squarefree_iff_factorization_le_one (prod_ne_zero_iff.2 fun p hp => (hpr p hp).ne_zero)]
  intro q
  rw [factorization_prod_primes hpr]
  split_ifs <;> norm_num

lemma groupPart_prod {S : Finset ℕ} (hS : S ⊆ groupPrimes x a) :
    groupPart x a (∏ p ∈ S, p) = ∏ p ∈ S, p := by
  unfold groupPart
  have hpr : ∀ p ∈ S, p.Prime := fun p hp => prime_of_mem_groupPrimes (hS hp)
  have hfac : ∀ q, (∏ p ∈ S, p).factorization q = if q ∈ S then 1 else 0 := by
    intro q
    rw [Nat.factorization_prod (fun p hp => (hpr p hp).ne_zero), Finsupp.finsetSum_apply]
    rw [sum_congr rfl (fun p hp => by
      rw [(hpr p hp).factorization, Finsupp.single_apply] :
      ∀ p ∈ S, p.factorization q = if p = q then 1 else 0)]
    rw [sum_ite_eq']
  simp_rw [hfac]
  rw [prod_congr rfl (fun q _ => by split_ifs <;> simp :
    ∀ q ∈ groupPrimes x a, (q ^ (if q ∈ S then 1 else 0)) = if q ∈ S then q else 1)]
  rw [prod_ite_mem, inter_eq_right.2 hS]

end GroupPart

/-! ## Lists of a state -/

section Lists

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

/-- The structural hypotheses on a list: entries in their groups, injective in each group,
groups pairwise disjoint. -/
structure ListOK (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (ℓ : Fin K → Fin (J + 1) → ℕ) : Prop where
  grp : ∀ i j, ℓ i j ∈ primeGroup x (a i)
  inj : ∀ i, Function.Injective (ℓ i)
  disj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))

/-- The set of entries of a list. -/
def entries (ℓ : Fin K → Fin (J + 1) → ℕ) : Finset ℕ :=
  univ.image fun q : Fin K × Fin (J + 1) => ℓ q.1 q.2

lemma ListOK.prime {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) (i j) :
    (ℓ i j).Prime := by
  have := h.grp i j; unfold primeGroup at this; exact (mem_filter.1 this).2.1

lemma ListOK.pair_inj {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    Function.Injective fun q : Fin K × Fin (J + 1) => ℓ q.1 q.2 := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ heq
  simp only at heq
  by_cases hi : i = i'
  · subst hi; rw [h.inj i heq]
  · exact absurd (h.grp i' j') (Finset.disjoint_left.1 (h.disj i i' hi) (heq ▸ h.grp i j) |> fun h' =>
      by rw [← heq] at *; exact h')

lemma ListOK.listProd_eq {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    listProd ℓ = ∏ p ∈ entries ℓ, p := by
  unfold listProd entries
  rw [prod_image (fun q _ q' _ hq => h.pair_inj hq), ← Fintype.prod_prod_type']

lemma ListOK.entries_sub {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    entries ℓ ⊆ groupPrimes x a := by
  intro p hp
  obtain ⟨⟨i, j⟩, -, rfl⟩ := mem_image.1 hp
  exact mem_groupPrimes_of (h.grp i j)

lemma ListOK.entries_prime {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    ∀ p ∈ entries ℓ, p.Prime := by
  intro p hp
  obtain ⟨⟨i, j⟩, -, rfl⟩ := mem_image.1 hp
  exact h.prime i j

lemma ListOK.listProd_pos {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    0 < listProd ℓ := by
  rw [h.listProd_eq]; exact prod_pos fun p hp => (h.entries_prime p hp).pos

lemma ListOK.groupPart_listProd {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) :
    groupPart x a (listProd ℓ) = listProd ℓ := by
  rw [h.listProd_eq]; exact groupPart_prod h.entries_sub

/-- The group-`i` primes dividing `G m` (with `G` the list product and `m` free of group primes) are
exactly the group-`i` entries. -/
lemma ListOK.filter_dvd {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) {m : ℕ}
    (hm : ∀ p ∈ groupPrimes x a, ¬ p ∣ m) (i : Fin K) :
    (primeGroup x (a i)).filter (· ∣ listProd ℓ * m) = univ.image (ℓ i) := by
  ext p
  simp only [mem_filter, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨hpi, hpd⟩
    have hpr : p.Prime := by unfold primeGroup at hpi; exact (mem_filter.1 hpi).2.1
    rcases (Nat.Prime.dvd_mul hpr).1 hpd with hG | hM
    · rw [h.listProd_eq] at hG
      obtain ⟨q, hq, hpq⟩ := (Nat.prime_iff.1 hpr).dvd_finsetProd_iff _ |>.1 hG
      have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hpr (h.entries_prime q hq)).1 hpq
      obtain ⟨⟨i', j⟩, -, hq'⟩ := mem_image.1 hq
      subst hpq'
      by_cases hii : i' = i
      · subst hii; exact ⟨j, hq'⟩
      · exfalso
        exact Finset.disjoint_left.1 (h.disj i' i hii) (hq' ▸ h.grp i' j) hpi
    · exact absurd hM (hm p (mem_groupPrimes_of hpi))
  · rintro ⟨j, rfl⟩
    refine ⟨h.grp i j, Dvd.dvd.mul_right ?_ m⟩
    unfold listProd
    exact (dvd_prod_of_mem (fun j => ℓ i j) (mem_univ j)).trans
      (dvd_prod_of_mem (fun i => ∏ j, ℓ i j) (mem_univ i))

end Lists

/-! ## The endpoint vector at a constructed position -/

section Endpoint

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

open Classical in
/-- The endpoint vector as a function of the position. -/
noncomputable def endPos (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (α β : ℕ → ℂ)
    (P : ℕ × ℕ) : ℂ :=
  if (∀ i, groupOmega x (a i) P.1 = J + 1) ∧ Squarefree (groupPart x a P.1) then
    (starRingEnd ℂ) (α (P.1 / groupPart x a P.1)) * β P.2 else 0

lemma endpointVec_eq {U V : ℝ} (α β : ℕ → ℂ) (s : PhysState x a J U V) :
    endpointVec x a J U V α β s = endPos x a J α β s.1.1 := rfl

/-- `f((G m, s), ℓ) = 1_{groupPart m = 1} conj(α_m) β_s` for the list product `G`. -/
lemma endPos_listProd_mul {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) (α β : ℕ → ℂ)
    {m : ℕ} (hm : m ≠ 0) (s : ℕ) :
    endPos x a J α β (listProd ℓ * m, s) =
      if groupPart x a m = 1 then (starRingEnd ℂ) (α m) * β s else 0 := by
  classical
  have hG := h.listProd_pos
  have hgp : groupPart x a (listProd ℓ * m) = listProd ℓ * groupPart x a m := by
    rw [groupPart_mul hG.ne' hm, h.groupPart_listProd]
  by_cases h1 : groupPart x a m = 1
  · have hno : ∀ p ∈ groupPrimes x a, ¬ p ∣ m := fun p hp hpm => groupPart_ne_one_of hm hp hpm h1
    have hω : ∀ i, groupOmega x (a i) (listProd ℓ * m) = J + 1 := by
      intro i
      unfold groupOmega
      rw [h.filter_dvd hno i, card_image_of_injective _ (h.inj i), card_univ, Fintype.card_fin]
    have hsq : Squarefree (groupPart x a (listProd ℓ * m)) := by
      rw [hgp, h1, mul_one, h.listProd_eq]; exact squarefree_prod_primes h.entries_prime
    unfold endPos
    rw [if_pos ⟨hω, hsq⟩, if_pos h1]
    simp only
    rw [hgp, h1, mul_one, Nat.mul_div_cancel_left m hG]
  · rw [if_neg h1]
    unfold endPos
    rw [if_neg]
    rintro ⟨hω, hsq⟩
    obtain ⟨p, hp, hpm⟩ : ∃ p ∈ groupPrimes x a, p ∣ m := by
      by_contra hc; push Not at hc; exact h1 (groupPart_eq_one_of hc)
    have hpr := prime_of_mem_groupPrimes hp
    by_cases hpE : p ∈ entries ℓ
    · have hpG : p ∣ listProd ℓ := by rw [h.listProd_eq]; exact dvd_prod_of_mem _ hpE
      have hpg : p ∣ groupPart x a m := dvd_groupPart_of hm hp hpm
      have : p * p ∣ groupPart x a (listProd ℓ * m) := by rw [hgp]; exact mul_dvd_mul hpG hpg
      exact hpr.not_isUnit (hsq p this)
    · obtain ⟨i, -, hpi⟩ := mem_biUnion.1 hp
      have hsub : insert p (univ.image (ℓ i)) ⊆
          (primeGroup x (a i)).filter (· ∣ listProd ℓ * m) := by
        intro q hq
        rw [mem_insert] at hq
        rw [mem_filter]
        rcases hq with rfl | hq
        · exact ⟨hpi, Dvd.dvd.mul_left hpm _⟩
        · obtain ⟨j, -, rfl⟩ := mem_image.1 hq
          refine ⟨h.grp i j, Dvd.dvd.mul_right ?_ m⟩
          rw [h.listProd_eq]
          exact dvd_prod_of_mem _ (mem_image.2 ⟨(i, j), mem_univ _, rfl⟩)
      have hnot : p ∉ univ.image (ℓ i) := by
        intro hq
        obtain ⟨j, -, rfl⟩ := mem_image.1 hq
        exact hpE (mem_image.2 ⟨(i, j), mem_univ _, rfl⟩)
      have hc := card_le_card hsub
      rw [card_insert_of_notMem hnot, card_image_of_injective _ (h.inj i), card_univ,
        Fintype.card_fin] at hc
      have := hω i
      unfold groupOmega at this
      simp only at this
      omega

end Endpoint

/-! ## Step A: `⟨f, S T S f⟩ = ⟨f, T f⟩` -/

section SlotSym

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ} {U V : ℝ}

/-- The orbit relation of the slot permutations. -/
def orbRel (s t : PhysState x a J U V) : Prop :=
  t.1.1 = s.1.1 ∧ ∀ i, Set.range (t.1.2 i) = Set.range (s.1.2 i)

lemma orbRel_symm {s t : PhysState x a J U V} (h : orbRel s t) : orbRel t s :=
  ⟨h.1.symm, fun i => (h.2 i).symm⟩

lemma orbRel_trans {s t u : PhysState x a J U V} (h1 : orbRel s t) (h2 : orbRel t u) :
    orbRel s u :=
  ⟨h2.1.trans h1.1, fun i => (h2.2 i).trans (h1.2 i)⟩

open Classical in
lemma slotSym_apply (s s' : PhysState x a J U V) :
    slotSym x a J U V s s' = if orbRel s s' then
      ((univ.filter fun t => orbRel s t).card : ℂ)⁻¹ else 0 := by
  unfold slotSym orbRel
  by_cases h : s'.1.1 = s.1.1 ∧ ∀ i, Set.range (s'.1.2 i) = Set.range (s.1.2 i)
  · rw [if_pos ⟨h.1.symm, h.2⟩, if_pos h]; congr 2; convert rfl
  · rw [if_neg (fun h' => h ⟨h'.1.symm, h'.2⟩), if_neg h]

open Classical in
lemma orbit_card_eq {s s' : PhysState x a J U V} (h : orbRel s s') :
    (univ.filter fun t => orbRel s t).card = (univ.filter fun t => orbRel s' t).card := by
  congr 1; ext t; simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun ht => orbRel_trans (orbRel_symm h) ht, fun ht => orbRel_trans h ht⟩

open Classical in
lemma slotSym_row_sum (s : PhysState x a J U V) : ∑ s', slotSym x a J U V s s' = 1 := by
  simp only [slotSym_apply]
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hpos : 0 < (univ.filter fun t => orbRel s t).card :=
    card_pos.2 ⟨s, mem_filter.2 ⟨mem_univ _, rfl, fun i => rfl⟩⟩
  have : ((univ.filter fun t => orbRel s t).card : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  field_simp

open Classical in
lemma slotSym_col_sum (s' : PhysState x a J U V) : ∑ s, slotSym x a J U V s s' = 1 := by
  have : ∀ s, slotSym x a J U V s s' = slotSym x a J U V s' s := by
    intro s
    simp only [slotSym_apply]
    by_cases h : orbRel s s'
    · rw [if_pos h, if_pos (orbRel_symm h), orbit_card_eq h]
    · rw [if_neg h, if_neg (fun h' => h (orbRel_symm h'))]
  simp only [this]
  exact slotSym_row_sum s'

lemma endpoint_eq_of_slotSym (α β : ℕ → ℂ) {s s' : PhysState x a J U V}
    (h : slotSym x a J U V s s' ≠ 0) :
    endpointVec x a J U V α β s = endpointVec x a J U V α β s' := by
  rw [endpointVec_eq, endpointVec_eq, slotSym_ne_zero h]

lemma slotSym_mulVec (α β : ℕ → ℂ) :
    (slotSym x a J U V).mulVec (endpointVec x a J U V α β) = endpointVec x a J U V α β := by
  funext s
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ s', slotSym x a J U V s s' * endpointVec x a J U V α β s'
      = ∑ s', slotSym x a J U V s s' * endpointVec x a J U V α β s := by
        refine sum_congr rfl fun s' _ => ?_
        by_cases h : slotSym x a J U V s s' = 0
        · rw [h, zero_mul, zero_mul]
        · rw [endpoint_eq_of_slotSym α β h]
    _ = endpointVec x a J U V α β s := by rw [← sum_mul, slotSym_row_sum, one_mul]

lemma vecMul_slotSym (α β : ℕ → ℂ) :
    Matrix.vecMul (fun s => (starRingEnd ℂ) (endpointVec x a J U V α β s)) (slotSym x a J U V) =
      fun s => (starRingEnd ℂ) (endpointVec x a J U V α β s) := by
  funext s'
  simp only [Matrix.vecMul, dotProduct]
  calc ∑ s, (starRingEnd ℂ) (endpointVec x a J U V α β s) * slotSym x a J U V s s'
      = ∑ s, (starRingEnd ℂ) (endpointVec x a J U V α β s') * slotSym x a J U V s s' := by
        refine sum_congr rfl fun s _ => ?_
        by_cases h : slotSym x a J U V s s' = 0
        · rw [h, mul_zero, mul_zero]
        · rw [endpoint_eq_of_slotSym α β h]
    _ = (starRingEnd ℂ) (endpointVec x a J U V α β s') := by
        rw [← mul_sum, slotSym_col_sum, mul_one]

lemma opPairing_eq_dot (α β : ℕ → ℂ) (B : Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ) :
    opPairing x a J U V α β B = (stateNorm x a J : ℂ) *
      dotProduct (fun s => (starRingEnd ℂ) (endpointVec x a J U V α β s))
        (B.mulVec (endpointVec x a J U V α β)) := by
  unfold opPairing
  congr 1
  simp only [dotProduct, Matrix.mulVec, mul_sum]
  refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => by ring

/-- The pairing with `S M S` equals the pairing with `M`. -/
theorem opPairing_slotSym (α β : ℕ → ℂ) (M : Matrix (PhysState x a J U V) (PhysState x a J U V) ℂ) :
    opPairing x a J U V α β (slotSym x a J U V * M * slotSym x a J U V) =
      opPairing x a J U V α β M := by
  rw [opPairing_eq_dot, opPairing_eq_dot, ← Matrix.mulVec_mulVec, slotSym_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, vecMul_slotSym]

end SlotSym

/-! ## Step B: configurations and state pairs -/

section Configs

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

/-- A configuration `(pads, p, q, m, n, r, s)`: pads, target new labels `p` (product `a`), source
last labels `q` (product `b`), and the four coefficient variables. -/
abbrev Cfg (K J : ℕ) := (Fin K → Fin J → ℕ) × (Fin K → ℕ) × (Fin K → ℕ) × ℕ × ℕ × ℕ × ℕ

/-- The list with the given pads and last labels. -/
def mkList {K J : ℕ} (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) : Fin K → Fin (J + 1) → ℕ :=
  fun i => Fin.lastCases (last i) (fun j => pads i j)

/-- The pad product. -/
def padsProd {K J : ℕ} (pads : Fin K → Fin J → ℕ) : ℕ := ∏ i, ∏ j, pads i j

/-- The harmonic weight `∏_{i,j} μᵢ(pad_{ij})`. -/
noncomputable def padsWeight (x : ℝ) {K J : ℕ} (a : Fin K → ℝ) (pads : Fin K → Fin J → ℕ) : ℝ :=
  ∏ i, ∏ j, 1 / ((pads i j : ℝ) * groupReciprocalSum x (a i))

/-- The pad tuples. -/
noncomputable def padSet (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) : Finset (Fin K → Fin J → ℕ) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ : Fin J => primeGroup x (a i)

/-- The configurations. -/
noncomputable def cfgSet (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (Hm Hn : ℝ) : Finset (Cfg K J) :=
  padSet x a J ×ˢ (labelTuples x a ×ˢ (labelTuples x a ×ˢ (range (⌊2 * Hm⌋₊ + 1) ×ˢ
    (range (⌊2 * Hn⌋₊ + 1) ×ˢ (range (⌊2 * Hm⌋₊ + 1) ×ˢ range (⌊2 * Hn⌋₊ + 1))))))

/-- The pads are distinct in each group and avoid both unshared labels, which differ. -/
def PadsOK {K J : ℕ} (pads : Fin K → Fin J → ℕ) (p q : Fin K → ℕ) : Prop :=
  (∀ i, Function.Injective (pads i)) ∧ (∀ i j, pads i j ≠ p i ∧ pads i j ≠ q i) ∧ ∀ i, p i ≠ q i

/-- The configuration term `∏Vᵢ⁻² ∏μ(pads) η(a/Y)η(b/Y) α_m ᾱ_r β_n β̄_s H_𝔪(bmn − ars; a, b)`. -/
noncomputable def cfgTerm (x : ℝ) {K J : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (α β : ℕ → ℂ)
    (c : Cfg K J) : ℂ :=
  (squareNorm x a : ℂ) * (padsWeight x a c.1 : ℂ) *
    sqWeight Y (∏ i, c.2.1 i) (∏ i, c.2.2.1 i) c.2.2.2.1 c.2.2.2.2.1 c.2.2.2.2.2.1 c.2.2.2.2.2.2 α β *
    minorKernel x A₀ Y (sqDet (∏ i, c.2.1 i) (∏ i, c.2.2.1 i) c.2.2.2.1 c.2.2.2.2.1
      c.2.2.2.2.2.1 c.2.2.2.2.2.2) (∏ i, c.2.1 i) (∏ i, c.2.2.1 i)

/-- The state pair of a configuration: source `((D b m, s), pads‖q)`, target `((D a r, n), pads‖p)`. -/
def cfgPair {K J : ℕ} (c : Cfg K J) :
    ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) × ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) :=
  (((listProd (mkList c.1 c.2.2.1) * c.2.2.2.1, c.2.2.2.2.2.2), mkList c.1 c.2.2.1),
    ((listProd (mkList c.1 c.2.1) * c.2.2.2.2.2.1, c.2.2.2.2.1), mkList c.1 c.2.1))

open Classical in
/-- The row kernel on ambient pairs (the body of `rowOp`). -/
noncomputable def rowAmb (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J d₀ : ℕ)
    (z z' : (ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) : ℂ :=
  if (∀ i (j : Fin J), z'.2 i j.castSucc = z.2 i j.castSucc) ∧
      (∀ i, z'.2 i (Fin.last J) ∉ Set.range (z.2 i)) ∧
      d₀ ≤ padProd z.2 ∧ padProd z.2 < 2 * d₀ then
    (((∏ i, (groupReciprocalSum x (a i))⁻¹) * ((d₀ : ℝ) / padProd z.2) *
        dyadicBump ((lastProd z.2 : ℝ) / Y) * dyadicBump ((lastProd z'.2 : ℝ) / Y) *
        (1 / 2 : ℝ) ^ (excessOmega x a J z.1.1 + excessOmega x a J z'.1.1) : ℝ) : ℂ) *
      minorKernel x A₀ Y (((z.1.1 : ℤ) * z'.1.2 - (z.1.2 : ℤ) * z'.1.1) / (padProd z.2 : ℤ))
        (lastProd z'.2) (lastProd z.2)
  else 0

lemma rowOp_eq_rowAmb (A₀ Y : ℝ) (d₀ : ℕ) {U V : ℝ} (s s' : PhysState x a J U V) :
    rowOp x a A₀ Y J d₀ U V s s' = rowAmb x a A₀ Y J d₀ s.1 s'.1 := rfl

/-- The ambient pair term of `(2^k)⁻¹ ⟨f, T f⟩_σ`. -/
noncomputable def pairTerm (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (A₀ Y : ℝ) (J k : ℕ) (α β : ℕ → ℂ)
    (z : ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ)) × ((ℕ × ℕ) × (Fin K → Fin (J + 1) → ℕ))) : ℂ :=
  ((2 : ℂ) ^ k)⁻¹ * (stateNorm x a J : ℂ) * (starRingEnd ℂ) (endPos x a J α β z.1.1) *
    rowAmb x a A₀ Y J (2 ^ k) z.1 z.2 * endPos x a J α β z.2.1

lemma dyad_pairing_eq_sum (A₀ Y : ℝ) (k : ℕ) {U V : ℝ} (α β : ℕ → ℂ) :
    ((2 : ℂ) ^ k)⁻¹ * opPairing x a J U V α β (rowOp x a A₀ Y J (2 ^ k) U V) =
      ∑ z ∈ stateSet x a J U V ×ˢ stateSet x a J U V, pairTerm x a A₀ Y J k α β z := by
  calc ((2 : ℂ) ^ k)⁻¹ * opPairing x a J U V α β (rowOp x a A₀ Y J (2 ^ k) U V)
      = ∑ s : PhysState x a J U V, ∑ s' : PhysState x a J U V,
          pairTerm x a A₀ Y J k α β (s.1, s'.1) := by
        unfold opPairing
        simp only [mul_sum]
        refine sum_congr rfl fun s _ => sum_congr rfl fun s' _ => ?_
        simp only [pairTerm, endpointVec_eq, rowOp_eq_rowAmb]
        ring
    _ = ∑ q ∈ stateSet x a J U V, ∑ q' ∈ stateSet x a J U V,
          pairTerm x a A₀ Y J k α β (q, q') := by
        rw [← Finset.sum_coe_sort (stateSet x a J U V)
          (fun q => ∑ q' ∈ stateSet x a J U V, pairTerm x a A₀ Y J k α β (q, q'))]
        refine sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_coe_sort (stateSet x a J U V)
          (fun q' => pairTerm x a A₀ Y J k α β (s.1, q'))]
    _ = _ := (sum_product _ _ _).symm

lemma mkList_castSucc (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) (i : Fin K) (j : Fin J) :
    mkList pads last i j.castSucc = pads i j := by
  simp [mkList]

lemma mkList_last (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) (i : Fin K) :
    mkList pads last i (Fin.last J) = last i := by
  simp [mkList]

lemma padProd_mkList (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) :
    padProd (mkList pads last) = padsProd pads := by
  unfold padProd padsProd; simp only [mkList_castSucc]

lemma lastProd_mkList (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) :
    lastProd (mkList pads last) = ∏ i, last i := by
  unfold lastProd; simp only [mkList_last]

lemma listProd_mkList (pads : Fin K → Fin J → ℕ) (last : Fin K → ℕ) :
    listProd (mkList pads last) = padsProd pads * ∏ i, last i := by
  unfold listProd padsProd
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp only [mkList_castSucc, mkList_last]

lemma mem_range_mkList {pads : Fin K → Fin J → ℕ} {last : Fin K → ℕ} {i : Fin K} {v : ℕ} :
    v ∈ Set.range (mkList pads last i) ↔ v = last i ∨ ∃ j, pads i j = v := by
  constructor
  · rintro ⟨j, rfl⟩
    induction j using Fin.lastCases with
    | last => left; rw [mkList_last]
    | cast j => right; exact ⟨j, (mkList_castSucc _ _ _ _).symm⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last J, mkList_last _ _ _⟩
    · exact ⟨j.castSucc, mkList_castSucc _ _ _ _⟩

lemma mkList_injective {pads : Fin K → Fin J → ℕ} {last : Fin K → ℕ}
    (hinj : ∀ i, Function.Injective (pads i)) (hne : ∀ i j, pads i j ≠ last i) (i : Fin K) :
    Function.Injective (mkList pads last i) := by
  intro j j' h
  induction j using Fin.lastCases with
  | last =>
    induction j' using Fin.lastCases with
    | last => rfl
    | cast j' =>
      rw [mkList_last, mkList_castSucc] at h; exact absurd h.symm (hne i j')
  | cast j =>
    induction j' using Fin.lastCases with
    | last => rw [mkList_last, mkList_castSucc] at h; exact absurd h (hne i j)
    | cast j' => rw [mkList_castSucc, mkList_castSucc] at h; rw [hinj i h]

lemma listOK_mkList {pads : Fin K → Fin J → ℕ} {last : Fin K → ℕ}
    (hpads : pads ∈ padSet x a J) (hlast : last ∈ labelTuples x a)
    (hinj : ∀ i, Function.Injective (pads i)) (hne : ∀ i j, pads i j ≠ last i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j))) :
    ListOK x a J (mkList pads last) := by
  refine ⟨fun i j => ?_, mkList_injective hinj hne, hdisj⟩
  induction j using Fin.lastCases with
  | last => rw [mkList_last]; exact Fintype.mem_piFinset.1 hlast i
  | cast j =>
    rw [mkList_castSucc]
    exact Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hpads i) j

end Configs

/-! ## The value identity -/

section Value

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

lemma norm_identity (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (pads : Fin K → Fin J → ℕ)
    (hpos : ∀ i j, 0 < pads i j) :
    stateNorm x a J * (∏ i, (groupReciprocalSum x (a i))⁻¹) / (padsProd pads : ℝ) =
      squareNorm x a * padsWeight x a pads := by
  unfold stateNorm squareNorm padsWeight padsProd
  push_cast
  rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
  refine prod_congr rfl fun i _ => ?_
  have hV := (hVpos i).ne'
  have hp : ∀ j, (pads i j : ℝ) ≠ 0 := fun j => by exact_mod_cast (hpos i j).ne'
  rw [show (∏ j, 1 / ((pads i j : ℝ) * groupReciprocalSum x (a i))) =
      (groupReciprocalSum x (a i))⁻¹ ^ J / ∏ j, (pads i j : ℝ) by
    rw [prod_div_distrib, prod_const_one, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
    field_simp
    rw [← mul_pow, mul_one_div_cancel hV, one_pow]]
  have hP : (∏ j, (pads i j : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun j _ => hp j
  field_simp
  rw [pow_succ]
  field_simp

lemma markOmega_listProd_mul {ℓ : Fin K → Fin (J + 1) → ℕ} (h : ListOK x a J ℓ) {m : ℕ}
    (hm : ∀ p ∈ groupPrimes x a, ¬ p ∣ m) :
    excessOmega x a J (listProd ℓ * m) = 0 := by
  unfold excessOmega markOmega
  have : ∀ i, groupOmega x (a i) (listProd ℓ * m) = J + 1 := by
    intro i; unfold groupOmega
    rw [h.filter_dvd hm i, card_image_of_injective _ (h.inj i), card_univ, Fintype.card_fin]
  simp only [this, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.sub_self]

lemma endPos_zero_left (α β : ℕ → ℂ) (hα0 : α 0 = 0) (s : ℕ) :
    endPos x a J α β (0, s) = 0 := by
  unfold endPos; split_ifs <;> simp [Nat.zero_div, hα0]

/-- **The value identity**: on a configuration with good pads in dyad `k`, the ambient pair term
of its state pair equals the configuration term. -/
theorem pairTerm_cfgPair (A₀ Y : ℝ) (k : ℕ) (α β : ℕ → ℂ) {Hm Hn : ℝ} {c : Cfg K J}
    (hc : c ∈ cfgSet x a J Hm Hn) (hok : PadsOK c.1 c.2.1 c.2.2.1)
    (hdy : 2 ^ k ≤ padsProd c.1 ∧ padsProd c.1 < 2 * 2 ^ k)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (hα0 : α 0 = 0)
    (hαg : ∀ m, α m ≠ 0 → ∀ p ∈ groupPrimes x a, ¬ p ∣ m) :
    pairTerm x a A₀ Y J k α β (cfgPair c) = cfgTerm x a A₀ Y α β c := by
  obtain ⟨pads, p, q, m, n, r, s⟩ := c
  simp only [cfgSet, mem_product] at hc
  obtain ⟨hpads, hp, hq, -, -, -, -⟩ := hc
  obtain ⟨hinj, hne, hpq⟩ := hok
  simp only at hdy hinj hne hpq
  have hOKs : ListOK x a J (mkList pads q) :=
    listOK_mkList hpads hq hinj (fun i j => (hne i j).2) hdisj
  have hOKt : ListOK x a J (mkList pads p) :=
    listOK_mkList hpads hp hinj (fun i j => (hne i j).1) hdisj
  have hD : 0 < padsProd pads := by
    have := hOKs.listProd_pos; rw [listProd_mkList] at this; exact Nat.pos_of_mul_pos_right this
  have hcond : (∀ i (j : Fin J), mkList pads p i j.castSucc = mkList pads q i j.castSucc) ∧
      (∀ i, mkList pads p i (Fin.last J) ∉ Set.range (mkList pads q i)) ∧
      2 ^ k ≤ padProd (mkList pads q) ∧ padProd (mkList pads q) < 2 * 2 ^ k := by
    refine ⟨fun i j => by rw [mkList_castSucc, mkList_castSucc], fun i h => ?_, ?_, ?_⟩
    · rw [mkList_last, mem_range_mkList] at h
      rcases h with h | ⟨j, hj⟩
      · exact hpq i h
      · exact (hne i j).1 hj
    · rw [padProd_mkList]; exact hdy.1
    · rw [padProd_mkList]; exact hdy.2
  unfold pairTerm cfgPair rowAmb
  simp only
  rw [if_pos hcond]
  simp only [padProd_mkList, lastProd_mkList]
  -- the coefficient cases
  by_cases hm : α m = 0
  · have hP : endPos x a J α β (listProd (mkList pads q) * m, s) = 0 := by
      by_cases hm0 : m = 0
      · rw [hm0, mul_zero]; exact endPos_zero_left α β hα0 s
      · rw [endPos_listProd_mul hOKs α β hm0]; split_ifs <;> simp [hm]
    unfold cfgTerm sqWeight
    simp [hP, hm]
  by_cases hr : α r = 0
  · have hQ : endPos x a J α β (listProd (mkList pads p) * r, n) = 0 := by
      by_cases hr0 : r = 0
      · rw [hr0, mul_zero]; exact endPos_zero_left α β hα0 n
      · rw [endPos_listProd_mul hOKt α β hr0]; split_ifs <;> simp [hr]
    unfold cfgTerm sqWeight
    simp [hQ, hr]
  have hm0 : m ≠ 0 := by rintro rfl; exact hm hα0
  have hr0 : r ≠ 0 := by rintro rfl; exact hr hα0
  have hgm := groupPart_eq_one_of (x := x) (a := a) (hαg m hm)
  have hgr := groupPart_eq_one_of (x := x) (a := a) (hαg r hr)
  rw [endPos_listProd_mul hOKs α β hm0, endPos_listProd_mul hOKt α β hr0, if_pos hgm, if_pos hgr,
    markOmega_listProd_mul hOKs (hαg m hm), markOmega_listProd_mul hOKt (hαg r hr)]
  have ht : (((listProd (mkList pads q) * m : ℕ) : ℤ) * (n : ℤ) -
      ((s : ℕ) : ℤ) * ((listProd (mkList pads p) * r : ℕ) : ℤ)) / ((padsProd pads : ℕ) : ℤ) =
      sqDet (∏ i, p i) (∏ i, q i) m n r s := by
    rw [listProd_mkList, listProd_mkList]
    unfold sqDet
    have hD' : ((padsProd pads : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
    rw [show (((padsProd pads * ∏ i, q i) * m : ℕ) : ℤ) * (n : ℤ) -
        ((s : ℕ) : ℤ) * (((padsProd pads * ∏ i, p i) * r : ℕ) : ℤ) =
        ((padsProd pads : ℕ) : ℤ) * (((∏ i, q i : ℕ) : ℤ) * m * n - ((∏ i, p i : ℕ) : ℤ) * r * s) by
      push_cast; ring]
    rw [Int.mul_ediv_cancel_left _ hD']
  rw [ht]
  unfold cfgTerm sqWeight
  have hpos : ∀ i j, 0 < pads i j := fun i j =>
    pos_of_mem_primeGroup (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hpads i) j)
  have hid := norm_identity hVpos pads hpos
  have hk : ((2 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hDc : ((padsProd pads : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have key : (stateNorm x a J : ℂ) * ∏ i, ((groupReciprocalSum x (a i) : ℂ))⁻¹ =
      (squareNorm x a : ℂ) * (padsWeight x a pads : ℂ) * ((padsProd pads : ℕ) : ℂ) := by
    have : stateNorm x a J * (∏ i, (groupReciprocalSum x (a i))⁻¹) =
        squareNorm x a * padsWeight x a pads * (padsProd pads : ℝ) := by
      rw [← hid]; field_simp
    have h2 := congrArg (fun t : ℝ => (t : ℂ)) this
    push_cast at h2
    exact h2
  have e2 : ((2 : ℂ) ^ k)⁻¹ * ((2 : ℂ) ^ k / ((padsProd pads : ℕ) : ℂ)) =
      1 / ((padsProd pads : ℕ) : ℂ) := by field_simp
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    pow_zero, add_zero, Complex.ofReal_one, map_mul, Complex.conj_conj]
  push_cast
  set MK := minorKernel x A₀ Y (sqDet (∏ i, p i) (∏ i, q i) m n r s) (∏ i, (p i : ℤ)) (∏ i, (q i : ℤ))
  set ηq := ((dyadicBump ((∏ i, (q i : ℝ)) / Y) : ℝ) : ℂ)
  set ηp := ((dyadicBump ((∏ i, (p i : ℝ)) / Y) : ℝ) : ℂ)
  calc ((2 : ℂ) ^ k)⁻¹ * (stateNorm x a J : ℂ) * (α m * (starRingEnd ℂ) (β s)) *
        ((∏ i, ((groupReciprocalSum x (a i) : ℂ))⁻¹) * ((2 : ℂ) ^ k / ((padsProd pads : ℕ) : ℂ)) *
          ηq * ηp * 1 * MK) * ((starRingEnd ℂ) (α r) * β n)
      = ((stateNorm x a J : ℂ) * ∏ i, ((groupReciprocalSum x (a i) : ℂ))⁻¹) *
          (((2 : ℂ) ^ k)⁻¹ * ((2 : ℂ) ^ k / ((padsProd pads : ℕ) : ℂ))) *
          (ηq * ηp * MK * (α m * (starRingEnd ℂ) (β s)) * ((starRingEnd ℂ) (α r) * β n)) := by ring
    _ = ((squareNorm x a : ℂ) * (padsWeight x a pads : ℂ) * ((padsProd pads : ℕ) : ℂ)) *
          (1 / ((padsProd pads : ℕ) : ℂ)) *
          (ηq * ηp * MK * (α m * (starRingEnd ℂ) (β s)) * ((starRingEnd ℂ) (α r) * β n)) := by
        rw [key, e2]
    _ = (squareNorm x a : ℂ) * (padsWeight x a pads : ℂ) *
          (ηp * ηq * α m * (starRingEnd ℂ) (α r) * β n * (starRingEnd ℂ) (β s)) * MK := by
        field_simp

end Value

/-! ## The bijection -/

section Bijection

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

lemma minorKernel_ne_zero_abs {A₀ Y : ℝ} {t a' b' : ℤ} (hY : 0 < Y)
    (h : minorKernel x A₀ Y t a' b' ≠ 0) : |(t : ℝ)| < 5 * Y := by
  have hψ : arcCutoff ((t : ℝ) / Y) ≠ 0 := by
    intro h0; apply h; unfold minorKernel; rw [h0]; simp
  have ht : |(t : ℝ) / Y| < 5 := by
    by_contra hge
    have := abs_arcCutoff_le ((t : ℝ) / Y)
    rw [if_neg hge] at this
    exact hψ (abs_nonpos_iff.1 this)
  rwa [abs_div, abs_of_pos hY, div_lt_iff₀ hY] at ht

lemma not_dvd_of_rough {W : ℝ} {n p : ℕ} (hn : IsRough W n) (hp : p.Prime) (hpW : (p : ℝ) ≤ W) :
    ¬ p ∣ n := by
  intro h
  have := hn.2 p (Nat.mem_primeFactors.2 ⟨hp, h, hn.1.ne'⟩)
  linarith

/-- The two positions of a configuration with nonzero term are primitive. -/
lemma cfg_primitive {W Y : ℝ} (hK : 1 ≤ K) (hYW : 5 * Y < W)
    {p q : Fin K → ℕ} {m n r s : ℕ}
    (hp : p ∈ labelTuples x a) (hq : q ∈ labelTuples x a) (hpq : ∀ i, p i ≠ q i)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hgW : ∀ v ∈ groupPrimes x a, (v : ℝ) ≤ W)
    (hn : IsRough W n) (hr : IsRough W r) (hs : IsRough W s)
    (ht : |((sqDet (∏ i, p i) (∏ i, q i) m n r s : ℤ) : ℝ)| < 5 * Y)
    {G G' : ℕ} (hG : ∀ v, v.Prime → v ∣ G → (v : ℝ) ≤ W) (hG' : ∀ v, v.Prime → v ∣ G' → (v : ℝ) ≤ W) :
    Nat.Coprime (G * m) s ∧ Nat.Coprime (G' * r) n := by
  -- `t = 0` is impossible
  have ht0 : sqDet (∏ i, p i) (∏ i, q i) m n r s ≠ 0 := by
    intro h0
    unfold sqDet at h0
    have heq : (∏ i, q i) * m * n = (∏ i, p i) * r * s := by
      have : ((∏ i, q i : ℕ) : ℤ) * m * n = ((∏ i, p i : ℕ) : ℤ) * r * s := by linarith
      exact_mod_cast this
    set i₀ : Fin K := ⟨0, hK⟩
    have hqi : (q i₀).Prime := by
      have := Fintype.mem_piFinset.1 hq i₀; unfold primeGroup at this; exact (mem_filter.1 this).2.1
    have hqW : (q i₀ : ℝ) ≤ W := hgW _ (mem_groupPrimes_of (Fintype.mem_piFinset.1 hq i₀))
    have hdvd : q i₀ ∣ (∏ i, p i) * r * s := by
      rw [← heq]; exact Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_prod_of_mem _ (mem_univ _)) _) _
    rcases (Nat.Prime.dvd_mul hqi).1 hdvd with h1 | h1
    · rcases (Nat.Prime.dvd_mul hqi).1 h1 with h2 | h2
      · obtain ⟨i, -, hi⟩ := (Nat.prime_iff.1 hqi).dvd_finsetProd_iff _ |>.1 h2
        have hpi : (p i).Prime := by
          have := Fintype.mem_piFinset.1 hp i; unfold primeGroup at this; exact (mem_filter.1 this).2.1
        have he : q i₀ = p i := (Nat.prime_dvd_prime_iff_eq hqi hpi).1 hi
        by_cases hii : i = i₀
        · rw [hii] at he; exact hpq i₀ he.symm
        · have hq0 : q i₀ ∈ primeGroup x (a i₀) := Fintype.mem_piFinset.1 hq i₀
          rw [he] at hq0
          exact Finset.disjoint_left.1 (hdisj i i₀ hii) (Fintype.mem_piFinset.1 hp i) hq0
      · exact not_dvd_of_rough hr hqi hqW h2
    · exact not_dvd_of_rough hs hqi hqW h1
  have hbig : ∀ v : ℕ, v.Prime → W < v → (v : ℤ) ∣ sqDet (∏ i, p i) (∏ i, q i) m n r s → False := by
    intro v hv hvW hdv
    obtain ⟨c, hc⟩ := hdv
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact ht0 hc
    have : (v : ℝ) ≤ |((sqDet (∏ i, p i) (∏ i, q i) m n r s : ℤ) : ℝ)| := by
      rw [hc]; push_cast
      rw [abs_mul, abs_of_pos (by exact_mod_cast hv.pos)]
      exact le_mul_of_one_le_right (by positivity) (by exact_mod_cast Int.one_le_abs hc0)
    linarith
  constructor
  · refine Nat.coprime_of_dvd fun v hv h1 h2 => ?_
    have hvW : W < v := hs.2 v (Nat.mem_primeFactors.2 ⟨hv, h2, hs.1.ne'⟩)
    have hvm : v ∣ m := by
      rcases (Nat.Prime.dvd_mul hv).1 h1 with h | h
      · exact absurd (hG v hv h) (not_le.2 hvW)
      · exact h
    refine hbig v hv hvW ?_
    unfold sqDet
    exact dvd_sub (Dvd.dvd.mul_right (Dvd.dvd.mul_left (by exact_mod_cast hvm) _) _)
      (Dvd.dvd.mul_left (by exact_mod_cast h2) _)
  · refine Nat.coprime_of_dvd fun v hv h1 h2 => ?_
    have hvW : W < v := hn.2 v (Nat.mem_primeFactors.2 ⟨hv, h2, hn.1.ne'⟩)
    have hvr : v ∣ r := by
      rcases (Nat.Prime.dvd_mul hv).1 h1 with h | h
      · exact absurd (hG' v hv h) (not_le.2 hvW)
      · exact h
    refine hbig v hv hvW ?_
    unfold sqDet
    exact dvd_sub (Dvd.dvd.mul_left (by exact_mod_cast h2) _)
      (Dvd.dvd.mul_right (Dvd.dvd.mul_left (by exact_mod_cast hvr) _) _)

end Bijection

section Bijection2

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

open Classical in
/-- **Step B.** The configuration sum at dyad `k` equals `2^{-k} ⟨f, T f⟩_σ`. -/
theorem cfg_sum_eq_pairing (A₀ Y Hm Hn : ℝ) (k : ℕ) (α β : ℕ → ℂ) (hK : 1 ≤ K) (hY : 0 < Y)
    (hHm : 0 < Hm) (hHn : 0 < Hn)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (hα0 : α 0 = 0)
    (hαS : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough (sieveLevel x) m)
    (hβS : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n)
    (hgW : ∀ v ∈ groupPrimes x a, (v : ℝ) ≤ sieveLevel x) (hYW : 5 * Y < sieveLevel x) :
    ∑ c ∈ cfgSet x a J Hm Hn, (if PadsOK c.1 c.2.1 c.2.2.1 ∧ 2 ^ k ≤ padsProd c.1 ∧
        padsProd c.1 < 2 * 2 ^ k then cfgTerm x a A₀ Y α β c else 0) =
      ((2 : ℂ) ^ k)⁻¹ * opPairing x a J (2 ^ k * Y * Hm) Hn α β
        (rowOp x a A₀ Y J (2 ^ k) (2 ^ k * Y * Hm) Hn) := by
  rw [dyad_pairing_eq_sum]
  set W := sieveLevel x
  set U := 2 ^ k * Y * Hm
  have hU : 0 < U := by positivity
  have hαg : ∀ m, α m ≠ 0 → ∀ v ∈ groupPrimes x a, ¬ v ∣ m := fun m hm v hv =>
    not_dvd_of_rough (hαS m hm).2.2 (prime_of_mem_groupPrimes hv) (hgW v hv)
  have hgW' : ∀ ℓ : Fin K → Fin (J + 1) → ℕ, ListOK x a J ℓ →
      ∀ v, v.Prime → v ∣ listProd ℓ → (v : ℝ) ≤ W := by
    intro ℓ hℓ v hv hvd
    rw [hℓ.listProd_eq] at hvd
    obtain ⟨w, hw, hvw⟩ := (Nat.prime_iff.1 hv).dvd_finsetProd_iff _ |>.1 hvd
    rw [(Nat.prime_dvd_prime_iff_eq hv (hℓ.entries_prime w hw)).1 hvw]
    exact hgW w (hℓ.entries_sub hw)
  refine Finset.sum_bij_ne_zero (fun c _ _ => cfgPair c) ?_ ?_ ?_ ?_
  · -- membership
    rintro ⟨pads, p, q, m, n, r, s⟩ hc hne
    simp only at hne
    by_cases hcond : PadsOK pads p q ∧ 2 ^ k ≤ padsProd pads ∧ padsProd pads < 2 * 2 ^ k
    swap
    · rw [if_neg hcond] at hne; exact absurd rfl hne
    rw [if_pos hcond] at hne
    obtain ⟨hok, hdy1, hdy2⟩ := hcond
    obtain ⟨hinj, hne', hpq⟩ := hok
    have hc' := hc
    simp only [cfgSet, mem_product] at hc'
    obtain ⟨hpads, hp, hq, -, -, -, -⟩ := hc'
    have hOKs : ListOK x a J (mkList pads q) :=
      listOK_mkList hpads hq hinj (fun i j => (hne' i j).2) hdisj
    have hOKt : ListOK x a J (mkList pads p) :=
      listOK_mkList hpads hp hinj (fun i j => (hne' i j).1) hdisj
    -- nonvanishing of the factors
    unfold cfgTerm sqWeight at hne
    simp only at hne
    have hMK := right_ne_zero_of_mul hne
    have h1 := left_ne_zero_of_mul hne
    have hβs : β s ≠ 0 := by
      intro h0; apply h1; simp [h0]
    have hβn : β n ≠ 0 := by
      intro h0; apply h1; simp [h0]
    have hαr : α r ≠ 0 := by
      intro h0; apply h1; simp [h0]
    have hαm : α m ≠ 0 := by
      intro h0; apply h1; simp [h0]
    have hηp : dyadicBump ((∏ i, p i : ℕ) / Y) ≠ 0 := by
      intro h0; apply h1; push_cast at h0; simp [h0]
    have hηq : dyadicBump ((∏ i, q i : ℕ) / Y) ≠ 0 := by
      intro h0; apply h1; push_cast at h0; simp [h0]
    obtain ⟨hm1, hm2, hmR⟩ := hαS m hαm
    obtain ⟨hr1, hr2, hrR⟩ := hαS r hαr
    obtain ⟨hn1, hn2, hnR⟩ := hβS n hβn
    obtain ⟨hs1, hs2, hsR⟩ := hβS s hβs
    obtain ⟨hp1, hp4⟩ := dyadicBump_ne_zero hηp
    obtain ⟨hq1, hq4⟩ := dyadicBump_ne_zero hηq
    rw [one_lt_div hY] at hp1 hq1
    rw [div_lt_iff₀ hY] at hp4 hq4
    have ht := minorKernel_ne_zero_abs hY hMK
    obtain ⟨hcop1, hcop2⟩ := cfg_primitive (W := W) hK hYW hp hq hpq hdisj hgW hnR hrR hsR ht
      (hgW' _ hOKs) (hgW' _ hOKt)
    have hDr1 : (2 : ℝ) ^ k ≤ padsProd pads := by exact_mod_cast hdy1
    have hDr2 : (padsProd pads : ℝ) < 2 * 2 ^ k := by exact_mod_cast hdy2
    have hstate : ∀ (last : Fin K → ℕ) (hl : last ∈ labelTuples x a) (hOK : ListOK x a J (mkList pads last))
        (u v : ℕ), (Y < (∏ i, last i : ℕ)) → ((∏ i, last i : ℕ) : ℝ) < 4 * Y → Hm ≤ u → (u : ℝ) ≤ 2 * Hm →
        Hn ≤ v → (v : ℝ) ≤ 2 * Hn → Nat.Coprime (listProd (mkList pads last) * u) v →
        ((listProd (mkList pads last) * u, v), mkList pads last) ∈ stateSet x a J U Hn := by
      intro last hl hOK u v hb1 hb4 hu1 hu2 hv1 hv2 hcop
      refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, hOK.inj, fun i j => ?_⟩
      · simp only [posBox, mem_filter, mem_product, mem_Icc]
        have hb : ((∏ i, last i : ℕ) : ℝ) = ∏ i, (last i : ℝ) := by push_cast; ring
        rw [hb] at hb1 hb4
        have hP1 : ((listProd (mkList pads last) * u : ℕ) : ℝ) =
            (padsProd pads : ℝ) * (∏ i, (last i : ℝ)) * (u : ℝ) := by
          rw [listProd_mkList]; push_cast; ring
        have hprod0 : (0 : ℝ) ≤ ∏ i, (last i : ℝ) := by positivity
        refine ⟨⟨⟨Nat.ceil_le.2 ?_, Nat.le_floor ?_⟩, Nat.ceil_le.2 hv1, Nat.le_floor hv2⟩, hcop⟩
        · rw [hP1]
          calc U = 2 ^ k * Y * Hm := rfl
            _ ≤ (padsProd pads : ℝ) * (∏ i, (last i : ℝ)) * (u : ℝ) :=
              mul_le_mul (mul_le_mul hDr1 hb1.le hY.le (by positivity)) hu1 hHm.le (by positivity)
        · rw [hP1]
          calc (padsProd pads : ℝ) * (∏ i, (last i : ℝ)) * (u : ℝ)
              ≤ (2 * 2 ^ k) * (4 * Y) * (2 * Hm) :=
                mul_le_mul (mul_le_mul hDr2.le hb4.le hprod0 (by positivity)) hu2 (by positivity)
                  (by positivity)
            _ = 16 * U := by simp only [U]; ring
      · refine Fintype.mem_piFinset.2 fun i => Fintype.mem_piFinset.2 fun j => hOK.grp i j
      · refine Dvd.dvd.mul_right ?_ u
        rw [hOK.listProd_eq]
        exact dvd_prod_of_mem _ (mem_image.2 ⟨(i, j), mem_univ _, rfl⟩)
    exact mem_product.2 ⟨hstate q hq hOKs m s hq1 hq4 hm1 hm2 hs1 hs2 hcop1,
      hstate p hp hOKt r n hp1 hp4 hr1 hr2 hn1 hn2 hcop2⟩
  · -- injectivity
    rintro ⟨pads, p, q, m, n, r, s⟩ hc _ ⟨pads', p', q', m', n', r', s'⟩ hc' _ heq
    simp only [cfgPair, Prod.mk.injEq] at heq
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩ := heq
    have hpads : pads = pads' := funext fun i => funext fun j => by
      have := congrFun (congrFun h3 i) j.castSucc; simpa [mkList_castSucc] using this
    have hq : q = q' := funext fun i => by
      have := congrFun (congrFun h3 i) (Fin.last J); simpa [mkList_last] using this
    have hp : p = p' := funext fun i => by
      have := congrFun (congrFun h6 i) (Fin.last J); simpa [mkList_last] using this
    subst hpads hq hp
    have hpos : ∀ last ∈ labelTuples x a, 0 < listProd (mkList pads last) := by
      intro last hl
      rw [listProd_mkList]
      simp only [cfgSet, mem_product] at hc
      refine Nat.mul_pos (prod_pos fun i _ => prod_pos fun j _ => ?_) (prod_pos fun i _ => ?_)
      · exact pos_of_mem_primeGroup (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hc.1 i) j)
      · exact pos_of_mem_primeGroup (Fintype.mem_piFinset.1 hl i)
    simp only [cfgSet, mem_product] at hc
    have hm : m = m' := Nat.eq_of_mul_eq_mul_left (hpos q hc.2.2.1) h1
    have hr : r = r' := Nat.eq_of_mul_eq_mul_left (hpos p hc.2.1) h4
    subst hm hr h2 h5
    rfl
  · -- surjectivity
    rintro ⟨z1, z2⟩ hz hne
    obtain ⟨hz1, hz2⟩ := mem_product.1 hz
    unfold pairTerm at hne
    have hP0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hne))
    have hP : endPos x a J α β z1.1 ≠ 0 := fun h => hP0 (by rw [h, map_zero])
    have hT := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
    have hQ := right_ne_zero_of_mul hne
    simp only at hP hT hQ
    unfold rowAmb at hT
    by_cases hcond : (∀ i (j : Fin J), z2.2 i j.castSucc = z1.2 i j.castSucc) ∧
      (∀ i, z2.2 i (Fin.last J) ∉ Set.range (z1.2 i)) ∧
      2 ^ k ≤ padProd z1.2 ∧ padProd z1.2 < 2 * 2 ^ k
    swap
    · rw [if_neg hcond] at hT; exact absurd rfl hT
    obtain ⟨hcopy, hban, hdy1, hdy2⟩ := hcond
    set pads : Fin K → Fin J → ℕ := fun i j => z1.2 i j.castSucc
    set q : Fin K → ℕ := fun i => z1.2 i (Fin.last J)
    set p : Fin K → ℕ := fun i => z2.2 i (Fin.last J)
    have hs1 : z1.2 = mkList pads q := funext fun i => funext fun j => by
      induction j using Fin.lastCases with
      | last => rw [mkList_last]
      | cast j => rw [mkList_castSucc]
    have hs2 : z2.2 = mkList pads p := funext fun i => funext fun j => by
      induction j using Fin.lastCases with
      | last => rw [mkList_last]
      | cast j => rw [mkList_castSucc]; exact hcopy i j
    have hst1 := mem_filter.1 hz1
    have hst2 := mem_filter.1 hz2
    have hOK1 : ListOK x a J z1.2 := ⟨fun i j => Fintype.mem_piFinset.1
      (Fintype.mem_piFinset.1 (mem_product.1 hst1.1).2 i) j, hst1.2.1, hdisj⟩
    have hOK2 : ListOK x a J z2.2 := ⟨fun i j => Fintype.mem_piFinset.1
      (Fintype.mem_piFinset.1 (mem_product.1 hst2.1).2 i) j, hst2.2.1, hdisj⟩
    have hdv1 : listProd z1.2 ∣ z1.1.1 := listProd_dvd_of_disjoint hdisj ⟨z1, hz1⟩
    have hdv2 : listProd z2.2 ∣ z2.1.1 := listProd_dvd_of_disjoint hdisj ⟨z2, hz2⟩
    set m := z1.1.1 / listProd z1.2
    set r := z2.1.1 / listProd z2.2
    have hz1e : z1.1.1 = listProd z1.2 * m := (Nat.mul_div_cancel' hdv1).symm
    have hz2e : z2.1.1 = listProd z2.2 * r := (Nat.mul_div_cancel' hdv2).symm
    have hpos1 := (state_pos_bounds hU hHn ⟨z1, hz1⟩)
    have hpos2 := (state_pos_bounds hU hHn ⟨z2, hz2⟩)
    have hm0 : m ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hz1e
      have : (0 : ℝ) < z1.1.1 := lt_of_lt_of_le hU hpos1.1
      rw [hz1e] at this; simp at this
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hz2e
      have : (0 : ℝ) < z2.1.1 := lt_of_lt_of_le hU hpos2.1
      rw [hz2e] at this; simp at this
    have hP' : endPos x a J α β (listProd z1.2 * m, z1.1.2) ≠ 0 := by
      rw [← hz1e]; exact hP
    have hQ' : endPos x a J α β (listProd z2.2 * r, z2.1.2) ≠ 0 := by
      rw [← hz2e]; exact hQ
    rw [endPos_listProd_mul hOK1 α β hm0] at hP'
    rw [endPos_listProd_mul hOK2 α β hr0] at hQ'
    by_cases hg1 : groupPart x a m = 1
    swap
    · rw [if_neg hg1] at hP'; exact absurd rfl hP'
    by_cases hg2 : groupPart x a r = 1
    swap
    · rw [if_neg hg2] at hQ'; exact absurd rfl hQ'
    rw [if_pos hg1] at hP'
    rw [if_pos hg2] at hQ'
    have hαm : α m ≠ 0 := by intro h0; apply hP'; simp [h0]
    have hβs : β z1.1.2 ≠ 0 := by intro h0; apply hP'; simp [h0]
    have hαr : α r ≠ 0 := by intro h0; apply hQ'; simp [h0]
    have hβn : β z2.1.2 ≠ 0 := by intro h0; apply hQ'; simp [h0]
    have hpads : pads ∈ padSet x a J := Fintype.mem_piFinset.2 fun i =>
      Fintype.mem_piFinset.2 fun j => hOK1.grp i j.castSucc
    have hq : q ∈ labelTuples x a := Fintype.mem_piFinset.2 fun i => hOK1.grp i (Fin.last J)
    have hp : p ∈ labelTuples x a := Fintype.mem_piFinset.2 fun i => hOK2.grp i (Fin.last J)
    have hrange : ∀ {H : ℝ} {u : ℕ}, (u : ℝ) ≤ 2 * H → u ∈ range (⌊2 * H⌋₊ + 1) :=
      fun h => mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor h))
    refine ⟨(pads, p, q, m, z2.1.2, r, z1.1.2), ?_, ?_, ?_⟩
    · simp only [cfgSet, mem_product]
      exact ⟨hpads, hp, hq, hrange (hαS m hαm).2.1, hrange (hβS _ hβn).2.1,
        hrange (hαS r hαr).2.1, hrange (hβS _ hβs).2.1⟩
    · have hok : PadsOK pads p q := by
        refine ⟨fun i j j' h => Fin.castSucc_injective _ (hst1.2.1 i h), fun i j => ⟨?_, ?_⟩,
          fun i h => ?_⟩
        · intro h; exact hban i ⟨j.castSucc, h⟩
        · intro h; exact absurd (hst1.2.1 i h) (Fin.castSucc_ne_last j)
        · exact hban i ⟨Fin.last J, h.symm⟩
      have hdy : 2 ^ k ≤ padsProd pads ∧ padsProd pads < 2 * 2 ^ k := by
        have : padProd z1.2 = padsProd pads := rfl
        exact ⟨this ▸ hdy1, this ▸ hdy2⟩
      simp only
      rw [if_pos ⟨hok, hdy⟩]
      have hval := pairTerm_cfgPair (x := x) (a := a) A₀ Y k α β (Hm := Hm) (Hn := Hn)
        (c := (pads, p, q, m, z2.1.2, r, z1.1.2)) (by
          simp only [cfgSet, mem_product]
          exact ⟨hpads, hp, hq, hrange (hαS m hαm).2.1, hrange (hβS _ hβn).2.1,
            hrange (hαS r hαr).2.1, hrange (hβS _ hβs).2.1⟩) hok hdy hdisj hVpos hα0 hαg
      rw [← hval]
      have : cfgPair (pads, p, q, m, z2.1.2, r, z1.1.2) = (z1, z2) := by
        simp only [cfgPair]
        rw [← hs1, ← hs2, ← hz1e, ← hz2e]
      rw [this]; unfold pairTerm; exact hne
    · simp only [cfgPair]
      rw [← hs1, ← hs2, ← hz1e, ← hz2e]
  · -- values
    rintro c hc hne
    by_cases hcond : PadsOK c.1 c.2.1 c.2.2.1 ∧ 2 ^ k ≤ padsProd c.1 ∧ padsProd c.1 < 2 * 2 ^ k
    swap
    · rw [if_neg hcond] at hne; exact absurd rfl hne
    rw [if_pos hcond]
    exact (pairTerm_cfgPair A₀ Y k α β hc hcond.1 hcond.2 hdisj hVpos hα0 hαg).symm

end Bijection2

/-! ## Steps C and D -/

section StepsCD

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

lemma sum_dyad_indicator (D N : ℕ) (hD1 : 1 ≤ D) (hDN : D < 2 ^ (N + 1)) :
    ∑ k ∈ range (N + 1), (if 2 ^ k ≤ D ∧ D < 2 * 2 ^ k then (1 : ℂ) else 0) = 1 := by
  have hD0 : D ≠ 0 := by omega
  have hlog : Nat.log 2 D < N + 1 := Nat.log_lt_of_lt_pow hD0 hDN
  rw [sum_eq_single (Nat.log 2 D)]
  · rw [if_pos ⟨Nat.pow_log_le_self 2 hD0, by
      have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) D
      rw [pow_succ] at this; linarith⟩]
  · intro k _ hk
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hk
    exact (Nat.log_eq_of_pow_le_of_lt_pow h1 (by rw [pow_succ]; linarith)).symm
  · intro h; exact absurd (mem_range.2 hlog) h

lemma sum_padsWeight (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) :
    ∑ pads ∈ padSet x a J, padsWeight x a pads = 1 := by
  unfold padSet padsWeight
  rw [← Finset.prod_univ_sum (fun i => Fintype.piFinset fun _ : Fin J => primeGroup x (a i))
    (fun i (row : Fin J → ℕ) => ∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_eq_one fun i _ => ?_
  rw [← Finset.prod_univ_sum (fun _ : Fin J => primeGroup x (a i))
    (fun _ (v : ℕ) => 1 / ((v : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_eq_one fun j _ => ?_
  have hV := (hVpos i).ne'
  rw [show ∑ v ∈ primeGroup x (a i), 1 / ((v : ℝ) * groupReciprocalSum x (a i)) =
      (∑ v ∈ primeGroup x (a i), 1 / (v : ℝ)) / groupReciprocalSum x (a i) by
    rw [sum_div]; exact sum_congr rfl fun v _ => by rw [div_div]]
  exact div_self hV

open Classical in
/-- **Step D.** `Q^min = Σ_configs 1[(a,b)=1]·cfgTerm` (the pads are independent harmonic draws). -/
theorem minorSquare_eq_cfg_sum (A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ)
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) :
    minorSquare x a A₀ Y Hm Hn α β = ∑ c ∈ cfgSet x a J Hm Hn,
      (if Nat.Coprime (∏ i, c.2.1 i) (∏ i, c.2.2.1 i) then cfgTerm x a A₀ Y α β c else 0) := by
  unfold cfgSet
  simp only [sum_product]
  have hw := sum_padsWeight (J := J) hVpos
  have hrow : ∀ pads : Fin K → Fin J → ℕ,
      ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a,
        ∑ m ∈ range (⌊2 * Hm⌋₊ + 1), ∑ n ∈ range (⌊2 * Hn⌋₊ + 1),
        ∑ r ∈ range (⌊2 * Hm⌋₊ + 1), ∑ s ∈ range (⌊2 * Hn⌋₊ + 1),
          (if Nat.Coprime (∏ i, p i) (∏ i, q i) then
            cfgTerm x a A₀ Y α β (pads, p, q, m, n, r, s) else 0) =
      (padsWeight x a pads : ℂ) * ((squareNorm x a : ℂ) * ∑ p ∈ labelTuples x a,
        ∑ q ∈ labelTuples x a, if Nat.Coprime (∏ i, p i) (∏ i, q i) then
          minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) else 0) := by
    intro pads
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun q _ => ?_
    split_ifs with hcop
    · unfold minInner cfgTerm
      simp only [mul_sum]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
        sum_congr rfl fun s _ => by push_cast; ring
    · simp
  simp only [hrow]
  rw [← sum_mul]
  have hw' : ∑ pads ∈ padSet x a J, (padsWeight x a pads : ℂ) = 1 := by
    exact_mod_cast hw
  rw [hw', one_mul]
  rfl

end StepsCD

/-! ## The difference identity -/

section Difference

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

/-- The pads are distinct in each group and avoid both unshared labels. -/
def PadsGood {K J : ℕ} (pads : Fin K → Fin J → ℕ) (p q : Fin K → ℕ) : Prop :=
  (∀ i, Function.Injective (pads i)) ∧ ∀ i j, pads i j ≠ p i ∧ pads i j ≠ q i

open Classical in
/-- The harmonic mass of the colliding pad tuples. -/
noncomputable def badMass (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (J : ℕ) (p q : Fin K → ℕ) : ℝ :=
  ∑ pads ∈ padSet x a J, if PadsGood pads p q then 0 else padsWeight x a pads

lemma ne_of_coprime {p q : Fin K → ℕ} (hp : p ∈ labelTuples x a)
    (hcop : Nat.Coprime (∏ i, p i) (∏ i, q i)) (i : Fin K) : p i ≠ q i := by
  intro h
  have hpr : (p i).Prime := by
    have := Fintype.mem_piFinset.1 hp i; unfold primeGroup at this; exact (mem_filter.1 this).2.1
  have h1 : p i ∣ ∏ i, p i := dvd_prod_of_mem _ (mem_univ i)
  have h2 : p i ∣ ∏ i, q i := h ▸ dvd_prod_of_mem _ (mem_univ i)
  have h3 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop] at h3
  exact hpr.one_lt.ne' (Nat.dvd_one.1 h3)

lemma coprime_of_padsOK {p q : Fin K → ℕ} (hp : p ∈ labelTuples x a) (hq : q ∈ labelTuples x a)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hpq : ∀ i, p i ≠ q i) : Nat.Coprime (∏ i, p i) (∏ i, q i) := by
  by_contra h
  obtain ⟨i, j, hij⟩ := exists_eq_of_not_coprime hp hq h
  by_cases h' : i = j
  · subst h'; exact hpq i hij
  · exact Finset.disjoint_left.1 (hdisj i j h') (Fintype.mem_piFinset.1 hp i)
      (hij ▸ Fintype.mem_piFinset.1 hq j)

open Classical in
/-- **Steps C–D combined.** `Q^min − Σ_{k≤N} 2^{-k}⟨f,STSf⟩ = Σ_{(a,b)=1} sqN · badMass · minInner`. -/
theorem minorSquare_sub_pairings (A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (N : ℕ) (hK : 1 ≤ K)
    (hY : 0 < Y) (hHm : 0 < Hm) (hHn : 0 < Hn)
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (hα0 : α 0 = 0)
    (hαS : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough (sieveLevel x) m)
    (hβS : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n)
    (hgW : ∀ v ∈ groupPrimes x a, (v : ℝ) ≤ sieveLevel x) (hYW : 5 * Y < sieveLevel x)
    (hDN : ∀ pads ∈ padSet x a (padCount x), padsProd pads < 2 ^ (N + 1)) :
    minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (N + 1),
        ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k =
      ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a,
        if Nat.Coprime (∏ i, p i) (∏ i, q i) then
          (squareNorm x a : ℂ) * (badMass x a (padCount x) p q : ℂ) *
            minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) else 0 := by
  set J := padCount x
  -- the dyadic sum of pairings is the sum over good configurations
  have hpair : ∑ k ∈ range (N + 1), ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k =
      ∑ c ∈ cfgSet x a J Hm Hn, if PadsOK c.1 c.2.1 c.2.2.1 then cfgTerm x a A₀ Y α β c else 0 := by
    have hk : ∀ k, ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k =
        ∑ c ∈ cfgSet x a J Hm Hn, (if PadsOK c.1 c.2.1 c.2.2.1 ∧ 2 ^ k ≤ padsProd c.1 ∧
          padsProd c.1 < 2 * 2 ^ k then cfgTerm x a A₀ Y α β c else 0) := by
      intro k
      unfold dyadPairingSTS
      rw [opPairing_slotSym]
      exact (cfg_sum_eq_pairing A₀ Y Hm Hn k α β hK hY hHm hHn hdisj hVpos hα0 hαS hβS hgW
        hYW).symm
    simp only [hk]
    rw [sum_comm]
    refine sum_congr rfl fun c hc => ?_
    by_cases hok : PadsOK c.1 c.2.1 c.2.2.1
    · simp only [hok, true_and, if_true]
      have hD1 : 1 ≤ padsProd c.1 := by
        have hpads := (mem_product.1 hc).1
        unfold padsProd
        exact prod_pos fun i _ => prod_pos fun j _ =>
          pos_of_mem_primeGroup (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hpads i) j)
      have := sum_dyad_indicator (padsProd c.1) N hD1 (hDN c.1 (mem_product.1 hc).1)
      calc ∑ k ∈ range (N + 1), (if 2 ^ k ≤ padsProd c.1 ∧ padsProd c.1 < 2 * 2 ^ k then
            cfgTerm x a A₀ Y α β c else 0)
          = ∑ k ∈ range (N + 1), (if 2 ^ k ≤ padsProd c.1 ∧ padsProd c.1 < 2 * 2 ^ k then
            (1 : ℂ) else 0) * cfgTerm x a A₀ Y α β c := by
            refine sum_congr rfl fun k _ => by split_ifs <;> simp
        _ = cfgTerm x a A₀ Y α β c := by rw [← sum_mul, this, one_mul]
    · simp [hok]
  rw [hpair, minorSquare_eq_cfg_sum (J := J) A₀ Y Hm Hn α β hVpos, ← sum_sub_distrib]
  unfold cfgSet
  simp only [sum_product]
  rw [sum_comm]
  refine sum_congr rfl fun p hp => ?_
  rw [sum_comm]
  refine sum_congr rfl fun q hq => ?_
  by_cases hcop : Nat.Coprime (∏ i, p i) (∏ i, q i)
  · have hpq := ne_of_coprime hp hcop
    rw [if_pos hcop]
    have hiff : ∀ pads : Fin K → Fin J → ℕ, PadsOK pads p q ↔ PadsGood pads p q := fun pads =>
      ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hpq⟩⟩
    have hR : (squareNorm x a : ℂ) * (badMass x a J p q : ℂ) *
        minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) =
        ∑ pads ∈ padSet x a J, if PadsGood pads p q then 0 else
          (squareNorm x a : ℂ) * (padsWeight x a pads : ℂ) *
            minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) := by
      unfold badMass
      push_cast
      rw [mul_sum, sum_mul]
      refine sum_congr rfl fun pads _ => ?_
      split_ifs <;> simp
    rw [hR]
    refine sum_congr rfl fun pads _ => ?_
    simp only [if_pos hcop]
    by_cases hg : PadsGood pads p q
    · rw [if_pos hg]
      simp only [if_pos ((hiff pads).2 hg), sub_self, sum_const_zero]
    · rw [if_neg hg]
      simp only [if_neg (fun h => hg ((hiff pads).1 h)), sub_zero]
      unfold minInner cfgTerm
      simp only [mul_sum]
      refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
        sum_congr rfl fun s _ => by push_cast; ring
  · rw [if_neg hcop]
    refine sum_eq_zero fun pads hpads => ?_
    have hnok : ¬ PadsOK pads p q := fun h => hcop (coprime_of_padsOK hp hq hdisj h.2.2)
    simp [hcop, hnok]

end Difference

/-! ## Step E: the collision mass -/

section Collision

variable {J : ℕ}

open Classical in
lemma rowsum_eq_val (T : Finset ℕ) (μ : ℕ → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u ∈ T, μ u ≤ 1)
    (M : ℝ) (hM : ∀ u ∈ T, μ u ≤ M) (hM0 : 0 ≤ M) (j : Fin J) (v : ℕ) :
    ∑ row ∈ Fintype.piFinset (fun _ : Fin J => T),
      (∏ l, μ (row l)) * (if row j = v then 1 else 0) ≤ M := by
  have hrw : ∀ row : Fin J → ℕ, (∏ l, μ (row l)) * (if row j = v then 1 else 0) =
      ∏ l, (μ (row l) * (if l = j then (if row l = v then 1 else 0) else 1)) := by
    intro row
    rw [prod_mul_distrib, prod_ite_eq' univ j (fun l => if row l = v then (1 : ℝ) else 0)]
    simp
  simp only [hrw]
  rw [← Finset.prod_univ_sum (fun _ : Fin J => T)
    (fun l (u : ℕ) => μ u * (if l = j then (if u = v then 1 else 0) else 1))]
  calc ∏ l, ∑ u ∈ T, μ u * (if l = j then (if u = v then (1 : ℝ) else 0) else 1)
      ≤ ∏ l, (if l = j then M else 1) := by
        refine prod_le_prod (fun l _ => sum_nonneg fun u _ => ?_) fun l _ => ?_
        · have := hμ0 u; split_ifs <;> simp [this]
        · by_cases hl : l = j
          · simp only [hl, if_true, mul_ite, mul_one, mul_zero]
            rw [sum_ite_eq']
            split_ifs with hv
            · exact hM v hv
            · exact hM0
          · simp only [hl, if_false, mul_one]; exact hμ1
    _ = M := by rw [prod_ite_eq']; simp

open Classical in
lemma rowsum_eq_pair (T : Finset ℕ) (μ : ℕ → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u ∈ T, μ u ≤ 1)
    (M : ℝ) (hM : ∀ u ∈ T, μ u ≤ M) (hM0 : 0 ≤ M) (j j' : Fin J) (hjj : j ≠ j') :
    ∑ row ∈ Fintype.piFinset (fun _ : Fin J => T),
      (∏ l, μ (row l)) * (if row j = row j' then 1 else 0) ≤ M := by
  have hsplit : ∀ row ∈ Fintype.piFinset (fun _ : Fin J => T),
      (∏ l, μ (row l)) * (if row j = row j' then (1 : ℝ) else 0) =
        ∑ v ∈ T, ∏ l, (μ (row l) * (if l = j ∨ l = j' then (if row l = v then 1 else 0) else 1)) := by
    intro row hrow
    have hj : row j ∈ T := Fintype.mem_piFinset.1 hrow j
    rw [sum_eq_single (row j)]
    · rw [prod_mul_distrib]
      congr 1
      rw [Finset.prod_eq_mul j j' hjj (fun l _ hl => by simp [hl.1, hl.2]) (by simp) (by simp)]
      simp only [true_or, or_true, if_true]
      by_cases h : row j = row j'
      · simp [h]
      · rw [if_neg h, if_neg (Ne.symm h)]; simp
    · intro v _ hv
      refine prod_eq_zero (mem_univ j) ?_
      simp [Ne.symm hv]
    · intro h; exact absurd hj h
  rw [sum_congr rfl hsplit, sum_comm]
  calc ∑ v ∈ T, ∑ row ∈ Fintype.piFinset (fun _ : Fin J => T),
        ∏ l, (μ (row l) * (if l = j ∨ l = j' then (if row l = v then (1 : ℝ) else 0) else 1))
      = ∑ v ∈ T, ∏ l, ∑ u ∈ T,
          μ u * (if l = j ∨ l = j' then (if u = v then (1 : ℝ) else 0) else 1) :=
        sum_congr rfl fun v _ => (Finset.prod_univ_sum (fun _ : Fin J => T)
          (fun l (u : ℕ) => μ u * (if l = j ∨ l = j' then (if u = v then 1 else 0) else 1))).symm
    _ ≤ ∑ v ∈ T, μ v * M := by
        refine sum_le_sum fun v hv => ?_
        calc ∏ l, ∑ u ∈ T, μ u * (if l = j ∨ l = j' then (if u = v then (1 : ℝ) else 0) else 1)
            ≤ ∏ l, (if l = j ∨ l = j' then μ v else 1) := by
              refine prod_le_prod (fun l _ => sum_nonneg fun u _ => ?_) fun l _ => ?_
              · have := hμ0 u; split_ifs <;> simp [this]
              · by_cases hl : l = j ∨ l = j'
                · simp only [hl, if_true, mul_ite, mul_one, mul_zero]
                  rw [sum_ite_eq', if_pos hv]
                · simp only [hl, if_false, mul_one]; exact hμ1
          _ = μ v * μ v := by
              rw [Finset.prod_eq_mul j j' hjj (fun l _ hl => by simp [hl.1, hl.2]) (by simp)
                (by simp)]
              simp
          _ ≤ μ v * M := mul_le_mul_of_nonneg_left (hM v hv) (hμ0 v)
    _ = (∑ v ∈ T, μ v) * M := by rw [sum_mul]
    _ ≤ 1 * M := mul_le_mul_of_nonneg_right hμ1 hM0
    _ = M := one_mul M

end Collision

section Collision2

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {J : ℕ}

lemma rowWeight_sum (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (i : Fin K) :
    ∑ row ∈ Fintype.piFinset (fun _ : Fin J => primeGroup x (a i)),
      ∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i)) = 1 := by
  rw [← Finset.prod_univ_sum (fun _ : Fin J => primeGroup x (a i))
    (fun _ (u : ℕ) => 1 / ((u : ℝ) * groupReciprocalSum x (a i)))]
  refine prod_eq_one fun j _ => ?_
  have hV := (hVpos i).ne'
  rw [show ∑ v ∈ primeGroup x (a i), 1 / ((v : ℝ) * groupReciprocalSum x (a i)) =
      (∑ v ∈ primeGroup x (a i), 1 / (v : ℝ)) / groupReciprocalSum x (a i) by
    rw [sum_div]; exact sum_congr rfl fun v _ => by rw [div_div]]
  exact div_self hV

lemma outer_event (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (i : Fin K)
    (E : (Fin J → ℕ) → Prop) [DecidablePred E] :
    ∑ pads ∈ padSet x a J, padsWeight x a pads * (if E (pads i) then 1 else 0) ≤
      ∑ row ∈ Fintype.piFinset (fun _ : Fin J => primeGroup x (a i)),
        (∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i))) * (if E row then 1 else 0) := by
  have hrw : ∀ pads : Fin K → Fin J → ℕ, padsWeight x a pads * (if E (pads i) then 1 else 0) =
      ∏ i', ((∏ j, 1 / ((pads i' j : ℝ) * groupReciprocalSum x (a i'))) *
        (if i' = i then (if E (pads i') then 1 else 0) else 1)) := by
    intro pads
    unfold padsWeight
    rw [prod_mul_distrib, prod_ite_eq' univ i (fun i' => if E (pads i') then (1 : ℝ) else 0)]
    simp
  simp only [hrw]
  unfold padSet
  rw [← Finset.prod_univ_sum (fun i' => Fintype.piFinset fun _ : Fin J => primeGroup x (a i'))
    (fun i' (row : Fin J → ℕ) => (∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i'))) *
      (if i' = i then (if E row then 1 else 0) else 1))]
  have hnn : ∀ i' (row : Fin J → ℕ), 0 ≤ ∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i')) :=
    fun i' row => prod_nonneg fun j _ => by have := (hVpos i').le; positivity
  calc ∏ i', ∑ row ∈ Fintype.piFinset (fun _ : Fin J => primeGroup x (a i')),
        (∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i'))) *
          (if i' = i then (if E row then (1 : ℝ) else 0) else 1)
      ≤ ∏ i', (if i' = i then ∑ row ∈ Fintype.piFinset (fun _ : Fin J => primeGroup x (a i)),
          (∏ j, 1 / ((row j : ℝ) * groupReciprocalSum x (a i))) * (if E row then 1 else 0)
          else 1) := by
        refine prod_le_prod (fun i' _ => sum_nonneg fun row _ => ?_) fun i' _ => ?_
        · exact mul_nonneg (hnn i' row) (by split_ifs <;> norm_num)
        · by_cases hi : i' = i
          · subst hi; simp
          · simp only [hi, if_false, mul_one]; rw [rowWeight_sum hVpos]
    _ = _ := by rw [prod_ite_eq']; simp

open Classical in
/-- **The collision mass**: `badMass ≤ K (J² + 2J) M` when every `μᵢ(u) = 1/(u Vᵢ) ≤ M`. -/
theorem badMass_le (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ i, ∀ u ∈ primeGroup x (a i), 1 / ((u : ℝ) * groupReciprocalSum x (a i)) ≤ M)
    (p q : Fin K → ℕ) :
    badMass x a J p q ≤ K * ((J : ℝ) ^ 2 + 2 * J) * M := by
  set ind : (Fin K → Fin J → ℕ) → ℝ := fun pads => ∑ i, (∑ j, ∑ j' ∈ univ.erase j,
      (if pads i j = pads i j' then (1 : ℝ) else 0) +
    ∑ j, (if pads i j = p i then (1 : ℝ) else 0) + ∑ j, (if pads i j = q i then (1 : ℝ) else 0))
  have hind0 : ∀ pads, 0 ≤ ind pads := fun pads =>
    sum_nonneg fun i _ => by
      refine add_nonneg (add_nonneg (sum_nonneg fun j _ => sum_nonneg fun j' _ => ?_)
        (sum_nonneg fun j _ => ?_)) (sum_nonneg fun j _ => ?_) <;> split_ifs <;> norm_num
  have hpt : ∀ pads, (if PadsGood pads p q then (0 : ℝ) else 1) ≤ ind pads := by
    intro pads
    split_ifs with hg
    · exact hind0 pads
    · have hterm : ∀ i, 0 ≤ ∑ j, ∑ j' ∈ univ.erase j,
          (if pads i j = pads i j' then (1 : ℝ) else 0) +
          ∑ j, (if pads i j = p i then (1 : ℝ) else 0) +
          ∑ j, (if pads i j = q i then (1 : ℝ) else 0) := fun i => by
        refine add_nonneg (add_nonneg (sum_nonneg fun j _ => sum_nonneg fun j' _ => ?_)
          (sum_nonneg fun j _ => ?_)) (sum_nonneg fun j _ => ?_) <;> split_ifs <;> norm_num
      have h01 : ∀ (P : Prop) [Decidable P], (0 : ℝ) ≤ if P then 1 else 0 := fun P _ => by
        split_ifs <;> norm_num
      unfold PadsGood at hg
      rw [not_and_or] at hg
      rcases hg with hg | hg
      · push Not at hg
        obtain ⟨i, hi⟩ := hg
        obtain ⟨j, j', hjj, hne⟩ : ∃ j j', pads i j = pads i j' ∧ j ≠ j' := by
          unfold Function.Injective at hi; push Not at hi; exact hi
        calc (1 : ℝ) ≤ ∑ j, ∑ j' ∈ univ.erase j, (if pads i j = pads i j' then (1 : ℝ) else 0) := by
              refine le_trans ?_ (single_le_sum (fun j _ => sum_nonneg fun j' _ => h01 _)
                (mem_univ j))
              refine le_trans ?_ (single_le_sum (fun j' _ => h01 _)
                (mem_erase.2 ⟨Ne.symm hne, mem_univ j'⟩))
              rw [if_pos hjj]
          _ ≤ _ := by linarith [sum_nonneg fun j (_ : j ∈ univ) => h01 (pads i j = p i),
                sum_nonneg fun j (_ : j ∈ univ) => h01 (pads i j = q i)]
          _ ≤ ind pads := single_le_sum (fun i _ => hterm i) (mem_univ i)
      · push Not at hg
        obtain ⟨i, j, hj⟩ := hg
        have h1 : (1 : ℝ) ≤ ∑ j, (if pads i j = p i then (1 : ℝ) else 0) +
            ∑ j, (if pads i j = q i then (1 : ℝ) else 0) := by
          by_cases hp' : pads i j = p i
          · have := single_le_sum (f := fun j => if pads i j = p i then (1 : ℝ) else 0)
              (fun j _ => h01 _) (mem_univ j)
            simp only [hp', if_true] at this
            linarith [sum_nonneg fun j (_ : j ∈ univ) => h01 (pads i j = q i)]
          · have hq' := hj hp'
            have := single_le_sum (f := fun j => if pads i j = q i then (1 : ℝ) else 0)
              (fun j _ => h01 _) (mem_univ j)
            simp only [hq', if_true] at this
            linarith [sum_nonneg fun j (_ : j ∈ univ) => h01 (pads i j = p i)]
        calc (1 : ℝ) ≤ _ := h1
          _ ≤ ∑ j, ∑ j' ∈ univ.erase j, (if pads i j = pads i j' then (1 : ℝ) else 0) +
              ∑ j, (if pads i j = p i then (1 : ℝ) else 0) +
              ∑ j, (if pads i j = q i then (1 : ℝ) else 0) := by
            linarith [sum_nonneg fun j (_ : j ∈ univ) => sum_nonneg fun j' (_ : j' ∈ univ.erase j) =>
              h01 (pads i j = pads i j')]
          _ ≤ ind pads := single_le_sum (fun i _ => hterm i) (mem_univ i)
  have hw0 : ∀ pads : Fin K → Fin J → ℕ, 0 ≤ padsWeight x a pads := fun pads =>
    prod_nonneg fun i _ => prod_nonneg fun j _ => by have := (hVpos i).le; positivity
  unfold badMass
  calc ∑ pads ∈ padSet x a J, (if PadsGood pads p q then 0 else padsWeight x a pads)
      ≤ ∑ pads ∈ padSet x a J, padsWeight x a pads * ind pads := by
        refine sum_le_sum fun pads _ => ?_
        have := mul_le_mul_of_nonneg_left (hpt pads) (hw0 pads)
        split_ifs at this ⊢ <;> simp_all
    _ = ∑ i, (∑ j, ∑ j' ∈ univ.erase j, ∑ pads ∈ padSet x a J,
          padsWeight x a pads * (if pads i j = pads i j' then 1 else 0) +
        ∑ j, ∑ pads ∈ padSet x a J, padsWeight x a pads * (if pads i j = p i then 1 else 0) +
        ∑ j, ∑ pads ∈ padSet x a J, padsWeight x a pads * (if pads i j = q i then 1 else 0)) := by
        simp only [ind]
        rw [show (∑ pads ∈ padSet x a J, padsWeight x a pads * ∑ i, ((∑ j, ∑ j' ∈ univ.erase j,
            (if pads i j = pads i j' then (1 : ℝ) else 0)) +
            ∑ j, (if pads i j = p i then (1 : ℝ) else 0) +
            ∑ j, (if pads i j = q i then (1 : ℝ) else 0))) =
            ∑ i, ∑ pads ∈ padSet x a J, padsWeight x a pads * ((∑ j, ∑ j' ∈ univ.erase j,
            (if pads i j = pads i j' then (1 : ℝ) else 0)) +
            ∑ j, (if pads i j = p i then (1 : ℝ) else 0) +
            ∑ j, (if pads i j = q i then (1 : ℝ) else 0)) by
          simp only [mul_sum]; exact sum_comm]
        refine sum_congr rfl fun i _ => ?_
        simp only [mul_add, sum_add_distrib]
        congr 1
        congr 1
        · simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_comm]
        · simp only [mul_sum]
          rw [sum_comm]
        · simp only [mul_sum]
          rw [sum_comm]
    _ ≤ ∑ _i : Fin K, ((J : ℝ) * J * M + J * M + J * M) := by
        refine sum_le_sum fun i _ => add_le_add (add_le_add ?_ ?_) ?_
        · calc ∑ j, ∑ j' ∈ univ.erase j, ∑ pads ∈ padSet x a J,
                padsWeight x a pads * (if pads i j = pads i j' then 1 else 0)
              ≤ ∑ _j : Fin J, ∑ _j' ∈ (univ : Finset (Fin J)), M := by
                refine sum_le_sum fun j _ => ?_
                refine (sum_le_sum fun j' hj' => ?_).trans
                  (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun _ _ _ => hM0)
                refine (outer_event hVpos i (fun row => row j = row j')).trans ?_
                exact rowsum_eq_pair _ _ (fun u => by have := (hVpos i).le; positivity)
                  (sum_inv_mul_groupReciprocalSum_le x (a i)) M (hM i) hM0 j j' (mem_erase.1 hj').1.symm
            _ = J * J * M := by simp [sum_const, card_univ]; ring
        · calc ∑ j, ∑ pads ∈ padSet x a J, padsWeight x a pads * (if pads i j = p i then 1 else 0)
              ≤ ∑ _j : Fin J, M := by
                refine sum_le_sum fun j _ => (outer_event hVpos i (fun row => row j = p i)).trans ?_
                exact rowsum_eq_val _ _ (fun u => by have := (hVpos i).le; positivity)
                  (sum_inv_mul_groupReciprocalSum_le x (a i)) M (hM i) hM0 j (p i)
            _ = J * M := by simp [sum_const, card_univ]
        · calc ∑ j, ∑ pads ∈ padSet x a J, padsWeight x a pads * (if pads i j = q i then 1 else 0)
              ≤ ∑ _j : Fin J, M := by
                refine sum_le_sum fun j _ => (outer_event hVpos i (fun row => row j = q i)).trans ?_
                exact rowsum_eq_val _ _ (fun u => by have := (hVpos i).le; positivity)
                  (sum_inv_mul_groupReciprocalSum_le x (a i)) M (hM i) hM0 j (q i)
            _ = J * M := by simp [sum_const, card_univ]
    _ = K * ((J : ℝ) ^ 2 + 2 * J) * M := by simp [sum_const, card_univ]; ring

end Collision2

/-! ## Step E: the bound at one `x` -/

section StepE

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ}

lemma minInner_eq_sub (A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    {a' b' : ℕ} (ha : 0 < a') (hab : Nat.Coprime a' b') :
    minInner x A₀ Y Hm Hn α β a' b' = rawInner Y Hm Hn α β a' b' - majInner x A₀ Y Hm Hn α β a' b' := by
  classical
  unfold minInner rawInner majInner
  simp only [← sum_sub_distrib]
  refine sum_congr rfl fun m _ => sum_congr rfl fun n _ => sum_congr rfl fun r _ =>
    sum_congr rfl fun s _ => ?_
  exact (term_identity x A₀ Y α β hα0 hβ0 ha hab m n r s).symm

/-- `∏Vᵢ⁻² Σ_{p,q} |η(a/Y) η(b/Y)| ≤ 16 Y²`. -/
lemma mass_all_le (Y : ℝ) (hY : 0 < Y) (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) :
    ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a,
      squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| ≤
      16 * Y ^ 2 := by
  have hpos : ∀ r ∈ labelTuples x a, ∀ i, 0 < r i := fun r hr i =>
    pos_of_mem_primeGroup ((Fintype.mem_piFinset.1 hr) i)
  have hpt : ∀ p ∈ labelTuples x a, ∀ q ∈ labelTuples x a,
      squareNorm x a * |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| ≤
        16 * Y ^ 2 * (labelWeight x a p * labelWeight x a q) := by
    intro p hp q hq
    have ha : 0 < ∏ i, p i := prod_pos fun i _ => hpos p hp i
    have hb : 0 < ∏ i, q i := prod_pos fun i _ => hpos q hq i
    have h1 := abs_dyadicBump_le_div _ Y hY ha
    have h2 := abs_dyadicBump_le_div _ Y hY hb
    have hsq : 0 ≤ squareNorm x a := prod_nonneg fun i _ => by positivity
    rw [abs_mul]
    have hpi : ∀ i, (p i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos p hp i).ne'
    have hqi : ∀ i, (q i : ℝ) ≠ 0 := fun i => by exact_mod_cast (hpos q hq i).ne'
    have hVi : ∀ i, groupReciprocalSum x (a i) ≠ 0 := fun i => (hVpos i).ne'
    have h_aux : ∏ i, (groupReciprocalSum x (a i))⁻¹ ^ 2 =
        labelWeight x a p * labelWeight x a q * ((∏ i, (p i : ℝ)) * ∏ i, (q i : ℝ)) := by
      unfold labelWeight
      rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
      refine prod_congr rfl fun i _ => ?_
      have := hpi i; have := hqi i; have := hVi i
      field_simp
    calc squareNorm x a * (|dyadicBump ((∏ i, p i : ℕ) / Y)| * |dyadicBump ((∏ i, q i : ℕ) / Y)|)
        ≤ squareNorm x a * ((4 * Y / (∏ i, p i : ℕ)) * (4 * Y / (∏ i, q i : ℕ))) := by gcongr
      _ = 16 * Y ^ 2 * (labelWeight x a p * labelWeight x a q) := by
          have hPi : (∏ i, (p i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hpi i
          have hQi : (∏ i, (q i : ℝ)) ≠ 0 := prod_ne_zero_iff.2 fun i _ => hqi i
          unfold squareNorm; push_cast; rw [h_aux]; field_simp; ring
  calc _ ≤ ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a,
        16 * Y ^ 2 * (labelWeight x a p * labelWeight x a q) :=
        sum_le_sum fun p hp => sum_le_sum fun q hq => hpt p hp q hq
    _ = 16 * Y ^ 2 * ((∑ p ∈ labelTuples x a, labelWeight x a p) *
          (∑ q ∈ labelTuples x a, labelWeight x a q)) := by
        rw [sum_mul_sum, mul_sum]; simp only [mul_sum]
    _ ≤ 16 * Y ^ 2 * (1 * 1) := by
        have h1 := sum_labelWeight_le_one x a
        have h0 := sum_nonneg fun p (_ : p ∈ labelTuples x a) => labelWeight_nonneg x a p
        gcongr
    _ = 16 * Y ^ 2 := by ring

/-- **Step E at one `x`.** If `‖rawInner‖, ‖majInner‖ ≤ |η η| M` on coprime pairs and every
collision mass is `≤ B`, then `‖Q^min − Σ_k 2^{-k}⟨f,STSf⟩‖ ≤ 16 Y² B · 2M`. -/
theorem diff_bound (A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (hY : 0 < Y)
    (hVpos : ∀ i, 0 < groupReciprocalSum x (a i)) (hα0 : α 0 = 0) (hβ0 : β 0 = 0)
    (B M : ℝ) (hB : ∀ p q, badMass x a (padCount x) p q ≤ B) (hM0 : 0 ≤ M)
    (hraw : ∀ p ∈ labelTuples x a, ∀ q ∈ labelTuples x a, Nat.Coprime (∏ i, p i) (∏ i, q i) →
      ‖rawInner Y Hm Hn α β (∏ i, p i) (∏ i, q i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| * M)
    (hmaj : ∀ p ∈ labelTuples x a, ∀ q ∈ labelTuples x a, Nat.Coprime (∏ i, p i) (∏ i, q i) →
      ‖majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| * M) :
    ‖∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a,
        (if Nat.Coprime (∏ i, p i) (∏ i, q i) then
          (squareNorm x a : ℂ) * (badMass x a (padCount x) p q : ℂ) *
            minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) else 0)‖ ≤
      16 * Y ^ 2 * B * (2 * M) := by
  classical
  have hsq : 0 ≤ squareNorm x a := prod_nonneg fun i _ => by positivity
  have hbad0 : ∀ p q, 0 ≤ badMass x a (padCount x) p q := fun p q =>
    sum_nonneg fun pads _ => by
      split_ifs
      · rfl
      · exact prod_nonneg fun i _ => prod_nonneg fun j _ => by
          have := (hVpos i).le; positivity
  have hB0 : 0 ≤ B := (hbad0 (fun _ => 0) (fun _ => 0)).trans (hB _ _)
  have hpt : ∀ p ∈ labelTuples x a, ∀ q ∈ labelTuples x a,
      ‖(if Nat.Coprime (∏ i, p i) (∏ i, q i) then
          (squareNorm x a : ℂ) * (badMass x a (padCount x) p q : ℂ) *
            minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) else 0)‖ ≤
        B * (2 * M) * (squareNorm x a *
          |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)|) := by
    intro p hp q hq
    split_ifs with hcop
    · have ha : 0 < ∏ i, p i := prod_pos fun i _ =>
        pos_of_mem_primeGroup ((Fintype.mem_piFinset.1 hp) i)
      rw [minInner_eq_sub A₀ Y Hm Hn α β hα0 hβ0 ha hcop, norm_mul, norm_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hsq,
        abs_of_nonneg (hbad0 p q)]
      have h1 := (norm_sub_le _ _).trans (add_le_add (hraw p hp q hq hcop) (hmaj p hp q hq hcop))
      have hη0 := abs_nonneg (dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y))
      calc squareNorm x a * badMass x a (padCount x) p q *
            ‖rawInner Y Hm Hn α β (∏ i, p i) (∏ i, q i) -
              majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i)‖
          ≤ squareNorm x a * B *
            (|dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| * M +
              |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| * M) := by
            gcongr; exact hB p q
        _ = _ := by ring
    · rw [norm_zero]; positivity
  have hm := mass_all_le (x := x) (a := a) Y hY hVpos
  calc _ ≤ ∑ p ∈ labelTuples x a, ‖∑ q ∈ labelTuples x a,
          (if Nat.Coprime (∏ i, p i) (∏ i, q i) then
            (squareNorm x a : ℂ) * (badMass x a (padCount x) p q : ℂ) *
              minInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, q i) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a, B * (2 * M) * (squareNorm x a *
          |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)|) :=
        sum_le_sum fun p hp => (norm_sum_le _ _).trans (sum_le_sum fun q hq => hpt p hp q hq)
    _ = B * (2 * M) * ∑ p ∈ labelTuples x a, ∑ q ∈ labelTuples x a, squareNorm x a *
          |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, q i : ℕ) / Y)| := by
        simp only [mul_sum]
    _ ≤ B * (2 * M) * (16 * Y ^ 2) := by gcongr
    _ = 16 * Y ^ 2 * B * (2 * M) := by ring

end StepE

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D1b, the shared-label bound (uses Mertens through the stub for `Vⱼ ≥ 1/2`) -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-- `Vⱼ ≥ 1/2` for large `x` (Mertens: `Vⱼ → log 2`). -/
lemma eventually_groupReciprocalSum_ge {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j) := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 : ℝ) / 2 < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have hev := hm.eventually (lt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  filter_upwards [hy.eventually hev] with x hx
  refine hx.le.trans ?_
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, Real.rpow_one] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.le⟩

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D8bc (`PadLiftStmt`) for large `x`

Uses Mertens (through the stub, for `Vᵢ ≥ 1/2`) to bound the pad-collision probability by
`2K(J+1)²/P`, `P = exp(L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-- The uniform bound for the raw inner sums. -/
noncomputable def rawM (x Y Hm Hn C : ℝ) : ℝ :=
  (log x ^ C) ^ 4 * (4 * ((⌊4 * Hm * Hn / Y⌋₊ : ℝ) + (⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ)) *
    (1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ)) ^ 3)

/-- The uniform bound for the major inner sums. -/
noncomputable def majM (x A₀ Y Hm Hn C : ℝ) : ℝ :=
  (log x ^ C) ^ 4 * (volume (majorArcs x A₀ Y)).toReal *
    (10 * ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) * (1 + log ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ^ 3)

section Pieces

variable {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {Y Hm Hn : ℝ} {α β : ℕ → ℂ} {C : ℝ}

lemma rawM_nonneg (S : SharedSetting x a Y Hm Hn α β C) : 0 ≤ rawM x Y Hm Hn C := by
  unfold rawM
  have hlogT : 0 ≤ 1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊; linarith
  have := S.hL1
  positivity

lemma majM_nonneg (A₀ : ℝ) (S : SharedSetting x a Y Hm Hn α β C) :
    0 ≤ majM x A₀ Y Hm Hn C := by
  unfold majM
  have hlogN : 0 ≤ 1 + log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) := by
    have := Real.log_natCast_nonneg (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊); linarith
  have := S.hL1
  have : (0 : ℝ) ≤ (volume (majorArcs x A₀ Y)).toReal := ENNReal.toReal_nonneg
  positivity

lemma raw_pair (S : SharedSetting x a Y Hm Hn α β C) :
    ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      ‖rawInner Y Hm Hn α β (∏ i, p i) (∏ i, p' i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| * rawM x Y Hm Hn C := by
  have hY0 : 0 < Y := by linarith [S.hY]
  have hHm := S.hHm
  have hHn := S.hHn
  have hZ : (⌊4 * Hm * Hn / Y⌋₊ : ℝ) ≤ 4 * (Hm * Hn) / Y := by
    have := Nat.floor_le (show 0 ≤ 4 * Hm * Hn / Y by have := S.hHm; have := S.hHn; positivity)
    rw [show 4 * (Hm * Hn) / Y = 4 * Hm * Hn / Y by ring]; exact this
  have hTgen : ∀ a' : ℕ, (a' : ℝ) < 4 * Y → ∀ m : ℕ,
      m ^ 4 ≤ (1 + a' * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 → m ≤ ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ := by
    intro a' ha' m hm
    apply Nat.le_floor
    have h1aZ : ((1 + a' * ⌊4 * Hm * Hn / Y⌋₊ : ℕ) : ℝ) ≤ 17 * (Hm * Hn) := by
      push_cast
      have : (a' : ℝ) * ⌊4 * Hm * Hn / Y⌋₊ ≤ 4 * Y * (4 * (Hm * Hn) / Y) :=
        mul_le_mul ha'.le hZ (Nat.cast_nonneg _) (by positivity)
      have e : 4 * Y * (4 * (Hm * Hn) / Y) = 16 * (Hm * Hn) := by field_simp; ring
      linarith [S.hX1]
    have hm' : ((m : ℝ) ^ 4) ≤ (17 * (Hm * Hn)) ^ 3 := by
      have : ((m ^ 4 : ℕ) : ℝ) ≤ (((1 + a' * ⌊4 * Hm * Hn / Y⌋₊) ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast hm
      rw [Nat.cast_pow, Nat.cast_pow] at this
      exact this.trans (pow_le_pow_left₀ (by positivity) h1aZ 3)
    have := Real.rpow_le_rpow (by positivity) hm' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
      ← Real.rpow_natCast (17 * (Hm * Hn)), ← Real.rpow_mul (by positivity)] at this
    norm_num at this
    exact this
  intro p hp p' hp'
  by_cases hη : dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) = 0
  · rw [rawInner_eq_zero Y Hm Hn α β _ _ hη, hη]; simp
  · obtain ⟨hηa, hηb⟩ := mul_ne_zero_iff.1 hη
    obtain ⟨ha1, ha4⟩ := dyadicBump_ne_zero hηa
    obtain ⟨hb1, hb4⟩ := dyadicBump_ne_zero hηb
    rw [one_lt_div hY0] at ha1 hb1
    rw [div_lt_iff₀ hY0] at ha4 hb4
    have := norm_rawInner_le Y Hm Hn α β (log x ^ C) S.hα0 S.hβ0 S.hαb S.hβb S.hHm.le
      S.hHn.le hY0 (∏ i, p i) (∏ i, p' i) ha1 hb1 _ (hTgen _ (by linarith))
      (hTgen _ (by linarith))
    unfold rawM
    calc _ ≤ _ := this
      _ = _ := by ring

lemma raw_numeric (S : SharedSetting x a Y Hm Hn α β C)
    (hTY : (17 * (Hm * Hn)) ^ (3 / 4 : ℝ) * Y ≤ Hm * Hn) (K' : ℕ) (hK' : 1 ≤ K') (A : ℝ)
    (hc5 : log (5120 * K' ^ 2) + (4 * C + 3 + A) * log (log x) ≤ log x ^ (0.1 : ℝ)) :
    32 * K' ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) * rawM x Y Hm Hn C ≤
      1 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hY0 : 0 < Y := by linarith [S.hY]
  have hX0 : 0 < Hm * Hn := mul_pos S.hHm S.hHn
  have hZ : (⌊4 * Hm * Hn / Y⌋₊ : ℝ) ≤ 4 * (Hm * Hn) / Y := by
    have := Nat.floor_le (show 0 ≤ 4 * Hm * Hn / Y by have := S.hHm; have := S.hHn; positivity)
    rw [show 4 * (Hm * Hn) / Y = 4 * Hm * Hn / Y by ring]; exact this
  have hT17 : ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ (17 * (Hm * Hn)) ^ (3 / 4 : ℝ) :=
    Nat.floor_le (by positivity)
  have hlog17pos : 0 ≤ log (17 * (Hm * Hn)) := log_nonneg (by linarith [S.hX1])
  have hlogT : 0 ≤ 1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) := by
    have := Real.log_natCast_nonneg ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊; linarith
  have hlogT2 : 1 + log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ 2 * log x := by
    rcases Nat.eq_zero_or_pos ⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ with hT0 | hT0
    · rw [hT0]; simp only [Nat.cast_zero, log_zero]; linarith [S.hL1]
    · have hTr : (0 : ℝ) < (⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) := by exact_mod_cast hT0
      have : log ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ log (17 * (Hm * Hn)) := by
        calc _ ≤ log ((17 * (Hm * Hn)) ^ (3 / 4 : ℝ)) := log_le_log hTr hT17
          _ = 3 / 4 * log (17 * (Hm * Hn)) := Real.log_rpow (by positivity) _
          _ ≤ log (17 * (Hm * Hn)) := by nlinarith
      linarith [S.hlog]
  have hTX : ((⌊(17 * (Hm * Hn)) ^ (3 / 4 : ℝ)⌋₊ : ℕ) : ℝ) ≤ Hm * Hn / Y := by
    rw [le_div_iff₀ hY0]
    exact (mul_le_mul_of_nonneg_right hT17 hY0.le).trans hTY
  exact numeric_raw K' hK' (log x) (Hm * Hn) Y C A _ _ S.hL1 hX0 hY0 (Nat.cast_nonneg _) hZ
    (Nat.cast_nonneg _) hTX hlogT hlogT2 hc5

lemma maj_pair (A₀ : ℝ) (S : SharedSetting x a Y Hm Hn α β C) :
    ∀ p ∈ labelTuples x a, ∀ p' ∈ labelTuples x a,
      ‖majInner x A₀ Y Hm Hn α β (∏ i, p i) (∏ i, p' i)‖ ≤
        |dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y)| *
          majM x A₀ Y Hm Hn C := by
  have hY0 : 0 < Y := by linarith [S.hY]
  intro p hp p' hp'
  by_cases hη : dyadicBump ((∏ i, p i : ℕ) / Y) * dyadicBump ((∏ i, p' i : ℕ) / Y) = 0
  · rw [majInner_eq_zero x A₀ Y Hm Hn α β _ _ hη, hη]; simp
  · obtain ⟨hηa, hηb⟩ := mul_ne_zero_iff.1 hη
    have ha1 := (dyadicBump_ne_zero hηa).1
    have hb1 := (dyadicBump_ne_zero hηb).1
    rw [one_lt_div hY0] at ha1 hb1
    have := norm_majInner_le x A₀ Y Hm Hn α β (log x ^ C) S.hα0 S.hβ0 S.hαb S.hβb hY0
      (∏ i, p i) (∏ i, p' i) ha1 hb1
    unfold majM
    calc _ ≤ _ := this
      _ = _ := by ring

lemma maj_numeric (A₀ : ℝ) (hA₀ : 0 ≤ A₀) (S : SharedSetting x a Y Hm Hn α β C) (K' : ℕ)
    (hK' : 1 ≤ K') (A : ℝ)
    (hc6 : log (40960 * K' ^ 2) + (4 * C + 3 * A₀ + 3 + A) * log (log x) ≤ log x ^ (0.1 : ℝ)) :
    32 * K' ^ 2 * Y ^ 2 / exp (log x ^ (0.1 : ℝ)) * majM x A₀ Y Hm Hn C ≤
      1 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hY0 : 0 < Y := by linarith [S.hY]
  have hX0 : 0 < Hm * Hn := mul_pos S.hHm S.hHn
  have hμ : (volume (majorArcs x A₀ Y)).toReal ≤ 4 * log x ^ (3 * A₀) / Y :=
    ENNReal.toReal_le_of_le_ofReal (by have := S.hL1; positivity)
      (volume_majorArcs_le x A₀ Y S.hL1 hA₀ hY0)
  have hN : (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ 4 * (Hm * Hn) := by
    push_cast
    have h1 : (⌊2 * Hm⌋₊ : ℝ) ≤ 2 * Hm := Nat.floor_le (by linarith [S.hHm])
    have h2 : (⌊2 * Hn⌋₊ : ℝ) ≤ 2 * Hn := Nat.floor_le (by linarith [S.hHn])
    calc (⌊2 * Hm⌋₊ : ℝ) * ⌊2 * Hn⌋₊ ≤ 2 * Hm * (2 * Hn) :=
          mul_le_mul h1 h2 (Nat.cast_nonneg _) (by linarith [S.hHm])
      _ = 4 * (Hm * Hn) := by ring
  have hlogN : 0 ≤ 1 + log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) := by
    have := Real.log_natCast_nonneg (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊); linarith
  have hlogN2 : 1 + log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ 2 * log x := by
    rcases Nat.eq_zero_or_pos (⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊) with hN0 | hN0
    · rw [hN0]; simp only [Nat.cast_zero, log_zero]; linarith [S.hL1]
    · have hNr : (0 : ℝ) < ((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN0
      have : log (((⌊2 * Hm⌋₊ * ⌊2 * Hn⌋₊ : ℕ) : ℝ)) ≤ log (17 * (Hm * Hn)) :=
        log_le_log hNr (by linarith)
      linarith [S.hlog]
  exact numeric_major K' hK' (log x) (Hm * Hn) Y C A A₀ _ _ S.hL1 hX0 hY0 ENNReal.toReal_nonneg hμ
    (Nat.cast_nonneg _) hN hlogN hlogN2 hc6

end Pieces

/-- `(17X)^{3/4} Y ≤ X` when `Y` is below the largest label product (for large `x`). -/
lemma TY_bound {x c₁ Hm Hn Y : ℝ} {K : ℕ} {a : Fin K → ℝ} (hc₁ : 0 < c₁) (hxpos : 0 < x)
    (hL1 : 1 ≤ log x) (hab : ∀ i, a i < 0.2)
    (hc2 : 2 * K * log x ^ (0.2 : ℝ) + log 17 - log c₁ / 4 ≤ log x / 4)
    (hHm : 0 < Hm) (hHn : 0 < Hn) (h1 : c₁ * x ≤ Hm * Hn) (hY0 : 0 < Y)
    (hYm : Y < ∏ i, exp (2 * log x ^ a i)) :
    (17 * (Hm * Hn)) ^ (3 / 4 : ℝ) * Y ≤ Hm * Hn := by
  have hX0 : 0 < Hm * Hn := mul_pos hHm hHn
  have hYmax : ∏ i, exp (2 * log x ^ a i) ≤ exp (2 * K * log x ^ (0.2 : ℝ)) := by
    rw [← exp_sum]
    apply exp_le_exp.2
    calc ∑ i, 2 * log x ^ a i ≤ ∑ _i : Fin K, 2 * log x ^ (0.2 : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).le
          linarith
      _ = 2 * K * log x ^ (0.2 : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hX4 : Hm * Hn = (Hm * Hn) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have h17' : (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 := by
    calc (17 : ℝ) ^ (3 / 4 : ℝ) ≤ 17 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 17 := Real.rpow_one 17
  have hXq : exp ((log c₁ + log x) / 4) ≤ (Hm * Hn) ^ (1 / 4 : ℝ) := by
    rw [show (log c₁ + log x) / 4 = log (c₁ * x) * (1 / 4) by
      rw [log_mul hc₁.ne' hxpos.ne']; ring, Real.exp_mul, exp_log (by positivity)]
    exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have hkey : (17 : ℝ) ^ (3 / 4 : ℝ) * Y ≤ (Hm * Hn) ^ (1 / 4 : ℝ) := by
    calc (17 : ℝ) ^ (3 / 4 : ℝ) * Y ≤ 17 * exp (2 * K * log x ^ (0.2 : ℝ)) :=
          mul_le_mul h17' (hYm.le.trans hYmax) hY0.le (by norm_num)
      _ = exp (log 17 + 2 * K * log x ^ (0.2 : ℝ)) := by rw [exp_add, exp_log (by norm_num)]
      _ ≤ exp ((log c₁ + log x) / 4) := exp_le_exp.2 (by linarith)
      _ ≤ _ := hXq
  rw [Real.mul_rpow (by norm_num) hX0.le]
  calc (17 : ℝ) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (3 / 4 : ℝ) * Y
      = (Hm * Hn) ^ (3 / 4 : ℝ) * ((17 : ℝ) ^ (3 / 4 : ℝ) * Y) := by ring
    _ ≤ (Hm * Hn) ^ (3 / 4 : ℝ) * (Hm * Hn) ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = Hm * Hn := hX4.symm

lemma minInner_eq_zero (x A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ) (a' b' : ℕ)
    (h : dyadicBump (a' / Y) * dyadicBump (b' / Y) = 0) : minInner x A₀ Y Hm Hn α β a' b' = 0 := by
  unfold minInner sqWeight
  rcases mul_eq_zero.1 h with h | h <;> simp [h]


/-- Pad products are `< 2^{⌊L⌋+1}` for large `x`. -/
lemma padsProd_lt {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (hL1 : 1 ≤ log x) (hab : ∀ i, a i < 0.2)
    (hW3 : 2 * K * log x ^ (0.21 : ℝ) < 0.69 * log x) :
    ∀ pads ∈ padSet x a (padCount x), padsProd pads < 2 ^ (⌊log x⌋₊ + 1) := by
  intro pads hpads
  have hent : ∀ i, ∀ v ∈ primeGroup x (a i), (v : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) := by
    intro i v hv
    refine (le_of_mem_primeGroup hv).2.trans (exp_le_exp.2 ?_)
    have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).le
    linarith
  have hJ : (padCount x : ℝ) ≤ log x ^ (0.01 : ℝ) := Nat.floor_le (by positivity)
  have hb : (padsProd pads : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) ^ (K * padCount x) := by
    unfold padsProd; push_cast
    calc ∏ i, ∏ j, (pads i j : ℝ) ≤
        ∏ _i : Fin K, ∏ _j : Fin (padCount x), exp (2 * log x ^ (0.2 : ℝ)) :=
          prod_le_prod (fun i _ => prod_nonneg fun j _ => Nat.cast_nonneg _) fun i _ =>
            prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ =>
              hent i _ (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hpads i) j)
      _ = _ := by simp [prod_const, ← pow_mul, mul_comm]
  have hexp : exp (2 * log x ^ (0.2 : ℝ)) ^ (K * padCount x) ≤
      exp (2 * K * log x ^ (0.21 : ℝ)) := by
    rw [← exp_nat_mul]
    apply exp_le_exp.2
    have hp : log x ^ (0.01 : ℝ) * log x ^ (0.2 : ℝ) = log x ^ (0.21 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    have h02 : 0 ≤ log x ^ (0.2 : ℝ) := by positivity
    push_cast
    calc (K : ℝ) * (padCount x : ℝ) * (2 * log x ^ (0.2 : ℝ)) ≤
          K * log x ^ (0.01 : ℝ) * (2 * log x ^ (0.2 : ℝ)) := by gcongr
      _ = 2 * K * (log x ^ (0.01 : ℝ) * log x ^ (0.2 : ℝ)) := by ring
      _ = 2 * K * log x ^ (0.21 : ℝ) := by rw [hp]
  have h2 : exp (2 * K * log x ^ (0.21 : ℝ)) < (2 : ℝ) ^ (⌊log x⌋₊ + 1) := by
    have hlog2 := Real.log_two_gt_d9
    calc exp (2 * K * log x ^ (0.21 : ℝ)) < exp (log x * log 2) := by
          apply exp_lt_exp.2
          have : 0.69 * log x ≤ log x * log 2 := by nlinarith
          linarith
      _ = (2 : ℝ) ^ log x := by rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
      _ ≤ (2 : ℝ) ^ ((⌊log x⌋₊ + 1 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
            have := Nat.lt_floor_add_one (log x); push_cast; linarith)
      _ = (2 : ℝ) ^ (⌊log x⌋₊ + 1) := Real.rpow_natCast _ _
  exact_mod_cast hb.trans_lt (hexp.trans_lt h2)

/-- The large-`Y` case: both sides vanish. -/
lemma pad_lift_large_Y {x : ℝ} {K : ℕ} {a : Fin K → ℝ} (A₀ Y Hm Hn : ℝ) (α β : ℕ → ℂ)
    (hY0 : 0 < Y) (hYm : ∏ i, exp (2 * log x ^ a i) ≤ Y) :
    minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
      ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k = 0 := by
  have hz : ∀ p ∈ labelTuples x a, dyadicBump ((∏ i, p i : ℕ) / Y) = 0 := by
    intro p hp
    apply dyadicBump_eq_zero_of_le_one
    rw [div_le_one hY0]
    exact (prod_le_of_mem_labelTuples hp).trans hYm
  have hmin : minorSquare x a A₀ Y Hm Hn α β = 0 := by
    unfold minorSquare
    rw [sum_eq_zero fun p hp => sum_eq_zero fun q _ => by
      split_ifs
      · exact minInner_eq_zero x A₀ Y Hm Hn α β _ _ (by rw [hz p hp, zero_mul])
      · rfl, mul_zero]
  have hpair : ∀ k, dyadPairingSTS x a A₀ Y Hm Hn α β k = 0 := by
    intro k
    unfold dyadPairingSTS
    rw [opPairing_slotSym]
    unfold opPairing
    rw [sum_eq_zero fun s _ => sum_eq_zero fun s' _ => ?_, mul_zero]
    by_cases hT : rowOp x a A₀ Y (padCount x) (2 ^ k) (2 ^ k * Y * Hm) Hn s s' = 0
    · rw [hT, mul_zero, zero_mul]
    · exfalso
      have hη := (rowOp_ne_zero hT).2.2
      have hl : (lastProd s.1.2 : ℝ) ≤ ∏ i, exp (2 * log x ^ a i) := by
        have hcand := (mem_product.1 (mem_filter.1 s.2).1).2
        unfold lastProd; push_cast
        exact prod_le_prod (fun i _ => Nat.cast_nonneg _) fun i _ =>
          (le_of_mem_primeGroup (Fintype.mem_piFinset.1 (Fintype.mem_piFinset.1 hcand i) _)).2
      exact hη (dyadicBump_eq_zero_of_le_one (by rw [div_le_one hY0]; exact hl.trans hYm))
  rw [hmin, sum_eq_zero fun k _ => by rw [hpair k, mul_zero], sub_zero]

/-- The final numerical step of D8bc. -/
lemma pad_lift_numeric {x Y Hm Hn A P : ℝ} {K J : ℕ} (hK : 1 ≤ K) (hL1 : 1 ≤ log x)
    (hJ : (J : ℝ) ≤ log x ^ (0.01 : ℝ)) (hP : P = exp (log x ^ (0.1 : ℝ)))
    (rM mM : ℝ) (hrm : 0 ≤ rM) (hmm : 0 ≤ mM)
    (hr : 32 * ((2 * K : ℕ) : ℝ) ^ 2 * Y ^ 2 / P * rM ≤ 1 * (Hm * Hn * Y * log x ^ (-(A + 1))))
    (hm : 32 * ((2 * K : ℕ) : ℝ) ^ 2 * Y ^ 2 / P * mM ≤ 1 * (Hm * Hn * Y * log x ^ (-(A + 1)))) :
    16 * Y ^ 2 * ((K : ℝ) * ((J : ℝ) ^ 2 + 2 * J) * (2 / P)) * (2 * (rM + mM)) ≤
      4 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hPpos : 0 < P := by rw [hP]; exact exp_pos _
  have hJL : (K : ℝ) * ((J : ℝ) ^ 2 + 2 * J) ≤ ((2 * K : ℕ) : ℝ) ^ 2 * log x := by
    have h01 : 1 ≤ log x ^ (0.01 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have h02 : log x ^ (0.01 : ℝ) * log x ^ (0.01 : ℝ) ≤ log x := by
      rw [← Real.rpow_add (by linarith)]
      calc log x ^ (0.01 + 0.01 : ℝ) ≤ log x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = log x := Real.rpow_one _
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    have hJJ : (J : ℝ) ^ 2 + 2 * J ≤ 4 * log x := by nlinarith
    push_cast
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    calc (K : ℝ) * ((J : ℝ) ^ 2 + 2 * J) ≤ K * (4 * log x) :=
          mul_le_mul_of_nonneg_left hJJ (by linarith)
      _ ≤ K * K * (4 * log x) := by
          have : (0 : ℝ) ≤ K * (4 * log x) := by positivity
          nlinarith
      _ = (2 * (K : ℝ)) ^ 2 * log x := by ring
  have hLA : log x * (Hm * Hn * Y * log x ^ (-(A + 1))) = Hm * Hn * Y * log x ^ (-A) := by
    have hL0 : 0 < log x := by linarith
    rw [show -A = -(A + 1) + 1 by ring, Real.rpow_add hL0, Real.rpow_one]; ring
  have hL0 : 0 ≤ 2 * log x := by linarith
  set Q := 32 * ((2 * K : ℕ) : ℝ) ^ 2 * Y ^ 2 / P
  have hQ : 0 ≤ Q := by positivity
  calc 16 * Y ^ 2 * ((K : ℝ) * ((J : ℝ) ^ 2 + 2 * J) * (2 / P)) * (2 * (rM + mM))
      ≤ 16 * Y ^ 2 * (((2 * K : ℕ) : ℝ) ^ 2 * log x * (2 / P)) * (2 * (rM + mM)) := by
        gcongr
    _ = 2 * log x * (Q * rM) + 2 * log x * (Q * mM) := by
        simp only [Q]; field_simp; ring
    _ ≤ 2 * log x * (1 * (Hm * Hn * Y * log x ^ (-(A + 1)))) +
        2 * log x * (1 * (Hm * Hn * Y * log x ^ (-(A + 1)))) :=
        add_le_add (mul_le_mul_of_nonneg_left hr hL0) (mul_le_mul_of_nonneg_left hm hL0)
    _ = 4 * (Hm * Hn * Y * log x ^ (-A)) := by rw [← hLA]; ring

/-- **D8bc at one `x`.** -/
lemma pad_lift_at {x c₁ c₂ δ C A₀ A Hm Hn Y : ℝ} {K : ℕ} (hK : 1 ≤ K) {a : Fin K → ℝ}
    (hab : ∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) (α β : ℕ → ℂ) (hc₁ : 0 < c₁) (hA₀ : 0 < A₀)
    (hxpos : 0 < x) (hL1 : 1 ≤ log x)
    (hc2 : 2 * K * log x ^ (0.2 : ℝ) + log 17 - log c₁ / 4 ≤ log x / 4)
    (hc3 : 1 + log (17 * c₂) ≤ log x) (hc7 : log (1 / c₁) ≤ log x)
    (hc5 : log (5120 * ((2 * K : ℕ) : ℝ) ^ 2) + (4 * C + 3 + (A + 1)) * log (log x) ≤
      log x ^ (0.1 : ℝ))
    (hc6 : log (40960 * ((2 * K : ℕ) : ℝ) ^ 2) + (4 * C + 3 * A₀ + 3 + (A + 1)) * log (log x) ≤
      log x ^ (0.1 : ℝ))
    (hW1 : 2 * log x ^ (0.2 : ℝ) ≤ log x ^ (0.24 : ℝ))
    (hW2 : log 5 + 2 * K * log x ^ (0.2 : ℝ) < log x ^ (0.24 : ℝ))
    (hW3 : 2 * K * log x ^ (0.21 : ℝ) < 0.69 * log x)
    (hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j))
    (hdisj : ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)))
    (hm : x ^ δ ≤ Hm) (hn : x ^ δ ≤ Hn) (h1 : c₁ * x ≤ Hm * Hn) (h2 : Hm * Hn ≤ c₂ * x)
    (hαs : ∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
      ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m)
    (hβs : ∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n)
    (hαb : ∀ m, ‖α m‖ ≤ log x ^ C) (hβb : ∀ n, ‖β n‖ ≤ log x ^ C) (hY : 1 ≤ Y) :
    ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
        ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
      4 * (Hm * Hn * Y * log x ^ (-A)) := by
  have hVpos : ∀ i, 0 < groupReciprocalSum x (a i) := fun i => by linarith [hV i]
  have hY0 : 0 < Y := by linarith
  have hHm : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hm
  have hHn : 0 < Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hn
  have hc₂ : 0 < c₂ := by
    by_contra h; push Not at h
    have : c₂ * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hxpos.le
    have := mul_pos hHm hHn
    linarith only [this, h2, ‹c₂ * x ≤ 0›]
  have hX1 : 1 ≤ Hm * Hn := by
    have : 1 ≤ c₁ * x := by
      rw [show c₁ * x = exp (log c₁ + log x) by rw [exp_add, exp_log hc₁, exp_log hxpos]]
      apply one_le_exp
      have : log (1 / c₁) = - log c₁ := by rw [one_div, log_inv]
      linarith
    linarith
  have hα0 : α 0 = 0 := by
    by_contra h
    obtain ⟨J, -, -, hJ⟩ := hαs
    exact absurd (hJ 0 h).2.1 (lt_irrefl 0)
  have hβ0 : β 0 = 0 := by
    by_contra h
    exact absurd (hβs 0 h).2.2.1 (lt_irrefl 0)
  have hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x := by
    have : log (17 * (Hm * Hn)) ≤ log (17 * c₂) + log x := by
      rw [← log_mul (by positivity) hxpos.ne']
      exact log_le_log (by positivity) (by linarith only [h2])
    linarith
  have S : SharedSetting x a Y Hm Hn α β C :=
    ⟨hL1, hxpos, hHm, hHn, hY, hX1, hα0, hβ0, hαb, hβb, hV, fun i => (hab i).1, hlog⟩
  have hRHS : 0 ≤ 4 * (Hm * Hn * Y * log x ^ (-A)) := by
    have : 0 < log x := by linarith
    positivity
  by_cases hYm : ∏ i, exp (2 * log x ^ a i) ≤ Y
  · rw [pad_lift_large_Y A₀ Y Hm Hn α β hY0 hYm, norm_zero]; exact hRHS
  push Not at hYm
  have hTY := TY_bound hc₁ hxpos hL1 (fun i => (hab i).2) hc2 hHm hHn h1 hY0 hYm
  have hent : ∀ i, ∀ v ∈ primeGroup x (a i), (v : ℝ) ≤ exp (2 * log x ^ (0.2 : ℝ)) := by
    intro i v hv
    refine (le_of_mem_primeGroup hv).2.trans (exp_le_exp.2 ?_)
    have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).2.le
    linarith
  have hYmax : ∏ i, exp (2 * log x ^ a i) ≤ exp (2 * K * log x ^ (0.2 : ℝ)) := by
    rw [← exp_sum]
    apply exp_le_exp.2
    calc ∑ i, 2 * log x ^ a i ≤ ∑ _i : Fin K, 2 * log x ^ (0.2 : ℝ) := by
          refine sum_le_sum fun i _ => ?_
          have := Real.rpow_le_rpow_of_exponent_le hL1 (hab i).2.le
          linarith
      _ = 2 * K * log x ^ (0.2 : ℝ) := by
          rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hYW : 5 * Y < sieveLevel x := by
    unfold sieveLevel
    calc 5 * Y < 5 * exp (2 * K * log x ^ (0.2 : ℝ)) := by linarith [hYm.trans_le hYmax]
      _ = exp (log 5 + 2 * K * log x ^ (0.2 : ℝ)) := by rw [exp_add, exp_log (by norm_num)]
      _ < exp (log x ^ (0.24 : ℝ)) := exp_lt_exp.2 hW2
  have hgW : ∀ v ∈ groupPrimes x a, (v : ℝ) ≤ sieveLevel x := by
    intro v hv
    obtain ⟨i, -, hi⟩ := mem_biUnion.1 hv
    exact (hent i v hi).trans (exp_le_exp.2 hW1)
  have hαS : ∀ m, α m ≠ 0 → Hm ≤ m ∧ (m : ℝ) ≤ 2 * Hm ∧ IsRough (sieveLevel x) m := by
    intro m hm0
    obtain ⟨J', -, hJ', hJ⟩ := hαs
    have h := hJ m hm0
    exact ⟨(hJ' h.1).1, (hJ' h.1).2, h.2⟩
  rw [minorSquare_sub_pairings A₀ Y Hm Hn α β ⌊log x⌋₊ hK hY0 hHm hHn hdisj hVpos hα0 hαS hβs
    hgW hYW (padsProd_lt hL1 (fun i => (hab i).2) hW3)]
  set P := exp (log x ^ (0.1 : ℝ)) with hP
  have hPpos : 0 < P := exp_pos _
  have hMu : ∀ i, ∀ u ∈ primeGroup x (a i), 1 / ((u : ℝ) * groupReciprocalSum x (a i)) ≤ 2 / P := by
    intro i u hu
    have hu1 : P ≤ u := le_trans (exp_le_exp.2 (Real.rpow_le_rpow_of_exponent_le hL1 (hab i).1.le))
      (le_of_mem_primeGroup hu).1
    have hVi := hV i
    rw [div_le_div_iff₀ (mul_pos (hPpos.trans_le hu1) (hVpos i)) hPpos]
    have h1 : P * (1 / 2) ≤ (u : ℝ) * groupReciprocalSum x (a i) :=
      mul_le_mul hu1 hVi (by norm_num) (Nat.cast_nonneg u)
    linarith only [h1]
  have hd := diff_bound (x := x) (a := a) A₀ Y Hm Hn α β hY0 hVpos hα0 hβ0 _
    (rawM x Y Hm Hn C + majM x A₀ Y Hm Hn C)
    (fun p q => badMass_le (J := padCount x) hVpos (2 / P) (by positivity) hMu p q)
    (add_nonneg (rawM_nonneg S) (majM_nonneg A₀ S))
    (fun p hp q hq _ => (raw_pair S p hp q hq).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (majM_nonneg A₀ S)) (abs_nonneg _)))
    (fun p hp q hq _ => (maj_pair A₀ S p hp q hq).trans (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (rawM_nonneg S)) (abs_nonneg _)))
  refine hd.trans ?_
  have hK2 : 1 ≤ 2 * K := by omega
  exact pad_lift_numeric hK hL1 (Nat.floor_le (by positivity)) hP _ _ (rawM_nonneg S)
    (majM_nonneg A₀ S) (raw_numeric S hTY (2 * K) hK2 (A + 1) hc5)
    (maj_numeric A₀ hA₀.le S (2 * K) hK2 (A + 1) hc6)

/-- **D8bc (PROVED).** -/
theorem pad_lift (δ C c₁ c₂ : ℝ) (hc₁ : 0 < c₁) : PadLiftStmt δ C c₁ c₂ := by
  intro A₀ hA₀ K hK a ha hab A hA
  have hapos : ∀ i, 0 < a i := fun i => (by norm_num : (0 : ℝ) < 0.1).trans (hab i).1
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hE2 : ∀ᶠ L : ℝ in Filter.atTop, 2 * K * L ^ (0.2 : ℝ) + log 17 - log c₁ / 4 ≤ L / 4 := by
    have e1 := eventually_rpow_le_rpow (b := 0.2) (c := 1) (by norm_num) (ε := 1 / (16 * K))
      (by positivity)
    have e2 := Filter.tendsto_id.eventually_ge_atTop (8 * (log 17 - log c₁ / 4))
    filter_upwards [e1, e2, Filter.eventually_gt_atTop 0] with L h1 h2 h3
    rw [Real.rpow_one] at h1
    have : 2 * K * L ^ (0.2 : ℝ) ≤ L / 8 := by
      calc 2 * K * L ^ (0.2 : ℝ) ≤ 2 * K * (1 / (16 * K) * L) := by gcongr
        _ = L / 8 := by field_simp; ring
    simp only [id] at h2
    linarith
  have hE3 : ∀ᶠ L : ℝ in Filter.atTop, 1 + log (17 * c₂) ≤ L ∧ 1 ≤ L ∧ log (1 / c₁) ≤ L :=
    (Filter.eventually_ge_atTop (1 + log (17 * c₂))).and
      ((Filter.eventually_ge_atTop 1).and (Filter.eventually_ge_atTop (log (1 / c₁))))
  have hE5 : ∀ᶠ L : ℝ in Filter.atTop,
      log (5120 * ((2 * K : ℕ) : ℝ) ^ 2) + (4 * C + 3 + (A + 1)) * log L ≤ L ^ (0.1 : ℝ) := by
    filter_upwards [eventually_log_le_rpow (a := 0.1) (by norm_num) (4 * C + 3 + (A + 1))
      (log (5120 * ((2 * K : ℕ) : ℝ) ^ 2)) (ε := 1) one_pos] with L h
    linarith
  have hE6 : ∀ᶠ L : ℝ in Filter.atTop,
      log (40960 * ((2 * K : ℕ) : ℝ) ^ 2) + (4 * C + 3 * A₀ + 3 + (A + 1)) * log L ≤
        L ^ (0.1 : ℝ) := by
    filter_upwards [eventually_log_le_rpow (a := 0.1) (by norm_num) (4 * C + 3 * A₀ + 3 + (A + 1))
      (log (40960 * ((2 * K : ℕ) : ℝ) ^ 2)) (ε := 1) one_pos] with L h
    linarith
  have hEW : ∀ᶠ L : ℝ in Filter.atTop, 2 * L ^ (0.2 : ℝ) ≤ L ^ (0.24 : ℝ) ∧
      log 5 + 2 * K * L ^ (0.2 : ℝ) < L ^ (0.24 : ℝ) ∧ 2 * K * L ^ (0.21 : ℝ) < 0.69 * L := by
    have e1 := eventually_rpow_le_rpow (b := 0.2) (c := 0.24) (by norm_num) (ε := 1 / (4 * K))
      (by positivity)
    have e2 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.24)).eventually_gt_atTop (2 * log 5)
    have e3 := eventually_rpow_le_rpow (b := 0.21) (c := 1) (by norm_num) (ε := 1 / (4 * K))
      (by positivity)
    filter_upwards [e1, e2, e3, Filter.eventually_gt_atTop 0] with L h1 h2 h3 h4
    rw [Real.rpow_one] at h3
    have hp : 0 < L ^ (0.24 : ℝ) := by positivity
    have hA : 2 * K * L ^ (0.2 : ℝ) ≤ L ^ (0.24 : ℝ) / 2 := by
      calc 2 * K * L ^ (0.2 : ℝ) ≤ 2 * K * (1 / (4 * K) * L ^ (0.24 : ℝ)) := by gcongr
        _ = L ^ (0.24 : ℝ) / 2 := by field_simp; ring
    refine ⟨?_, ?_, ?_⟩
    · have : 2 * L ^ (0.2 : ℝ) ≤ 2 * K * L ^ (0.2 : ℝ) := by
        have := Real.rpow_nonneg h4.le (0.2 : ℝ); nlinarith
      linarith
    · linarith
    · calc 2 * K * L ^ (0.21 : ℝ) ≤ 2 * K * (1 / (4 * K) * L) := by gcongr
        _ = L / 2 := by field_simp; ring
        _ < 0.69 * L := by linarith
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.1
    (hE2.and (hE3.and (hE5.and (hE6.and hEW))))
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1
    ((eventually_groupReciprocalSum_ge a hapos).and (eventually_disjoint_groups a ha hapos))
  refine ⟨4, max x₁ (exp L₀), fun x Hm Hn hx hm hn h1 h2 α β hαs hβs hαb hβb Y hY => ?_⟩
  have hxpos : 0 < x := lt_of_lt_of_le (exp_pos _) (le_of_max_le_right hx)
  have hLL : L₀ ≤ log x := (Real.le_log_iff_exp_le hxpos).2 (le_of_max_le_right hx)
  obtain ⟨hc2, ⟨hc3, hL1, hc7⟩, hc5, hc6, hW1, hW2, hW3⟩ := hL₀ (log x) hLL
  obtain ⟨hV, hdisj⟩ := hx₁ x (le_of_max_le_left hx)
  exact pad_lift_at hK hab α β hc₁ hA₀ hxpos hL1 hc2 hc3 hc7 hc5 hc6 hW1 hW2 hW3 hV hdisj hm hn
    h1 h2 hαs hβs hαb hβb hY

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_norm_minorSquare_sub_sum_dyadPairingSTS_le`, the published statement `norm_minorSquare_sub_sum_dyadPairingSTS_le` verbatim, proved from the
development. -/

namespace ArtinPrimitiveRoots

open Real Finset

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real Finset
theorem solution (δ C c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
    ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ A : ℝ, 0 < A →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
                ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) :=
  L102D.pad_lift δ C c₁ c₂ hc₁
end

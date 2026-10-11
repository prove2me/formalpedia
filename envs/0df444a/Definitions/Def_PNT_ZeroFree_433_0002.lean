-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0002
-- name    : PNT_ZeroFree_433_0002
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-10T11:59:12.81524+00:00
-- url     : https://prove2.me/theorems/9783d299-48c6-42b1-b542-87b8b5daaf17
-- title:
--   Zero-free region foundations: Mellin.ExponentialSmoothing [0002]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L14-L647

import Definitions.Def_PNT_ZeroFree_433_0001

/- Supporting source modules for the zero-free-region proof.
Ported and checked against Lean 4.33.1 / Mathlib 0df444a.
Original source attribution:
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L14-L647
-/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Mellin.ExponentialSmoothing
section
namespace OAI

open scoped BigOperators
open MulChar AddChar

open scoped BigOperators

namespace AnalyticBridge

variable {Ω : Type*}

theorem weighted_cauchy_sq
    (S : Finset Ω) (w U V : Ω → ℂ) :
    ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
  have htri : ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
      ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
    calc
      ‖∑ ω ∈ S, w ω * U ω * star (V ω)‖ ≤
          ∑ ω ∈ S, ‖w ω * U ω * star (V ω)‖ := norm_sum_le _ _
      _ = ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ := by
        apply Finset.sum_congr rfl
        intro ω hω
        simp [ ]
  have hnonneg : 0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖ :=
    Finset.sum_nonneg (by intro ω hω; positivity)
  have hsq :
      (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2 ≤
        (∑ ω ∈ S, ‖w ω‖ * ‖U ω‖ ^ 2) *
          (∑ ω ∈ S, ‖w ω‖ * ‖V ω‖ ^ 2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
      (fun ω hω => by positivity) (fun ω hω => by positivity)
    intro ω hω
    (convert! le_refl ((‖w ω‖ * ‖U ω‖ * ‖V ω‖) ^ 2) using 1 ; try ring)
  exact (sq_le_sq₀ (norm_nonneg _) hnonneg).2 htri |>.trans hsq

theorem fiber_mass_bound {Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (weight : Ω → ℝ) (A : Λ → ℂ) (M : ℝ)
    (hmap : ∀ ω ∈ S, label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, weight ω) ≤ M) :
    (∑ ω ∈ S, weight ω * ‖A (label ω)‖ ^ 2) ≤
      M * (∑ a ∈ T, ‖A a‖ ^ 2) := by
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    (∑ a ∈ T, ∑ ω ∈ S with label ω = a,
        weight ω * ‖A (label ω)‖ ^ 2) =
      ∑ a ∈ T, (∑ ω ∈ S with label ω = a, weight ω) * ‖A a‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        have hl : label ω = a := (Finset.mem_filter.mp hω).2
        rw [hl]
    _ ≤ ∑ a ∈ T, M * ‖A a‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right (hfiber a ha) (sq_nonneg _)
    _ = M * (∑ a ∈ T, ‖A a‖ ^ 2) := by rw [Finset.mul_sum]

theorem reassembled_bilinear_bound
    {Λ₁ Λ₂ : Type*} [DecidableEq Λ₁] [DecidableEq Λ₂]
    (S : Finset Ω) (T₁ : Finset Λ₁) (T₂ : Finset Λ₂)
    (label₁ : Ω → Λ₁) (label₂ : Ω → Λ₂)
    (w : Ω → ℂ) (A : Λ₁ → ℂ) (B : Λ₂ → ℂ)
    (M₁ M₂ : ℝ)
    (hM₁ : 0 ≤ M₁)
    (hmap₁ : ∀ ω ∈ S, label₁ ω ∈ T₁)
    (hmap₂ : ∀ ω ∈ S, label₂ ω ∈ T₂)
    (hfiber₁ : ∀ a ∈ T₁,
      (∑ ω ∈ S with label₁ ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T₂,
      (∑ ω ∈ S with label₂ ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
  have hcs := weighted_cauchy_sq S w (fun ω => A (label₁ ω))
    (fun ω => B (label₂ ω))
  have hside₁ := fiber_mass_bound S T₁ label₁
    (fun ω => ‖w ω‖) A M₁ hmap₁ hfiber₁
  have hside₂ := fiber_mass_bound S T₂ label₂
    (fun ω => ‖w ω‖) B M₂ hmap₂ hfiber₂
  calc
    ‖∑ ω ∈ S, w ω * A (label₁ ω) * star (B (label₂ ω))‖ ^ 2 ≤
      (∑ ω ∈ S, ‖w ω‖ * ‖A (label₁ ω)‖ ^ 2) *
        (∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2) := hcs
    _ ≤ (M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T₂, ‖B a‖ ^ 2) := by
      have hlow₂ :
          0 ≤ ∑ ω ∈ S, ‖w ω‖ * ‖B (label₂ ω)‖ ^ 2 :=
        Finset.sum_nonneg (by intro ω hω; positivity)
      have hupp₁ : 0 ≤ M₁ * ∑ a ∈ T₁, ‖A a‖ ^ 2 := by positivity
      exact mul_le_mul hside₁ hside₂ hlow₂ hupp₁

theorem square_label_count (F : Finset ℕ) (y E : ℕ)
    (hy : y ≠ 0) (hF : ∀ f ∈ F, f ^ 2 * E ∣ y) :
    F.card ≤ y.divisors.card := by
  apply Finset.card_le_card
  intro f hf
  apply Nat.mem_divisors.mpr
  constructor
  · apply Nat.dvd_trans (Nat.dvd_mul_right f (f * E))
    simpa [pow_two, mul_assoc] using hF f hf
  · exact hy

theorem four_factor_label_count (Q : Finset (ℕ × ℕ × ℕ × ℕ))
    (F : ℕ) (hF : F ≠ 0)
    (hQ : ∀ q ∈ Q, q.1 * q.2.1 * q.2.2.1 * q.2.2.2 = F) :
    Q.card ≤ F.divisors.card ^ 4 := by
  let D := F.divisors
  have hsubset : Q ⊆ D ×ˢ (D ×ˢ (D ×ˢ D)) := by
    intro q hq
    rcases q with ⟨J, C, e, v⟩
    have hprod := hQ (J, C, e, v) hq
    have hJ : J ∣ F := by
      refine ⟨C * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = J * (C * e * v) := by ring
    have hC : C ∣ F := by
      refine ⟨J * e * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = C * (J * e * v) := by ring
    have he : e ∣ F := by
      refine ⟨J * C * v, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = e * (J * C * v) := by ring
    have hv : v ∣ F := by
      refine ⟨J * C * e, ?_⟩
      calc F = J * C * e * v := hprod.symm
           _ = v * (J * C * e) := by ring
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hJ, hF⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Nat.mem_divisors.mpr ⟨hC, hF⟩
    apply Finset.mem_product.mpr
    exact ⟨Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩
  have hcard := Finset.card_le_card hsubset
  simpa [D, Finset.card_product, pow_succ, pow_zero, mul_assoc] using hcard

structure CRTChoice where
  J : ℕ
  C : ℕ
  e : ℕ
  v : ℕ
  s : ℕ
  J2 : ℕ
  b1 : ℕ
  b2 : ℕ
  A1 : ℕ
  A2 : ℕ
  d : ℕ
  kpp : ℕ
  deriving DecidableEq

private def CRTChoice.coordinates (q : CRTChoice) :
    (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) × (ℕ × ℕ × ℕ × ℕ) :=
  ((q.J, q.C, q.e, q.v), (q.s, q.J2, q.b1, q.b2),
    (q.A1, q.A2, q.d, q.kpp))

private theorem CRTChoice.coordinates_injective :
    Function.Injective CRTChoice.coordinates := by
  intro x y h
  cases x
  cases y
  simp only [CRTChoice.coordinates, Prod.mk.injEq] at h ⊢
  simp_all

theorem fixed_crt_choice_count
    (Q : Finset CRTChoice) (F K b0 : ℕ)
    (hF : F ≠ 0) (hK : K ≠ 0) (hb0 : b0 ≠ 0)
    (hQ : ∀ q ∈ Q,
      q.J * q.C * q.e * q.v = F ∧
      q.J = q.s * q.J2 ∧
      q.b1 * q.b2 = b0 ^ 2 * q.J2 ^ 2 * q.s ∧
      q.A1 ∣ q.b1 * q.b2 ∧ q.A2 ∣ q.b1 * q.b2 ∧
      q.d ∣ F * b0 ∧ q.d * q.e * q.kpp = K) :
    Q.card ≤ F.divisors.card ^ 6 *
      (b0 ^ 2 * F ^ 3).divisors.card ^ 4 *
      (F * b0).divisors.card * K.divisors.card := by
  let DF := F.divisors
  let P := b0 ^ 2 * F ^ 3
  let DP := P.divisors
  let DFB := (F * b0).divisors
  let DK := K.divisors
  let T := (DF ×ˢ (DF ×ˢ (DF ×ˢ DF))) ×ˢ
      ((DF ×ˢ (DF ×ˢ (DP ×ˢ DP))) ×ˢ
      (DP ×ˢ (DP ×ˢ (DFB ×ˢ DK))))
  have hP : P ≠ 0 := by simp [P, hb0, hF]
  have hmap : Set.MapsTo CRTChoice.coordinates (Q : Set CRTChoice) (T : Set _) := by
    intro q hq
    obtain ⟨hlabel, hJ, hbprod, hA1, hA2, hd, hrow⟩ := hQ q hq
    have hJdvd : q.J ∣ F := by
      refine ⟨q.C * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.J * (q.C * q.e * q.v) := by ring
    have hsF : q.s ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.J2, ?_⟩
      exact hJ
    have hJ2F : q.J2 ∣ F := by
      apply Nat.dvd_trans _ hJdvd
      refine ⟨q.s, ?_⟩
      simpa [mul_comm] using hJ
    have hcore : q.J2 ^ 2 * q.s ∣ F ^ 3 := by
      convert! mul_dvd_mul (pow_dvd_pow_of_dvd hJ2F 2) hsF using 1 ; try ring
    have hbP : q.b1 * q.b2 ∣ P := by
      rw [hbprod]
      convert! Nat.mul_dvd_mul_left (b0 ^ 2) hcore using 1 ; try ring
    have hb1P : q.b1 ∣ P := (Nat.dvd_mul_right q.b1 q.b2).trans hbP
    have hb2P : q.b2 ∣ P := (Nat.dvd_mul_left q.b2 q.b1).trans hbP
    have hkppK : q.kpp ∣ K := by
      refine ⟨q.d * q.e, ?_⟩
      calc K = q.d * q.e * q.kpp := hrow.symm
           _ = q.kpp * (q.d * q.e) := by ring
    have hC : q.C ∣ F := by
      refine ⟨q.J * q.e * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.C * (q.J * q.e * q.v) := by ring
    have he : q.e ∣ F := by
      refine ⟨q.J * q.C * q.v, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.e * (q.J * q.C * q.v) := by ring
    have hv : q.v ∣ F := by
      refine ⟨q.J * q.C * q.e, ?_⟩
      calc F = q.J * q.C * q.e * q.v := hlabel.symm
           _ = q.v * (q.J * q.C * q.e) := by ring
    change CRTChoice.coordinates q ∈ T
    simp only [CRTChoice.coordinates, T, Finset.mem_product]
    exact ⟨⟨Nat.mem_divisors.mpr ⟨hJdvd, hF⟩,
      Nat.mem_divisors.mpr ⟨hC, hF⟩,
      Nat.mem_divisors.mpr ⟨he, hF⟩,
      Nat.mem_divisors.mpr ⟨hv, hF⟩⟩,
      ⟨⟨Nat.mem_divisors.mpr ⟨hsF, hF⟩,
        Nat.mem_divisors.mpr ⟨hJ2F, hF⟩,
        Nat.mem_divisors.mpr ⟨hb1P, hP⟩,
        Nat.mem_divisors.mpr ⟨hb2P, hP⟩⟩,
       ⟨Nat.mem_divisors.mpr ⟨hA1.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hA2.trans hbP, hP⟩,
        Nat.mem_divisors.mpr ⟨hd, mul_ne_zero hF hb0⟩,
        Nat.mem_divisors.mpr ⟨hkppK, hK⟩⟩⟩⟩
  have hcard := Finset.card_le_card_of_injOn CRTChoice.coordinates hmap
    CRTChoice.coordinates_injective.injOn
  convert! hcard using 1
  simp [T, DF, DP, DFB, DK, P, Finset.card_product]
  ring

theorem b0_count_scale
    (b0 J2 s c B : ℝ)
    (hb0 : 0 ≤ b0) (hJ2 : 0 ≤ J2) (hs : 0 ≤ s)
    (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hsc : s ≤ c)
    (hprod : b0 ^ 2 * J2 ^ 2 * s ≤ B ^ 2) :
    b0 * (s * J2) ≤ B * Real.sqrt c := by
  have hl : 0 ≤ b0 * (s * J2) := by positivity
  have hr : 0 ≤ B * Real.sqrt c := by positivity
  apply (sq_le_sq₀ hl hr).mp
  calc
    (b0 * (s * J2)) ^ 2 = (b0 ^ 2 * J2 ^ 2 * s) * s := by ring
    _ ≤ B ^ 2 * s := mul_le_mul_of_nonneg_right hprod hs
    _ ≤ B ^ 2 * c := mul_le_mul_of_nonneg_left hsc (sq_nonneg _)
    _ = (B * Real.sqrt c) ^ 2 := by rw [mul_pow, Real.sq_sqrt hc]

private def bit6 (b : Bool) : ZMod 6 := if b then 1 else 0
def localExponent (π ε1 ε2 : Bool) : ZMod 6 :=
  bit6 ε1 - bit6 ε2 + 3 * bit6 π
def finalExponent1 (π ε1 ε2 : Bool) : ZMod 6 :=
  let e := localExponent π ε1 ε2
  4 * bit6 ε1 + (if e = 0 then 0 else 1 + e) + bit6 π * (bit6 ε1 + bit6 ε2)
private def finalExponent2 (π ε1 ε2 : Bool) : ZMod 6 :=
  let e := localExponent π ε1 ε2
  4 * bit6 ε2 + (if e = 0 then 0 else 1 - e) + bit6 π * (bit6 ε1 + bit6 ε2)

theorem local_parity_table (π ε1 ε2 : Bool) :
    finalExponent1 π ε1 ε2 =
        (if π || (ε1 && ε2) then 4 else 0 : ZMod 6) ∧
      finalExponent2 π ε1 ε2 =
        (if π || (ε1 && ε2) then 4 else 0 : ZMod 6) := by
  cases π <;> cases ε1 <;> cases ε2 <;> decide

theorem inactive_conductor_case (π ε1 ε2 : Bool)
    (h : localExponent π ε1 ε2 = 0) :
    π = false ∧ ε1 = ε2 := by
  revert h
  cases π <;> cases ε1 <;> cases ε2 <;> decide

theorem new_label_squarefree
    (J C g e v : ℕ)
    (hJ : Squarefree J) (hC : Squarefree C)
    (he : Squarefree e) (hv : Squarefree v)
    (hCJ : C.Coprime J)
    (hg : g.Coprime (C * J))
    (hvold : v.Coprime (g * C * J))
    (he_g : e ∣ g) : Squarefree (J * C * e * v) := by
  have hJC : J.Coprime C := hCJ.symm
  have hJCe : (J * C).Coprime e := by
    have h := Nat.Coprime.of_dvd_left he_g hg
    simpa [mul_comm] using h.symm
  have hdiv : J * C * e ∣ g * C * J := by
    have h := Nat.mul_dvd_mul_left (J * C) he_g
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hJCev : (J * C * e).Coprime v :=
    (Nat.Coprime.of_dvd_right hdiv hvold).symm
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCev, ?_, hv⟩
  apply Nat.squarefree_mul_iff.mpr
  refine ⟨hJCe, ?_, he⟩
  exact Nat.squarefree_mul_iff.mpr ⟨hJC, hJ, hC⟩

end AnalyticBridge

open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ExpBound

theorem exp_neg_le_half {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-t) ≤ (1 : ℝ) / 2 := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hinv : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) he)
  exact (Real.exp_le_exp.mpr (by linarith)).trans hinv

theorem norm_tsum_exp_le_two
    (a : ℕ → ℂ) (ha0 : a 0 = 0)
    (ha : ∀ n, ‖a n‖ ≤ 1)
    (t : ℝ) (ht : 1 ≤ t)
    (hsum : Summable (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t))) :
    ‖∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)‖ ≤
      2 * Real.exp (-t) := by
  let r : ℝ := Real.exp (-t)
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hrhalf : r ≤ (1 : ℝ) / 2 := exp_neg_le_half ht
  have hbound (n : ℕ) :
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ ≤
        r * ((1 : ℝ) / 2) ^ n := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (-(↑(n + 1) : ℝ) * t) = r ^ (n + 1) := by
      dsimp [r]
      rw [show -(↑(n + 1) : ℝ) * t = (↑(n + 1) : ℝ) * (-t) by ring,
        Real.exp_nat_mul]
    rw [hexp, pow_succ]
    calc
      ‖a (n + 1)‖ * (r ^ n * r) ≤
          1 * (r ^ n * r) := by gcongr; exact ha _
      _ ≤ r * ((1 : ℝ) / 2) ^ n := by
        have hp : r ^ n ≤ ((1 : ℝ) / 2) ^ n := pow_le_pow_left₀ hr0 hrhalf _
        nlinarith [mul_nonneg (sub_nonneg.mpr hp) hr0]
  have hbdsum : Summable (fun n : ℕ => r * ((1 : ℝ) / 2) ^ n) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 : ℝ) / 2 < 1)).mul_left r
  have hshift :
      (∑' n : ℕ, a n * Real.exp (-(n : ℝ) * t)) =
        ∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t) := by
    have h := hsum.sum_add_tsum_nat_add 1
    simpa [ha0] using h.symm
  rw [hshift]
  have hnormsum : Summable (fun n : ℕ =>
      ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖) :=
    hbdsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  calc
    ‖∑' n : ℕ, a (n + 1) * Real.exp (-(↑(n + 1) : ℝ) * t)‖ ≤
        ∑' n : ℕ,
          ‖a (n + 1) * (Real.exp (-(↑(n + 1) : ℝ) * t) : ℂ)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, r * ((1 : ℝ) / 2) ^ n :=
      hnormsum.tsum_le_tsum hbound hbdsum
    _ = 2 * Real.exp (-t) := by
      rw [tsum_mul_left, tsum_geometric_two]
      dsimp [r]
      ring

end ExpBound

namespace ShortDraftMellin

theorem inverse_mellin_analytic
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := by
    exact hzero.isBigO.trans (isBigO_zero _ _)
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt

theorem dirichlet_zero_free_of_mellin_bound
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ : σ < 1)
    (A : ℝ → ℂ) (W : ℂ → ℂ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (hW : Differentiable ℂ W)
    (heq : ∀ s : ℂ, 1 < s.re →
      χ.LFunction s * mellin A (-s) = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) U :=
    inverse_mellin_analytic A σ hlocal htop hzero
  have hWa : AnalyticOnNhd ℂ W U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2 hW.differentiableOn
  have htwo : (2 : ℂ) ∈ U := by
    change σ < (2 : ℂ).re
    norm_num at *
    linarith
  have heventual : (fun s : ℂ => χ.LFunction s * mellin A (-s)) =ᶠ[𝓝 (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num :
      (2 : ℂ) ∈ {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hid : Set.EqOn (fun s : ℂ => χ.LFunction s * mellin A (-s)) W U :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hWa
      ((convex_halfSpace_re_gt σ).isPreconnected) htwo heventual
  intro hzeroL
  have heqρ := hid hρ
  change χ.LFunction ρ * mellin A (-ρ) = W ρ at heqρ
  rw [hzeroL, zero_mul] at heqρ
  exact hWρ heqρ.symm

theorem mellin_of_exponential_smoothing
    (a : ℕ → ℂ) (F : ℝ → ℂ) (s : ℂ)
    (hs : 1 < s.re) (ha0 : a 0 = 0)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ => a n * Real.exp (-(n : ℝ) * t)) (F t))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) = Complex.Gamma s * LSeries a s := by
  have hp (n : ℕ) : a n = 0 ∨ 0 < (n : ℝ) := by
    rcases n with _ | n
    · exact Or.inl ha0
    · exact Or.inr (by exact_mod_cast Nat.succ_pos n)
  have hnorm : (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) =
      fun n : ℕ => ‖LSeries.term a s n‖ := by
    funext n
    rw [LSeries.norm_term_eq]
    by_cases hn : n = 0
    · subst n
      simp [ha0]
    · simp [hn]
  have hsum : Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ s.re) := by
    rw [hnorm]
    exact hlsum.norm
  have hM := hasSum_mellin hp (by linarith) hF hsum
  have hterm (n : ℕ) : Complex.Gamma s * a n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn]
      simp only [Complex.ofReal_natCast]
      ring
  have hM' : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n) (mellin F s) := by
    simpa only [hterm] using hM
  have hseries : HasSum (fun n : ℕ => Complex.Gamma s * LSeries.term a s n)
      (Complex.Gamma s * LSeries a s) := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (Complex.Gamma s)
  have heq : mellin F s = Complex.Gamma s * LSeries a s := hM'.unique hseries
  simpa only [mellin_comp_inv, neg_neg] using heq

theorem dirichlet_exponential_mellin_identity
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (F : ℝ → ℂ)
    (hF : ∀ t ∈ Set.Ioi (0 : ℝ),
      HasSum (fun n : ℕ =>
        χ n * (ArithmeticFunction.moebius n : ℂ) *
          Real.exp (-(n : ℝ) * t)) (F t))
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s * mellin (fun D : ℝ => F D⁻¹) (-s) =
      Complex.Gamma s := by
  let a : ℕ → ℂ :=
    (fun n : ℕ => χ n) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
  have ha0 : a 0 = 0 := by simp [a]
  have hsum : LSeriesSummable a s := by
    simpa only [a] using
      (DirichletCharacter.LSeriesSummable_mul χ
        (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs))
  have hM := mellin_of_exponential_smoothing a F s hs ha0 hF hsum
  have hprod : LSeries (χ ·) s * LSeries a s = 1 := by
    simpa only [a] using
      DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [χ.LFunction_eq_LSeries hs, hM]
  calc
    LSeries (χ ·) s * (Complex.Gamma s * LSeries a s) =
        (LSeries (χ ·) s * LSeries a s) * Complex.Gamma s := by ring
    _ = Complex.Gamma s := by rw [hprod, one_mul]

theorem mobius_char_exp_summable
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℕ =>
      χ n * (ArithmeticFunction.moebius n : ℂ) *
        Real.exp (-(n : ℝ) * t)) := by
  have hexp : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * t)) := by
    convert! (Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr ht)) using 1
    ext n
    congr 1
    ring
  apply hexp.of_norm_bounded
  intro n
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hprod : ‖χ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  nlinarith [mul_nonneg (sub_nonneg.mpr hprod)
    (le_of_lt (Real.exp_pos (-(n : ℝ) * t)))]

noncomputable def mobiusExpSum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  ∑' n : ℕ, χ n * (ArithmeticFunction.moebius n : ℂ) *
    Real.exp (-(n : ℝ) * t)

theorem mobiusExpSum_norm_le_two
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖mobiusExpSum χ t‖ ≤ 2 * Real.exp (-t) := by
  have hcoeff (n : ℕ) :
      ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [norm_mul]
    have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
    have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
    nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
      (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
      mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
  exact ExpBound.norm_tsum_exp_le_two
    (fun n => χ n * (ArithmeticFunction.moebius n : ℂ))
    (by simp) hcoeff t ht
    (mobius_char_exp_summable χ t (lt_of_lt_of_le zero_lt_one ht))

theorem mobiusExpSum_flat_at_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by
  have hExp : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => Real.exp (-t)) := by
    apply isBigO_iff_isBigOWith.mpr
    refine ⟨2, IsBigOWith.of_bound ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mobiusExpSum_norm_le_two χ t ht
  have hpow : (fun t : ℝ => mobiusExpSum χ t) =O[atTop]
      (fun t : ℝ => t ^ (-b)) := by
    apply hExp.trans
    simpa only [one_mul, neg_one_mul] using
      (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-b)).isBigO
  have hcomp := hpow.comp_tendsto tendsto_inv_nhdsGT_zero
  refine hcomp.congr (fun _ => rfl) ?_
  intro D
  dsimp
  rw [← Real.rpow_neg_eq_inv_rpow]
  simp

theorem dirichlet_exp_mellin_identity
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    χ.LFunction s *
      mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s) =
        Complex.Gamma s := by
  apply dirichlet_exponential_mellin_identity χ (mobiusExpSum χ)
  · intro t ht
    exact (mobius_char_exp_summable χ t ht).hasSum
  · exact hs

theorem inverse_mellin_analytic_of_flat
    (A : ℝ → ℂ) (σ : ℝ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hflat : ∀ b : ℝ, A =O[𝓝[>] (0 : ℝ)] (fun t : ℝ => t ^ b)) :
    AnalyticOnNhd ℂ (fun s : ℂ => mellin A (-s)) {s : ℂ | σ < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt σ)).2
  intro s hs
  change σ < s.re at hs
  have htop' : A =O[atTop] (fun t : ℝ => t ^ (-(-σ))) := by
    simpa only [neg_neg] using htop
  have hbot : A =O[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => t ^ (-((-s).re - 1))) := hflat _
  have hdiff : DifferentiableAt ℂ (mellin A) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow hlocal htop'
      (by simpa using neg_lt_neg hs) hbot (by linarith)
  exact (hdiff.comp s (differentiableAt_id.neg)).differentiableWithinAt

theorem dirichlet_exp_zero_free_of_power_bound
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (hlocal : LocallyIntegrableOn
      (fun D : ℝ => mobiusExpSum χ D⁻¹) (Set.Ioi 0))
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (hflat : ∀ b : ℝ,
      (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
        (fun D : ℝ => D ^ b))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by
  let U : Set ℂ := {s | σ < s.re}
  have hopen : IsOpen U := Complex.isOpen_re_gt σ
  have hL : AnalyticOnNhd ℂ χ.LFunction U :=
    (Complex.analyticOnNhd_iff_differentiableOn hopen).2
      (χ.differentiable_LFunction hχ).differentiableOn
  have hM : AnalyticOnNhd ℂ
      (fun s : ℂ => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s)) U :=
    inverse_mellin_analytic_of_flat _ σ hlocal htop hflat
  have hW : AnalyticOnNhd ℂ Complex.Gamma U := by
    apply (Complex.analyticOnNhd_iff_differentiableOn hopen).2
    intro s hs
    apply (Complex.differentiableAt_Gamma s ?_).differentiableWithinAt
    intro m hm
    have hreal : s.re = -(m : ℝ) := by
      simpa using congrArg Complex.re hm
    have hspos : 0 < s.re := lt_trans hσpos hs
    linarith [Nat.cast_nonneg (α := ℝ) m]
  have hWρ : Complex.Gamma ρ ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (lt_trans hσpos hρ)
  exact ShortDraft.zero_free_of_analytic_identity σ hσ χ.LFunction
    (fun s => mellin (fun D : ℝ => mobiusExpSum χ D⁻¹) (-s))
    Complex.Gamma hL hM hW
    (fun s hs => dirichlet_exp_mellin_identity χ s hs) ρ hρ hWρ

end ShortDraftMellin


end OAI

end



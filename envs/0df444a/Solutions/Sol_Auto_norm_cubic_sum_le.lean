-- Prove2me | solution 1 for Auto.norm_cubic_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:11:15.579644+00:00
-- url     : https://prove2.me/submissions/0556a139-5ee1-4967-95cc-d2aa0935387e

module
public import Mathlib
public import Definitions.Def_Triangular_Defs
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Theorems.Thm_Auto_sum_triple_by_min
public import Theorems.Thm_Auto_sum_pair_by_min
public import Theorems.Thm_Auto_norm_entry_sum_sq_le
public import Theorems.Thm_Auto_norm_diag_le
public import Theorems.Thm_Auto_norm_quadForm_le

set_option autoImplicit true
@[expose] public section
public section
public section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder ENNReal NNReal
open Matrix MeasureTheory Filter Topology
open Auto
noncomputable section
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1611
attribute [local instance] Auto._p2m_local_instance_5846efa9ac_1612
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
namespace Auto
theorem _root_.solution (m : κ → ℝ) {D : Matrix κ κ ℂ} (hD : D.IsHermitian) {d : ℝ}
    (hd : 0 ≤ d) (hDd : ((d ^ 2 : ℝ) • (1 : Matrix κ κ ℂ) - D * D).PosSemidef) :
    ‖∑ i, ∑ j, ∑ k, ((m i * m j * m k : ℝ) : ℂ) * D i j * D j k * D k i‖ ≤ 5 * d * ∑ i, ∑ j, |m
      i| ^ 2 * |m j| ^ 2 * ‖D i j‖ ^ 2 / (|m i| + |m j|) := by
  classical
  set q : κ → ℝ := fun i => |m i| with hqdef
  have hq0 : ∀ i, 0 ≤ q i := fun i => abs_nonneg _
  set e := Fintype.equivFin κ
  let : LinearOrder κ := LinearOrder.lift' (fun i => toLex (OrderDual.toDual (q i), e i)) (fun i j h
      => by
      have := congrArg (fun x => (ofLex x).2) h
      exact e.injective this)
  have hord : ∀ i j, i < j → q j ≤ q i := by
    intro i j hij
    have h : toLex (OrderDual.toDual (q i), e i) < toLex (OrderDual.toDual (q j), e j) := hij
    rw [Prod.Lex.toLex_lt_toLex] at h
    rcases h with h | ⟨h, _⟩
    · exact (OrderDual.toDual_lt_toDual.1 h).le
    · exact (OrderDual.toDual_inj.1 h) ▸ le_rfl
  have hDn : ∀ i j, ‖D j i‖ = ‖D i j‖ := fun i j => by rw [← hD.apply i j, norm_star]
  have hrow := norm_entry_sum_sq_le hD hDd
  have hdiag := norm_diag_le hD hd hDd
  set f : κ → κ → κ → ℂ := fun i j k => ((m i * m j * m k : ℝ) : ℂ) * D i j * D j k * D k i
  have hf : ∀ i j k, f i j k = f j k i := by intro i j k; simp only [f]; push_cast; ring
  have hsum := sum_triple_by_min f hf Finset.univ
  simp only [f] at hsum
  rw [hsum]
  set F : κ → Finset κ := fun μ => Finset.univ.filter (μ < ·)
  set A : κ → ℝ := fun μ => q μ ^ 3 * ‖D μ μ‖ ^ 2
  set S : κ → ℝ := fun μ => ∑ j ∈ F μ, q j ^ 2 * ‖D μ j‖ ^ 2
  set E : κ → ℝ := fun μ => q μ * S μ
  have hA0 : ∀ μ, 0 ≤ A μ := fun μ => by have := hq0 μ; positivity
  have hS0 : ∀ μ, 0 ≤ S μ := fun μ => Finset.sum_nonneg fun j _ => by
    have := hq0 j; positivity
  have hE0 : ∀ μ, 0 ≤ E μ := fun μ => mul_nonneg (hq0 μ) (hS0 μ)
  have hT1 : ∀ μ, ‖∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ‖ ≤
      d * E μ := by
    intro μ
    set v : κ → ℂ := fun j => if μ < j then (m j : ℂ) * D j μ else 0
    have hv : ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ = (m μ : ℂ)
        * ∑ j, ∑ k, star (v j) * D j k * v k := by
      rw [Finset.mul_sum]
      simp only [F, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      split_ifs with hj
      · refine Finset.sum_congr rfl fun k _ => ?_
        simp only [v, hj, ite_true]
        split_ifs with hk
        · rw [star_mul', ← hD.apply μ j]
          simp only [RCLike.star_def, Complex.conj_ofReal]
          push_cast; ring
        · simp
      · simp [v, hj]
    rw [hv, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hq := norm_quadForm_le hD hd hDd v
    have hvn : ∑ j, ‖v j‖ ^ 2 = S μ := by
      simp only [S, F, Finset.sum_filter, v]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, hDn]
      · simp
    rw [hvn] at hq
    calc |m μ| * ‖∑ j, ∑ k, star (v j) * D j k * v k‖ ≤ |m μ| * (d * S μ) := by gcongr
      _ = d * E μ := by simp only [E, q]; ring
  have hT2 : ∀ μ, ‖∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ‖ ≤
      d * (√(A μ) * √(E μ)) := by
    intro μ
    have e1 : ∀ k, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ = ((m μ * m μ : ℝ) : ℂ) * D μ
        μ * ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      have hp : D μ k * D k μ = ((‖D μ k‖ ^ 2 : ℝ) : ℂ) := by
        rw [← hD.apply k μ, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc
        _ = ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * (D μ k * D k μ) := by ring
        _ = _ := by rw [hp]; push_cast; ring
    simp_rw [e1]
    rw [← Finset.mul_sum, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : ‖∑ k ∈ F μ, ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ)‖ ≤ ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ‖D μ k‖)]
    have h2 : ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 ≤ √(S μ) * d := by
      have := Real.sum_mul_le_sqrt_mul_sqrt (F μ) (fun k => q k * ‖D μ k‖) (fun k => ‖D μ k‖)
      have hs1 : ∑ k ∈ F μ, (q k * ‖D μ k‖) ^ 2 = S μ :=
        Finset.sum_congr rfl fun k _ => by ring
      have hs2 : √(∑ k ∈ F μ, ‖D μ k‖ ^ 2) ≤ d := by
        refine Real.sqrt_le_iff.2 ⟨hd, ?_⟩
        exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun k _ _ => sq_nonneg _).trans (hrow μ)
      calc ∑ k ∈ F μ, q k * ‖D μ k‖ ^ 2 = ∑ k ∈ F μ, (q k * ‖D μ k‖) * ‖D μ k‖ :=
            Finset.sum_congr rfl fun k _ => by ring
        _ ≤ √(∑ k ∈ F μ, (q k * ‖D μ k‖) ^ 2) * √(∑ k ∈ F μ, ‖D μ k‖ ^ 2) := this
        _ ≤ √(S μ) * d := by rw [hs1]; exact mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
    have hmm : |m μ * m μ| = q μ ^ 2 := by simp [q, abs_mul, sq]
    rw [hmm]
    calc q μ ^ 2 * ‖D μ μ‖ * ‖∑ k ∈ F μ, ((m k * ‖D μ k‖ ^ 2 : ℝ) : ℂ)‖
        ≤ q μ ^ 2 * ‖D μ μ‖ * (√(S μ) * d) := by
          have := hq0 μ
          gcongr
          exact h1.trans h2
      _ = d * (√(A μ) * √(E μ)) := by
          have hq := hq0 μ
          rw [← Real.sqrt_mul (hA0 μ), show A μ * E μ = (q μ ^ 2 * ‖D μ μ‖) ^ 2 * S μ by
            simp only [A, E]; ring, Real.sqrt_mul (sq_nonneg _),
            Real.sqrt_sq (by positivity)]
          ring
  have hT3 : ∀ μ, ‖((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ‖ ≤ d * A μ := by
    intro μ
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, A]
    have h := hdiag μ
    have := norm_nonneg (D μ μ)
    have hq := hq0 μ
    calc |m μ| * |m μ| * |m μ| * ‖D μ μ‖ * ‖D μ μ‖ * ‖D μ μ‖ =
        q μ ^ 3 * ‖D μ μ‖ ^ 2 * ‖D μ μ‖ := by simp only [q]; ring
      _ ≤ q μ ^ 3 * ‖D μ μ‖ ^ 2 * d := by gcongr
      _ = _ := by ring
  have hgroup : ∀ μ, ‖3 • ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k *
      D k μ + 3 • ∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ +
      ((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ‖ ≤
        d * (3 * E μ + 3 * (√(A μ) * √(E μ)) + A μ) := by
    intro μ
    refine (norm_add₃_le).trans ?_
    rw [nsmul_eq_mul, nsmul_eq_mul, norm_mul, norm_mul]
    simp only [Nat.cast_ofNat, Complex.norm_ofNat]
    nlinarith [hT1 μ, hT2 μ, hT3 μ]
  have hA : ∑ μ, √(A μ) * √(E μ) ≤ √(∑ μ, A μ) * √(∑ μ, E μ) := by
    have := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun μ => √(A μ)) (fun μ => √(E μ))
    simpa [Real.sq_sqrt (hA0 _), Real.sq_sqrt (hE0 _)] using this
  have hAE : 3 * (√(∑ μ, A μ) * √(∑ μ, E μ)) ≤ (3 / 2) * (∑ μ, A μ + ∑ μ, E μ) := by
    have hSA : 0 ≤ ∑ μ, A μ := Finset.sum_nonneg fun μ _ => hA0 μ
    have hSE : 0 ≤ ∑ μ, E μ := Finset.sum_nonneg fun μ _ => hE0 μ
    have h1 := Real.sq_sqrt hSA
    have h2 := Real.sq_sqrt hSE
    nlinarith [sq_nonneg (√(∑ μ, A μ) - √(∑ μ, E μ))]
  set g : κ → κ → ℝ := fun i j => |m i| ^ 2 * |m j| ^ 2 * ‖D i j‖ ^ 2 / (|m i| + |m j|)
  have hQ : ∑ μ, (A μ / 2 + E μ) ≤ ∑ i, ∑ j, g i j := by
    rw [sum_pair_by_min g Finset.univ]
    refine Finset.sum_le_sum fun μ _ => ?_
    have hg1 : g μ μ = A μ / 2 := by
      simp only [g, A, q]
      rcases (abs_nonneg (m μ)).eq_or_lt with h | h
      · rw [← h]; simp
      · field_simp; ring
    have hg2 : E μ ≤ ∑ j ∈ F μ, (g μ j + g j μ) := by
      simp only [E, S, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjμ : q j ≤ q μ := hord μ j (Finset.mem_filter.1 hj).2
      simp only [g, hDn μ j]
      have h1 := hq0 μ; have h2 := hq0 j
      change q μ * (q j ^ 2 * ‖D μ j‖ ^ 2) ≤ q μ ^ 2 * q j ^ 2 * ‖D μ j‖ ^ 2 / (q μ + q j) +
        q j ^ 2 * q μ ^ 2 * ‖D μ j‖ ^ 2 / (q j + q μ)
      rcases (add_nonneg h1 h2).eq_or_lt with h0 | h0
      · have hμ0 : q μ = 0 := by linarith
        simp [hμ0]
      · rw [add_comm (q j) (q μ), ← add_div, le_div_iff₀ h0]
        have := norm_nonneg (D μ j)
        nlinarith [mul_nonneg (mul_nonneg h1 (sq_nonneg (q j))) (sq_nonneg ‖D μ j‖),
          mul_nonneg (mul_nonneg (mul_nonneg h1 (sq_nonneg (q j))) (sq_nonneg ‖D μ j‖))
              (sub_nonneg.2 hjμ)]
    linarith
  calc ‖∑ μ, (3 • ∑ j ∈ F μ, ∑ k ∈ F μ, ((m μ * m j * m k : ℝ) : ℂ) * D μ j * D j k * D k μ +
        3 • ∑ k ∈ F μ, ((m μ * m μ * m k : ℝ) : ℂ) * D μ μ * D μ k * D k μ +
        ((m μ * m μ * m μ : ℝ) : ℂ) * D μ μ * D μ μ * D μ μ)‖
      ≤ ∑ μ, d * (3 * E μ + 3 * (√(A μ) * √(E μ)) + A μ) := (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun μ _ => hgroup μ)
    _ = d * (3 * ∑ μ, E μ + 3 * ∑ μ, √(A μ) * √(E μ) + ∑ μ, A μ) := by
        rw [← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ d * (5 * ∑ μ, (A μ / 2 + E μ)) := by
        apply mul_le_mul_of_nonneg_left _ hd
        have hsplit : ∑ μ, (A μ / 2 + E μ) = (∑ μ, A μ) / 2 + ∑ μ, E μ := by
          rw [Finset.sum_add_distrib, Finset.sum_div]
        have hE : 0 ≤ ∑ μ, E μ := Finset.sum_nonneg fun μ _ => hE0 μ
        rw [hsplit]
        nlinarith [hA, hAE]
    _ ≤ 5 * d * ∑ i, ∑ j, g i j := by nlinarith [hQ]
end Auto

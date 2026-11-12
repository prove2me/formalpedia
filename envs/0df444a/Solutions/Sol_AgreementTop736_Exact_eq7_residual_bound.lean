-- Prove2me | solution 1 for AgreementTop736.Exact.eq7_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T02:27:06.695781+00:00
-- url     : https://prove2.me/submissions/e69e80e2-ca49-493b-9208-c79a4c4f768f

import Mathlib
import Definitions.Def_AgreementTop736_Exact_Regularized
import Theorems.Thm_AgreementTop736_Exact_sec3_1_regularizer_comparison

section
set_option autoImplicit false
namespace AgreementTop736.Exact.Dev.Eq7
open AgreementTop736.Exact Finset Scheme

variable {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]

lemma rho_pos (S : Scheme V) (hS : S.IsValid) : 0 < S.ρ := by
  unfold Scheme.ρ
  have : (0:ℝ) < S.n := by exact_mod_cast hS.n_pos
  have : (0:ℝ) < S.N := by exact_mod_cast (hS.n_pos.trans hS.n_lt_N)
  positivity

lemma rho_le_one (S : Scheme V) (hS : S.IsValid) : S.ρ ≤ 1 := by
  unfold Scheme.ρ
  have : (0:ℝ) < S.N := by exact_mod_cast (hS.n_pos.trans hS.n_lt_N)
  rw [div_le_one this]
  exact_mod_cast hS.n_lt_N.le

/-- residual formula for `H ⊆ K`. -/
lemma residualSq_eq (S : Scheme V) (F : Finset V → V → α) (g : V → α) (a : ℝ) (K H : Finset V)
    (hHK : H ⊆ K) :
    S.residualSq F g a K H = (localErr F g K H : ℝ) *
      (fReg a (errCount F g K) - fReg a ((localErr F g K H : ℝ) / S.ρ)) ^ 2 := by
  unfold Scheme.residualSq
  have h1 : ∀ x ∈ H, ∑ s ∈ offLabels g x, (phi F g a x s K - S.psi F g a x s K H) ^ 2 =
      if F K x ≠ g x then (fReg a (errCount F g K) - fReg a ((localErr F g K H : ℝ) / S.ρ)) ^ 2
      else 0 := by
    intro x hx
    have hxK : x ∈ K := hHK hx
    by_cases hF : F K x = g x
    · rw [Finset.sum_eq_zero]
      · simp [hF]
      · intro s hs
        have : s ≠ g x := by simpa [offLabels] using hs
        have : F K x ≠ s := by rw [hF]; exact fun h => this h.symm
        simp [phi, Scheme.psi, this]
    · have hmem : F K x ∈ offLabels g x := by simp [offLabels, hF]
      rw [Finset.sum_eq_single (F K x)]
      · simp [phi, Scheme.psi, hx, hxK, hF]
      · intro s _ hs; simp [phi, Scheme.psi, Ne.symm hs]
      · intro h; exact absurd hmem h
  rw [Finset.sum_congr rfl h1]
  unfold localErr
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]

lemma filter_inter (F : Finset V → V → α) (g : V → α) (K H : Finset V) (hHK : H ⊆ K) :
    H.filter (fun x => F K x ≠ g x) = (K.filter (fun x => F K x ≠ g x)) ∩ H := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨hHK h1, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

lemma perK (S : Scheme V) (hS : S.IsValid) (h2 : S.VarianceBound) (F : Finset V → V → α)
    (g : V → α) {a : ℝ} (ha : 0 < a) (K : Finset V) (hK : 0 < S.μ K) :
    ∑ H, S.D K H * S.residualSq F g a K H ≤
      (1 - S.ρ) / a * ((errCount F g K : ℝ) / ((errCount F g K : ℝ) + a)) := by
  have hρ := rho_pos S hS
  have hρ1 := rho_le_one S hS
  set m : ℝ := (errCount F g K : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hma : 0 < m + a := by linarith
  set E := K.filter (fun x => F K x ≠ g x) with hE
  have hEc : (E.card : ℝ) = m := by rw [hm]; rfl
  obtain ⟨hmean, hvar⟩ := h2 K hK E (Finset.filter_subset _ _)
  rw [hEc] at hmean hvar
  set Zf : Finset V → ℝ := fun H => ((E ∩ H).card : ℝ) with hZf
  -- weighted agreement of Z and Zf
  have hZ : ∀ H, 0 < S.D K H → (localErr F g K H : ℝ) = Zf H := by
    intro H hH
    have hHK := (hS.D_support K hK H hH).1
    simp only [hZf]; unfold localErr; rw [filter_inter F g K H hHK]
  have hDnn := hS.D_nonneg K hK
  -- pointwise bound
  have hA : ∀ H, S.D K H * S.residualSq F g a K H ≤
      S.D K H * (S.ρ * (m - (localErr F g K H : ℝ) / S.ρ) ^ 2 / (m + a) ^ 2) := by
    intro H
    rcases (hDnn H).eq_or_lt with h | h
    · rw [← h]; simp
    · apply mul_le_mul_of_nonneg_left _ h.le
      have hHK := (hS.D_support K hK H h).1
      rw [residualSq_eq S F g a K H hHK]
      have := sec3_1_regularizer_comparison hρ ha hm0 (Nat.cast_nonneg (localErr F g K H)) rfl
      rw [this.1]; exact this.2
  refine (Finset.sum_le_sum fun H _ => hA H).trans ?_
  -- variance computation
  have hB : ∑ H, S.D K H * (S.ρ * (m - (localErr F g K H : ℝ) / S.ρ) ^ 2 / (m + a) ^ 2) =
      (1 / (S.ρ * (m + a) ^ 2)) * S.condVar K Zf := by
    unfold Scheme.condVar
    rw [hmean, Finset.mul_sum]
    refine Finset.sum_congr rfl fun H _ => ?_
    rcases (hDnn H).eq_or_lt with h | h
    · rw [← h]; simp
    · rw [hZ H h]
      field_simp
      ring
  rw [hB]
  have hv : S.condVar K Zf ≤ S.ρ * (1 - S.ρ) * m := hvar
  have hc : 0 < S.ρ * (m + a) ^ 2 := by positivity
  calc 1 / (S.ρ * (m + a) ^ 2) * S.condVar K Zf
      ≤ 1 / (S.ρ * (m + a) ^ 2) * (S.ρ * (1 - S.ρ) * m) :=
        mul_le_mul_of_nonneg_left hv (by positivity)
    _ = (1 - S.ρ) * m / (m + a) ^ 2 := by field_simp
    _ ≤ (1 - S.ρ) / a * (m / (m + a)) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
        have h1 : 0 ≤ (1 - S.ρ) * m := mul_nonneg (by linarith) hm0
        nlinarith [mul_nonneg h1 (mul_nonneg ha.le hma.le), mul_nonneg h1 ha.le,
          mul_nonneg h1 (sq_nonneg (m + a)), mul_nonneg (mul_nonneg h1 ha.le) hm0]

end AgreementTop736.Exact.Dev.Eq7
namespace AgreementTop736.Exact
open Finset Scheme
open AgreementTop736.Exact.Dev.Eq7 in
theorem chk_eq7_residual_bound {V : Type*} [Fintype V] [DecidableEq V] {α : Type*} [Fintype α] [DecidableEq α]
    (S : Scheme V) (hS : S.IsValid) (h2 : S.VarianceBound) (F : Finset V → V → α) (g : V → α)
    {a : ℝ} (ha : 0 < a) :
    ∑ K, ∑ H, S.μ K * S.D K H * S.residualSq F g a K H ≤ (1 - S.ρ) / a * S.Vreg F g a := by
  unfold Scheme.Vreg
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun K _ => ?_
  rcases (hS.μ_nonneg K).eq_or_lt with h | h
  · rw [← h]; simp
  · have := perK S hS h2 F g ha K h
    calc ∑ H, S.μ K * S.D K H * S.residualSq F g a K H
        = S.μ K * ∑ H, S.D K H * S.residualSq F g a K H := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun H _ => by ring
      _ ≤ S.μ K * ((1 - S.ρ) / a * ((errCount F g K : ℝ) / ((errCount F g K : ℝ) + a))) :=
          mul_le_mul_of_nonneg_left this h.le
      _ = _ := by ring
end AgreementTop736.Exact
end

theorem solution : type_of% @AgreementTop736.Exact.chk_eq7_residual_bound := @AgreementTop736.Exact.chk_eq7_residual_bound

-- Prove2me | solution 1 for Arxiv2610_39302.next_token_minimizers_gl_invariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T07:32:45.605001+00:00
-- url     : https://prove2.me/submissions/2ea6a4cc-773f-45e3-bd1c-bb8e81e14408

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open Matrix

noncomputable section
namespace NTX

lemma factor {V C : Type*} [Fintype V] [Fintype C] [DecidableEq C] {k : ℕ}
    (M : Matrix V C ℝ) (hM : M.rank ≤ k) :
    ∃ (h : C → Fin k → ℝ) (w : V → Fin k → ℝ), ∀ c v, h c ⬝ᵥ w v = M v c := by
  set S := LinearMap.range M.mulVecLin
  set r := Module.finrank ℝ S
  have hr : r ≤ k := hM
  let b := Module.finBasis ℝ S
  have mem : ∀ c, (fun v => M v c) ∈ S := fun c => by
    refine ⟨Pi.single c 1, ?_⟩
    ext v; simp [Matrix.mulVecLin_apply]
  let coef : C → Fin r → ℝ := fun c => b.repr ⟨_, mem c⟩
  let e : Fin r → Fin k := Fin.castLE hr
  refine ⟨fun c j => ∑ i, if e i = j then coef c i else 0,
    fun v j => ∑ i, if e i = j then (b i : V → ℝ) v else 0, fun c v => ?_⟩
  have hsum := b.sum_repr ⟨_, mem c⟩
  have hv := congrArg (fun x : S => (x : V → ℝ) v) hsum
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul] at hv
  rw [← hv]
  unfold dotProduct
  symm
  apply Fintype.sum_of_injective e (Fin.castLE_injective hr)
  · intro j hj
    have : ∀ i, e i ≠ j := fun i hi => hj ⟨i, hi⟩
    simp [this]
  · intro i
    have hi : ∀ i', e i' = e i ↔ i' = i := fun i' => (Fin.castLE_injective hr).eq_iff
    simp [hi, coef]


lemma gibbs_term (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    0 ≤ p * (Real.log p - Real.log q) - (p - q) ∧
    (p * (Real.log p - Real.log q) - (p - q) = 0 → q = p) := by
  have hx : 0 < q / p := div_pos hq hp
  have hl : Real.log (q / p) = Real.log q - Real.log p := Real.log_div hq.ne' hp.ne'
  have key : p * (Real.log p - Real.log q) - (p - q) = p * ((q / p - 1) - Real.log (q / p)) := by
    rw [hl]; field_simp; ring
  rw [key]
  constructor
  · exact mul_nonneg hp.le (by linarith [Real.log_le_sub_one_of_pos hx])
  · intro h0
    by_contra hne
    have : q / p ≠ 1 := by
      intro h1; apply hne; field_simp at h1; linarith
    have := Real.log_lt_sub_one_of_pos hx this
    have : 0 < p * ((q / p - 1) - Real.log (q / p)) := mul_pos hp (by linarith)
    linarith

lemma gibbs {V : Type*} [Fintype V] (p q : V → ℝ) (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hp1 : ∑ v, p v = 1) (hq1 : ∑ v, q v = 1) :
    ∑ v, p v * (-Real.log (p v)) ≤ ∑ v, p v * (-Real.log (q v)) ∧
    (∑ v, p v * (-Real.log (q v)) = ∑ v, p v * (-Real.log (p v)) → ∀ v, q v = p v) := by
  have hdiff : ∑ v, p v * (-Real.log (q v)) - ∑ v, p v * (-Real.log (p v)) =
      ∑ v, (p v * (Real.log (p v) - Real.log (q v)) - (p v - q v)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hp1, hq1, ← Finset.sum_sub_distrib]
    simp only [sub_self, sub_zero]
    congr 1; funext v; ring
  have hnn : ∀ v, 0 ≤ p v * (Real.log (p v) - Real.log (q v)) - (p v - q v) :=
    fun v => (gibbs_term _ _ (hp v) (hq v)).1
  constructor
  · have := Finset.sum_nonneg (fun v (_ : v ∈ Finset.univ) => hnn v)
    linarith
  · intro heq v
    have h0 : ∑ v, (p v * (Real.log (p v) - Real.log (q v)) - (p v - q v)) = 0 := by
      rw [← hdiff, heq, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ Finset.univ) => hnn v)).1 h0 v
      (Finset.mem_univ v)
    exact (gibbs_term _ _ (hp v) (hq v)).2 this

open Arxiv2610_39302

def sm {V : Type*} [Fintype V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) (v : V) : ℝ :=
  Real.exp (h ⬝ᵥ w v) / ∑ u, Real.exp (h ⬝ᵥ w u)

lemma sm_pos {V : Type*} [Fintype V] [Nonempty V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) (v : V) :
    0 < sm w h v :=
  div_pos (Real.exp_pos _) (Finset.sum_pos (fun u _ => Real.exp_pos _) Finset.univ_nonempty)

lemma sm_sum {V : Type*} [Fintype V] [Nonempty V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) :
    ∑ v, sm w h v = 1 := by
  unfold sm
  rw [← Finset.sum_div]
  exact div_self (Finset.sum_pos (fun u _ => Real.exp_pos _) Finset.univ_nonempty).ne'

lemma loss_eq {V : Type*} [Fintype V] {k : ℕ} (w : V → Fin k → ℝ) (h : Fin k → ℝ) (v : V) :
    ntpLoss w h v = -Real.log (sm w h v) := rfl


section
variable {C V : Type*} [Fintype C] [Fintype V] [Nonempty V] {k : ℕ} (P : C → ℝ) (cond : C → V → ℝ)

def Hent : ℝ := ∑ c, P c * ∑ v, cond c v * (-Real.log (cond c v))

lemma risk_ge (hP : ∀ c, 0 < P c) (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) : Hent P cond ≤ ntpRisk P cond h w := by
  unfold Hent ntpRisk
  apply Finset.sum_le_sum; intro c _
  apply mul_le_mul_of_nonneg_left _ (hP c).le
  simp only [loss_eq]
  exact (gibbs (cond c) (sm w (h c)) (hcond c) (sm_pos w (h c)) (hcond1 c) (sm_sum w (h c))).1

lemma risk_eq (hP : ∀ c, 0 < P c) (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) (heq : ntpRisk P cond h w = Hent P cond) :
    ∀ c v, sm w (h c) v = cond c v := by
  intro c
  have hle : ∀ c ∈ Finset.univ, P c * ∑ v, cond c v * (-Real.log (cond c v)) ≤
      P c * ∑ v, cond c v * ntpLoss w (h c) v := by
    intro c _
    apply mul_le_mul_of_nonneg_left _ (hP c).le
    simp only [loss_eq]
    exact (gibbs (cond c) (sm w (h c)) (hcond c) (sm_pos w (h c)) (hcond1 c) (sm_sum w (h c))).1
  have := (Finset.sum_eq_sum_iff_of_le hle).1 (by unfold Hent ntpRisk at heq; exact heq.symm) c
    (Finset.mem_univ c)
  have h2 := mul_left_cancel₀ (hP c).ne' this
  simp only [loss_eq] at h2
  exact (gibbs (cond c) (sm w (h c)) (hcond c) (sm_pos w (h c)) (hcond1 c) (sm_sum w (h c))).2 h2.symm

lemma sm_of_logits (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (c : C) (b : ℝ) (h : Fin k → ℝ) (w : V → Fin k → ℝ)
    (hb : ∀ v, h ⬝ᵥ w v = Real.log (cond c v) + b) (v : V) : sm w h v = cond c v := by
  unfold sm
  simp only [hb, Real.exp_add, Real.exp_log (hcond c _)]
  rw [← Finset.sum_mul, hcond1 c, one_mul]
  field_simp

lemma risk_of_logits (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) (b : C → ℝ)
    (hb : ∀ c v, h c ⬝ᵥ w v = Real.log (cond c v) + b c) : ntpRisk P cond h w = Hent P cond := by
  unfold ntpRisk Hent
  simp only [loss_eq, sm_of_logits cond hcond hcond1 _ _ _ _ (hb _)]

lemma logits_of_sm (hcond : ∀ c v, 0 < cond c v) (c : C) (h : Fin k → ℝ) (w : V → Fin k → ℝ)
    (hs : ∀ v, sm w h v = cond c v) :
    ∀ v, h ⬝ᵥ w v = Real.log (cond c v) + Real.log (∑ u, Real.exp (h ⬝ᵥ w u)) := by
  intro v
  have hZ : 0 < ∑ u, Real.exp (h ⬝ᵥ w u) :=
    Finset.sum_pos (fun u _ => Real.exp_pos _) Finset.univ_nonempty
  rw [← hs v, sm, ← Real.log_mul (div_pos (Real.exp_pos _) hZ).ne' hZ.ne', div_mul_cancel₀ _ hZ.ne',
    Real.log_exp]
end

lemma gl_dot {k : ℕ} (G : Matrix.GeneralLinearGroup (Fin k) ℝ) (x y : Fin k → ℝ) :
    ((G : Matrix (Fin k) (Fin k) ℝ) *ᵥ x) ⬝ᵥ
      ((((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec]
  have : ((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ) *
      (G : Matrix (Fin k) (Fin k) ℝ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [this, Matrix.one_mulVec]

end NTX
end

open NTX Arxiv2610_39302 in
theorem solution {C V : Type*} [Fintype C] [Fintype V] [Nonempty V]
    {k : ℕ} (P : C → ℝ) (hP : ∀ c, 0 < P c) (hP1 : ∑ c, P c = 1)
    (cond : C → V → ℝ) (hcond : ∀ c v, 0 < cond c v) (hcond1 : ∀ c, ∑ v, cond c v = 1)
    (hrank : ∃ b : C → ℝ, (Matrix.of fun (v : V) (c : C) => Real.log (cond c v) + b c).rank ≤ k) :
    (∀ (h : C → Fin k → ℝ) (w : V → Fin k → ℝ),
      (∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond h w ≤ ntpRisk P cond h' w') ↔
        ∃ b : C → ℝ, ∀ c v, h c ⬝ᵥ w v = Real.log (cond c v) + b c) ∧
    (∀ (G : Matrix.GeneralLinearGroup (Fin k) ℝ) (h : C → Fin k → ℝ) (w : V → Fin k → ℝ) c v,
      ((G : Matrix (Fin k) (Fin k) ℝ) *ᵥ h c) ⬝ᵥ
          ((((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ w v) =
        h c ⬝ᵥ w v) ∧
    (∀ (G : Matrix.GeneralLinearGroup (Fin k) ℝ) (h : C → Fin k → ℝ) (w : V → Fin k → ℝ),
      (∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond h w ≤ ntpRisk P cond h' w') →
      ∀ (h' : C → Fin k → ℝ) (w' : V → Fin k → ℝ), ntpRisk P cond (fun c => (G : Matrix (Fin k) (Fin k) ℝ) *ᵥ h c)
          (fun v => (((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ w v)
        ≤ ntpRisk P cond h' w') := by
  classical
  refine ⟨fun h w => ⟨fun hmin => ?_, fun ⟨b, hb⟩ h' w' => ?_⟩,
    fun G h w c v => gl_dot G (h c) (w v), fun G h w hmin h' w' => ?_⟩
  · obtain ⟨b0, hb0⟩ := hrank
    obtain ⟨h0, w0, hf⟩ := factor _ hb0
    have r0 := risk_of_logits P cond hcond hcond1 h0 w0 b0 (fun c v => by rw [hf]; rfl)
    have heq : ntpRisk P cond h w = Hent P cond :=
      le_antisymm (r0 ▸ hmin h0 w0) (risk_ge P cond hP hcond hcond1 h w)
    have hs := risk_eq P cond hP hcond hcond1 h w heq
    exact ⟨fun c => Real.log (∑ u, Real.exp (h c ⬝ᵥ w u)),
      fun c v => logits_of_sm cond hcond c (h c) w (hs c) v⟩
  · rw [risk_of_logits P cond hcond hcond1 h w b hb]
    exact risk_ge P cond hP hcond hcond1 h' w'
  · have : ntpRisk P cond (fun c => (G : Matrix (Fin k) (Fin k) ℝ) *ᵥ h c)
          (fun v => (((G⁻¹ : Matrix.GeneralLinearGroup (Fin k) ℝ) : Matrix (Fin k) (Fin k) ℝ)ᵀ) *ᵥ w v)
        = ntpRisk P cond h w := by
      unfold ntpRisk ntpLoss
      simp only [gl_dot]
    rw [this]; exact hmin h' w'

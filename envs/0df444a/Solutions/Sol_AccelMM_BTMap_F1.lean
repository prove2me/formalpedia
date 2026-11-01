-- Prove2me | solution 1 for AccelMM.BTMap.F1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:36:44.865551+00:00
-- url     : https://prove2.me/submissions/ccc15cd6-b6b5-4ab1-a4fb-8bd8731aa56f

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

open scoped InnerProductSpace

namespace Aux_AccelMM_F1

open AccelMM.BTMap

lemma rho_diff {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) : Differentiable ℝ (rho α β d) := by
  have hc : ∀ i : Fin n, Differentiable ℝ (fun x : E n => x i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable
  unfold rho loglik logPrior
  fun_prop (disch := (intros; positivity))

lemma dir_deriv {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) (x z : E n) :
    fderiv ℝ (rho α β d) x z =
      ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (z a -
        (Real.exp (x a) * z a + Real.exp (x b) * z b) / (Real.exp (x a) + Real.exp (x b))) +
      ∑ a, ((α - 1) * z a - β * (Real.exp (x a) * z a)) := by
  have hline : HasDerivAt (fun s : ℝ => x + s • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have h1 : HasDerivAt (fun s : ℝ => rho α β d (x + s • z)) (fderiv ℝ (rho α β d) x z) 0 :=
    HasFDerivAt.comp_hasDerivAt_of_eq 0 ((rho_diff α β d) x).hasFDerivAt hline (by simp)
  have hc : ∀ a, HasDerivAt (fun s : ℝ => x a + s * z a) (z a) 0 := by
    intro a
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (z a)).const_add (x a)
  have hterm : ∀ a b, HasDerivAt (fun s : ℝ => (d a b : ℝ) * ((x a + s * z a) -
      Real.log (Real.exp (x a + s * z a) + Real.exp (x b + s * z b))))
      ((d a b : ℝ) * (z a -
        (Real.exp (x a) * z a + Real.exp (x b) * z b) / (Real.exp (x a) + Real.exp (x b)))) 0 := by
    intro a b
    have hs := ((hc a).exp.add (hc b).exp)
    have hl := hs.log (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
    have := ((hc a).sub hl).const_mul (d a b : ℝ)
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have hprior : ∀ a, HasDerivAt (fun s : ℝ => (α - 1) * (x a + s * z a) - β * Real.exp (x a + s * z a))
      ((α - 1) * z a - β * (Real.exp (x a) * z a)) 0 := by
    intro a
    have := ((hc a).const_mul (α - 1)).sub ((hc a).exp.const_mul β)
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have h2 := (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
      HasDerivAt.fun_sum (u := Finset.univ.erase a) (fun b _ => hterm a b))).add
    (HasDerivAt.fun_sum (u := Finset.univ) (fun a _ => hprior a))
  have h2' := h2.congr_of_eventuallyEq (f₁ := fun s : ℝ => rho α β d (x + s • z))
    (Filter.Eventually.of_forall (fun s => by
      simp only [rho, loglik, logPrior, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
        Pi.add_apply]))
  exact h1.unique h2'

lemma inner_grad {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) (x z : E n) :
    ⟪gradient (rho α β d) x, z⟫_ℝ = fderiv ℝ (rho α β d) x z := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma sig_lip (s t : ℝ) :
    |Real.exp s / (Real.exp s + 1) - Real.exp t / (Real.exp t + 1)| ≤ 1 / 4 * |s - t| := by
  have hd : ∀ u, HasDerivAt (fun v => Real.exp v / (Real.exp v + 1))
      (Real.exp u / (Real.exp u + 1) ^ 2) u := by
    intro u
    have h := (Real.hasDerivAt_exp u).div ((Real.hasDerivAt_exp u).add_const 1)
      (by positivity)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hb : ∀ u, |Real.exp u / (Real.exp u + 1) ^ 2| ≤ 1 / 4 := by
    intro u
    have he := Real.exp_pos u
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (Real.exp u - 1)]
  have key : ∀ a b : ℝ, a < b →
      |Real.exp b / (Real.exp b + 1) - Real.exp a / (Real.exp a + 1)| ≤ 1 / 4 * |b - a| := by
    intro a b hab
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (fun v => Real.exp v / (Real.exp v + 1))
      (fun u => Real.exp u / (Real.exp u + 1) ^ 2) hab
      (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
    have hba : 0 < b - a := by linarith
    have : Real.exp b / (Real.exp b + 1) - Real.exp a / (Real.exp a + 1) =
        Real.exp c / (Real.exp c + 1) ^ 2 * (b - a) := by
      rw [hc]; field_simp
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_right (hb c) (abs_nonneg _)
  rcases lt_trichotomy s t with h | h | h
  · rw [abs_sub_comm, abs_sub_comm s t]; exact key s t h
  · subst h; simp
  · exact key t s h

lemma sig_eq (p q : ℝ) :
    Real.exp p / (Real.exp p + Real.exp q) = Real.exp (p - q) / (Real.exp (p - q) + 1) := by
  rw [Real.exp_sub]
  field_simp

lemma exp_lip (ω u v : ℝ) (hu : |u| ≤ ω) (hv : |v| ≤ ω) :
    |Real.exp u - Real.exp v| ≤ Real.exp ω * |u - v| := by
  have key : ∀ a b : ℝ, |a| ≤ ω → b ≤ a →
      |Real.exp a - Real.exp b| ≤ Real.exp ω * |a - b| := by
    intro a b ha hba
    have h1 := Real.add_one_le_exp (b - a)
    have h2 : Real.exp a * Real.exp (b - a) = Real.exp b := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp a ≤ Real.exp ω := Real.exp_le_exp.mpr (abs_le.mp ha).2
    have hea := Real.exp_pos a
    rw [abs_of_nonneg (by linarith [Real.exp_le_exp.mpr hba]), abs_of_nonneg (by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left h1 hea.le]
  rcases le_total v u with h | h
  · exact key u v hu h
  · rw [abs_sub_comm, abs_sub_comm u v]; exact key v u hv h

lemma sum_erase_ite {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ j, if j = i then 0 else f j := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl; intro j _
  by_cases h : j = i <;> simp [h]

lemma degM_ge {n : ℕ} (d : Fin n → Fin n → ℕ) (i : Fin n) : ∑ j, mM d i j ≤ degM d := by
  unfold degM
  exact le_ciSup (f := fun i => ∑ j, mM d i j) (Set.finite_range _).bddAbove i

lemma weight_sum {n : ℕ} (d : Fin n → Fin n → ℕ) (a : Fin n → ℝ) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (a i ^ 2 + a j ^ 2) ≤ degM d * ∑ i, a i ^ 2 := by
  have e : ∑ i, ∑ j ∈ Finset.univ.erase i, (d i j : ℝ) * (a i ^ 2 + a j ^ 2) =
      ∑ i, a i ^ 2 * ∑ j, mM d i j := by
    simp only [sum_erase_ite]
    have h1 : ∀ i, a i ^ 2 * ∑ j, mM d i j = ∑ j, ((if j = i then 0 else (d i j : ℝ) * a i ^ 2) +
        (if j = i then 0 else (d j i : ℝ) * a i ^ 2)) := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      unfold mM
      by_cases h : j = i
      · simp [h]
      · rw [if_neg (Ne.symm h), if_neg h, if_neg h]; ring
    simp only [h1, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, (if j = i then 0 else (d j i : ℝ) * a i ^ 2) =
        ∑ i, ∑ j, (if j = i then 0 else (d i j : ℝ) * a j ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [h2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _
    split_ifs <;> ring
  rw [e, Finset.mul_sum]
  apply Finset.sum_le_sum; intro i _
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (degM_ge d i) (sq_nonneg _)


lemma amgm (p q l : ℝ) (hl : 0 < l) : |p| * |q| ≤ (l * p ^ 2 + q ^ 2 / l) / 2 := by
  have h : 0 ≤ (l * |p| - |q|) ^ 2 / l := by positivity
  have e : (l * |p| - |q|) ^ 2 / l = l * p ^ 2 + q ^ 2 / l - 2 * (|p| * |q|) := by
    field_simp
    linear_combination l ^ 2 * (sq_abs p) + sq_abs q
  linarith

lemma grad_inner_diff {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) (x y z : E n) :
    ⟪gradient (fun w => -rho α β d w) x - gradient (fun w => -rho α β d w) y, z⟫_ℝ =
      ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) *
        ((Real.exp (x a) / (Real.exp (x a) + Real.exp (x b)) -
          Real.exp (y a) / (Real.exp (y a) + Real.exp (y b))) * (z a - z b)) +
      β * ∑ a, (Real.exp (x a) - Real.exp (y a)) * z a := by
  have gn : ∀ u, gradient (fun w => -rho α β d w) u = -gradient (rho α β d) u := by
    intro u; unfold gradient; rw [fderiv_fun_neg]; simp
  rw [gn, gn, inner_sub_left, inner_neg_left, inner_neg_left, inner_grad, inner_grad,
    dir_deriv, dir_deriv, Finset.mul_sum]
  have h1 : ∀ a b, (d a b : ℝ) * ((Real.exp (x a) / (Real.exp (x a) + Real.exp (x b)) -
          Real.exp (y a) / (Real.exp (y a) + Real.exp (y b))) * (z a - z b)) =
      -((d a b : ℝ) * (z a - (Real.exp (x a) * z a + Real.exp (x b) * z b) /
        (Real.exp (x a) + Real.exp (x b)))) +
      (d a b : ℝ) * (z a - (Real.exp (y a) * z a + Real.exp (y b) * z b) /
        (Real.exp (y a) + Real.exp (y b))) := by
    intro a b
    have : 0 < Real.exp (x a) + Real.exp (x b) := by positivity
    have : 0 < Real.exp (y a) + Real.exp (y b) := by positivity
    field_simp
    ring
  simp only [h1, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have h2 : ∀ a, β * ((Real.exp (x a) - Real.exp (y a)) * z a) =
      -((α - 1) * z a - β * (Real.exp (x a) * z a)) + ((α - 1) * z a - β * (Real.exp (y a) * z a)) := by
    intro a; ring
  simp only [h2, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

lemma diff_sq_sum {n : ℕ} (d : Fin n → Fin n → ℕ) (u : Fin n → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (u a - u b) ^ 2 ≤
      2 * degM d * ∑ a, u a ^ 2 := by
  have h := weight_sum d u
  have : ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (u a - u b) ^ 2 ≤
      ∑ a, ∑ b ∈ Finset.univ.erase a, 2 * ((d a b : ℝ) * (u a ^ 2 + u b ^ 2)) := by
    apply Finset.sum_le_sum; intro a _
    apply Finset.sum_le_sum; intro b _
    have : (0 : ℝ) ≤ d a b := by positivity
    nlinarith [sq_nonneg (u a + u b)]
  simp only [← Finset.mul_sum] at this
  linarith


end Aux_AccelMM_F1

open AccelMM.BTMap Aux_AccelMM_F1 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 ≤ α) (hβ : 0 < β) (hω : 0 ≤ ω) :
    SmoothOn (fun w => -rho α β d w) (box ω) (degM d / 2 + Real.exp ω * β) := by
  intro x hx y hy
  set D := gradient (fun w => -rho α β d w) x - gradient (fun w => -rho α β d w) y with hD
  have hdeg : 0 ≤ degM d := by
    unfold degM
    exact Real.iSup_nonneg fun i => Finset.sum_nonneg fun j _ => by
      unfold mM; split_ifs <;> positivity
  have hnorm : ∀ v : E n, ‖v‖ ^ 2 = ∑ i, v i ^ 2 := fun v => EuclideanSpace.real_norm_sq_eq v
  -- the key bound
  have bound : ∀ z : E n, ∀ l : ℝ, 0 < l →
      ⟪D, z⟫_ℝ ≤ (degM d / 4 + Real.exp ω * β / 2) * (l * ‖x - y‖ ^ 2 + ‖z‖ ^ 2 / l) := by
    intro z l hl
    rw [hD, grad_inner_diff, hnorm, hnorm]
    set u : Fin n → ℝ := fun i => x i - y i with hu
    have T1 : ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) *
        ((Real.exp (x a) / (Real.exp (x a) + Real.exp (x b)) -
          Real.exp (y a) / (Real.exp (y a) + Real.exp (y b))) * (z a - z b)) ≤
        ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) *
          (1 / 8 * (l * (u a - u b) ^ 2 + (z a - z b) ^ 2 / l)) := by
      apply Finset.sum_le_sum; intro a _
      apply Finset.sum_le_sum; intro b _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [sig_eq, sig_eq]
      have hs := sig_lip (x a - x b) (y a - y b)
      have hm := amgm (u a - u b) (z a - z b) l hl
      have e : x a - x b - (y a - y b) = u a - u b := by simp only [hu]; ring
      rw [e] at hs
      calc _ ≤ |Real.exp (x a - x b) / (Real.exp (x a - x b) + 1) -
            Real.exp (y a - y b) / (Real.exp (y a - y b) + 1)| * |z a - z b| := by
              rw [← abs_mul]; exact le_abs_self _
        _ ≤ 1 / 4 * |u a - u b| * |z a - z b| :=
              mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        _ ≤ _ := by nlinarith
    have T1' : ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) *
          (1 / 8 * (l * (u a - u b) ^ 2 + (z a - z b) ^ 2 / l)) =
        l / 8 * (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (u a - u b) ^ 2) +
          (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (z a - z b) ^ 2) / l / 8 := by
      have h : ∀ a b, (d a b : ℝ) * (1 / 8 * (l * (u a - u b) ^ 2 + (z a - z b) ^ 2 / l)) =
          l / 8 * ((d a b : ℝ) * (u a - u b) ^ 2) + 1 / (8 * l) * ((d a b : ℝ) * (z a - z b) ^ 2) := by
        intro a b; field_simp
      simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
      field_simp
    have Du := diff_sq_sum d u
    have Dz := diff_sq_sum d (fun i => z i)
    have T2 : ∑ a, (Real.exp (x a) - Real.exp (y a)) * z a ≤
        Real.exp ω * l / 2 * (∑ a, u a ^ 2) + Real.exp ω * ((∑ a, z a ^ 2) / l) / 2 := by
      have h : ∑ a, (Real.exp (x a) - Real.exp (y a)) * z a ≤
          ∑ a, (Real.exp ω * l / 2 * u a ^ 2 + Real.exp ω / (2 * l) * z a ^ 2) := by
        apply Finset.sum_le_sum; intro a _
        have he := exp_lip ω (x a) (y a) (hx a) (hy a)
        have hm := amgm (u a) (z a) l hl
        have heω := Real.exp_pos ω
        have e2 : Real.exp ω * l / 2 * u a ^ 2 + Real.exp ω / (2 * l) * z a ^ 2 =
            Real.exp ω * ((l * u a ^ 2 + z a ^ 2 / l) / 2) := by field_simp
        rw [e2]
        calc (Real.exp (x a) - Real.exp (y a)) * z a
            ≤ |Real.exp (x a) - Real.exp (y a)| * |z a| := by
                rw [← abs_mul]; exact le_abs_self _
          _ ≤ Real.exp ω * |u a| * |z a| :=
                mul_le_mul_of_nonneg_right he (abs_nonneg _)
          _ = Real.exp ω * (|u a| * |z a|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hm heω.le
      have e : ∑ a, (Real.exp ω * l / 2 * u a ^ 2 + Real.exp ω / (2 * l) * z a ^ 2) =
          Real.exp ω * l / 2 * (∑ a, u a ^ 2) + Real.exp ω * ((∑ a, z a ^ 2) / l) / 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        field_simp
      linarith
    have A1 := mul_le_mul_of_nonneg_left Du (show (0 : ℝ) ≤ l / 8 by positivity)
    have A2 := div_le_div_of_nonneg_right Dz hl.le
    have e5 : (∑ i, (x - y) i ^ 2) = ∑ a, u a ^ 2 := by
      apply Finset.sum_congr rfl; intro i _; simp [hu]
    rw [e5]
    rw [T1'] at T1
    have A3 := mul_le_mul_of_nonneg_left T2 hβ.le
    have e7 : (2 * degM d * ∑ a, z a ^ 2) / l = 2 * degM d * ((∑ a, z a ^ 2) / l) := by ring
    rw [e7] at A2
    set U := ∑ a, u a ^ 2
    set Z := ∑ a, z a ^ 2
    set Zl := Z / l
    have goal_eq : (degM d / 4 + Real.exp ω * β / 2) * (l * U + Zl) =
        l / 8 * (2 * degM d * U) + 2 * degM d * Zl / 8 +
          β * (Real.exp ω * l / 2 * U + Real.exp ω * Zl / 2) := by ring
    rw [goal_eq]
    linarith
  -- conclude
  have hμ : 0 ≤ degM d / 2 + Real.exp ω * β := by positivity
  by_cases hD0 : ‖D‖ = 0
  · rw [hD0]; positivity
  by_cases hxy : ‖x - y‖ = 0
  · have : x = y := by rw [norm_eq_zero, sub_eq_zero] at hxy; exact hxy
    subst this
    exfalso; apply hD0; rw [hD, sub_self, norm_zero]
  have hNp : 0 < ‖D‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD0)
  have hMp : 0 < ‖x - y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hxy)
  have hb := bound D (‖D‖ / ‖x - y‖) (by positivity)
  rw [real_inner_self_eq_norm_sq] at hb
  have e1 : ‖D‖ / ‖x - y‖ * ‖x - y‖ ^ 2 + ‖D‖ ^ 2 / (‖D‖ / ‖x - y‖) = 2 * (‖D‖ * ‖x - y‖) := by
    field_simp; ring
  rw [e1] at hb
  have : ‖D‖ * ‖D‖ ≤ ((degM d / 2 + Real.exp ω * β) * ‖x - y‖) * ‖D‖ := by nlinarith
  exact le_of_mul_le_mul_right this hNp
-- touch

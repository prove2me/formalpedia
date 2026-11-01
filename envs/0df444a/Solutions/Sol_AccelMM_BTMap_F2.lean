-- Prove2me | solution 1 for AccelMM.BTMap.F2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:42:48.776198+00:00
-- url     : https://prove2.me/submissions/7aa16a11-d15c-40c1-b605-e754f9551b92

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

open scoped InnerProductSpace

namespace Aux_AccelMM_F2

open AccelMM.BTMap Matrix

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


lemma inner_dot {n : ℕ} (x y : E n) : ⟪x, y⟫_ℝ = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; simp

lemma quad_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (w : E n) :
    w.ofLp ⬝ᵥ (A *ᵥ w.ofLp) =
      ∑ j, hA.eigenvalues j * ⟪hA.eigenvectorBasis j, w⟫_ℝ ^ 2 := by
  set b := hA.eigenvectorBasis
  have hw : w = ∑ j, ⟪b j, w⟫_ℝ • b j := (b.sum_repr' w).symm
  have hAw : A *ᵥ w.ofLp = ∑ j, (⟪b j, w⟫_ℝ * hA.eigenvalues j) • (b j).ofLp := by
    conv_lhs => rw [hw]
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Matrix.mulVec_sum, Matrix.mulVec_smul]
    apply Finset.sum_congr rfl; intro j _
    rw [show (b j).ofLp = ⇑(b j) from rfl, hA.mulVec_eigenvectorBasis j, smul_smul]
  rw [hAw, dotProduct_sum]
  apply Finset.sum_congr rfl; intro j _
  rw [dotProduct_smul, ← inner_dot, real_inner_comm, smul_eq_mul]
  ring

lemma mM_symm {n : ℕ} (d : Fin n → Fin n → ℕ) (i j : Fin n) : mM d i j = mM d j i := by
  unfold mM
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), add_comm]

lemma mM_nonneg {n : ℕ} (d : Fin n → Fin n → ℕ) (i j : Fin n) : 0 ≤ mM d i j := by
  unfold mM; split_ifs <;> positivity

lemma lap_quad {n : ℕ} (d : Fin n → Fin n → ℕ) (v : Fin n → ℝ) :
    0 ≤ v ⬝ᵥ (lapM d *ᵥ v) := by
  have e1 : v ⬝ᵥ (lapM d *ᵥ v) =
      ∑ i, ∑ j, mM d i j * v i ^ 2 - ∑ i, ∑ j, mM d i j * v i * v j := by
    have hrow : ∀ i, ∑ j, lapM d i j * v j = (∑ j, mM d i j) * v i - ∑ j, mM d i j * v j := by
      intro i
      simp [lapM, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul, Finset.sum_sub_distrib,
        ite_mul]
    simp only [dotProduct, Matrix.mulVec, hrow]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have e2 : ∑ i, ∑ j, mM d i j * v j ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mM_symm]
  have e3 : 2 * (v ⬝ᵥ (lapM d *ᵥ v)) = ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 := by
    rw [e1]
    have : ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2
        - 2 * ∑ i, ∑ j, mM d i j * v i * v j + ∑ i, ∑ j, mM d i j * v j ^ 2 := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, e2]; ring
  have : 0 ≤ ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mM_nonneg d i j) (sq_nonneg _)
  linarith


lemma lap_ones {n : ℕ} (d : Fin n → Fin n → ℕ) : lapM d *ᵥ (ones n).ofLp = 0 := by
  ext i
  simp [lapM, ones, Matrix.sub_mulVec, Matrix.mulVec, dotProduct, Matrix.diagonal_apply]

lemma spec {n : ℕ} (d : Fin n → Fin n → ℕ) (w : E n) (hw : ⟪w, ones n⟫_ℝ = 0) :
    algConn d * ‖w‖ ^ 2 ≤ w.ofLp ⬝ᵥ (lapM d *ᵥ w.ofLp) := by
  have hq := lap_quad d w.ofLp
  unfold algConn
  split_ifs with h
  swap
  · simpa using hq
  set hA := lapM_isHermitian d
  set lam2 := hA.eigenvalues₀ ⟨Fintype.card (Fin n) - 2, by omega⟩
  by_cases hl : lam2 ≤ 0
  · nlinarith [sq_nonneg ‖w‖]
  push_neg at hl
  set b := hA.eigenvectorBasis
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
  set k0 := e ⟨Fintype.card (Fin n) - 1, by omega⟩
  have hev : ∀ j, hA.eigenvalues j = hA.eigenvalues₀ (e.symm j) := by
    intro j; simp [Matrix.IsHermitian.eigenvalues, e]
  have factA : ∀ j, j ≠ k0 → lam2 ≤ hA.eigenvalues j := by
    intro j hj
    rw [hev]
    apply hA.eigenvalues₀_antitone
    have h1 : e.symm j ≠ ⟨Fintype.card (Fin n) - 1, by omega⟩ := by
      intro h2; apply hj; rw [show k0 = e ⟨Fintype.card (Fin n) - 1, by omega⟩ from rfl, ← h2]; simp
    have h3 := (e.symm j).isLt
    have h4 : (e.symm j).val ≠ Fintype.card (Fin n) - 1 := fun h5 => h1 (Fin.ext h5)
    show (e.symm j).val ≤ Fintype.card (Fin n) - 2
    omega
  -- ones expansion
  have hsym : ∀ j, hA.eigenvalues j * ⟪b j, ones n⟫_ℝ = 0 := by
    intro j
    have h1 : (b j).ofLp ⬝ᵥ (lapM d *ᵥ (ones n).ofLp) = 0 := by rw [lap_ones]; simp
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at h1
    have ht : (lapM d)ᵀ = lapM d := by
      have := hA.eq
      rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
      exact this
    rw [ht, show (b j).ofLp = ⇑(b j) from rfl, hA.mulVec_eigenvectorBasis j, smul_dotProduct,
      smul_eq_mul] at h1
    rw [inner_dot]; exact h1
  have hb0 : ∀ j, j ≠ k0 → ⟪b j, ones n⟫_ℝ = 0 := by
    intro j hj
    have := hsym j
    have hpos : 0 < hA.eigenvalues j := lt_of_lt_of_le hl (factA j hj)
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact h
  have hones : ones n = ⟪b k0, ones n⟫_ℝ • b k0 := by
    conv_lhs => rw [← b.sum_repr' (ones n)]
    rw [Finset.sum_eq_single k0]
    · intro j _ hj; rw [hb0 j hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hones_ne : ones n ≠ 0 := by
    intro h0
    have : (ones n) ⟨0, by simp at h; omega⟩ = 0 := by rw [h0]; rfl
    simp [ones] at this
  have hck0 : ⟪b k0, w⟫_ℝ = 0 := by
    have h1 : ⟪b k0, ones n⟫_ℝ ≠ 0 := by
      intro h0; apply hones_ne; rw [hones, h0, zero_smul]
    have h2 : ⟪w, ones n⟫_ℝ = ⟪b k0, ones n⟫_ℝ * ⟪w, b k0⟫_ℝ := by
      conv_lhs => rw [hones]
      rw [real_inner_smul_right]
    rw [hw] at h2
    rcases mul_eq_zero.mp h2.symm with h | h
    · exact absurd h h1
    · rw [real_inner_comm]; exact h
  rw [quad_expand _ hA w, ← b.sum_sq_inner_right w, Finset.mul_sum]
  apply Finset.sum_le_sum; intro j _
  by_cases hj : j = k0
  · rw [hj, hck0]; simp
  · exact mul_le_mul_of_nonneg_right (factA j hj) (sq_nonneg _)

lemma lap_two {n : ℕ} (d : Fin n → Fin n → ℕ) (v : Fin n → ℝ) :
    2 * (v ⬝ᵥ (lapM d *ᵥ v)) = ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 := by
  have e1 : v ⬝ᵥ (lapM d *ᵥ v) =
      ∑ i, ∑ j, mM d i j * v i ^ 2 - ∑ i, ∑ j, mM d i j * v i * v j := by
    have hrow : ∀ i, ∑ j, lapM d i j * v j = (∑ j, mM d i j) * v i - ∑ j, mM d i j * v j := by
      intro i
      simp [lapM, Matrix.sub_apply, Matrix.diagonal_apply, sub_mul, Finset.sum_sub_distrib,
        ite_mul]
    simp only [dotProduct, Matrix.mulVec, hrow]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro i _
    rw [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  have e2 : ∑ i, ∑ j, mM d i j * v j ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    rw [mM_symm]
  have e3 : 2 * (v ⬝ᵥ (lapM d *ᵥ v)) = ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 := by
    rw [e1]
    have : ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 = ∑ i, ∑ j, mM d i j * v i ^ 2
        - 2 * ∑ i, ∑ j, mM d i j * v i * v j + ∑ i, ∑ j, mM d i j * v j ^ 2 := by
      rw [Finset.mul_sum]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this, e2]; ring
  exact e3


lemma QL_eq {n : ℕ} (d : Fin n → Fin n → ℕ) (v : Fin n → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2 = v ⬝ᵥ (lapM d *ᵥ v) := by
  have h2 := lap_two d v
  have h3 : ∑ i, ∑ j, mM d i j * (v i - v j) ^ 2 =
      2 * ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2 := by
    simp only [sum_erase_ite]
    have h1 : ∀ i j, mM d i j * (v i - v j) ^ 2 =
        (if j = i then 0 else (d i j : ℝ) * (v i - v j) ^ 2) +
        (if j = i then 0 else (d j i : ℝ) * (v j - v i) ^ 2) := by
      intro i j
      unfold mM
      by_cases h : j = i
      · simp [h]
      · rw [if_neg (Ne.symm h), if_neg h, if_neg h]; ring
    simp only [h1, Finset.sum_add_distrib]
    have h4 : ∑ i, ∑ j, (if j = i then 0 else (d j i : ℝ) * (v j - v i) ^ 2) =
        ∑ i, ∑ j, (if j = i then 0 else (d i j : ℝ) * (v i - v j) ^ 2) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      by_cases h : j = i
      · subst h; simp
      · rw [if_neg h, if_neg (Ne.symm h)]
    rw [h4]; ring
  linarith

lemma sig_lower (ω s t : ℝ) (hs : |s| ≤ 2 * ω) (ht : |t| ≤ 2 * ω) :
    cOmega ω * (s - t) ^ 2 ≤
      (Real.exp s / (Real.exp s + 1) - Real.exp t / (Real.exp t + 1)) * (s - t) := by
  have hd : ∀ u, HasDerivAt (fun v => Real.exp v / (Real.exp v + 1))
      (Real.exp u / (Real.exp u + 1) ^ 2) u := by
    intro u
    have h := (Real.hasDerivAt_exp u).div ((Real.hasDerivAt_exp u).add_const 1)
      (by positivity)
    refine h.congr_deriv ?_
    field_simp
    ring
  have hb : ∀ u, |u| ≤ 2 * ω → cOmega ω ≤ Real.exp u / (Real.exp u + 1) ^ 2 := by
    intro u hu
    rw [abs_le] at hu
    unfold cOmega
    have E1 : Real.exp (2 * ω) * Real.exp (-(2 * ω)) = 1 := by rw [← Real.exp_add]; simp
    have E2 : (Real.exp (-ω) + Real.exp ω) ^ 2 = Real.exp (-(2 * ω)) + 2 + Real.exp (2 * ω) := by
      have a1 : Real.exp (-ω) ^ 2 = Real.exp (-(2 * ω)) := by rw [← Real.exp_nat_mul]; ring_nf
      have a2 : Real.exp ω ^ 2 = Real.exp (2 * ω) := by rw [← Real.exp_nat_mul]; ring_nf
      have a3 : Real.exp (-ω) * Real.exp ω = 1 := by rw [← Real.exp_add]; simp
      nlinarith
    have y1 : Real.exp u ≤ Real.exp (2 * ω) := Real.exp_le_exp.mpr hu.2
    have y2 : Real.exp (-(2 * ω)) ≤ Real.exp u := Real.exp_le_exp.mpr (by linarith)
    have hy := Real.exp_pos u
    rw [E2, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (sub_nonneg.mpr y1) (sub_nonneg.mpr y2)]
  have key : ∀ a b : ℝ, a < b → |a| ≤ 2 * ω → |b| ≤ 2 * ω →
      cOmega ω * (b - a) ^ 2 ≤
        (Real.exp b / (Real.exp b + 1) - Real.exp a / (Real.exp a + 1)) * (b - a) := by
    intro a b hab ha hb'
    obtain ⟨c, hc1, hc⟩ := exists_hasDerivAt_eq_slope (fun v => Real.exp v / (Real.exp v + 1))
      (fun u => Real.exp u / (Real.exp u + 1) ^ 2) hab
      (fun u _ => (hd u).continuousAt.continuousWithinAt) (fun u _ => hd u)
    have hba : 0 < b - a := by linarith
    have hcb : |c| ≤ 2 * ω := by
      rw [abs_le] at ha hb' ⊢; constructor <;> linarith [hc1.1, hc1.2]
    have : Real.exp b / (Real.exp b + 1) - Real.exp a / (Real.exp a + 1) =
        Real.exp c / (Real.exp c + 1) ^ 2 * (b - a) := by
      rw [hc]; field_simp
    rw [this]
    have := hb c hcb
    nlinarith [sq_nonneg (b - a)]
  rcases lt_trichotomy s t with h | h | h
  · have := key s t h hs ht
    nlinarith
  · subst h; simp
  · exact key t s h ht hs

lemma exp_lower (ω u v : ℝ) (hu : |u| ≤ ω) (hv : |v| ≤ ω) :
    Real.exp (-ω) * (u - v) ^ 2 ≤ (Real.exp u - Real.exp v) * (u - v) := by
  have key : ∀ a b : ℝ, |b| ≤ ω → b ≤ a →
      Real.exp (-ω) * (a - b) ^ 2 ≤ (Real.exp a - Real.exp b) * (a - b) := by
    intro a b hb hba
    have h1 := Real.add_one_le_exp (a - b)
    have h2 : Real.exp b * Real.exp (a - b) = Real.exp a := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 : Real.exp (-ω) ≤ Real.exp b := Real.exp_le_exp.mpr (by linarith [(abs_le.mp hb).1])
    have heb := Real.exp_pos b
    have h4 : Real.exp b * (a - b) ≤ Real.exp a - Real.exp b := by nlinarith
    have h5 : 0 ≤ a - b := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h3 h5, mul_le_mul_of_nonneg_right h4 h5]
  rcases le_total v u with h | h
  · exact key u v hv h
  · have := key v u hu h; nlinarith

lemma grad_mono {n : ℕ} (α β ω : ℝ) (d : Fin n → Fin n → ℕ) (hβ : 0 < β)
    (p q v : E n) (hp : p ∈ box ω) (hq : q ∈ box ω) (t : ℝ) (ht : 0 < t)
    (hpq : ∀ a, p a - q a = t * v a) :
    t * (cOmega ω * (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2) +
        Real.exp (-ω) * β * ∑ a, v a ^ 2) ≤
      ⟪gradient (fun w => -rho α β d w) p - gradient (fun w => -rho α β d w) q, v⟫_ℝ := by
  rw [grad_inner_diff]
  have T1 : ∀ a b, t * (cOmega ω * ((d a b : ℝ) * (v a - v b) ^ 2)) ≤ (d a b : ℝ) *
        ((Real.exp (p a) / (Real.exp (p a) + Real.exp (p b)) -
          Real.exp (q a) / (Real.exp (q a) + Real.exp (q b))) * (v a - v b)) := by
    intro a b
    rw [sig_eq, sig_eq]
    have hs : |p a - p b| ≤ 2 * ω := by
      have := hp a; have := hp b; rw [abs_le] at *; constructor <;> linarith
    have hs' : |q a - q b| ≤ 2 * ω := by
      have := hq a; have := hq b; rw [abs_le] at *; constructor <;> linarith
    have h := sig_lower ω _ _ hs hs'
    have e : p a - p b - (q a - q b) = t * (v a - v b) := by
      have := hpq a; have := hpq b; linarith
    rw [e] at h
    set X := Real.exp (p a - p b) / (Real.exp (p a - p b) + 1) -
      Real.exp (q a - q b) / (Real.exp (q a - q b) + 1)
    have h' : t * (t * (cOmega ω * (v a - v b) ^ 2)) ≤ t * (X * (v a - v b)) := by nlinarith
    have h'' := le_of_mul_le_mul_left h' ht
    have hd : (0 : ℝ) ≤ d a b := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h'' hd]
  have T2 : ∀ a, t * (Real.exp (-ω) * β * v a ^ 2) ≤ β * ((Real.exp (p a) - Real.exp (q a)) * v a) := by
    intro a
    have h := exp_lower ω (p a) (q a) (hp a) (hq a)
    rw [hpq a] at h
    have h' : t * (t * (Real.exp (-ω) * v a ^ 2)) ≤ t * ((Real.exp (p a) - Real.exp (q a)) * v a) := by
      nlinarith
    have h'' := le_of_mul_le_mul_left h' ht
    nlinarith [mul_le_mul_of_nonneg_left h'' hβ.le]
  have S1 := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ.erase a) => T1 a b
  have S2 := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => T2 a
  simp only [← Finset.mul_sum] at S1 S2
  rw [mul_add]
  linarith

lemma box_convex {n : ℕ} (ω : ℝ) : Convex ℝ (box (n := n) ω) := by
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  have e : (a • x + b • y) i = a * x i + b * y i := by simp
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith

lemma algConn_nonneg {n : ℕ} (d : Fin n → Fin n → ℕ) : 0 ≤ algConn d := by
  unfold algConn
  split_ifs with h
  · set hA := lapM_isHermitian d
    set k : Fin (Fintype.card (Fin n)) := ⟨Fintype.card (Fin n) - 2, by omega⟩
    set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))
    have h1 : hA.eigenvalues₀ k = hA.eigenvalues (e k) := by
      simp [Matrix.IsHermitian.eigenvalues, e]
    rw [h1, hA.eigenvalues_eq]
    simpa using lap_quad d _
  · exact le_refl 0


lemma strong_lower {n : ℕ} (α β ω : ℝ) (d : Fin n → Fin n → ℕ) (hβ : 0 < β)
    (x y : E n) (hx : x ∈ box ω) (hy : y ∈ box ω) :
    -rho α β d x + ⟪gradient (fun w => -rho α β d w) x, y - x⟫_ℝ +
      1 / 2 * (cOmega ω * (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * ((y - x) a - (y - x) b) ^ 2) +
        Real.exp (-ω) * β * ∑ a, (y - x) a ^ 2) ≤ -rho α β d y := by
  set f : E n → ℝ := fun w => -rho α β d w with hf
  set v := y - x with hv
  set K := cOmega ω * (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2) +
        Real.exp (-ω) * β * ∑ a, v a ^ 2 with hK
  set c := ⟪gradient f x, v⟫_ℝ with hc
  have hfd : Differentiable ℝ f := (rho_diff α β d).neg
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - t ^ 2 / 2 * K
  have hderiv : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • v), v⟫_ℝ - c - t * K) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h1 := (hfd (x + t • v)).hasFDerivAt.comp_hasDerivAt t hline
    have hg : fderiv ℝ f (x + t • v) v = ⟪gradient f (x + t • v), v⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [hg] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => s ^ 2 / 2 * K) (t * K) t := by
      have := ((hasDerivAt_pow 2 t).div_const 2).mul_const K
      refine this.congr_deriv ?_
      push_cast; ring
    exact (h1.sub h2).sub h3
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hmem : x + t • v ∈ box ω := (box_convex ω).add_smul_sub_mem hx hy ⟨ht.1.le, ht.2.le⟩
      have hm := grad_mono α β ω d hβ (x + t • v) x v hmem hx t ht.1 (fun a => by simp)
      rw [inner_sub_left] at hm
      rw [hK]; linarith
  have h := hmono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = y := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  simp only [hf] at h hc ⊢
  linarith

end Aux_AccelMM_F2

open AccelMM.BTMap Aux_AccelMM_F2 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 ≤ α) (hβ : 0 < β) (hω : 0 ≤ ω)
    (wstar : E n) (hstar : ∀ w, rho α β d w ≤ rho α β d wstar) (hstarW : wstar ∈ box ω) :
    PLOn (fun w => -rho α β d w) (X0 (fun w => -rho α β d w) (box ω) (ones n))
      (cOmega ω * algConn d + Real.exp (-ω) * β) wstar := by
  intro x hx
  obtain ⟨hxb, hxg⟩ := hx
  simp only [Set.mem_setOf_eq] at hxg
  set f : E n → ℝ := fun w => -rho α β d w with hf
  set g := gradient f x with hg
  set γ := cOmega ω * algConn d + Real.exp (-ω) * β with hγ
  have hcO : 0 ≤ cOmega ω := by unfold cOmega; positivity
  have hγpos : 0 < γ := by
    have := algConn_nonneg d
    have : 0 < Real.exp (-ω) * β := by positivity
    have : 0 ≤ cOmega ω * algConn d := mul_nonneg hcO (algConn_nonneg d)
    linarith
  have hSL := strong_lower α β ω d hβ x wstar hxb hstarW
  set v := wstar - x with hv
  set c : ℝ := (∑ i, v i) / n with hc
  set w : E n := v - c • ones n with hw
  have hwi : ∀ i, w i = v i - c := by intro i; simp [hw, ones]
  have hsumw : ∑ i, w i = 0 := by
    simp only [hwi, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · rw [hc]; field_simp; ring
  have hwones : ⟪w, ones n⟫_ℝ = 0 := by
    rw [inner_dot]; simp [ones, dotProduct, hsumw]
  have hQL : ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2 =
      ∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (w a - w b) ^ 2 := by
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hwi, hwi]; ring
  have hsq : ‖w‖ ^ 2 ≤ ∑ a, v a ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have : ∑ a, v a ^ 2 = ∑ a, w a ^ 2 + 2 * c * ∑ a, w a + ∑ a : Fin n, c ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [hwi]; ring
    rw [this, hsumw]
    have : 0 ≤ ∑ a : Fin n, c ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg c
    linarith
  have hspec := spec d w hwones
  rw [← QL_eq] at hspec
  have hgv : ⟪g, v⟫_ℝ = ⟪g, w⟫_ℝ := by
    have : v = w + c • ones n := by rw [hw]; abel
    rw [this, inner_add_right, real_inner_smul_right, hxg, mul_zero, add_zero]
  have hK : γ * ‖w‖ ^ 2 ≤ cOmega ω * (∑ a, ∑ b ∈ Finset.univ.erase a, (d a b : ℝ) * (v a - v b) ^ 2) +
      Real.exp (-ω) * β * ∑ a, v a ^ 2 := by
    rw [hQL, hγ, add_mul, mul_assoc]
    have h1 := mul_le_mul_of_nonneg_left hspec hcO
    have h2 := mul_le_mul_of_nonneg_left hsq (show (0 : ℝ) ≤ Real.exp (-ω) * β by positivity)
    linarith
  have hcs : -⟪g, w⟫_ℝ ≤ ‖g‖ * ‖w‖ := by
    have := real_inner_le_norm g (-w)
    rw [inner_neg_right, norm_neg] at this; exact this
  have hSL' : -rho α β d x + ⟪g, w⟫_ℝ + 1 / 2 * (cOmega ω * (∑ a, ∑ b ∈ Finset.univ.erase a,
      (d a b : ℝ) * (v a - v b) ^ 2) + Real.exp (-ω) * β * ∑ a, v a ^ 2) ≤ -rho α β d wstar := by
    rw [← hgv]; exact hSL
  show -rho α β d x - -rho α β d wstar ≤ 1 / (2 * γ) * ‖g‖ ^ 2
  have key : ‖g‖ * ‖w‖ - γ / 2 * ‖w‖ ^ 2 ≤ 1 / (2 * γ) * ‖g‖ ^ 2 := by
    have : 0 ≤ (‖g‖ - γ * ‖w‖) ^ 2 / (2 * γ) := by positivity
    have e : (‖g‖ - γ * ‖w‖) ^ 2 / (2 * γ) =
        1 / (2 * γ) * ‖g‖ ^ 2 - (‖g‖ * ‖w‖ - γ / 2 * ‖w‖ ^ 2) := by
      field_simp; ring
    linarith
  linarith

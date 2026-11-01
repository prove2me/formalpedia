-- Prove2me | solution 1 for AccelMM.BTMap.corollary_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:20:34.2332+00:00
-- url     : https://prove2.me/submissions/c6c9d317-fdbe-4f43-99e2-45e2f082dd45

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model
import Theorems.Thm_AccelMM_BTMap_F1
import Theorems.Thm_AccelMM_BTMap_F2
import Theorems.Thm_AccelMM_BTMap_lemma_3_5
import Theorems.Thm_AccelMM_BTMap_lemma_4_2
import Theorems.Thm_AccelMM_BTMap_surr_minorizes

open scoped InnerProductSpace

namespace Aux_AccelMM_Cor42

open AccelMM.BTMap Matrix

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

lemma descent {n : ℕ} (f : E n → ℝ) (hf : Differentiable ℝ f) (X : Set (E n))
    (hX : Convex ℝ X) (μ : ℝ) (hS : SmoothOn f X μ) (x z : E n) (hx : x ∈ X) (hz : z ∈ X) :
    f z ≤ f x + ⟪gradient f x, z - x⟫_ℝ + μ / 2 * ‖z - x‖ ^ 2 := by
  set v := z - x with hv
  set c := ⟪gradient f x, v⟫_ℝ with hc
  let ψ : ℝ → ℝ := fun t => f (x + t • v) - t * c - μ / 2 * t ^ 2 * ‖v‖ ^ 2
  have hderiv : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • v), v⟫_ℝ - c - μ * t * ‖v‖ ^ 2) t := by
    intro t
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have hfd : HasFDerivAt f (fderiv ℝ f (x + t • v)) (x + t • v) := (hf _).hasFDerivAt
    have h1 := hfd.comp_hasDerivAt t hline
    have hg : fderiv ℝ f (x + t • v) v = ⟪gradient f (x + t • v), v⟫_ℝ := by
      rw [gradient, InnerProductSpace.toDual_symm_apply]
    rw [hg] at h1
    have h2 : HasDerivAt (fun s : ℝ => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun s : ℝ => μ / 2 * s ^ 2 * ‖v‖ ^ 2) (μ * t * ‖v‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (μ / 2)).mul_const (‖v‖ ^ 2)
      refine this.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t).deriv]
      have hmem : x + t • v ∈ X := hX.add_smul_sub_mem hx hz ⟨ht.1.le, ht.2.le⟩
      have hL := hS (x + t • v) hmem x hx
      have hn : ‖x + t • v - x‖ = t * ‖v‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      have hi : ⟪gradient f (x + t • v), v⟫_ℝ - c ≤
          ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := by
        rw [hc, ← inner_sub_left]
        exact real_inner_le_norm _ _
      rw [hn] at hL
      nlinarith [norm_nonneg v, mul_le_mul_of_nonneg_right hL (norm_nonneg v)]
  have h := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  have e1 : x + (1 : ℝ) • v = z := by rw [one_smul, hv, add_sub_cancel]
  have e0 : x + (0 : ℝ) • v = x := by rw [zero_smul, add_zero]
  simp only [ψ, e1, e0] at h
  norm_num at h
  linarith


lemma degM_nonneg {n : ℕ} (d : Fin n → Fin n → ℕ) : 0 ≤ degM d := by
  unfold degM
  apply Real.iSup_nonneg
  intro i
  exact Finset.sum_nonneg fun j _ => mM_nonneg d i j

lemma rho_diff {n : ℕ} (α β : ℝ) (d : Fin n → Fin n → ℕ) : Differentiable ℝ (rho α β d) := by
  have hc : ∀ i : Fin n, Differentiable ℝ (fun x : E n => x i) := fun i =>
    (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable
  unfold rho loglik logPrior
  fun_prop (disch := (intros; positivity))

lemma grad_neg {n : ℕ} (f : E n → ℝ) (x : E n) : gradient (fun w => - f w) x = - gradient f x := by
  unfold gradient
  rw [fderiv_fun_neg]; simp

lemma box_convex {n : ℕ} (ω : ℝ) : Convex ℝ (box (n := n) ω) := by
  intro x hx y hy a b ha hb hab i
  have h1 := hx i
  have h2 := hy i
  have e : (a • x + b • y) i = a * x i + b * y i := by simp
  rw [e]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> nlinarith

end Aux_AccelMM_Cor42

open AccelMM.BTMap Aux_AccelMM_Cor42 in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 < α) (hβ : 0 < β) (hω : 0 ≤ ω)
    (wstar : E n) (hstar : ∀ w, rho α β d w ≤ rho α β d wstar) (hstarW : wstar ∈ box ω)
    (w : E n) (hwW : w ∈ box ω) (hwPi : ∃ v, w = Pi α β v)
    (hvirt : w + (1 / ((degM d / 2 + Real.exp ω * β) + Real.exp (2 * ω) * degM d / 2)) •
        gradient (rho α β d) w ∈ box ω)
    (xm : E n) (hxm : ∀ z, rhoSurr α β d z w ≤ rhoSurr α β d xm w) :
    rho α β d wstar - rho α β d (Pi α β xm) ≤
      (1 - (2 * cOmega ω * algConn d + 2 * Real.exp (-ω) * β) /
            ((1 + Real.exp (2 * ω)) * degM d + 2 * Real.exp ω * β)) *
        (rho α β d wstar - rho α β d w) := by
  set f : E n → ℝ := fun x => -rho α β d x with hfdef
  set μ := degM d / 2 + Real.exp ω * β with hμdef
  set δ := Real.exp (2 * ω) * degM d / 2 with hδdef
  set γ := cOmega ω * algConn d + Real.exp (-ω) * β with hγdef
  have hdeg := degM_nonneg d
  have hμ : 0 < μ := by positivity
  have hδ : 0 ≤ δ := by positivity
  have hcO : 0 ≤ cOmega ω := by unfold cOmega; positivity
  have hγ : 0 < γ := by
    have := algConn_nonneg d
    have : 0 < Real.exp (-ω) * β := by positivity
    have : 0 ≤ cOmega ω * algConn d := by positivity
    linarith
  have hμδ : 0 < μ + δ := by linarith
  set G := gradient (rho α β d) w with hG
  set η := 1 / (μ + δ) with hη
  set z := w + η • G with hz
  have hηpos : 0 < η := by positivity
  have hfd : Differentiable ℝ f := (rho_diff α β d).neg
  have hgradf : ∀ x, gradient f x = - gradient (rho α β d) x := fun x => grad_neg _ x
  -- chain
  have L42 := AccelMM.BTMap.lemma_4_2 d α β hα hβ
  have SM := AccelMM.BTMap.surr_minorizes d
  have c1 : rho α β d xm ≤ rho α β d (Pi α β xm) := L42.1 xm
  have c2 : rhoSurr α β d xm w ≤ rho α β d xm := by
    unfold rhoSurr rho; linarith [SM.1 xm w]
  have c3 : rhoSurr α β d z w ≤ rhoSurr α β d xm w := hxm z
  have c4 := AccelMM.BTMap.lemma_3_5 d α β ω hω z w hvirt hwW
  have c5 := descent f hfd (box ω) (box_convex ω) μ (AccelMM.BTMap.F1 d α β ω hα.le hβ hω)
    w z hwW hvirt
  have hzx : z - w = η • G := by rw [hz]; abel
  have hin : ⟪gradient f w, z - w⟫_ℝ = -(η * ‖G‖ ^ 2) := by
    rw [hzx, hgradf, ← hG, inner_neg_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnz : ‖z - w‖ ^ 2 = η ^ 2 * ‖G‖ ^ 2 := by
    rw [hzx, norm_smul, mul_pow, Real.norm_of_nonneg hηpos.le]
  rw [hin, hnz] at c5
  rw [hnz] at c4
  simp only [hfdef] at c5
  have hdesc : rho α β d w + η * ‖G‖ ^ 2 / 2 ≤ rho α β d (Pi α β xm) := by
    have h1 : rho α β d w + η * ‖G‖ ^ 2 - (μ + δ) / 2 * (η ^ 2 * ‖G‖ ^ 2) ≤
        rho α β d (Pi α β xm) := by
      have : -((1 / 2 * Real.exp (2 * ω) * degM d) / 2) = -(δ / 2) := by rw [hδdef]; ring
      rw [this] at c4
      nlinarith
    have e : (μ + δ) / 2 * (η ^ 2 * ‖G‖ ^ 2) = η * ‖G‖ ^ 2 / 2 := by
      have : (μ + δ) * η = 1 := by rw [hη]; field_simp
      have : (μ + δ) * η ^ 2 = η := by rw [pow_two, ← mul_assoc, this, one_mul]
      calc (μ + δ) / 2 * (η ^ 2 * ‖G‖ ^ 2) = ((μ + δ) * η ^ 2) * ‖G‖ ^ 2 / 2 := by ring
        _ = _ := by rw [this]
    linarith
  -- PL at w
  have hwX0 : w ∈ X0 f (box ω) (ones n) := by
    refine ⟨hwW, ?_⟩
    show ⟪gradient f w, ones n⟫_ℝ = 0
    obtain ⟨v, rfl⟩ := hwPi
    rw [hgradf, inner_neg_left, L42.2 v, neg_zero]
  have hPL := AccelMM.BTMap.F2 d α β ω hα.le hβ hω wstar hstar hstarW w hwX0
  simp only [hfdef] at hPL
  rw [hgradf, norm_neg, ← hG] at hPL
  have hPL' : 2 * γ * (rho α β d wstar - rho α β d w) ≤ ‖G‖ ^ 2 := by
    have h2 : 1 / (2 * γ) * ‖G‖ ^ 2 = ‖G‖ ^ 2 / (2 * γ) := by ring
    rw [h2, le_div_iff₀ (by positivity)] at hPL
    linarith
  have hrate : (2 * cOmega ω * algConn d + 2 * Real.exp (-ω) * β) /
      ((1 + Real.exp (2 * ω)) * degM d + 2 * Real.exp ω * β) = γ * η := by
    rw [hη, hγdef, hμdef, hδdef]
    have : 0 < (1 + Real.exp (2 * ω)) * degM d + 2 * Real.exp ω * β := by positivity
    field_simp
    ring
  rw [hrate]
  nlinarith [mul_le_mul_of_nonneg_left hPL' hηpos.le]

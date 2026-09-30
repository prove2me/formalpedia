-- Prove2me | solution 1 for ArrowDebreu.ThmI.lemma_2_5
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T21:31:03.585213+00:00
-- url     : https://prove2.me/submissions/70b21537-40ea-44de-a248-84176564f090

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
open ArrowDebreu.Shared

open Metric Set MeasureTheory

namespace ArrowDebreu.ThmI

namespace BrouwerAux

/-! Brouwer fixed-point theorem, analytic (Milnor–Rogers) route.

* (A)–(D), (L1): there is no `C¹` retraction `r` of the closed unit ball `B ⊆ ℝᵈ` onto the
  sphere. For small `t`, `x ↦ x + t (r x - x)` is a bijection of `B`, so by change of variables
  `∫_B det(1 + t A) = vol B`; the left side is a polynomial in `t`, hence equals `vol B` at
  `t = 1`, where the integrand `det (Dr)` vanishes because `r` takes values on the sphere.
* (L2): a fixed-point-free `C¹` self-map of `B` would give such a retraction.
* (L3): continuous maps are approximated by `C¹` maps (Stone–Weierstrass).
* (L4): a compact convex set is a retract of a ball (nearest-point map) after a linear
  identification of `E` with `ℝᵈ`. -/

/-- Helper for `A_perturb`: a Lipschitz map vanishing on the sphere is controlled by the
distance to any point outside the ball. -/
theorem A_perturb_boundary {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    {x z : EuclideanSpace ℝ (Fin d)} (hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
    (hz : z ∉ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
    ‖h x‖ ≤ L * dist x z := by
  have hx' : ‖x‖ ≤ 1 := by simpa using hx
  have hz' : 1 < ‖z‖ := by simpa using hz
  have hcont : ContinuousOn (fun s : ℝ => ‖x + s • (z - x)‖) (Icc 0 1) := by
    fun_prop
  have h1 : (1 : ℝ) ∈ Icc ((fun s : ℝ => ‖x + s • (z - x)‖) 0)
      ((fun s : ℝ => ‖x + s • (z - x)‖) 1) := by
    simp only [zero_smul, add_zero, one_smul, add_sub_cancel]
    exact ⟨hx', hz'.le⟩
  obtain ⟨s, ⟨hs0, hs1⟩, hs⟩ := intermediate_value_Icc zero_le_one hcont h1
  have hwS : x + s • (z - x) ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 := by simpa using hs
  have hwB : x + s • (z - x) ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    sphere_subset_closedBall hwS
  have hhw : h (x + s • (z - x)) = 0 := h0 _ hwS
  calc ‖h x‖ = dist (h x) (h (x + s • (z - x))) := by rw [hhw, dist_zero_right]
    _ ≤ L * dist x (x + s • (z - x)) := hL.dist_le_mul x hx _ hwB
    _ ≤ L * dist x z := by
      gcongr
      rw [dist_eq_norm, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
        Real.norm_of_nonneg hs0, norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) hs1

/-- Helper for `A_perturb`: the extension by zero outside the ball is globally Lipschitz. -/
theorem A_perturb_ext_lip {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (L : NNReal) (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0) :
    LipschitzWith L ((closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  by_cases hx : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 <;>
    by_cases hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
    exact hL.dist_le_mul x hx y hy
  · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem hy, dist_zero_right]
    exact A_perturb_boundary h L hL h0 hx hy
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem hy, dist_zero_left, dist_comm]
    exact A_perturb_boundary h L hL h0 hy hx
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy, dist_self]
    positivity

/-- (A) Lipschitz perturbation of the identity on the unit ball: injective and onto the ball. -/
theorem A_perturb {d : ℕ} (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (L : NNReal)
    (hL : LipschitzOnWith L h (closedBall 0 1))
    (h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0)
    (hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htL : t * L < 1) :
    InjOn (fun x => x + t • h x) (closedBall 0 1) ∧
      (fun x => x + t • h x) '' closedBall 0 1 = closedBall 0 1 := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    simp only at hxy
    have h1 : x - y = t • h y - t • h x := by
      rw [sub_eq_sub_iff_add_eq_add, hxy, add_comm]
    have h2 : ‖x - y‖ ≤ t * L * ‖x - y‖ := by
      calc ‖x - y‖ = t * ‖h y - h x‖ := by
            rw [h1, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0]
        _ ≤ t * (L * ‖y - x‖) := by
          gcongr
          rw [← dist_eq_norm, ← dist_eq_norm]
          exact hL.dist_le_mul y hy x hx
        _ = t * L * ‖x - y‖ := by rw [norm_sub_rev]; ring
    have h3 : ‖x - y‖ ≤ 0 := by
      have := norm_nonneg (x - y)
      nlinarith
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h3)
  · apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      have hc : x + t • h x = (1 - t) • x + t • (x + h x) := by
        rw [smul_add, sub_smul, one_smul]; abel
      simp only
      rw [hc]
      exact convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 hx (hB x hx)
        (sub_nonneg.2 ht1) ht0 (by ring)
    · intro y hy
      set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
        (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator h with hg
      have hgL : LipschitzWith L g := A_perturb_ext_lip h L hL h0
      set G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => y - t • g x
        with hG
      have hGc : ContractingWith (Real.toNNReal t * L) G := by
        refine ⟨?_, ?_⟩
        · rw [← NNReal.coe_lt_coe]
          simpa [Real.coe_toNNReal t ht0] using htL
        · refine LipschitzWith.of_dist_le_mul fun a b => ?_
          have : dist (G a) (G b) = t * dist (g a) (g b) := by
            simp only [hG, dist_eq_norm]
            rw [sub_sub_sub_cancel_left, ← smul_sub, norm_smul, Real.norm_of_nonneg ht0,
              norm_sub_rev]
          rw [this, NNReal.coe_mul, Real.coe_toNNReal t ht0, mul_assoc]
          gcongr
          exact hgL.dist_le_mul a b
      set x := ContractingWith.fixedPoint G hGc with hx
      have hfix : G x = x := ContractingWith.fixedPoint_isFixedPt hGc
      by_cases hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1
      · refine ⟨x, hxB, ?_⟩
        have : y - t • h x = x := by simpa [hG, hg, Set.indicator_of_mem hxB] using hfix
        exact (sub_eq_iff_eq_add.mp this).symm
      · exfalso
        have : y = x := by simpa [hG, hg, Set.indicator_of_notMem hxB] using hfix
        exact hxB (this ▸ hy)

section C_poly_section
open Polynomial

/-- `t ↦ det (1 + t • T)` is a real polynomial of degree `≤ d`. -/
theorem C_poly_det_poly {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ p : ℝ[X], p.natDegree ≤ d ∧ ∀ t : ℝ, (1 + t • T).det = p.eval t := by
  classical
  let b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  let M := LinearMap.toMatrix b b (T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d))
  refine ⟨Matrix.det ((X : ℝ[X]) • M.map C + (1 : Matrix (Fin d) (Fin d) ℝ).map C), ?_, ?_⟩
  · simpa using natDegree_det_X_add_C_le M 1
  · intro t
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, ← Polynomial.coe_evalRingHom,
      RingHom.map_det]
    congr 1
    ext i j
    by_cases h : i = j <;> simp [M, h] <;> ring

/-- Lagrange interpolation at `d + 1` distinct nodes recovers the value at `1`
of any polynomial of degree `≤ d`. -/
theorem C_poly_interp {d : ℕ} (v : Fin (d+1) → ℝ) (hv : Function.Injective v) (p : ℝ[X])
    (hp : p.natDegree ≤ d) :
    p.eval 1 = ∑ i, (Lagrange.basis Finset.univ v i).eval 1 * p.eval (v i) := by
  have hdeg : p.degree < ((Finset.univ : Finset (Fin (d+1))).card : WithBot ℕ) := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self d))
  conv_lhs => rw [Lagrange.eq_interpolate hv.injOn hdeg]
  simp [Lagrange.interpolate_apply, eval_finsetSum, mul_comm]

end C_poly_section

/-- (C) If `t ↦ ∫_s det(1 + t A)` is constant on an interval `(0, t₀)`, it has the same value at `t = 1`. -/
theorem C_poly {d : ℕ} (A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (s : Set (EuclideanSpace ℝ (Fin d))) (hs : MeasurableSet s) (hfin : volume s < ⊤)
    (hA : ∃ C, ∀ x ∈ s, ‖A x‖ ≤ C) (hmeas : AEStronglyMeasurable A (volume.restrict s))
    (c t₀ : ℝ) (ht₀ : 0 < t₀)
    (hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in s, (1 + t • A x).det = c) :
    ∫ x in s, (1 + A x).det = c := by
  classical
  obtain ⟨C, hC⟩ := hA
  -- interpolation nodes in `(0, t₀)`
  set v : Fin (d+1) → ℝ := fun i => t₀ * ((i : ℕ) + 1 : ℝ) / ((d : ℝ) + 2) with hv_def
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hv_inj : Function.Injective v := by
    intro i j hij
    simp only [v] at hij
    have h1 : t₀ * (((i : ℕ) : ℝ) + 1) = t₀ * (((j : ℕ) : ℝ) + 1) := by
      have := congrArg (· * ((d : ℝ) + 2)) hij
      simpa [div_mul_cancel₀, hd2.ne'] using this
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := mul_left_cancel₀ ht₀.ne' h1
      linarith
    exact Fin.ext (by exact_mod_cast h2)
  have hv_mem : ∀ i, v i ∈ Ioo 0 t₀ := by
    intro i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (d : ℝ) + 1 := by
      have : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
      have : ((i : ℕ) : ℝ) ≤ d := by exact_mod_cast this
      linarith
    refine ⟨by positivity, ?_⟩
    simp only [v]
    rw [div_lt_iff₀ hd2]
    nlinarith
  -- interpolation weights
  set ℓ : Fin (d+1) → ℝ := fun i => (Lagrange.basis Finset.univ v i).eval 1 with hℓ_def
  have key : ∀ T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d),
      (1 + T).det = ∑ i, ℓ i * (1 + v i • T).det := by
    intro T
    obtain ⟨p, hp, hpt⟩ := C_poly_det_poly T
    have hint := C_poly_interp v hv_inj p hp
    rw [show (1 + T) = 1 + (1 : ℝ) • T by simp, hpt 1, hint]
    simp [ℓ, hpt]
  have hsum : ∑ i, ℓ i = 1 := by
    have h0 : ∀ a : ℝ, a • (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) = 0 :=
      fun a => by ext x; simp
    have h1 : (1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)).det = 1 := by
      simp [ContinuousLinearMap.det]
    have := key 0
    simp only [h0, add_zero, h1, mul_one] at this
    exact this.symm
  -- integrability of `x ↦ det (1 + t • A x)` on `s`
  have hint : ∀ t : ℝ, IntegrableOn (fun x => (1 + t • A x).det) s volume := by
    intro t
    have hcont : Continuous fun T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) =>
        (1 + t • T).det :=
      ContinuousLinearMap.continuous_det.comp (continuous_const.add (continuous_const_smul t))
    obtain ⟨K, hK⟩ := (isCompact_closedBall
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) C).exists_bound_of_continuousOn
      hcont.continuousOn
    refine IntegrableOn.of_bound hfin (hcont.comp_aestronglyMeasurable hmeas) K ?_
    refine ae_restrict_of_forall_mem hs (fun x hx => hK _ ?_)
    rw [mem_closedBall, dist_zero_right]
    exact hC x hx
  calc ∫ x in s, (1 + A x).det = ∫ x in s, ∑ i, ℓ i * (1 + v i • A x).det := by
        congr 1
        funext x
        exact key (A x)
    _ = ∑ i, ∫ x in s, ℓ i * (1 + v i • A x).det :=
        integral_finsetSum _ (fun i _ => (hint (v i)).const_mul (ℓ i))
    _ = ∑ i, ℓ i * c := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, hconst _ (hv_mem i)]
    _ = c := by rw [← Finset.sum_mul, hsum, one_mul]

/-- (D) A map with values on the unit sphere near `x` has singular derivative at `x`. -/
theorem D_det_zero {d : ℕ} (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) (U : Set (EuclideanSpace ℝ (Fin d))) (hU : U ∈ nhds x)
    (hr : DifferentiableAt ℝ r x) (hsph : ∀ y ∈ U, ‖r y‖ = 1) :
    (fderiv ℝ r x).det = 0 := by
  classical
  set Dr := fderiv ℝ r x with hDr
  -- derivative of `y ↦ ⟪r y, r y⟫` via the product rule
  have hφ : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      ((fderivInnerCLM ℝ (r x, r x)).comp (Dr.prod Dr)) x :=
    hr.hasFDerivAt.inner ℝ hr.hasFDerivAt
  -- but `⟪r y, r y⟫ = 1` near `x`, so the derivative vanishes
  have hconst : (fun y => inner ℝ (r y) (r y)) =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [hU] with y hy
    rw [real_inner_self_eq_norm_sq, hsph y hy]
    norm_num
  have h0 : HasFDerivAt (fun y => inner ℝ (r y) (r y))
      (0 : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (1 : ℝ) x).congr_of_eventuallyEq hconst
  have heq := hφ.unique h0
  have horth : ∀ v, inner ℝ (r x) (Dr v) = 0 := by
    intro v
    have hv := congrArg (fun L => L v) heq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply, zero_apply] at hv
    have hc := real_inner_comm (Dr v) (r x)
    linarith
  -- if `det Dr ≠ 0`, then `Dr` is surjective, so `r x ∈ range Dr`, forcing `⟪r x, r x⟫ = 0`
  by_contra hdet
  have hunit : IsUnit (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hsurj : Function.Surjective
      (Dr : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) := by
    rw [← LinearMap.range_eq_top]
    exact (LinearMap.isUnit_iff_range_eq_top _).1 hunit
  obtain ⟨v, hv⟩ := hsurj (r x)
  have h1 := horth v
  have hv' : Dr v = r x := hv
  rw [hv', real_inner_self_eq_norm_sq, hsph x (mem_of_mem_nhds hU)] at h1
  norm_num at h1

/-- Helper: `1 + T` has positive determinant when `‖T‖ < 1`. -/
theorem L1_no_retraction_det_pos {d : ℕ}
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) (hT : ‖T‖ < 1) :
    0 < (1 + T).det := by
  set f : ℝ → ℝ := fun s => (1 + s • T).det with hf
  have hcont : Continuous f :=
    ContinuousLinearMap.continuous_det.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, f s ≠ 0 := by
    intro s hs
    have hn : ‖-(s • T)‖ < 1 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖T‖ ≤ 1 * ‖T‖ := by gcongr; exact hs.2
        _ = ‖T‖ := one_mul _
        _ < 1 := hT
    have hu : IsUnit (1 + s • T) := by
      have := (Units.oneSub (-(s • T)) hn).isUnit
      simpa [Units.val_oneSub, sub_neg_eq_add] using this
    have hu' : IsUnit ((1 + s • T : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :
        EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) :=
      hu.map ContinuousLinearMap.toLinearMapRingHom
    exact (LinearMap.isUnit_det _ hu').ne_zero
  have h0 : f 0 = 1 := by simp [hf, ContinuousLinearMap.det]
  by_contra hneg
  rw [not_lt] at hneg
  have h1 : f 1 ≤ 0 := by simpa [hf] using hneg
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' zero_le_one hcont.continuousOn
    (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨h1, by rw [h0]; exact zero_le_one⟩)
  exact hne s hs hs0

/-- (L1) No `C¹` retraction of the closed unit ball onto the unit sphere. -/
theorem L1_no_retraction {d : ℕ} (hd : 0 < d)
    (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (U : Set (EuclideanSpace ℝ (Fin d))) (hU : IsOpen U) (hBU : closedBall 0 1 ⊆ U)
    (hr : ContDiffOn ℝ 1 r U)
    (hmaps : MapsTo r (closedBall 0 1) (sphere 0 1))
    (hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x) : False := by
  classical
  have hdiff : ∀ x ∈ U, HasFDerivAt r (fderiv ℝ r x) x := fun x hx =>
    ((hr.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hcontD : ContinuousOn (fderiv ℝ r) U := hr.continuousOn_fderiv_of_isOpen hU le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).exists_bound_of_continuousOn
    (hcontD.mono hBU)
  set K : ℝ := max M 0 + 1 with hK
  have hK1 : 1 ≤ K := by
    have := le_max_right M 0
    linarith
  have hKpos : 0 < K := by linarith
  set A : EuclideanSpace ℝ (Fin d) → (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    fun x => fderiv ℝ r x - 1 with hA
  have hAbound : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖A x‖ ≤ K := by
    intro x hx
    calc ‖A x‖ ≤ ‖fderiv ℝ r x‖ +
          ‖(1 : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))‖ := norm_sub_le _ _
      _ ≤ max M 0 + 1 :=
          add_le_add ((hM x hx).trans (le_max_left _ _)) ContinuousLinearMap.norm_id_le
  set h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => r x - x with hh
  have hhderiv : ∀ x ∈ U, HasFDerivAt h (A x) x := fun x hx =>
    (hdiff x hx).sub (hasFDerivAt_id x)
  set L : NNReal := ⟨K, hKpos.le⟩ with hL
  have hLip : LipschitzOnWith L h (closedBall 0 1) := by
    apply (convex_closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := A)
    · intro x hx
      exact (hhderiv x (hBU hx)).hasFDerivWithinAt
    · intro x hx
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      exact hAbound x hx
  have h0 : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, h x = 0 := by
    intro x hx
    simp [hh, hid x hx]
  have hB : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, x + h x ∈ closedBall 0 1 := by
    intro x hx
    have : x + h x = r x := by simp [hh]
    rw [this]
    exact sphere_subset_closedBall (hmaps hx)
  set t₀ : ℝ := 1 / K with ht₀
  have ht₀pos : 0 < t₀ := by positivity
  have ht₀le : t₀ ≤ 1 := by
    rw [ht₀, div_le_one hKpos]
    exact hK1
  have hconst : ∀ t ∈ Ioo 0 t₀, ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      (1 + t • A x).det = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    intro t ht
    have htK : t * K < 1 := by
      have := ht.2
      rw [ht₀, lt_div_iff₀ hKpos] at this
      exact this
    have htL : t * (L : ℝ) < 1 := htK
    obtain ⟨hinj, himg⟩ := A_perturb h L hLip h0 hB ht.1.le (ht.2.le.trans ht₀le) htL
    have hFd : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        HasFDerivWithinAt (fun x => x + t • h x) (1 + t • A x) (closedBall 0 1) x := by
      intro x hx
      exact ((hasFDerivAt_id x).add ((hhderiv x (hBU hx)).const_smul t)).hasFDerivWithinAt
    have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_closedBall
      hFd hinj (fun _ => (1 : ℝ))
    rw [himg, setIntegral_const, smul_eq_mul, mul_one] at hcov
    rw [hcov]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [smul_eq_mul, mul_one]
    have hn : ‖t • A x‖ < 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      calc t * ‖A x‖ ≤ t * K := mul_le_mul_of_nonneg_left (hAbound x hx) ht.1.le
        _ < 1 := htK
    exact (abs_of_pos (L1_no_retraction_det_pos _ hn)).symm
  have hmeas : AEStronglyMeasurable A (volume.restrict (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    (measurable_fderiv ℝ r).aestronglyMeasurable.sub aestronglyMeasurable_const
  have hC := C_poly A (closedBall 0 1) measurableSet_closedBall measure_closedBall_lt_top
    ⟨K, hAbound⟩ hmeas _ t₀ ht₀pos hconst
  simp only [hA, add_sub_cancel] at hC
  have hzero : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det = 0 := by
    have : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
      Module.finrank_pos_iff.1 (by rw [finrank_euclideanSpace_fin]; exact hd)
    have hsph : volume (sphere (0 : EuclideanSpace ℝ (Fin d)) 1) = 0 :=
      Measure.addHaar_sphere volume 0 1
    have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
        x ∉ sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      measure_eq_zero_iff_ae_notMem.1 hsph
    have : ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (fderiv ℝ r x).det =
        ∫ x in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, (0 : ℝ) := by
      apply setIntegral_congr_ae measurableSet_closedBall
      filter_upwards [hae] with x hx hxB
      have hxb : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := lt_of_le_of_ne hxB hx
      refine D_det_zero r x (ball 0 1) (isOpen_ball.mem_nhds hxb)
        (hdiff x (hBU (ball_subset_closedBall hxb))).differentiableAt ?_
      intro y hy
      have := hmaps (ball_subset_closedBall hy)
      simpa using this
    rw [this, integral_zero]
  have hpos : 0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
      measure_closedBall_lt_top.ne
  rw [hzero] at hC
  linarith

/-- Expansion of `‖x + λ v‖²`. -/
theorem L2_brouwer_C1_norm_sq_eq {d : ℕ} (x v : EuclideanSpace ℝ (Fin d)) (lam : ℝ) :
    ‖x + lam • v‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam * inner ℝ x v + lam ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- (L2) Brouwer for globally `C¹` self-maps of the closed unit ball. -/
theorem L2_brouwer_C1 {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContDiff ℝ 1 f) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨0, by simp, Subsingleton.elim _ _⟩
  by_contra hne
  push Not at hne
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      v = fun x => x - f x := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : EuclideanSpace ℝ (Fin d) → ℝ, a = fun x => inner ℝ x (v x) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : EuclideanSpace ℝ (Fin d) → ℝ, b = fun x => ‖v x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : EuclideanSpace ℝ (Fin d) → ℝ, c = fun x => 1 - ‖x‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨disc, hdisc⟩ : ∃ disc : EuclideanSpace ℝ (Fin d) → ℝ,
      disc = fun x => a x ^ 2 + b x * c x := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : EuclideanSpace ℝ (Fin d) → ℝ,
      lam = fun x => (-(a x) + Real.sqrt (disc x)) / b x := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      r = fun x => x + lam x • v x := ⟨_, rfl⟩
  -- smoothness of the ingredients
  have hvC : ContDiff ℝ 1 v := by rw [hv]; exact contDiff_id.sub hf
  have haC : ContDiff ℝ 1 a := by rw [ha]; exact contDiff_id.inner ℝ hvC
  have hbC : ContDiff ℝ 1 b := by rw [hb]; exact hvC.norm_sq ℝ
  have hcC : ContDiff ℝ 1 c := by rw [hc]; exact contDiff_const.sub (contDiff_norm_sq ℝ)
  have hdiscC : ContDiff ℝ 1 disc := by rw [hdisc]; exact (haC.pow 2).add (hbC.mul hcC)
  -- the open set
  set U : Set (EuclideanSpace ℝ (Fin d)) := {x | 0 < disc x ∧ 0 < b x} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const hdiscC.continuous).inter
      (isOpen_lt continuous_const hbC.continuous)
  -- key identity: `2 a = ‖x‖² - ‖f x‖² + b`
  have hkey : ∀ x, 2 * a x = ‖x‖ ^ 2 - ‖f x‖ ^ 2 + b x := by
    intro x
    have hfx : f x = x - v x := by rw [hv]; simp
    have h2 := norm_sub_sq_real x (v x)
    rw [← hfx] at h2
    rw [ha, hb]
    simp only
    linarith
  have hb_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < b x := by
    intro x hx
    have hvx : v x ≠ 0 := by
      rw [hv]; exact sub_ne_zero.mpr (hne x hx).symm
    rw [hb]
    simp only
    have := norm_pos_iff.mpr hvx
    positivity
  have hfx1 : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖f x‖ ≤ 1 :=
    fun x hx => mem_closedBall_zero_iff.mp (hmaps hx)
  have hc_nonneg : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 ≤ c x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    rw [hc]
    simp only
    nlinarith [norm_nonneg x]
  have hdisc_pos : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, 0 < disc x := by
    intro x hx
    have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
    have hbx := hb_pos x hx
    have hk := hkey x
    have hf1 := hfx1 x hx
    have hcx := hc_nonneg x hx
    rw [hdisc]
    simp only
    rcases hx1.lt_or_eq with hlt | heq
    · have hcpos : 0 < c x := by
        rw [hc]; simp only; nlinarith [norm_nonneg x]
      nlinarith [sq_nonneg (a x), mul_pos hbx hcpos]
    · have hax : 0 < a x := by
        rw [heq] at hk; nlinarith [norm_nonneg (f x)]
      nlinarith [mul_nonneg hbx.le hcx]
  have hBU : closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ U :=
    fun x hx => ⟨hdisc_pos x hx, hb_pos x hx⟩
  -- `r` is `C¹` on `U`
  have hrC : ContDiffOn ℝ 1 r U := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    have hsq : ContDiffAt ℝ 1 (fun y => Real.sqrt (disc y)) x :=
      hdiscC.contDiffAt.sqrt hx.1.ne'
    have hlamC : ContDiffAt ℝ 1 lam x := by
      rw [hlam]
      exact (haC.contDiffAt.neg.add hsq).fun_div hbC.contDiffAt hx.2.ne'
    rw [hr]
    exact contDiffAt_id.add (hlamC.smul hvC.contDiffAt)
  -- `r` maps the ball to the sphere
  have hr_norm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖r x‖ = 1 := by
    intro x hx
    have hbx := hb_pos x hx
    have hdx := hdisc_pos x hx
    have hs : Real.sqrt (disc x) ^ 2 = a x ^ 2 + b x * c x := by
      rw [Real.sq_sqrt hdx.le, hdisc]
    have hl : lam x * b x = -(a x) + Real.sqrt (disc x) := by
      rw [hlam]; simp only; field_simp
    have hcx : c x = 1 - ‖x‖ ^ 2 := by rw [hc]
    have h1 : ‖r x‖ ^ 2 = 1 := by
      have e : ‖r x‖ ^ 2 = ‖x‖ ^ 2 + 2 * lam x * a x + lam x ^ 2 * b x := by
        rw [hr, ha, hb]
        simp only
        exact L2_brouwer_C1_norm_sq_eq x (v x) (lam x)
      rw [e]
      apply mul_left_cancel₀ hbx.ne'
      linear_combination (lam x * b x + Real.sqrt (disc x) + a x) * hl + hs + b x * hcx
    have h0 := norm_nonneg (r x)
    nlinarith
  have hmapsr : MapsTo r (closedBall 0 1) (sphere 0 1) :=
    fun x hx => mem_sphere_zero_iff_norm.mpr (hr_norm x hx)
  -- `r` is the identity on the sphere
  have hid : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin d)) 1, r x = x := by
    intro x hx
    have hx1 : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    have hxB : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      sphere_subset_closedBall hx
    have hbx := hb_pos x hxB
    have hk := hkey x
    have hf1 := hfx1 x hxB
    have hcx : c x = 0 := by rw [hc]; simp [hx1]
    have hax : 0 < a x := by
      rw [hx1] at hk; nlinarith [norm_nonneg (f x)]
    have hdx : disc x = a x ^ 2 := by rw [hdisc]; simp [hcx]
    have hlx : lam x = 0 := by
      rw [hlam]; simp only; rw [hdx, Real.sqrt_sq hax.le]; simp
    rw [hr]; simp [hlx]
  exact L1_no_retraction hd r U hUo hBU hrC hmapsr hid

theorem L3_brouwer_ball_scalar_approx {d : ℕ} (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (hφ : ContinuousOn φ (closedBall 0 1)) (η : ℝ) (hη : 0 < η) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |G x - φ x| < η := by
  set B : Set (EuclideanSpace ℝ (Fin d)) := closedBall 0 1 with hB
  have : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall 0 1)
  let A : Subalgebra ℝ C(B, ℝ) :=
    { carrier := {g | ∃ G : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 G ∧ ∀ x : B, g x = G x}
      mul_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x * Gb x, hGa.mul hGb, fun x => by simp [ha, hb]⟩
      add_mem' := by
        rintro a b ⟨Ga, hGa, ha⟩ ⟨Gb, hGb, hb⟩
        exact ⟨fun x => Ga x + Gb x, hGa.add hGb, fun x => by simp [ha, hb]⟩
      algebraMap_mem' := fun r => ⟨fun _ => r, contDiff_const, fun x => by simp⟩ }
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    have : ∃ i, (x : EuclideanSpace ℝ (Fin d)) i ≠ (y : EuclideanSpace ℝ (Fin d)) i := by
      by_contra h
      push Not at h
      apply hxy
      apply Subtype.ext
      ext i
      exact h i
    obtain ⟨i, hi⟩ := this
    refine ⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, ?_, hi⟩
    refine ⟨⟨fun z : B => (z : EuclideanSpace ℝ (Fin d)) i, by fun_prop⟩, ?_, rfl⟩
    exact ⟨fun z => z i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).contDiff,
      fun z => rfl⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints A hsep
    (fun x : B => φ x) hφ.domRestrict η hη
  obtain ⟨G, hG, hgG⟩ := g.2
  refine ⟨G, hG, fun x hx => ?_⟩
  have := hg ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [hgG] using this

theorem L3_brouwer_ball_vec_approx {d : ℕ}
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), ContDiff ℝ 1 G ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x - f x‖ < δ := by
  set η : ℝ := δ / (d + 1) with hη_def
  have hd1 : (0 : ℝ) < d + 1 := by positivity
  have hη : 0 < η := div_pos hδ hd1
  have hcoord : ∀ i : Fin d, ∃ Gi : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ 1 Gi ∧
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, |Gi x - f x i| < η := by
    intro i
    refine L3_brouwer_ball_scalar_approx (fun x => f x i) ?_ η hη
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ).continuous.comp_continuousOn hf
  choose Gi hGi hGiapprox using hcoord
  refine ⟨fun x => (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x), ?_, ?_⟩
  · exact (EuclideanSpace.equiv (Fin d) ℝ).symm.contDiff.comp (contDiff_pi.2 fun i => hGi i)
  · intro x hx
    set v := (EuclideanSpace.equiv (Fin d) ℝ).symm (fun i => Gi i x) - f x with hv
    have hvi : ∀ i, v i = Gi i x - f x i := by
      intro i
      simp [hv]
    have hsq : ‖v‖ ^ 2 ≤ d * η ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, (v i) ^ 2 ≤ ∑ _i : Fin d, η ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            rw [hvi i]
            have := hGiapprox i x hx
            rw [← sq_abs]
            have h0 : 0 ≤ |Gi i x - f x i| := abs_nonneg _
            nlinarith
        _ = d * η ^ 2 := by simp
    have hlt : ‖v‖ ^ 2 < δ ^ 2 := by
      have hδη : δ = (d + 1) * η := by rw [hη_def]; field_simp
      rw [hδη]
      have : (d : ℝ) * η ^ 2 < ((d : ℝ) + 1) ^ 2 * η ^ 2 := by
        have hdd : (d : ℝ) < ((d : ℝ) + 1) ^ 2 := by nlinarith
        have := pow_pos hη 2
        nlinarith
      nlinarith
    have hn : 0 ≤ ‖v‖ := norm_nonneg _
    nlinarith

/-- (L3) Brouwer for continuous self-maps of the closed unit ball. -/
theorem L3_brouwer_ball {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hf : ContinuousOn f (closedBall 0 1)) (hmaps : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, f x = x := by
  by_contra hno
  push Not at hno
  -- Step 1: minimal displacement
  have hcpt : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) := isCompact_closedBall 0 1
  have hne : (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty :=
    ⟨0, mem_closedBall_self zero_le_one⟩
  have hcont : ContinuousOn (fun x => ‖f x - x‖) (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    (hf.sub continuousOn_id).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  set ε : ℝ := ‖f x₀ - x₀‖ with hε_def
  have hε : 0 < ε := norm_pos_iff.2 (sub_ne_zero.2 (hno x₀ hx₀))
  have hεle : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ε ≤ ‖f x - x‖ :=
    fun x hx => hmin hx
  -- Step 2: smooth approximation
  set η : ℝ := ε / 2 with hη_def
  have hη : 0 < η := half_pos hε
  obtain ⟨G, hG, hGapprox⟩ := L3_brouwer_ball_vec_approx f hf η hη
  -- Step 3: rescale
  set c : ℝ := 1 + η with hc_def
  have hc : 0 < c := by positivity
  set g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun x => c⁻¹ • G x with hg_def
  have hgC1 : ContDiff ℝ 1 g := hG.const_smul c⁻¹
  have hGnorm : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖G x‖ ≤ c := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    calc ‖G x‖ = ‖(G x - f x) + f x‖ := by rw [sub_add_cancel]
      _ ≤ ‖G x - f x‖ + ‖f x‖ := norm_add_le _ _
      _ ≤ c := by rw [hc_def]; linarith
  have hgmaps : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro x hx
    rw [mem_closedBall_zero_iff, hg_def]
    simp only
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]
    calc c⁻¹ * ‖G x‖ ≤ c⁻¹ * c := by
          exact mul_le_mul_of_nonneg_left (hGnorm x hx) (inv_pos.2 hc).le
      _ = 1 := inv_mul_cancel₀ hc.ne'
  have hgf : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ‖g x - f x‖ < ε := by
    intro x hx
    have h1 : ‖f x‖ ≤ 1 := by simpa using hmaps hx
    have h2 := hGapprox x hx
    have hkey : c • (g x - f x) = (G x - f x) - η • f x := by
      rw [hg_def]
      simp only
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc.ne', one_smul, hc_def, add_smul, one_smul]
      abel
    have hnorm : c * ‖g x - f x‖ ≤ ‖G x - f x‖ + η * ‖f x‖ := by
      have := congrArg norm hkey
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc] at this
      rw [this]
      calc ‖(G x - f x) - η • f x‖ ≤ ‖G x - f x‖ + ‖η • f x‖ := norm_sub_le _ _
        _ = ‖G x - f x‖ + η * ‖f x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have hc1 : 1 ≤ c := by rw [hc_def]; linarith
    have hn0 : 0 ≤ ‖g x - f x‖ := norm_nonneg _
    have : η * ‖f x‖ ≤ η := by nlinarith
    nlinarith
  obtain ⟨x, hx, hfix⟩ := L2_brouwer_C1 g hgC1 hgmaps
  have h1 := hεle x hx
  have h2 := hgf x hx
  rw [hfix, norm_sub_rev] at h2
  linarith

/-- Nearest-point retraction onto a nonempty complete convex set in a real inner product space. -/
theorem L4_retraction {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : F → F, Continuous p ∧ (∀ x, p x ∈ K) ∧ (∀ x ∈ K, p x = x) := by
  choose p hpK hpeq using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hin : ∀ x, ∀ w ∈ K, inner ℝ (x - p x) (w - p x) ≤ 0 := fun x =>
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hpK x)).1 (hpeq x)
  refine ⟨p, ?_, hpK, ?_⟩
  · have hlip : LipschitzWith 1 p := by
      refine LipschitzWith.of_dist_le_mul fun x y => ?_
      simp only [NNReal.coe_one, one_mul, dist_eq_norm]
      have h1 := hin x (p y) (hpK y)
      have h2 := hin y (p x) (hpK x)
      have key : ‖p x - p y‖ ^ 2 ≤ inner ℝ (x - y) (p x - p y) := by
        have e : inner ℝ (x - y) (p x - p y) - ‖p x - p y‖ ^ 2 =
            -inner ℝ (x - p x) (p y - p x) - inner ℝ (y - p y) (p x - p y) := by
          rw [← real_inner_self_eq_norm_sq]
          simp only [inner_sub_left, inner_sub_right, real_inner_comm]
          ring
        linarith
      have hcs := real_inner_le_norm (x - y) (p x - p y)
      rcases eq_or_lt_of_le (norm_nonneg (p x - p y)) with h | h
      · rw [← h]; exact norm_nonneg _
      · nlinarith
    exact hlip.continuous
  · intro x hx
    have h0 : ‖x - p x‖ ^ 2 ≤ 0 := by
      rw [← real_inner_self_eq_norm_sq]; exact hin x x hx
    have h1 : ‖x - p x‖ = 0 := by nlinarith [norm_nonneg (x - p x)]
    exact (norm_sub_eq_zero_iff.1 h1).symm

/-- Brouwer for compact convex nonempty subsets of `EuclideanSpace ℝ (Fin d)`. -/
theorem L4_brouwer_euclid {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hf : ContinuousOn f K)
    (hfK : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  obtain ⟨p, hpc, hpK, hpid⟩ := L4_retraction hKne hKcpt.isComplete hKconv
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hKcpt.isBounded
  set R : ℝ := max R₀ 1 with hR
  have hRpos : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKR : K ⊆ closedBall 0 R := hR₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  let g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun z => R⁻¹ • f (p (R • z))
  have hgc : ContinuousOn g (closedBall 0 1) := by
    have hc : ContinuousOn (fun z => f (p (R • z))) univ :=
      hf.comp (hpc.comp (continuous_const_smul R)).continuousOn (fun z _ => hpK _)
    exact (hc.mono (subset_univ _)).const_smul R⁻¹
  have hgm : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
    intro z _
    have h1 := hKR (hfK (hpK (R • z)))
    rw [mem_closedBall_zero_iff] at h1 ⊢
    simp only [g, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hRpos]
    rw [inv_mul_le_iff₀ hRpos]
    linarith
  obtain ⟨z, -, hz⟩ := L3_brouwer_ball g hgc hgm
  have hx : f (p (R • z)) = R • z := by
    have := congrArg (fun v => R • v) hz
    simpa [g, smul_smul, mul_inv_cancel₀ hRpos.ne'] using this
  have hxK : R • z ∈ K := hx ▸ hfK (hpK _)
  refine ⟨R • z, hxK, ?_⟩
  rw [hpid _ hxK] at hx
  exact hx

end BrouwerAux

open BrouwerAux in
/-- **Brouwer fixed-point theorem** (copied from the accepted solution of `AGT.brouwer_fixed_point`). -/
theorem brouwer_core {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (f : E → E) (hf : ContinuousOn f K) (hfK : Set.MapsTo f K K) :
    ∃ x ∈ K, f x = x := by
  classical
  let φ : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  have hconv' : Convex ℝ (φ '' K) :=
    hKconv.linear_image (φ : E →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))
  have hcont : ContinuousOn (φ ∘ f ∘ φ.symm) (φ '' K) := by
    refine φ.continuous.comp_continuousOn (hf.comp φ.symm.continuous.continuousOn ?_)
    rintro _ ⟨y, hy, rfl⟩
    simpa using hy
  have hmaps : MapsTo (φ ∘ f ∘ φ.symm) (φ '' K) (φ '' K) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨f y, hfK hy, by simp⟩
  obtain ⟨x, ⟨y, hyK, rfl⟩, hx⟩ :=
    L4_brouwer_euclid hconv' (hKcpt.image φ.continuous) (hKne.image φ) _ hcont hmaps
  refine ⟨y, hyK, ?_⟩
  apply φ.injective
  simpa using hx

section KakutaniSection

open Filter Topology

namespace KakutaniAux

/-! **Kakutani's fixed-point theorem** from Brouwer's, in a finite-dimensional real normed space.

For `ε > 0` the compact set `K` is covered by finitely many balls `B(c, ε)`, `c ∈ K`; with the
partition of unity `ψ_c(x) = max(0, ε − dist x c) / Σ_{c'} max(0, ε − dist x c')` and a choice
`y_c ∈ F c`, the map `f_ε x = Σ_c ψ_c(x) • y_c` is a continuous self-map of `K` whose value at
`x` is a convex combination of points of `F c` with `dist x c < ε`. Brouwer gives fixed points
`x_ε = f_ε x_ε`; a cluster point `x*` of the `x_ε` lies in `F x*`, because the closed graph makes
`F` upper hemicontinuous and the `δ`-thickenings of the convex set `F x*` are convex. -/

/-- **Approximate continuous selection.** Given a correspondence `F` with nonempty values on a
compact convex `K`, and `ε > 0`, there is a continuous self-map `f` of `K` such that `f x` is a
convex combination of points of `F x'` with `dist x x' < ε`: for every convex `C` containing all
`F x'` with `x' ∈ K`, `dist x x' < ε`, we have `f x ∈ C`. -/
theorem approx_selection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKcpt : IsCompact K) (hKconv : Convex ℝ K)
    (F : E → Set E) (hFne : ∀ x ∈ K, (F x).Nonempty) (hFK : ∀ x ∈ K, F x ⊆ K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : E → E, ContinuousOn f K ∧ MapsTo f K K ∧
      ∀ x ∈ K, ∀ C : Set E, Convex ℝ C → (∀ x' ∈ K, dist x x' < ε → F x' ⊆ C) → f x ∈ C := by
  classical
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hKcpt hε
  -- a selection `y c ∈ F c` for every `c ∈ K`
  let y : E → E := fun c => if h : (F c).Nonempty then h.some else c
  have hy : ∀ c ∈ K, y c ∈ F c := by
    intro c hc
    have h : (F c).Nonempty := hFne c hc
    simp only [y, dif_pos h]
    exact h.some_mem
  let s : Finset E := htfin.toFinset
  have hs : ∀ c, c ∈ s ↔ c ∈ t := fun c => htfin.mem_toFinset
  let w : E → E → ℝ := fun c x => max 0 (ε - dist x c)
  have hw_nonneg : ∀ c x, 0 ≤ w c x := fun c x => le_max_left _ _
  have hw_cont : ∀ c, Continuous (w c) := fun c =>
    continuous_const.max (continuous_const.sub (continuous_id.dist continuous_const))
  let S : E → ℝ := fun x => ∑ c ∈ s, w c x
  have hS_cont : Continuous S := continuous_finsetSum _ (fun c _ => hw_cont c)
  have hS_pos : ∀ x ∈ K, 0 < S x := by
    intro x hx
    have hx' := hcover hx
    rw [mem_iUnion₂] at hx'
    obtain ⟨c, hct, hxc⟩ := hx'
    refine Finset.sum_pos' (fun c _ => hw_nonneg c x) ⟨c, (hs c).2 hct, ?_⟩
    have : dist x c < ε := mem_ball.1 hxc
    simp only [w]
    exact lt_max_of_lt_right (by linarith)
  let f : E → E := fun x => ∑ c ∈ s, (w c x / S x) • y c
  have hsum1 : ∀ x ∈ K, ∑ c ∈ s, w c x / S x = 1 := by
    intro x hx
    rw [← Finset.sum_div]
    exact div_self (hS_pos x hx).ne'
  refine ⟨f, ?_, ?_, ?_⟩
  · -- continuity on `K`
    refine continuousOn_finsetSum _ (fun c _ => ?_)
    refine ContinuousOn.smul ?_ continuousOn_const
    exact ContinuousOn.div (hw_cont c).continuousOn hS_cont.continuousOn
      (fun x hx => (hS_pos x hx).ne')
  · -- maps `K` into `K`
    intro x hx
    refine hKconv.sum_mem (fun c _ => div_nonneg (hw_nonneg c x) (hS_pos x hx).le)
      (hsum1 x hx) (fun c hc => ?_)
    have hcK : c ∈ K := htK ((hs c).1 hc)
    exact hFK c hcK (hy c hcK)
  · -- convex combination of nearby values
    intro x hx C hC hFC
    have hsplit : f x = ∑ c ∈ s with w c x ≠ 0, (w c x / S x) • y c := by
      symm
      refine Finset.sum_filter_of_ne (fun c _ hne => ?_)
      intro h0
      apply hne
      simp [h0]
    rw [hsplit]
    refine hC.sum_mem (fun c _ => div_nonneg (hw_nonneg c x) (hS_pos x hx).le) ?_ ?_
    · rw [← hsum1 x hx]
      refine Finset.sum_filter_of_ne (fun c _ hne => ?_)
      intro h0
      apply hne
      simp [h0]
    · intro c hc
      rw [Finset.mem_filter] at hc
      obtain ⟨hcs, hcne⟩ := hc
      have hcK : c ∈ K := htK ((hs c).1 hcs)
      have hdist : dist x c < ε := by
        by_contra hge
        rw [not_lt] at hge
        apply hcne
        simp only [w]
        exact max_eq_left (by linarith)
      exact hFC c hcK hdist (hy c hcK)

/-- **Upper hemicontinuity from a closed graph** into a compact set: near `x₀ ∈ K`, the values
`F x` lie in any prescribed `δ`-thickening of `F x₀`. -/
theorem uhc_of_closed_graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hKcpt : IsCompact K) (F : E → Set E) (hFK : ∀ x ∈ K, F x ⊆ K)
    (hG : IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1})
    {x₀ : E} {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ x ∈ K, dist x x₀ < η → F x ⊆ thickening δ (F x₀) := by
  set G : Set (E × E) := {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1} with hGdef
  have hGcpt : IsCompact G :=
    (hKcpt.prod hKcpt).of_isClosed_subset hG (fun p hp => ⟨hp.1, hFK _ hp.1 hp.2⟩)
  set B : Set (E × E) := G ∩ (Prod.snd ⁻¹' (thickening δ (F x₀))ᶜ) with hBdef
  have hBcpt : IsCompact B :=
    hGcpt.inter_right (isOpen_thickening.isClosed_compl.preimage continuous_snd)
  have hPcl : IsClosed (Prod.fst '' B) := (hBcpt.image continuous_fst).isClosed
  have hx₀P : x₀ ∉ Prod.fst '' B := by
    rintro ⟨p, ⟨⟨hpK, hpF⟩, hpn⟩, rfl⟩
    exact hpn (self_subset_thickening hδ _ hpF)
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.1 hPcl.isOpen_compl x₀ hx₀P
  refine ⟨η, hη, fun x hxK hxd y hy => ?_⟩
  by_contra hyn
  exact hball (mem_ball.2 hxd) ⟨(x, y), ⟨⟨hxK, hy⟩, hyn⟩, rfl⟩

/-- **Kakutani's fixed-point theorem** (finite-dimensional): a correspondence with nonempty convex
values and closed graph on a nonempty compact convex set has a fixed point. -/
theorem kakutani_core {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set E}
    (hKconv : Convex ℝ K) (hKcpt : IsCompact K) (hKne : K.Nonempty)
    (F : E → Set E) (hFne : ∀ x ∈ K, (F x).Nonempty) (hFconv : ∀ x ∈ K, Convex ℝ (F x))
    (hFK : ∀ x ∈ K, F x ⊆ K)
    (hG : IsClosed {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1}) :
    ∃ x ∈ K, x ∈ F x := by
  classical
  have hε : ∀ n : ℕ, (0:ℝ) < 1 / ((n:ℝ) + 1) := fun n => Nat.one_div_pos_of_nat
  have hsel : ∀ n : ℕ, ∃ f : E → E, ContinuousOn f K ∧ MapsTo f K K ∧
      ∀ x ∈ K, ∀ C : Set E, Convex ℝ C →
        (∀ x' ∈ K, dist x x' < 1 / ((n:ℝ) + 1) → F x' ⊆ C) → f x ∈ C :=
    fun n => approx_selection hKcpt hKconv F hFne hFK (hε n)
  choose f hfc hfK hfC using hsel
  have hfix : ∀ n, ∃ x ∈ K, f n x = x :=
    fun n => brouwer_core hKconv hKcpt hKne (f n) (hfc n) (hfK n)
  choose x hxK hxf using hfix
  obtain ⟨x₀, hx₀K, φ, hφ, hlim⟩ := hKcpt.tendsto_subseq hxK
  refine ⟨x₀, hx₀K, ?_⟩
  have hFcl : IsClosed (F x₀) := by
    have : F x₀ = (fun y => (x₀, y)) ⁻¹' {p : E × E | p.1 ∈ K ∧ p.2 ∈ F p.1} := by
      ext y
      simp [hx₀K]
    rw [this]
    exact hG.preimage (continuous_const.prodMk continuous_id)
  have hFx₀ne : (F x₀).Nonempty := hFne x₀ hx₀K
  rw [hFcl.mem_iff_infDist_zero hFx₀ne]
  apply le_antisymm _ infDist_nonneg
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  rw [zero_add]
  obtain ⟨η, hη, huhc⟩ := uhc_of_closed_graph hKcpt F hFK hG (x₀ := x₀) hδ
  have h1 : ∀ᶠ n in atTop, dist (x (φ n)) x₀ < η / 2 :=
    (Metric.tendsto_nhds.1 hlim) _ (half_pos hη)
  have h2 : ∀ᶠ n in atTop, (1:ℝ) / ((φ n : ℝ) + 1) < η / 2 := by
    have hT : Tendsto (fun n => (1:ℝ) / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact (tendsto_order.1 hT).2 _ (half_pos hη)
  have hcont : Tendsto (fun n => infDist (x (φ n)) (F x₀)) atTop (𝓝 (infDist x₀ (F x₀))) :=
    ((continuous_infDist_pt (F x₀)).tendsto x₀).comp hlim
  refine le_of_tendsto hcont ?_
  filter_upwards [h1, h2] with n hn1 hn2
  have hmem : x (φ n) ∈ thickening δ (F x₀) := by
    have hCconv : Convex ℝ (thickening δ (F x₀)) := (hFconv x₀ hx₀K).thickening δ
    rw [← hxf (φ n)]
    refine hfC (φ n) (x (φ n)) (hxK _) _ hCconv (fun x' hx' hd => huhc x' hx' ?_)
    calc dist x' x₀ ≤ dist x' (x (φ n)) + dist (x (φ n)) x₀ := dist_triangle _ _ _
      _ = dist (x (φ n)) x' + dist (x (φ n)) x₀ := by rw [dist_comm x' (x (φ n))]
      _ < 1 / ((φ n : ℝ) + 1) + η / 2 := by linarith
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring
  exact ((mem_thickening_iff_infDist_lt hFx₀ne).1 hmem).le

end KakutaniAux

end KakutaniSection

section GameSection

open Filter Topology
open AbstractEconomy

namespace GameAux

variable {ι : Type*} [DecidableEq ι] {l : ℕ} (G : AbstractEconomy ι l)

/-- Membership in `𝔄` coordinatewise. -/
theorem mem_profiles_iff (a : ι → Fin l → ℝ) : a ∈ G.profiles ↔ ∀ i, a i ∈ G.act i :=
  Set.mem_univ_pi

/-- The constraint set is unchanged by updating the own coordinate. -/
theorem constr_update (i : ι) (a : ι → Fin l → ℝ) (b : Fin l → ℝ) :
    G.constr i (Function.update a i b) = G.constr i a :=
  G.constr_indep i _ _ (fun k hk => Function.update_of_ne hk b a)

/-- Profiles satisfy `OthersIn`. -/
theorem othersIn_of_mem_profiles {a : ι → Fin l → ℝ} (ha : a ∈ G.profiles) (i : ι) :
    G.OthersIn i a := fun k _ => (mem_profiles_iff G a).1 ha k

/-- Updating the own coordinate inside the action set stays in `𝔄`. -/
theorem update_mem_profiles {a : ι → Fin l → ℝ} (ha : a ∈ G.profiles) (i : ι)
    {b : Fin l → ℝ} (hb : b ∈ G.act i) : Function.update a i b ∈ G.profiles := by
  rw [mem_profiles_iff]
  intro k
  by_cases hk : k = i
  · subst hk; simpa using hb
  · rw [Function.update_of_ne hk]; exact (mem_profiles_iff G a).1 ha k

/-- `OthersIn` is preserved by updating the own coordinate. -/
theorem othersIn_update {i : ι} {a : ι → Fin l → ℝ} (ha : G.OthersIn i a) (b : Fin l → ℝ) :
    G.OthersIn i (Function.update a i b) := by
  intro k hk
  rw [Function.update_of_ne hk]
  exact ha k hk

/-- The constraint set is the slice of the graph through `a`. -/
theorem constr_eq_preimage_graph {i : ι} {a : ι → Fin l → ℝ} (ha : G.OthersIn i a) :
    G.constr i a = (fun b => Function.update a i b) ⁻¹' G.graph i := by
  ext b
  constructor
  · intro hb
    refine ⟨othersIn_update G ha b, ?_⟩
    show Function.update a i b i ∈ G.constr i (Function.update a i b)
    rw [Function.update_self, constr_update]
    exact hb
  · intro h
    have h2 : Function.update a i b i ∈ G.constr i (Function.update a i b) := h.2
    rwa [Function.update_self, constr_update] at h2

/-- For `ā_ι ∈ 𝔄̄_ι`, the constraint set `A_ι(ā_ι)` is closed (slice of the closed graph). -/
theorem isClosed_constr {i : ι} (hAgraph : IsClosed (G.graph i)) {a : ι → Fin l → ℝ}
    (ha : G.OthersIn i a) : IsClosed (G.constr i a) := by
  rw [constr_eq_preimage_graph G ha]
  exact hAgraph.preimage (continuous_const.update i continuous_id)

/-- The **best-response correspondence** of the abstract economy: `a'` is a best response to `a`
if, for every player `i`, `a'_i ∈ A_i(ā_i)` and `a'_i` maximizes `f_i(ā_i, ·)` over `A_i(ā_i)`. -/
def bestResponse (a : ι → Fin l → ℝ) : Set (ι → Fin l → ℝ) :=
  {a' | ∀ i, a' i ∈ G.constr i a ∧
    ∀ b ∈ G.constr i a, G.payoff i (Function.update a i b) ≤ G.payoff i (Function.update a i (a' i))}

theorem mem_bestResponse_iff (a a' : ι → Fin l → ℝ) :
    a' ∈ bestResponse G a ↔ ∀ i, a' i ∈ G.constr i a ∧
      ∀ b ∈ G.constr i a,
        G.payoff i (Function.update a i b) ≤ G.payoff i (Function.update a i (a' i)) :=
  Iff.rfl

/-- Best responses to a profile are profiles. -/
theorem bestResponse_subset {a : ι → Fin l → ℝ} (ha : a ∈ G.profiles) :
    bestResponse G a ⊆ G.profiles := by
  intro a' ha'
  rw [mem_profiles_iff]
  intro i
  exact G.constr_subset i a (othersIn_of_mem_profiles G ha i) (ha' i).1

/-- Best responses exist (Weierstrass). -/
theorem bestResponse_nonempty (hcpt : ∀ i, IsCompact (G.act i))
    (hcont : ∀ i, ContinuousOn (G.payoff i) G.profiles)
    (hAgraph : ∀ i, IsClosed (G.graph i))
    (hAne : ∀ i a, G.OthersIn i a → (G.constr i a).Nonempty)
    {a : ι → Fin l → ℝ} (ha : a ∈ G.profiles) : (bestResponse G a).Nonempty := by
  have hex : ∀ i, ∃ b ∈ G.constr i a, ∀ b' ∈ G.constr i a,
      G.payoff i (Function.update a i b') ≤ G.payoff i (Function.update a i b) := by
    intro i
    have hoi := othersIn_of_mem_profiles G ha i
    have hsub : G.constr i a ⊆ G.act i := G.constr_subset i a hoi
    have hc : IsCompact (G.constr i a) :=
      (hcpt i).of_isClosed_subset (isClosed_constr G (hAgraph i) hoi) hsub
    have hf : ContinuousOn (fun b => G.payoff i (Function.update a i b)) (G.constr i a) := by
      have hupd : Continuous (fun b : Fin l → ℝ => Function.update a i b) :=
        continuous_const.update i continuous_id
      refine (hcont i).comp hupd.continuousOn ?_
      intro b hb
      exact update_mem_profiles G ha i (hsub hb)
    obtain ⟨b, hb, hmax⟩ := hc.exists_isMaxOn (hAne i a hoi) hf
    exact ⟨b, hb, fun b' hb' => hmax hb'⟩
  choose a' ha' using hex
  exact ⟨a', fun i => ha' i⟩

/-- Best-response sets are convex (quasi-concavity of the pay-offs). -/
theorem bestResponse_convex
    (hqc : ∀ i a, G.OthersIn i a →
      QuasiconcaveOn ℝ (G.act i) (fun b => G.payoff i (Function.update a i b)))
    (hAconv : ∀ i a, G.OthersIn i a → Convex ℝ (G.constr i a))
    {a : ι → Fin l → ℝ} (ha : a ∈ G.profiles) : Convex ℝ (bestResponse G a) := by
  have heq : bestResponse G a = Set.univ.pi (fun i => {b | b ∈ G.constr i a ∧
      ∀ b' ∈ G.constr i a,
        G.payoff i (Function.update a i b') ≤ G.payoff i (Function.update a i b)}) := by
    ext a'
    rw [mem_bestResponse_iff, Set.mem_univ_pi]
    rfl
  rw [heq]
  refine convex_pi (fun i _ => ?_)
  intro b₁ hb₁ b₂ hb₂ s t hs ht hst
  have hoi := othersIn_of_mem_profiles G ha i
  have hsub : G.constr i a ⊆ G.act i := G.constr_subset i a hoi
  have hb₁' : b₁ ∈ G.constr i a ∧ ∀ b' ∈ G.constr i a,
      G.payoff i (Function.update a i b') ≤ G.payoff i (Function.update a i b₁) := hb₁
  have hb₂' : b₂ ∈ G.constr i a ∧ ∀ b' ∈ G.constr i a,
      G.payoff i (Function.update a i b') ≤ G.payoff i (Function.update a i b₂) := hb₂
  have hmem : s • b₁ + t • b₂ ∈ G.constr i a := hAconv i a hoi hb₁'.1 hb₂'.1 hs ht hst
  refine ⟨hmem, fun b' hb' => ?_⟩
  -- the value `M := f(b₁)`; both `b₁, b₂` lie in the superlevel set at `M`
  have hM := hqc i a hoi (G.payoff i (Function.update a i b₁))
  have h1 : b₁ ∈ {x | x ∈ G.act i ∧
      G.payoff i (Function.update a i b₁) ≤ G.payoff i (Function.update a i x)} :=
    ⟨hsub hb₁'.1, le_rfl⟩
  have h2 : b₂ ∈ {x | x ∈ G.act i ∧
      G.payoff i (Function.update a i b₁) ≤ G.payoff i (Function.update a i x)} :=
    ⟨hsub hb₂'.1, hb₂'.2 b₁ hb₁'.1⟩
  have h3 := hM h1 h2 hs ht hst
  exact le_trans (hb₁'.2 b' hb') h3.2

/-- The graph of the best-response correspondence over `𝔄` is closed. -/
theorem bestResponse_graph_closed [Fintype ι]
    (hcpt : ∀ i, IsCompact (G.act i))
    (hcont : ∀ i, ContinuousOn (G.payoff i) G.profiles)
    (hAcont : ∀ i, G.ConstrContinuous i)
    (hAgraph : ∀ i, IsClosed (G.graph i)) :
    IsClosed {p : (ι → Fin l → ℝ) × (ι → Fin l → ℝ) |
      p.1 ∈ G.profiles ∧ p.2 ∈ bestResponse G p.1} := by
  have hKcl : IsClosed G.profiles := isClosed_set_pi (fun i _ => (hcpt i).isClosed)
  refine IsSeqClosed.isClosed (fun u p hu hup => ?_)
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := hup.fst_nhds
  have h2 : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := hup.snd_nhds
  have hpK : p.1 ∈ G.profiles :=
    hKcl.mem_of_tendsto h1 (Eventually.of_forall (fun n => (hu n).1))
  refine ⟨hpK, fun i => ?_⟩
  have hoi := othersIn_of_mem_profiles G hpK i
  have hsub : G.constr i p.1 ⊆ G.act i := G.constr_subset i p.1 hoi
  -- membership in the constraint set: closed graph of `A_i`
  have hmemC : p.2 i ∈ G.constr i p.1 := by
    have hv : Tendsto (fun n => Function.update (u n).1 i ((u n).2 i)) atTop
        (𝓝 (Function.update p.1 i (p.2 i))) :=
      h1.update i (tendsto_pi_nhds.1 h2 i)
    have hvG : ∀ n, Function.update (u n).1 i ((u n).2 i) ∈ G.graph i := by
      intro n
      refine ⟨othersIn_update G (othersIn_of_mem_profiles G (hu n).1 i) _, ?_⟩
      rw [Function.update_self, constr_update]
      exact ((hu n).2 i).1
    have hlimG := (hAgraph i).mem_of_tendsto hv (Eventually.of_forall hvG)
    have := hlimG.2
    rwa [Function.update_self, constr_update] at this
  refine ⟨hmemC, fun b hb => ?_⟩
  -- optimality: lower hemicontinuity of `A_i` and continuity of `f_i`
  obtain ⟨t, ht, htmem⟩ := hAcont i p.1 hoi b hb (fun n => (u n).1)
    (fun n => othersIn_of_mem_profiles G (hu n).1 i)
    (fun κ _ => tendsto_pi_nhds.1 h1 κ)
  have hineq : ∀ n, G.payoff i (Function.update (u n).1 i (t n)) ≤
      G.payoff i (Function.update (u n).1 i ((u n).2 i)) :=
    fun n => ((hu n).2 i).2 (t n) (htmem n)
  have hL : Tendsto (fun n => G.payoff i (Function.update (u n).1 i (t n))) atTop
      (𝓝 (G.payoff i (Function.update p.1 i b))) := by
    have hmem : Function.update p.1 i b ∈ G.profiles := update_mem_profiles G hpK i (hsub hb)
    refine ((hcont i) _ hmem).tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h1.update i ht, Eventually.of_forall (fun n => ?_)⟩
    exact update_mem_profiles G (hu n).1 i
      (G.constr_subset i (u n).1 (othersIn_of_mem_profiles G (hu n).1 i) (htmem n))
  have hR : Tendsto (fun n => G.payoff i (Function.update (u n).1 i ((u n).2 i))) atTop
      (𝓝 (G.payoff i (Function.update p.1 i (p.2 i)))) := by
    have hmem : Function.update p.1 i (p.2 i) ∈ G.profiles :=
      update_mem_profiles G hpK i (hsub hmemC)
    refine ((hcont i) _ hmem).tendsto.comp ?_
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h1.update i (tendsto_pi_nhds.1 h2 i), Eventually.of_forall (fun n => ?_)⟩
    exact update_mem_profiles G (hu n).1 i
      (G.constr_subset i (u n).1 (othersIn_of_mem_profiles G (hu n).1 i) ((hu n).2 i).1)
  exact le_of_tendsto_of_tendsto' hL hR hineq

end GameAux

end GameSection

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI ArrowDebreu.ThmI.GameAux
open AbstractEconomy

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {l : ℕ} (G : AbstractEconomy ι l)
    (hne : ∀ i, (G.act i).Nonempty)
    (hcpt : ∀ i, IsCompact (G.act i)) (hconv : ∀ i, Convex ℝ (G.act i))
    (hcont : ∀ i, ContinuousOn (G.payoff i) G.profiles)
    (hqc : ∀ i a, G.OthersIn i a →
      QuasiconcaveOn ℝ (G.act i) (fun b => G.payoff i (Function.update a i b)))
    (hAcont : ∀ i, G.ConstrContinuous i)
    (hAgraph : ∀ i, IsClosed (G.graph i))
    (hAconv : ∀ i a, G.OthersIn i a → Convex ℝ (G.constr i a))
    (hAne : ∀ i a, G.OthersIn i a → (G.constr i a).Nonempty) :
    ∃ a, G.IsEquilibriumPoint a := by
  have hKconv : Convex ℝ G.profiles := convex_pi (fun i _ => hconv i)
  have hKcpt : IsCompact G.profiles := isCompact_univ_pi hcpt
  have hKne : G.profiles.Nonempty := Set.univ_pi_nonempty_iff.2 hne
  obtain ⟨a, haK, haF⟩ := KakutaniAux.kakutani_core hKconv hKcpt hKne (bestResponse G)
    (fun a ha => bestResponse_nonempty G hcpt hcont hAgraph hAne ha)
    (fun a ha => bestResponse_convex G hqc hAconv ha)
    (fun a ha => bestResponse_subset G ha)
    (bestResponse_graph_closed G hcpt hcont hAcont hAgraph)
  refine ⟨a, haK, fun i => ⟨(haF i).1, fun b hb => ?_⟩⟩
  have := (haF i).2 b hb
  rwa [Function.update_eq_self] at this

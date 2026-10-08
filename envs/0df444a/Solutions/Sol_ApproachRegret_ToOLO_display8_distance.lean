-- Prove2me | solution 1 for ApproachRegret.ToOLO.display8_distance
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T14:04:52.447304+00:00
-- url     : https://prove2.me/submissions/749a8418-6e74-48fa-b49c-da3fb669d1b7

import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne
import Theorems.Thm_ApproachRegret_ToOLO_lemma13_dist_cone

open scoped RealInnerProductSpace
set_option autoImplicit false

namespace Display8Internal

open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace LiftAlgebra
open ApproachRegret.ToOLO

@[simp] lemma lift_zero {d : ℕ} (a : ℝ) (x : E d) : lift a x 0 = a := by
  simp [lift]

@[simp] lemma lift_succ {d : ℕ} (a : ℝ) (x : E d) (i : Fin d) :
    lift a x i.succ = x i := by
  simp [lift]

lemma inner_lift {d : ℕ} (a b : ℝ) (x y : E d) :
    ⟪lift a x, lift b y⟫ = a*b + ⟪x,y⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_succ]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

lemma norm_lift_sq {d : ℕ} (a : ℝ) (x : E d) :
    ‖lift a x‖ ^ 2 = a^2 + ‖x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, inner_lift, real_inner_self_eq_norm_sq]
  ring

lemma payoff_inner {d : ℕ} (K : Set (E d)) (hk : 0 < kappa K) (x y f : E d) :
    ⟪payoff K x f, lift (kappa K) y⟫ = ⟪f,x⟫ - ⟪f,y⟫ := by
  rw [payoff, inner_lift, inner_neg_left, div_mul_cancel₀ _ (ne_of_gt hk)]
  rfl

lemma norm_le_kappa {d : ℕ} (K : Set (E d)) (hK : IsCompact K) {x : E d}
    (hx : x ∈ K) : ‖x‖ ≤ kappa K := by
  exact le_csSup (hK.image continuous_norm).bddAbove (mem_image_of_mem _ hx)

lemma norm_lift_bound {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (hk : 0 < kappa K) {x : E d} (hx : x ∈ K) :
    ‖lift (kappa K) x‖ ≤ 2 * kappa K := by
  have hn := norm_lift_sq (kappa K) x
  have hb := norm_le_kappa K hK hx
  nlinarith [norm_nonneg (lift (kappa K) x), norm_nonneg x]

end LiftAlgebra


open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace ParentClosedCone
open ApproachRegret.ToOLO LiftAlgebra

lemma continuous_lift {d : ℕ} (κ : ℝ) : Continuous (lift κ : E d → E (d + 1)) := by
  change Continuous (fun x : E d => WithLp.toLp 2
    (fun i : Fin (d + 1) => Fin.cases (motive := fun _ => ℝ) κ (fun j : Fin d => x j) i))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (d + 1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · exact PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) j

theorem isClosed_cone_lift {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (κ : ℝ) (hκ : 0 < κ) : IsClosed (cone (lift κ '' K)) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (E (d + 1) × K) :=
    {p | 0 ≤ p.1 0 ∧ p.1 = (p.1 0 / κ) • lift κ p.2}
  have hc0 : Continuous (fun p : E (d + 1) × K => p.1 0) :=
    (PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) 0).comp continuous_fst
  have hSl : IsClosed S := by
    apply IsClosed.inter
    · exact isClosed_le continuous_const hc0
    · apply isClosed_eq continuous_fst
      exact (hc0.div_const κ).smul ((continuous_lift κ).comp
        (continuous_subtype_val.comp continuous_snd))
  have hEq : Prod.fst '' S = cone (lift κ '' K) := by
    ext z
    constructor
    · rintro ⟨⟨v,x⟩,⟨hv0,hv⟩,rfl⟩
      exact ⟨v 0 / κ, div_nonneg hv0 hκ.le, lift κ x,
        ⟨x, x.property, rfl⟩, hv⟩
    · rintro ⟨α,hα,w,⟨x,hx,rfl⟩,rfl⟩
      refine ⟨(α • lift κ x, ⟨x,hx⟩), ?_, rfl⟩
      change 0 ≤ (α • lift κ x) 0 ∧
        α • lift κ x = ((α • lift κ x) 0 / κ) • lift κ x
      simpa [PiLp.smul_apply, hκ.ne'] using
        (show 0 ≤ α * κ ∧ α • lift κ x = α • lift κ x from
          ⟨mul_nonneg hα hκ.le, rfl⟩)
  rw [← hEq]
  exact isClosedMap_fst_of_compactSpace S hSl

theorem bipolar_of_closed_convex_cone {d : ℕ} (C : Set (E d))
    (hC : Convex ℝ C) (hcone : ∀ z ∈ C, ∀ α : ℝ, 0 ≤ α → α • z ∈ C)
    (hne : C.Nonempty) (hclosed : IsClosed C) : polar (polar C) = C := by
  have hzero : (0 : E d) ∈ C := by
    obtain ⟨z,hz⟩ := hne
    simpa using hcone z hz 0 le_rfl
  have hadd : ∀ x ∈ C, ∀ y ∈ C, x + y ∈ C := by
    intro x hx y hy
    have hmid := hC hx hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    have hh := hcone _ hmid 2 (by norm_num)
    convert hh using 1 <;> module
  let P : ProperCone ℝ (E d) :=
    { carrier := C
      zero_mem' := hzero
      add_mem' := fun hx hy => hadd _ hx _ hy
      smul_mem' := fun α z hz => hcone z hz α α.property
      isClosed' := hclosed }
  ext x
  constructor
  · intro hx
    by_contra hn
    have hnP : x ∉ P := hn
    obtain ⟨y,hy,hxy⟩ := P.hyperplane_separation' hnP
    have hny : -y ∈ polar C := by
      intro z hz
      have hh := hy z hz
      simpa only [inner_neg_left, real_inner_comm] using (neg_nonpos.mpr hh)
    have hh := hx (-y) hny
    rw [inner_neg_right] at hh
    linarith
  · intro hx θ hθ
    have hh := hθ x hx
    simpa only [real_inner_comm] using hh

lemma cone_nonempty {d : ℕ} (K : Set (E d)) (hne : K.Nonempty) : (cone K).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  exact ⟨0, 0, le_rfl, x, hx, by simp⟩

lemma cone_smul {d : ℕ} (K : Set (E d)) :
    ∀ z ∈ cone K, ∀ α : ℝ, 0 ≤ α → α • z ∈ cone K := by
  rintro z ⟨a,ha,x,hx,rfl⟩ b hb
  exact ⟨b * a, mul_nonneg hb ha, x, hx, by rw [smul_smul]⟩

lemma convex_cone {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) : Convex ℝ (cone K) := by
  have hadd : ∀ x ∈ cone K, ∀ y ∈ cone K, x + y ∈ cone K := by
    rintro u ⟨a,ha,x,hx,rfl⟩ v ⟨b,hb,y,hy,rfl⟩
    by_cases hz : a + b = 0
    · have ha0 : a = 0 := by linarith
      have hb0 : b = 0 := by linarith
      exact ⟨0, le_rfl, x, hx, by simp [ha0,hb0]⟩
    · have hp : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hz)
      have hsum : a / (a + b) + b / (a + b) = 1 := by field_simp
      refine ⟨a+b, hp.le, (a / (a+b)) • x + (b / (a+b)) • y,
        hK hx hy (div_nonneg ha hp.le) (div_nonneg hb hp.le) hsum, ?_⟩
      rw [smul_add, smul_smul, smul_smul]
      congr 1 <;> congr 1 <;> field_simp
  intro x hx y hy a b ha hb hab
  exact hadd _ (cone_smul K x hx a ha) _ (cone_smul K y hy b hb)

lemma convex_lift_image {d : ℕ} (K : Set (E d)) (hK : Convex ℝ K) (κ : ℝ) :
    Convex ℝ (lift κ '' K) := by
  rintro u ⟨x,hx,rfl⟩ v ⟨y,hy,rfl⟩ a b ha hb hab
  refine ⟨a • x + b • y, hK hx hy ha hb hab, ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [lift_zero, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [← add_mul, hab, one_mul]
  · simp

theorem bipolar_cone_lift {d : ℕ} (K : Set (E d)) (hK : IsCompact K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (κ : ℝ) (hκ : 0 < κ) :
    polar (polar (cone (lift κ '' K))) = cone (lift κ '' K) :=
  bipolar_of_closed_convex_cone _ (convex_cone _ (convex_lift_image K hconv κ))
    (cone_smul _) (cone_nonempty _ (hne.image (lift κ))) (isClosed_cone_lift K hK κ hκ)

end ParentClosedCone



open scoped RealInnerProductSpace
open Set
set_option autoImplicit false

namespace DisplayBound
open ApproachRegret.ToOLO

lemma polar_convex {d : ℕ} (C : Set (E d)) : Convex ℝ (polar C) := by
  intro x hx y hy a b ha hb hab z hz
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx z hz))
    (mul_nonpos_of_nonneg_of_nonpos hb (hy z hz))

lemma polar_smul {d : ℕ} (C : Set (E d)) :
    ∀ z ∈ polar C, ∀ t : ℝ, 0 ≤ t → t • z ∈ polar C := by
  intro z hz t ht y hy
  rw [inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hz y hy)

lemma polar_nonempty {d : ℕ} (C : Set (E d)) : (polar C).Nonempty := by
  refine ⟨0,?_⟩
  intro z hz
  simp

theorem display_from_bipolar {d : ℕ} (K : Set (E d)) (z : E (d+1))
    (hbip : polar (target K) = cone (lift (kappa K) '' K)) :
    IsGreatest ((fun w : E (d+1) => ⟪z,w⟫) ''
      (cone (lift (kappa K) '' K) ∩ Metric.closedBall 0 1))
      (Metric.infDist z (target K)) := by
  have h := lemma13_dist_cone (target K) z (polar_convex _)
    (polar_smul _) (polar_nonempty _)
  rw [hbip] at h
  simpa only [real_inner_comm] using h

end DisplayBound
end Display8Internal

open ApproachRegret.ToOLO

/-- Display (8), p. 37, for an arbitrary point in the lifted Euclidean space. -/
theorem solution {d : ℕ} (K : Set (E d)) (z : E (d + 1))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hk : 0 < kappa K) :
    IsGreatest ((fun w : E (d + 1) => ⟪z, w⟫) ''
      (cone (lift (kappa K) '' K) ∩ Metric.closedBall 0 1))
      (Metric.infDist z (target K)) := by
  exact Display8Internal.DisplayBound.display_from_bipolar K z
    (by simpa only [target] using
      Display8Internal.ParentClosedCone.bipolar_cone_lift K hK hconv hne (kappa K) hk)



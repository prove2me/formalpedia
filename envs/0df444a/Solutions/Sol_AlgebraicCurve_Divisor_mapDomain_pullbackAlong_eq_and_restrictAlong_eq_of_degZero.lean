-- Prove2me | solution 1 for AlgebraicCurve.Divisor.mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/6abc126b-76c8-5ab3-9bed-5aa97ab77189

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero

open AlgebraicCurve

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace P2mSolDeuringCriterion

open Finsupp

section Finsupp

variable {X Y : Type*}

theorem mapDomain_apply_eq_sum [DecidableEq Y] (r : X → Y) (D : X →₀ ℤ) (y : Y) :
    mapDomain r D y = ∑ x ∈ D.support, if r x = y then D x else 0 := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mapDomain_nonneg (r : X → Y) {D : X →₀ ℤ} (hD : ∀ x, 0 ≤ D x) (y : Y) :
    0 ≤ mapDomain r D y := by
  classical
  rw [mapDomain_apply_eq_sum]
  refine Finset.sum_nonneg fun x _ => ?_
  split_ifs
  · exact hD x
  · exact le_rfl

theorem le_mapDomain_apply_self (r : X → Y) {D : X →₀ ℤ} (hD : ∀ x, 0 ≤ D x) (x : X) :
    D x ≤ mapDomain r D (r x) := by
  classical
  by_cases hx : x ∈ D.support
  · rw [mapDomain_apply_eq_sum]
    have := Finset.single_le_sum (f := fun x' => if r x' = r x then D x' else 0)
      (fun x' _ => by
        split_ifs
        · exact hD x'
        · exact le_rfl) hx
    simpa using this
  · rw [Finsupp.notMem_support_iff.mp hx]
    exact mapDomain_nonneg r hD _

end Finsupp

section Rational

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (h1 : ∀ v : Place K F, v.deg = 1) (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v := by
  rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [h1 v]

theorem degree_nonneg (h1 : ∀ v : Place K F, v.deg = 1) {D : Divisor K F}
    (hD : ∀ v, 0 ≤ D v) : 0 ≤ Divisor.degree D := by
  rw [degree_eq_sum h1]
  exact Finset.sum_nonneg fun v _ => hD v

theorem eq_zero_of_nonneg_of_degree_eq_zero (h1 : ∀ v : Place K F, v.deg = 1)
    {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) (hdeg : Divisor.degree D = 0) : D = 0 := by
  rw [degree_eq_sum h1] at hdeg
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hD v)).mp hdeg
  ext v
  by_cases hv : v ∈ D.support
  · exact hall v hv
  · exact Finsupp.notMem_support_iff.mp hv

theorem degree_mapDomain_eq {K' F' : Type*} [Field K'] [Field F'] [Algebra K' F']
    (h1 : ∀ v : Place K F, v.deg = 1) (h1' : ∀ w : Place K' F', w.deg = 1)
    (r : Place K F → Place K' F') (D : Divisor K F) :
    Divisor.degree (mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, h1, h1']

end Rational

section Along

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

include hφ in
theorem ramificationIndexAlong_pos (w : Place K F') : 0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact w.ramificationIndex_pos (F := F)

theorem pullbackAlong_nonneg {D : Divisor K F} (hD : ∀ v, 0 ≤ D v) (w : Place K F') :
    0 ≤ Divisor.pullbackAlong φ hφ D w := by
  rw [Divisor.pullbackAlong_apply]
  exact mul_nonneg (Int.natCast_nonneg _) (hD _)

theorem single_one_nonneg {X : Type*} (x : X) : ∀ x', 0 ≤ (single x (1 : ℤ)) x' := by
  classical
  intro x'
  rw [Finsupp.single_apply]
  split_ifs <;> norm_num

theorem pullbackAlong_single_nonneg (v : Place K F) (w : Place K F') :
    0 ≤ Divisor.pullbackAlong φ hφ (single v 1) w :=
  pullbackAlong_nonneg φ hφ (single_one_nonneg v) w

theorem pullbackAlong_single_apply_of_ne {v : Place K F} {w : Place K F'}
    (h : w.restrictAlong φ hφ ≠ v) : Divisor.pullbackAlong φ hφ (single v 1) w = 0 := by
  classical
  rw [Divisor.pullbackAlong_apply, Finsupp.single_apply, if_neg (Ne.symm h), mul_zero]

theorem pullbackAlong_single_apply_self (w : Place K F') :
    Divisor.pullbackAlong φ hφ (single (w.restrictAlong φ hφ) 1) w
      = Place.ramificationIndexAlong φ w := by
  rw [Divisor.pullbackAlong_apply, Finsupp.single_eq_same, mul_one]

theorem inertiaDegAlong_eq_one (h1F : ∀ v : Place K F, v.deg = 1)
    (h1F' : ∀ w : Place K F', w.deg = 1) (w : Place K F') :
    (w.inertiaDegAlong φ hφ : ℤ) = 1 := by
  have h := Divisor.degree_pushforwardAlong φ hφ (Finsupp.single w 1)
  rw [Divisor.pushforwardAlong_single, Divisor.degree_single, Divisor.degree_single, h1F, h1F']
    at h
  push_cast at h
  linarith

theorem pushforwardAlong_single_one (h1F : ∀ v : Place K F, v.deg = 1)
    (h1F' : ∀ w : Place K F', w.deg = 1) (w : Place K F') :
    Divisor.pushforwardAlong φ hφ (single w 1) = single (w.restrictAlong φ hφ) 1 := by
  rw [Divisor.pushforwardAlong_single, one_mul, inertiaDegAlong_eq_one φ hφ h1F h1F' w]

end Along

section Engine

variable {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
variable {k C₁ C₂ : Type*} [Field k] [Field C₁] [Field C₂] [Algebra k C₁] [Algebra k C₂]
variable [HasPrincipalDivisors K F₂] [HasPrincipalDivisors k C₂]
variable (φ : F₁ →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral)
variable (φb : C₁ →ₐ[k] C₂) (hφb : φb.toRingHom.IsIntegral)
variable (r₁ : Place K F₁ → Place k C₁) (r : Place K F₂ → Place k C₂)

def defect (v : Place K F₁) : Divisor k C₂ :=
  mapDomain r (Divisor.pullbackAlong φ hφ (single v 1))
    - Divisor.pullbackAlong φb hφb (single (r₁ v) 1)

theorem defect_eq
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (mapDomain r₁ D))
    (v v' : Place K F₁) :
    defect φ hφ φb hφb r₁ r v = defect φ hφ φb hφb r₁ r v' := by
  have hD : single v (1 : ℤ) - single v' 1 ∈ Divisor.degZero (K := K) (F := F₁) := by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, h1F₁, h1F₁,
      sub_self]
  have h := hcompat _ hD
  rw [map_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_sub, Finsupp.mapDomain_single,
    Finsupp.mapDomain_single, map_sub] at h
  exact sub_eq_sub_iff_sub_eq_sub.mp h

theorem defect_nonneg
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (mapDomain r₁ D))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v)
    (v : Place K F₁) (Y : Place k C₂) : 0 ≤ defect φ hφ φb hφb r₁ r v Y := by
  obtain ⟨v', hv'⟩ := hnc v
  by_cases hY : Y.restrictAlong φb hφb = r₁ v
  · have hY' : Y.restrictAlong φb hφb ≠ r₁ v' := by rw [hY]; exact Ne.symm hv'
    rw [defect_eq φ hφ φb hφb r₁ r h1F₁ hcompat v v', defect, Finsupp.sub_apply,
      pullbackAlong_single_apply_of_ne φb hφb hY', sub_zero]
    exact mapDomain_nonneg r (pullbackAlong_single_nonneg φ hφ v') Y
  · rw [defect, Finsupp.sub_apply, pullbackAlong_single_apply_of_ne φb hφb hY, sub_zero]
    exact mapDomain_nonneg r (pullbackAlong_single_nonneg φ hφ v) Y

theorem defect_eq_zero
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1) (h1F₂ : ∀ W : Place K F₂, W.deg = 1)
    (h1C₂ : ∀ Y : Place k C₂, Y.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (mapDomain r₁ D))
    (hdeg : ∀ v : Place K F₁,
      Divisor.degree (Divisor.pullbackAlong φ hφ (single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong φb hφb (single (r₁ v) 1)))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v)
    (v : Place K F₁) : defect φ hφ φb hφb r₁ r v = 0 := by
  have hnonneg : ∀ Y, 0 ≤ defect φ hφ φb hφb r₁ r v Y :=
    defect_nonneg φ hφ φb hφb r₁ r h1F₁ hcompat hnc v
  have hle : Divisor.degree (defect φ hφ φb hφb r₁ r v) ≤ 0 := by
    rw [defect, map_sub, degree_mapDomain_eq h1F₂ h1C₂, sub_nonpos]
    exact hdeg v
  have hge : 0 ≤ Divisor.degree (defect φ hφ φb hφb r₁ r v) := degree_nonneg h1C₂ hnonneg
  exact eq_zero_of_nonneg_of_degree_eq_zero h1C₂ hnonneg (le_antisymm hle hge)

theorem engine
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1) (h1F₂ : ∀ W : Place K F₂, W.deg = 1)
    (h1C₁ : ∀ Q : Place k C₁, Q.deg = 1) (h1C₂ : ∀ Y : Place k C₂, Y.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (mapDomain r₁ D))
    (hdeg : ∀ v : Place K F₁,
      Divisor.degree (Divisor.pullbackAlong φ hφ (single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong φb hφb (single (r₁ v) 1)))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v) :
    (∀ D : Divisor K F₁, mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (mapDomain r₁ D)) ∧
    (∀ W : Place K F₂, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ)) ∧
    (∀ D : Divisor K F₂, mapDomain r₁ (Divisor.pushforwardAlong φ hφ D) =
        Divisor.pushforwardAlong φb hφb (mapDomain r D)) := by

  have hzero : ∀ v, mapDomain r (Divisor.pullbackAlong φ hφ (single v 1))
      = Divisor.pullbackAlong φb hφb (single (r₁ v) 1) := fun v =>
    sub_eq_zero.mp (defect_eq_zero φ hφ φb hφb r₁ r h1F₁ h1F₂ h1C₂ hcompat hdeg hnc v)

  have hpull : ∀ D : Divisor K F₁, mapDomain r (Divisor.pullbackAlong φ hφ D) =
      Divisor.pullbackAlong φb hφb (mapDomain r₁ D) := by
    intro D
    have hfg : (Finsupp.mapDomain.addMonoidHom r).comp (Divisor.pullbackAlong φ hφ) =
        (Divisor.pullbackAlong φb hφb).comp (Finsupp.mapDomain.addMonoidHom r₁) := by
      refine Finsupp.addHom_ext' fun v => AddMonoidHom.ext_int ?_
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
        Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
      exact hzero v
    have := congrArg (fun Φ => Φ D) hfg
    simpa only [AddMonoidHom.coe_comp, Function.comp_apply,
      Finsupp.mapDomain.addMonoidHom_apply] using this

  have hplace : ∀ W : Place K F₂, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ) := by
    intro W
    by_contra hne
    have heq := congrArg (fun E : Divisor k C₂ => E (r W)) (hzero (W.restrictAlong φ hφ))
    rw [pullbackAlong_single_apply_of_ne φb hφb hne] at heq
    have hle := le_mapDomain_apply_self r
      (pullbackAlong_single_nonneg φ hφ (W.restrictAlong φ hφ)) W
    rw [heq, pullbackAlong_single_apply_self] at hle
    have hpos := ramificationIndexAlong_pos φ hφ W
    omega
  refine ⟨hpull, hplace, fun D => ?_⟩

  have hfg : (Finsupp.mapDomain.addMonoidHom r₁).comp (Divisor.pushforwardAlong φ hφ) =
      (Divisor.pushforwardAlong φb hφb).comp (Finsupp.mapDomain.addMonoidHom r) := by
    refine Finsupp.addHom_ext' fun W => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, Finsupp.singleAddHom_apply,
      Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single]
    rw [pushforwardAlong_single_one φ hφ h1F₁ h1F₂, pushforwardAlong_single_one φb hφb h1C₁ h1C₂,
      Finsupp.mapDomain_single, hplace W]
  have := congrArg (fun Φ => Φ D) hfg
  simpa only [AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply] using this

end Engine

end P2mSolDeuringCriterion

end

open P2mSolDeuringCriterion in
theorem solution
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    {k C₁ C₂ : Type*} [Field k] [Field C₁] [Field C₂] [Algebra k C₁] [Algebra k C₂]
    [HasPrincipalDivisors K F₂] [HasPrincipalDivisors k C₂]
    (φ : F₁ →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral)
    (φb : C₁ →ₐ[k] C₂) (hφb : φb.toRingHom.IsIntegral)
    (r₁ : Place K F₁ → Place k C₁) (r : Place K F₂ → Place k C₂)
    (h1F₁ : ∀ v : Place K F₁, v.deg = 1) (h1F₂ : ∀ W : Place K F₂, W.deg = 1)
    (h1C₁ : ∀ Q : Place k C₁, Q.deg = 1) (h1C₂ : ∀ Y : Place k C₂, Y.deg = 1)
    (hcompat : ∀ D : Divisor K F₁, D ∈ Divisor.degZero (K := K) (F := F₁) →
      Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D))
    (hdeg : ∀ v : Place K F₁,
      Divisor.degree (Divisor.pullbackAlong φ hφ (Finsupp.single v 1)) ≤
        Divisor.degree (Divisor.pullbackAlong φb hφb (Finsupp.single (r₁ v) 1)))
    (hnc : ∀ v : Place K F₁, ∃ v' : Place K F₁, r₁ v' ≠ r₁ v) :
    (∀ D : Divisor K F₁, Finsupp.mapDomain r (Divisor.pullbackAlong φ hφ D) =
        Divisor.pullbackAlong φb hφb (Finsupp.mapDomain r₁ D)) ∧
    (∀ W : Place K F₂, (r W).restrictAlong φb hφb = r₁ (W.restrictAlong φ hφ)) ∧
    (∀ D : Divisor K F₂, Finsupp.mapDomain r₁ (Divisor.pushforwardAlong φ hφ D) =
        Divisor.pushforwardAlong φb hφb (Finsupp.mapDomain r D)) :=
  engine φ hφ φb hφb r₁ r h1F₁ h1F₂ h1C₁ h1C₂ hcompat hdeg hnc

end S_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero
end P2MW
export P2MW.S_AlgebraicCurve_Divisor_mapDomain_pullbackAlong_eq_and_restrictAlong_eq_of_degZero (solution)

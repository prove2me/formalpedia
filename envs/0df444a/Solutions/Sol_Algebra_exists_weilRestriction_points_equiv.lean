-- Prove2me | solution 1 for Algebra.exists_weilRestriction_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/44adc5c0-dea1-5c04-ae06-1793bb2b6ef2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_weilRestriction_points_equiv

set_option autoImplicit false

open scoped TensorProduct

universe u

namespace E90WR

open Algebra.TensorProduct

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)

section coords

variable {T : Type u} [CommRing T] [Algebra A T]

noncomputable def coord (i : ι) : B ⊗[A] T →ₗ[A] T :=
  TensorProduct.lift
    { toFun := fun b => (β.repr b i) • (LinearMap.id : T →ₗ[A] T)
      map_add' := fun b b' => by ext t; simp [add_smul]
      map_smul' := fun a b => by ext t; simp [mul_smul] }

@[scoped simp] theorem coord_tmul (i : ι) (b : B) (t : T) : coord β i (b ⊗ₜ t) = (β.repr b i) • t := by
  simp [coord]

theorem sum_basis_tmul_coord (z : B ⊗[A] T) : ∑ i, β i ⊗ₜ[A] coord β i z = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b t =>
      simp only [coord_tmul]
      calc ∑ i, β i ⊗ₜ[A] (β.repr b i • t) = ∑ i, (β.repr b i • β i) ⊗ₜ[A] t := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        _ = (∑ i, β.repr b i • β i) ⊗ₜ[A] t := by rw [TensorProduct.sum_tmul]
        _ = b ⊗ₜ t := by rw [β.sum_repr b]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib, hx, hy]

theorem coord_sum_basis_tmul (x : ι → T) (i : ι) : coord β i (∑ j, β j ⊗ₜ[A] x j) = x i := by
  simp [map_sum, coord_tmul, Module.Basis.repr_self, Finsupp.single_apply]

theorem ext_coord {z z' : B ⊗[A] T} (h : ∀ i, coord β i z = coord β i z') : z = z' := by
  rw [← sum_basis_tmul_coord β z, ← sum_basis_tmul_coord β z']
  simp [h]

theorem coord_mul (z z' : B ⊗[A] T) (i : ι) :
    coord β i (z * z') = ∑ j, ∑ k, β.repr (β j * β k) i • (coord β j z * coord β k z') := by
  conv_lhs => rw [← sum_basis_tmul_coord β z, ← sum_basis_tmul_coord β z']
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, map_sum, coord_tmul]

theorem coord_smul (b : B) (z : B ⊗[A] T) (i : ι) :
    coord β i (b • z) = ∑ j, β.repr (b * β j) i • coord β j z := by
  conv_lhs => rw [← sum_basis_tmul_coord β z]
  rw [Finset.smul_sum]
  simp_rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, coord_tmul]

theorem coord_one (i : ι) : coord β i (1 : B ⊗[A] T) = algebraMap A T (β.repr 1 i) := by
  rw [Algebra.TensorProduct.one_def, coord_tmul, Algebra.algebraMap_eq_smul_one]

theorem coord_map {T' : Type u} [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T') (z : B ⊗[A] T) (i : ι) :
    coord β i ((map (AlgHom.id B B) u) z) = u (coord β i z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b t => simp [map_tmul, coord_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

end coords

section points

variable {H : Type u} [CommRing H] [Algebra B H]
variable {T : Type u} [CommRing T] [Algebra A T]

structure IsCoords (x : H → ι → T) : Prop where
  add : ∀ h h' i, x (h + h') i = x h i + x h' i
  smul : ∀ (b : B) h i, x (b • h) i = ∑ j, β.repr (b * β j) i • x h j
  mul : ∀ h h' i, x (h * h') i = ∑ j, ∑ k, β.repr (β j * β k) i • (x h j * x h' k)
  one : ∀ i, x 1 i = algebraMap A T (β.repr 1 i)

theorem isCoords_coord (φ : H →ₐ[B] B ⊗[A] T) : IsCoords β (fun h i => coord β i (φ h)) where
  add h h' i := by simp [map_add]
  smul b h i := by rw [map_smul, coord_smul]
  mul h h' i := by rw [map_mul, coord_mul]
  one i := by rw [map_one, coord_one]

noncomputable def pointOfCoords (x : H → ι → T) (hx : IsCoords β x) : H →ₐ[B] B ⊗[A] T where
  toFun h := ∑ i, β i ⊗ₜ[A] x h i
  map_one' := by
    apply ext_coord β; intro i
    rw [coord_sum_basis_tmul, hx.one, coord_one]
  map_mul' h h' := by
    apply ext_coord β; intro i
    rw [coord_sum_basis_tmul, hx.mul, coord_mul]
    simp_rw [coord_sum_basis_tmul]
  map_zero' := by
    have h0 : ∀ i, x 0 i = 0 := by
      intro i
      have := hx.add 0 0 i
      rw [add_zero] at this
      exact left_eq_add.mp this
    simp [h0]
  map_add' h h' := by
    simp [hx.add, TensorProduct.tmul_add, Finset.sum_add_distrib]
  commutes' b := by
    apply ext_coord β; intro i
    rw [coord_sum_basis_tmul, Algebra.algebraMap_eq_smul_one, hx.smul]
    simp_rw [hx.one]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      show (b ⊗ₜ[A] (1 : T) : B ⊗[A] T) = b • (1 : B ⊗[A] T) by
        rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one],
      coord_smul]
    simp_rw [coord_one]

theorem pointOfCoords_apply (x : H → ι → T) (hx : IsCoords β x) (h : H) :
    pointOfCoords β x hx h = ∑ i, β i ⊗ₜ[A] x h i := rfl

theorem coord_pointOfCoords (x : H → ι → T) (hx : IsCoords β x) (h : H) (i : ι) :
    coord β i (pointOfCoords β x hx h) = x h i := by
  rw [pointOfCoords_apply, coord_sum_basis_tmul]

theorem pointOfCoords_coord (φ : H →ₐ[B] B ⊗[A] T) :
    pointOfCoords β (fun h i => coord β i (φ h)) (isCoords_coord β φ) = φ := by
  apply AlgHom.ext; intro h
  rw [pointOfCoords_apply, sum_basis_tmul_coord]

end points

end E90WR
p2m_reactivate "P2MW.S_Algebra_exists_weilRestriction_points_equiv.E90WR"

noncomputable section

namespace E90WR

open Algebra.TensorProduct MvPolynomial

variable {A : Type u} [CommRing A] {B : Type u} [CommRing B] [Algebra A B]
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (β : Module.Basis ι A B)
variable (H : Type u) [CommRing H] [Algebra B H]

def rels : Set (MvPolynomial (H × ι) A) :=
  {r | (∃ (h h' : H) (i : ι), r = X (h + h', i) - X (h, i) - X (h', i)) ∨
       (∃ (b : B) (h : H) (i : ι), r = X (b • h, i) - ∑ j, C (β.repr (b * β j) i) * X (h, j)) ∨
       (∃ (h h' : H) (i : ι), r = X (h * h', i) - ∑ j, ∑ k, C (β.repr (β j * β k) i) * (X (h, j) * X (h', k))) ∨
       (∃ i : ι, r = X ((1 : H), i) - C (β.repr 1 i))}

def relIdeal : Ideal (MvPolynomial (H × ι) A) := Ideal.span (rels β H)

def WR : Type u := MvPolynomial (H × ι) A ⧸ relIdeal β H

noncomputable scoped instance : CommRing (WR β H) := inferInstanceAs (CommRing (MvPolynomial (H × ι) A ⧸ relIdeal β H))
noncomputable scoped instance : Algebra A (WR β H) := inferInstanceAs (Algebra A (MvPolynomial (H × ι) A ⧸ relIdeal β H))

variable {H}
variable {T : Type u} [CommRing T] [Algebra A T]

theorem forall_aeval_rels_eq_zero_iff (x : H → ι → T) :
    (∀ r ∈ rels β H, aeval (fun p : H × ι => x p.1 p.2) r = 0) ↔ IsCoords β x := by
  constructor
  · intro hr
    refine ⟨fun h h' i => ?_, fun b h i => ?_, fun h h' i => ?_, fun i => ?_⟩
    · have := hr _ (Or.inl ⟨h, h', i, rfl⟩)
      simp only [map_sub, aeval_X] at this
      rw [sub_sub, sub_eq_zero] at this
      exact this
    · have := hr _ (Or.inr (Or.inl ⟨b, h, i, rfl⟩))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at this
      rw [sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def _ _).symm
    · have := hr _ (Or.inr (Or.inr (Or.inl ⟨h, h', i, rfl⟩)))
      simp only [map_sub, aeval_X, map_sum, map_mul, aeval_C] at this
      rw [sub_eq_zero] at this
      rw [this]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => (Algebra.smul_def _ _).symm
    · have := hr _ (Or.inr (Or.inr (Or.inr ⟨i, rfl⟩)))
      simp only [map_sub, aeval_X, aeval_C] at this
      rw [sub_eq_zero] at this
      exact this
  · rintro hx r (⟨h, h', i, rfl⟩ | ⟨b, h, i, rfl⟩ | ⟨h, h', i, rfl⟩ | ⟨i, rfl⟩)
    · simp only [map_sub, aeval_X, hx.add]; ring
    · rw [map_sub, aeval_X, hx.smul]
      simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
    · rw [map_sub, aeval_X, hx.mul]
      simp only [map_sum, map_mul, aeval_C, aeval_X, Algebra.smul_def, sub_self]
    · simp only [map_sub, aeval_X, aeval_C, hx.one, sub_self]

theorem aeval_mem_relIdeal_eq_zero (x : H → ι → T) (hx : IsCoords β x) :
    ∀ r ∈ relIdeal β H, aeval (fun p : H × ι => x p.1 p.2) r = 0 := by
  intro r hr
  have hle : relIdeal β H ≤ RingHom.ker (aeval (R := A) (fun p : H × ι => x p.1 p.2)) := by
    rw [relIdeal, Ideal.span_le]
    intro r hr
    exact (forall_aeval_rels_eq_zero_iff β x).2 hx r hr
  exact hle hr

def gen (h : H) (i : ι) : WR β H := Ideal.Quotient.mk (relIdeal β H) (X (h, i))

theorem mkₐ_X (h : H) (i : ι) : Ideal.Quotient.mkₐ A (relIdeal β H) (X (h, i)) = gen β h i := rfl

theorem isCoords_apply_gen (f : WR β H →ₐ[A] T) : IsCoords β (fun h i => f (gen β h i)) := by
  rw [← forall_aeval_rels_eq_zero_iff]
  intro r hr
  have hfm : (f.comp (Ideal.Quotient.mkₐ A (relIdeal β H))) = aeval (fun p : H × ι => f (gen β p.1 p.2)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  have hr0 : (Ideal.Quotient.mkₐ A (relIdeal β H) : MvPolynomial (H × ι) A →ₐ[A] WR β H) r = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span hr)
  rw [← hfm]
  show f ((Ideal.Quotient.mkₐ A (relIdeal β H) : MvPolynomial (H × ι) A →ₐ[A] WR β H) r) = 0
  rw [hr0]
  exact map_zero f

noncomputable def toPoint (f : WR β H →ₐ[A] T) : H →ₐ[B] B ⊗[A] T :=
  pointOfCoords β (fun h i => f (gen β h i)) (isCoords_apply_gen β f)

noncomputable def ofPoint (φ : H →ₐ[B] B ⊗[A] T) : WR β H →ₐ[A] T :=
  Ideal.Quotient.liftₐ (relIdeal β H)
    (aeval (fun p : H × ι => (fun (h : H) (i : ι) => coord β i (φ h)) p.1 p.2))
    (aeval_mem_relIdeal_eq_zero β (fun h i => coord β i (φ h)) (isCoords_coord β φ))

theorem ofPoint_gen (φ : H →ₐ[B] B ⊗[A] T) (h : H) (i : ι) : ofPoint β φ (gen β h i) = coord β i (φ h) := by
  show Ideal.Quotient.lift (relIdeal β H) _ _ (Ideal.Quotient.mk (relIdeal β H) (X (h, i))) = _
  rw [Ideal.Quotient.lift_mk]
  exact aeval_X _ _

theorem toPoint_apply (f : WR β H →ₐ[A] T) (h : H) : toPoint β f h = ∑ i, β i ⊗ₜ[A] f (gen β h i) := rfl

theorem pointOfCoords_congr {x x' : H → ι → T} (hx : IsCoords β x) (hx' : IsCoords β x') (e : x = x') :
    pointOfCoords β x hx = pointOfCoords β x' hx' := by
  subst e; rfl

noncomputable def pointsEquiv : (WR β H →ₐ[A] T) ≃ (H →ₐ[B] B ⊗[A] T) where
  toFun := toPoint β
  invFun := ofPoint β
  left_inv f := by
    refine Ideal.Quotient.algHom_ext A ?_
    apply MvPolynomial.algHom_ext
    intro p
    show ofPoint β (toPoint β f) (Ideal.Quotient.mkₐ A (relIdeal β H) (X p)) =
      f (Ideal.Quotient.mkₐ A (relIdeal β H) (X p))
    rw [mkₐ_X, ofPoint_gen, toPoint, coord_pointOfCoords]
  right_inv φ := by
    change pointOfCoords β _ _ = φ
    rw [pointOfCoords_congr β (isCoords_apply_gen β (ofPoint β φ)) (isCoords_coord β φ)
      (funext fun h => funext fun i => ofPoint_gen β φ h i)]
    exact pointOfCoords_coord β φ

theorem pointsEquiv_apply (f : WR β H →ₐ[A] T) (h : H) : pointsEquiv β f h = ∑ i, β i ⊗ₜ[A] f (gen β h i) := rfl

theorem pointsEquiv_natural {T' : Type u} [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T') (f : WR β H →ₐ[A] T) :
    pointsEquiv β (u.comp f) = (map (AlgHom.id B B) u).comp (pointsEquiv β f) := by
  apply AlgHom.ext; intro h
  rw [AlgHom.comp_apply, pointsEquiv_apply, pointsEquiv_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_tmul]; rfl

end E90WR
p2m_reactivate "P2MW.S_Algebra_exists_weilRestriction_points_equiv.E90WR"

end
p2m_reactivate "P2MW.S_Algebra_exists_weilRestriction_points_equiv.E90WR"

open E90WR in
theorem solution
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (H : Type u) [CommRing H] [Algebra B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : Algebra A W),
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T], (W →ₐ[A] T) ≃ (H →ₐ[B] (B ⊗[A] T)),
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : W →ₐ[A] T), e T' (u.comp f) = (Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f) := by
  classical
  let ι : Type u := Module.Free.ChooseBasisIndex A B
  haveI : Fintype ι := Module.Free.ChooseBasisIndex.fintype A B
  let β : Module.Basis ι A B := Module.Free.chooseBasis A B
  exact ⟨WR β H, inferInstance, inferInstance, fun T _ _ => pointsEquiv β,
    fun T T' _ _ _ _ u f => pointsEquiv_natural β u f⟩

end S_Algebra_exists_weilRestriction_points_equiv
end P2MW
export P2MW.S_Algebra_exists_weilRestriction_points_equiv (solution)

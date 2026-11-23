-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
-- name    : GroundTheory_AutomorphicForms_UnitaryGroupScheme
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:53.027576+00:00
-- url     : https://prove2.me/theorems/304a5ae5-61f6-4957-942c-72c3cf1953f0
-- title:
--   Unitary Group Scheme
-- statement:
--   Definitions and structural lemmas for Unitary Group Scheme, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitaryGroupScheme.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj


set_option autoImplicit false
namespace GroundTheory.Automorphic
open Module Matrix TensorProduct
section Transport
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Type*} [CommRing A] [CommRing B]
omit [DecidableEq ι] in

theorem map_unitaryExpr (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) (H M : Matrix ι ι A) :
    ((M.map sA)ᵀ * H * M).map φ = ((M.map φ).map sB)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ sA = sB ∘ φ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_map, hc]
theorem map_mem_unitaryGroupMatrix (φ : A →+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, φ (sA x) = sB (φ x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map φ = HB) {g : GL ι A} (hg : g ∈ unitaryGroupMatrix sA HA) :
    Matrix.GeneralLinearGroup.map φ g ∈ unitaryGroupMatrix sB HB := by
  rw [mem_unitaryGroupMatrix] at *
  have := congrArg (fun M => M.map φ) hg
  rw [map_unitaryExpr φ hs, hH] at this
  exact this
noncomputable def unitaryGroupMatrixCongr (e : A ≃+* B) {sA : A →+* A} {sB : B →+* B}
    (hs : ∀ x, e (sA x) = sB (e x)) {HA : Matrix ι ι A} {HB : Matrix ι ι B}
    (hH : HA.map e = HB) : unitaryGroupMatrix sA HA ≃* unitaryGroupMatrix sB HB where
  toFun g := ⟨Matrix.GeneralLinearGroup.map (e : A →+* B) g,
    map_mem_unitaryGroupMatrix (e : A →+* B) hs hH g.2⟩
  invFun g := ⟨Matrix.GeneralLinearGroup.map (e.symm : B →+* A) g,
    map_mem_unitaryGroupMatrix (e.symm : B →+* A)
      (fun x => by
        apply e.injective
        simp only [RingHom.coe_coe, RingEquiv.apply_symm_apply]
        rw [hs, RingEquiv.apply_symm_apply])
      (by rw [← hH, Matrix.map_map]; ext i j; simp) g.2⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  right_inv g := by
    apply Subtype.ext; apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  map_mul' a b := by
    apply Subtype.ext
    simp
end Transport
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
section BaseChange
variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]
noncomputable def conjBase : R ⊗[F] E →+* R ⊗[F] E :=
  (Algebra.TensorProduct.map (AlgHom.id R R) (conj F E).toAlgHom).toRingHom
variable {F E R S T}
@[simp]
theorem conjBase_tmul (r : R) (e : E) : conjBase F E R (r ⊗ₜ e) = r ⊗ₜ conj F E e := rfl
variable (E) in

noncomputable def tensorMap (f : R →ₐ[F] S) : R ⊗[F] E →ₐ[F] S ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)
omit [Algebra.IsQuadraticExtension F E] in
@[simp]
theorem tensorMap_tmul (f : R →ₐ[F] S) (r : R) (e : E) :
    tensorMap E f (r ⊗ₜ e) = f r ⊗ₜ e := rfl
theorem tensorMap_conjBase (f : R →ₐ[F] S) (z : R ⊗[F] E) :
    tensorMap E f (conjBase F E R z) = conjBase F E S (tensorMap E f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [conjBase_tmul, tensorMap_tmul, tensorMap_tmul, conjBase_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
omit [Algebra.IsQuadraticExtension F E] in
theorem tensorMap_includeRight (f : R →ₐ[F] S) (e : E) :
    tensorMap E f (Algebra.TensorProduct.includeRight e) =
      (Algebra.TensorProduct.includeRight e : S ⊗[F] E) := by
  simp [Algebra.TensorProduct.includeRight_apply]
omit [Algebra.IsQuadraticExtension F E] in
theorem tensorMap_id : tensorMap E (AlgHom.id F R) = AlgHom.id F (R ⊗[F] E) :=
  Algebra.TensorProduct.map_id
omit [Algebra.IsQuadraticExtension F E] in
theorem tensorMap_comp (f : R →ₐ[F] S) (g : S →ₐ[F] T) :
    tensorMap E (g.comp f) = (tensorMap E g).comp (tensorMap E f) :=
  Algebra.TensorProduct.ext' fun _ _ => rfl
end BaseChange
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
section Points
variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]
noncomputable def unitaryPoints : Subgroup (GL ι (R ⊗[F] E)) :=
  unitaryGroupMatrix (conjBase F E R)
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E))
variable {F E H R S T}
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_tensorMap (f : R →ₐ[F] S) :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E)).map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E) =
      H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] S ⊗[F] E) := by
  rw [Matrix.map_map]
  congr 1
  funext e
  exact tensorMap_includeRight f e
variable (F E H) in

noncomputable def unitaryMap (f : R →ₐ[F] S) : unitaryPoints F E H R →* unitaryPoints F E H S :=
  ((Matrix.GeneralLinearGroup.map
      ((tensorMap E f : R ⊗[F] E →ₐ[F] S ⊗[F] E) : R ⊗[F] E →+* S ⊗[F] E)).comp
    (unitaryPoints F E H R).subtype).codRestrict _ fun g =>
    map_mem_unitaryGroupMatrix _ (tensorMap_conjBase f) (map_includeRight_tensorMap f) g.2
theorem unitaryMap_apply (f : R →ₐ[F] S) (g : unitaryPoints F E H R) :
    ((unitaryMap F E H f g : GL ι (S ⊗[F] E)) : Matrix ι ι (S ⊗[F] E)) =
      ((g : GL ι (R ⊗[F] E)) : Matrix ι ι (R ⊗[F] E)).map (tensorMap E f) := rfl
theorem unitaryMap_id : unitaryMap F E H (AlgHom.id F R) = MonoidHom.id _ := by
  ext g : 1
  apply Subtype.ext; apply Units.ext
  rw [unitaryMap_apply, tensorMap_id]
  rfl
theorem unitaryMap_comp (f : R →ₐ[F] S) (g : S →ₐ[F] T) :
    unitaryMap F E H (g.comp f) = (unitaryMap F E H g).comp (unitaryMap F E H f) := by
  ext x : 1
  apply Subtype.ext; apply Units.ext
  rw [MonoidHom.comp_apply, unitaryMap_apply, unitaryMap_apply, unitaryMap_apply, tensorMap_comp,
    Matrix.map_map]
  rfl
end Points
section Functor
open CategoryTheory
universe u
variable (F E : Type u) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
noncomputable def unitaryFunctor (H : Matrix ι ι E) : CommAlgCat.{u} F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (unitaryPoints F E H R)
  map f := GrpCat.ofHom (unitaryMap F E H f.hom)
  map_id R := by
    rw [CommAlgCat.hom_id, unitaryMap_id]
    rfl
  map_comp f g := by
    rw [CommAlgCat.hom_comp, unitaryMap_comp]
    rfl
end Functor
section Rational
variable {F E H}
theorem lid_conjBase (z : F ⊗[F] E) :
    Algebra.TensorProduct.lid F E (conjBase F E F z) = conj F E (Algebra.TensorProduct.lid F E z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp only [conjBase_tmul, Algebra.TensorProduct.lid_tmul, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]
omit [Algebra.IsQuadraticExtension F E] [Fintype ι] [DecidableEq ι] in
theorem map_includeRight_lid :
    (H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] F ⊗[F] E)).map
      ((Algebra.TensorProduct.lid F E : F ⊗[F] E ≃ₐ[F] E) : F ⊗[F] E ≃+* E) = H := by
  rw [Matrix.map_map]
  conv_rhs => rw [← Matrix.map_id H]
  congr 1
  funext e
  simp [Algebra.TensorProduct.includeRight_apply]
variable (F E H) in

noncomputable def unitaryPointsRationalEquiv :
    unitaryPoints F E H F ≃* unitaryGroupMatrix (conjHom F E) H :=
  unitaryGroupMatrixCongr ((Algebra.TensorProduct.lid F E).toRingEquiv)
    (fun z => lid_conjBase z) map_includeRight_lid
variable {V : Type*} [AddCommGroup V] [Module E V]
variable (F E) in

noncomputable def unitaryPointsRationalEquivHermitian (h : HermitianForm F E V)
    (v : Basis ι E V) : unitaryPoints F E (gram h.toSesq v) F ≃* h.unitaryGroup :=
  (unitaryPointsRationalEquiv F E (gram h.toSesq v)).trans (unitaryGroupEquivMatrix h v).symm
end Rational
end GroundTheory.Automorphic



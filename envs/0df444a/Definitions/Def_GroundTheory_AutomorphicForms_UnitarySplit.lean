-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_UnitarySplit
-- name    : GroundTheory_AutomorphicForms_UnitarySplit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T08:04:05.504609+00:00
-- url     : https://prove2.me/theorems/b88d00c8-307a-45a7-a561-416367005ec6
-- title:
--   Unitary Split
-- statement:
--   Definitions and structural lemmas for Unitary Split, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/UnitarySplit.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme
import Theorems.Thm_GroundTheory_Automorphic_conj_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_unitaryGroupMatrix_iff
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
variable (F : Type*) [Field F]
instance isQuadraticExtension_prod : Algebra.IsQuadraticExtension F (F × F) where
  finrank_eq_two' := by rw [Module.finrank_prod, Module.finrank_self]
variable {F}
theorem trace_prod (x : F × F) : Algebra.trace F (F × F) x = x.1 + x.2 := by
  rw [Algebra.trace_eq_matrix_trace (Basis.finTwoProd F), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, Basis.finTwoProd_zero,
    Basis.finTwoProd_one, Basis.coe_finTwoProd_repr, Basis.coe_finTwoProd_repr]
  simp
theorem conj_prod (x : F × F) : conj F (F × F) x = (x.2, x.1) := by
  rw [conj_apply, trace_prod]
  ext <;> simp
section Split
variable (F) (R : Type*) [CommRing R] [Algebra F R]
noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))
variable {F R}
@[simp]
theorem splitEquiv_tmul (r : R) (x : F × F) : splitEquiv F R (r ⊗ₜ x) = (x.1 • r, x.2 • r) := rfl
variable (F R) in

noncomputable def splitFst : R ⊗[F] (F × F) →+* R :=
  (RingHom.fst R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)
variable (F R) in

noncomputable def splitSnd : R ⊗[F] (F × F) →+* R :=
  (RingHom.snd R R).comp ((splitEquiv F R : R ⊗[F] (F × F) ≃ₐ[R] R × R) : R ⊗[F] (F × F) →+* R × R)
theorem splitFst_apply (z : R ⊗[F] (F × F)) : splitFst F R z = (splitEquiv F R z).1 := rfl
theorem splitSnd_apply (z : R ⊗[F] (F × F)) : splitSnd F R z = (splitEquiv F R z).2 := rfl
theorem splitEquiv_conjBase (z : R ⊗[F] (F × F)) :
    splitEquiv F R (conjBase F (F × F) R z) = (splitEquiv F R z).swap := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [conj_prod]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, Prod.swap_add]
theorem splitFst_conjBase (z : R ⊗[F] (F × F)) :
    splitFst F R (conjBase F (F × F) R z) = splitSnd F R z := by
  rw [splitFst_apply, splitEquiv_conjBase]; rfl
theorem splitSnd_conjBase (z : R ⊗[F] (F × F)) :
    splitSnd F R (conjBase F (F × F) R z) = splitFst F R z := by
  rw [splitSnd_apply, splitEquiv_conjBase]; rfl
theorem splitFst_includeRight (x : F × F) :
    splitFst F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.1 := by
  simp [splitFst_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]
theorem splitSnd_includeRight (x : F × F) :
    splitSnd F R (Algebra.TensorProduct.includeRight x) = algebraMap F R x.2 := by
  simp [splitSnd_apply, Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one]
theorem splitFst_tensorMap {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (z : R ⊗[F] (F × F)) : splitFst F S (tensorMap (F × F) f z) = f (splitFst F R z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => simp [splitFst_apply]
  | add x y hx hy => simp only [map_add, hx, hy]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
theorem split_matrix_ext {X Y : Matrix ι ι (R ⊗[F] (F × F))}
    (h1 : X.map (splitFst F R) = Y.map (splitFst F R)) (h2 : X.map (splitSnd F R) = Y.map (splitSnd F R)) :
    X = Y := by
  ext i j
  apply (splitEquiv F R).injective
  exact Prod.ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)
omit [Fintype ι] [DecidableEq ι] in
theorem map_unitaryExpr_of_comp {A B : Type*} [CommRing A] [CommRing B] [Fintype ι]
    (φ ψ : A →+* B) (s : A →+* A) (hs : ∀ x, φ (s x) = ψ x) (H M : Matrix ι ι A) :
    ((M.map s)ᵀ * H * M).map φ = (M.map ψ)ᵀ * H.map φ * M.map φ := by
  have hc : (φ : A → B) ∘ s = ψ := funext hs
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hc]
variable (H : Matrix ι ι (F × F))
variable (R) in

noncomputable def splitHom : unitaryPoints F (F × F) H R →* GL ι R :=
  (Matrix.GeneralLinearGroup.map (splitFst F R)).comp (unitaryPoints F (F × F) H R).subtype
theorem splitHom_apply (g : unitaryPoints F (F × F) H R) :
    ((splitHom R H g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl
omit [Fintype ι] [DecidableEq ι] in
theorem map_splitFst_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitFst F R) =
      H.map fun x => algebraMap F R x.1 := by
  ext i j; exact splitFst_includeRight _
omit [Fintype ι] [DecidableEq ι] in
theorem map_splitSnd_H :
    (H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F))).map (splitSnd F R) =
      H.map fun x => algebraMap F R x.2 := by
  ext i j; exact splitSnd_includeRight _
omit [Fintype ι] [DecidableEq ι] in
theorem hermitian_split (hH : IsHermitianFor (conjHom F (F × F)) H) :
    (H.map fun x => algebraMap F R x.2) = (H.map fun x => algebraMap F R x.1)ᵀ := by
  ext i j
  have := congrFun (congrFun hH i) j
  simp only [transpose_apply, map_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    AlgEquiv.coe_toAlgHom, conj_prod] at this
  simp [← this]
theorem splitHom_bijective (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det) :
    Function.Bijective (splitHom R H) := by
  set HR := H.map (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)) with hHR
  set H₁ := H.map fun x => algebraMap F R x.1 with hH₁
  have h21 := hermitian_split (R := R) H hH
  have hU : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).2 hdet
  have hU₁ : IsUnit H₁ := hU.map (RingHom.mapMatrix ((algebraMap F R).comp (RingHom.fst F F)))
  have hUR : IsUnit HR := hU.map (RingHom.mapMatrix
    (Algebra.TensorProduct.includeRight : F × F →ₐ[F] R ⊗[F] (F × F)).toRingHom)
  have hdetR : IsUnit HR.det := (Matrix.isUnit_iff_isUnit_det HR).1 hUR
  have hR1 : HR.map (splitFst F R) = H₁ := map_splitFst_H H
  have hR2 : HR.map (splitSnd F R) = H₁ᵀ := (map_splitSnd_H H).trans h21

  have eq₁ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitFst F R) =
        (X.map (splitSnd F R))ᵀ * H₁ * X.map (splitFst F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitFst_conjBase, hR1]
  have eq₂ : ∀ X : Matrix ι ι (R ⊗[F] (F × F)),
      ((X.map (conjBase F (F × F) R))ᵀ * HR * X).map (splitSnd F R) =
        (X.map (splitFst F R))ᵀ * H₁ᵀ * X.map (splitSnd F R) := fun X => by
    rw [map_unitaryExpr_of_comp _ _ _ splitSnd_conjBase, hR2]
  constructor
  · intro g g' hgg'
    have h1 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := by
      rw [← splitHom_apply, ← splitHom_apply, hgg']
    have hg := congrArg (fun M => M.map (splitFst F R))
      (show (((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g.2)
    have hg' := congrArg (fun M => M.map (splitFst F R))
      (show (((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map
        (conjBase F (F × F) R))ᵀ * HR * ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F)))
          = HR from g'.2)
    simp only [eq₁, hR1] at hg hg'
    have hunit : IsUnit (H₁ * ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R)) := by
      refine hU₁.mul ?_
      rw [← splitHom_apply]
      exact Units.isUnit _
    have h2 : ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) =
        ((g' : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitSnd F R) := by
      apply Matrix.transpose_injective
      apply (hunit.mul_left_inj).1
      rw [← Matrix.mul_assoc, hg, h1, ← Matrix.mul_assoc, hg']
    exact Subtype.ext (Units.ext (split_matrix_ext h1 h2))
  · intro m
    set m₁ : Matrix ι ι R := (↑m : Matrix ι ι R)
    set g₂ : Matrix ι ι R := (H₁ * (↑m⁻¹ : Matrix ι ι R) * H₁⁻¹)ᵀ
    let X : Matrix ι ι (R ⊗[F] (F × F)) := fun i j => (splitEquiv F R).symm (m₁ i j, g₂ i j)
    have hX1 : X.map (splitFst F R) = m₁ := by
      ext i j
      show splitFst F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = m₁ i j
      rw [splitFst_apply, AlgEquiv.apply_symm_apply]
    have hX2 : X.map (splitSnd F R) = g₂ := by
      ext i j
      show splitSnd F R ((splitEquiv F R).symm (m₁ i j, g₂ i j)) = g₂ i j
      rw [splitSnd_apply, AlgEquiv.apply_symm_apply]
    have hdet₁ : IsUnit H₁.det := (Matrix.isUnit_iff_isUnit_det H₁).1 hU₁
    have key₁ : g₂ᵀ * H₁ * m₁ = H₁ := by
      simp only [g₂, transpose_transpose]
      rw [Matrix.mul_assoc (H₁ * _), Matrix.nonsing_inv_mul _ hdet₁, Matrix.mul_one,
        Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    have hXeq : (X.map (conjBase F (F × F) R))ᵀ * HR * X = HR := by
      apply split_matrix_ext
      · rw [eq₁, hR1, hX1, hX2, key₁]
      · rw [eq₂, hR2, hX1, hX2]
        conv_rhs => rw [← key₁]
        rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    obtain ⟨u, hu, hux⟩ := (exists_mem_unitaryGroupMatrix_iff _ hdetR X).2 hXeq
    refine ⟨⟨u, hu⟩, Units.ext ?_⟩
    rw [splitHom_apply]
    simp only [hux, hX1, m₁]
variable (R) in

noncomputable def unitaryPointsSplitEquiv (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) : unitaryPoints F (F × F) H R ≃* GL ι R :=
  MulEquiv.ofBijective (splitHom R H) (splitHom_bijective H hH hdet)
theorem unitaryPointsSplitEquiv_apply (hH : IsHermitianFor (conjHom F (F × F)) H)
    (hdet : IsUnit H.det) (g : unitaryPoints F (F × F) H R) :
    ((unitaryPointsSplitEquiv R H hH hdet g : GL ι R) : Matrix ι ι R) =
      ((g : GL ι (R ⊗[F] (F × F))) : Matrix ι ι (R ⊗[F] (F × F))).map (splitFst F R) := rfl
theorem unitaryPointsSplitEquiv_natural {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det)
    (g : unitaryPoints F (F × F) H R) :
    unitaryPointsSplitEquiv S H hH hdet (unitaryMap F (F × F) H f g) =
      Matrix.GeneralLinearGroup.map (f : R →+* S) (unitaryPointsSplitEquiv R H hH hdet g) := by
  apply Units.ext
  rw [unitaryPointsSplitEquiv_apply, unitaryMap_apply]
  ext i j
  simp [unitaryPointsSplitEquiv_apply, Matrix.GeneralLinearGroup.map, splitFst_tensorMap]
end Split
section SplitFunctor
open CategoryTheory
universe u
variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]
noncomputable def generalLinearFunctor : CommAlgCat.{u} F ⥤ GrpCat.{u} where
  obj R := GrpCat.of (GL ι R)
  map f := GrpCat.ofHom (Matrix.GeneralLinearGroup.map (f.hom : _ →+* _))
  map_id R := by
    rw [CommAlgCat.hom_id]
    exact congrArg GrpCat.ofHom Matrix.GeneralLinearGroup.map_id
  map_comp f g := by
    rw [CommAlgCat.hom_comp]
    exact congrArg GrpCat.ofHom (Matrix.GeneralLinearGroup.map_comp _ _)
variable {F ι}
noncomputable def unitaryFunctorSplitIso (H : Matrix ι ι (F × F))
    (hH : IsHermitianFor (conjHom F (F × F)) H) (hdet : IsUnit H.det) :
    unitaryFunctor F (F × F) H ≅ generalLinearFunctor F ι :=
  NatIso.ofComponents (fun R => (unitaryPointsSplitEquiv R H hH hdet).toGrpIso) fun {R S} f => by
    ext g : 2
    exact unitaryPointsSplitEquiv_natural H f.hom hH hdet g
end SplitFunctor
end GroundTheory.Automorphic



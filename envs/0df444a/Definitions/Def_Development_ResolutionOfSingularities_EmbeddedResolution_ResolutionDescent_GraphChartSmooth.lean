-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChartSmooth
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChartSmooth
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T13:35:00.66183+00:00
-- url     : https://prove2.me/theorems/978b13fb-472a-48d5-bd9a-f1f970d68e3e
-- title:
--   Graph Chart Smooth
-- statement:
--   Definitions and structural lemmas for Graph Chart Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/ResolutionDescent/GraphChartSmooth.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupProperties
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_ClopenRestriction
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceRelations
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_AffineSpaceCoordinates
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebra
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphChart
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraSpecSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_GraphAlgebraStandardSmooth
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionDescent_AffineSpaceGlobalSections
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInl_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_coordVectorInr_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphJacobianMinorMatrix_apply
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_map
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_graphPreSubmersivePresentation_relation
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_homOfSumCoords_appTop_coord_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_X
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mvPolynomialEquivGlobalSections_symm_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projLeft_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_appTop_coord
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_projRight_comp_affineSpaceIndexedByToSpec
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_pullbackCoord_def
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_range_specMap_algebraMap_graphAlgebraAway
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_inr
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inl
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_sumUliftEquivUliftSum_symm_inr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInl_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.coordVectorInr_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_map
attribute [local simp] FunctorialResolution.EmbeddedResolution.graphPreSubmersivePresentation_relation
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.homOfSumCoords_appTop_coord_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_X
attribute [local simp] FunctorialResolution.EmbeddedResolution.mvPolynomialEquivGlobalSections_symm_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_appTop_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projLeft_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_appTop_coord
attribute [local simp] FunctorialResolution.EmbeddedResolution.projRight_comp_affineSpaceIndexedByToSpec
attribute [local simp] FunctorialResolution.EmbeddedResolution.pullbackCoord_def
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_inr
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inl
attribute [local simp] FunctorialResolution.EmbeddedResolution.sumUliftEquivUliftSum_symm_inr


set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
def polynomialOfSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (j : Fin q) : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  (mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n))).symm (F j)
def sumVariableMap (M n q : ℕ) (s : Fin q → Fin n) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → ULift.{u, 0} (Fin M ⊕ Fin n) :=
  fun i =>
    ULift.up (Sum.elim (fun a : Fin M => Sum.inl a) (fun j : Fin q => Sum.inr (s j)) i.down)
def jacobianMatrixOfSections (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Matrix (Fin q) (Fin q) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) :=
  Matrix.of fun i j =>
    (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (polynomialOfSection k M n q F j)
def graphCoordinates (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤))) :
    ULift.{u, 0} (Fin M ⊕ Fin q) → MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k :=
  fun i =>
    Sum.elim
      (fun a : Fin M => MvPolynomial.X (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
      (fun j : Fin q => polynomialOfSection k M n q F j) i.down
theorem det_graphJacobianMinorMatrix_eq_det_jacobianMatrix (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
      (jacobianMatrixOfSections k M n q F s).det := by
  have hup : ∀ x y : Fin M ⊕ Fin n,
      (ULift.up x : ULift.{u, 0} (Fin M ⊕ Fin n)) = ULift.up y → x = y :=
    fun _ _ h => congrArg ULift.down h
  have hXne : ∀ i j : ULift.{u, 0} (Fin M ⊕ Fin n), i ≠ j →
      (MvPolynomial.pderiv i)
          (MvPolynomial.X j : MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k) = 0 := by
    intro i j h
    simp [MvPolynomial.pderiv_X, Ne.symm h]
  have key :
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).submatrix
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
          ⇑(Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q)) =
        Matrix.fromBlocks
          (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))
          (Matrix.of fun (a : Fin M) (j : Fin q) =>
            (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (polynomialOfSection k M n q F j))
          0 (jacobianMatrixOfSections k M n q F s) := by
    apply Matrix.ext
    intro x y
    simp only [Matrix.submatrix_apply, graphJacobianMinorMatrix_apply]
    cases x with
    | inl a =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inl a) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) =
            (1 : Matrix (Fin M) (Fin M) (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)) a b
        by_cases h : a = b
        · subst h
          rw [MvPolynomial.pderiv_X_self, Matrix.one_apply_eq]
        · rw [Matrix.one_apply_ne h]
          exact hXne _ _ fun hc => h (Sum.inl_injective (hup _ _ hc))
      | inr j => rfl
    | inr i =>
      cases y with
      | inl b =>
        show (MvPolynomial.pderiv (ULift.up (Sum.inr (s i)) : ULift.{u, 0} (Fin M ⊕ Fin n)))
              (MvPolynomial.X (ULift.up (Sum.inl b) : ULift.{u, 0} (Fin M ⊕ Fin n))) = 0
        refine hXne _ _ ?_
        intro hc
        have hc' := hup _ _ hc
        simp at hc'
      | inr j => rfl
  have hdet := Matrix.det_submatrix_equiv_self
      (Equiv.ulift.symm : (Fin M ⊕ Fin q) ≃ ULift.{u, 0} (Fin M ⊕ Fin q))
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  rw [key, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul] at hdet
  exact hdet.symm
theorem graphJacobianMinorDet_graphCoordinates (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s) =
      graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det := by
  have h := det_graphJacobianMinorMatrix_eq_det_jacobianMatrix k M n q F s
  show graphAlgebraEquiv (graphCoordinates k M n q F)
      (graphJacobianMinorMatrix (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)).det =
    graphAlgebraEquiv (graphCoordinates k M n q F) (jacobianMatrixOfSections k M n q F s).det
  rw [h]
def jacobianDetSection (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)) :=
  mvPolynomialEquivGlobalSections k (ULift.{u, 0} (Fin M ⊕ Fin n)) (jacobianMatrixOfSections k M n q F s).det
def specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (GraphAlgebra (graphCoordinates k M n q F))
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))
theorem isOpenImmersion_specGraphAwayToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) := by
  unfold specGraphAwayToSpecGraphAlgebra
  infer_instance
instance instIsOpenImmersionGraphAwaySpecHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (specGraphAwayToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_specGraphAwayToSpecGraphAlgebra k M n q F s
def basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme ⟶
      Spec (CommRingCat.of (GraphAlgebra (graphCoordinates k M n q F))) :=
  ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
      (jacobianDetSection k M n q F s)).ι ≫
    (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
      Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))
def specIsoOfRingEquiv {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Spec (CommRingCat.of B) ≅ Spec (CommRingCat.of A) :=
  Scheme.Spec.mapIso e.toCommRingCatIso.op
theorem isIso_spec_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) : IsIso (Spec.map (CommRingCat.ofHom e.toRingHom)) := by
  refine ⟨(specIsoOfRingEquiv e).inv, ?_, ?_⟩
  · exact (specIsoOfRingEquiv e).hom_inv_id
  · exact (specIsoOfRingEquiv e).inv_hom_id
theorem isOpenImmersion_basicOpenToSpecGraphAlgebra (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) := by
  have : IsIso (Spec.map (CommRingCat.ofHom
      ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))) :=
    isIso_spec_map_ringEquiv ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
  unfold basicOpenToSpecGraphAlgebra
  infer_instance
instance instIsOpenImmersionGraphChartHom (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    IsOpenImmersion (basicOpenToSpecGraphAlgebra k M n q F s) :=
  isOpenImmersion_basicOpenToSpecGraphAlgebra k M n q F s
theorem base_comp_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : ↥X) :
    ⇑(f ≫ g).base x = ⇑g.base (⇑f.base x) := rfl
theorem range_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Set.range ⇑(f ≫ g).base = ⇑g.base '' Set.range ⇑f.base := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⇑f.base x, ⟨x, rfl⟩, (base_comp_apply f g x).symm⟩
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, base_comp_apply f g x⟩
theorem image_base_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (S : Set ↥X) :
    ⇑(f ≫ g).base '' S = ⇑g.base '' (⇑f.base '' S) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⇑f.base x, ⟨x, hx, rfl⟩, (base_comp_apply f g x).symm⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, base_comp_apply f g x⟩
theorem image_hom_preimage_eq {X Y : Scheme.{u}} (e : X ≅ Y) (U : Y.Opens) :
    ⇑e.hom.base '' ((e.hom ⁻¹ᵁ U : X.Opens) : Set ↥X) = (U : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    refine ⟨⇑e.inv.base y, ?_, Scheme.inv_hom_apply e y⟩
    show ⇑e.hom.base (⇑e.inv.base y) ∈ (U : Set ↥Y)
    rw [Scheme.inv_hom_apply e y]
    exact hy
theorem image_hom_eq_preimage_inv {X Y : Scheme.{u}} (e : X ≅ Y) (U : X.Opens) :
    ⇑e.hom.base '' ((U : X.Opens) : Set ↥X) = ((e.inv ⁻¹ᵁ U : Y.Opens) : Set ↥Y) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    show ⇑e.inv.base (⇑e.hom.base x) ∈ ((U : X.Opens) : Set ↥X)
    rw [Scheme.hom_inv_apply e x]
    exact hx
  · intro hy
    exact ⟨⇑e.inv.base y, hy, Scheme.inv_hom_apply e y⟩
theorem image_basicOpen_spec_map_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (a : A) :
    ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  have h2 : (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))
      = (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)) := by
    have h2' : (Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
        = (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)) :=
      basicOpen_eq_of_affine _
    exact h2'.symm
  have h3 : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        ((Spec (CommRingCat.of B)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a)))
      = (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))) :=
    Scheme.preimage_basicOpen (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) _
  have h4 : (Scheme.Hom.appTop (Spec.map (CommRingCat.ofHom e.symm.toRingHom)))
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (e a))
      = (Scheme.ΓSpecIso (CommRingCat.of A)).inv ((e.symm.toRingHom) (e a)) :=
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom e.symm.toRingHom))) (e a)).symm
  have h5 : (e.symm.toRingHom) (e a) = a := by simp
  have h6 : (Spec (CommRingCat.of A)).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) :=
    basicOpen_eq_of_affine _
  have hop : (Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
        (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B)))
      = (PrimeSpectrum.basicOpen a : Opens (PrimeSpectrum A)) := by
    rw [h2, h3, h4, h5]
    exact h6
  have h1 : ⇑(Spec.map (CommRingCat.ofHom e.toRingHom)).base ''
        (PrimeSpectrum.basicOpen (e a) : Set (PrimeSpectrum B))
      = ((Spec.map (CommRingCat.ofHom e.symm.toRingHom) ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (e a) : Opens (PrimeSpectrum B))) :
          Set ↥(Spec (CommRingCat.of A))) :=
    image_hom_eq_preimage_inv (specIsoOfRingEquiv e) (PrimeSpectrum.basicOpen (e a))
  exact h1.trans (congrArg (fun U : (Spec (CommRingCat.of A)).Opens =>
    (U : Set ↥(Spec (CommRingCat.of A)))) hop)
theorem range_specGraphAwayToSpecGraphAlgebra_eq (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base := by
  have hL : Set.range ⇑(specGraphAwayToSpecGraphAlgebra k M n q F s).base =
      (PrimeSpectrum.basicOpen
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
        Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) :=
    range_specMap_algebraMap_graphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)
  have hR1 : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = ⇑((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
            Spec.map (CommRingCat.ofHom
              ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
          Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s)).ι).base :=
    range_base_comp
      (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι)
      ((affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ≫
        Spec.map (CommRingCat.ofHom
          ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom)))
  have hD : Set.range ⇑(((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).ι).base
      = (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n)))) :=
    Scheme.Opens.range_ι _
  have hDopen : (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)
      = (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom ⁻¹ᵁ
          (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det) :=
    mvPolynomialEquivGlobalSections_basicOpen_primeSpectrum k (ULift.{u, 0} (Fin M ⊕ Fin n))
      (jacobianMatrixOfSections k M n q F s).det
  have himg1 : ⇑(affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n))).hom.base ''
        (((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
            (jacobianDetSection k M n q F s) :
          (affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).Opens) :
          Set ↥(affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))))
      = (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k))) := by
    rw [hDopen]
    exact image_hom_preimage_eq (affineSpaceIsoSpecMvPolynomial k (ULift.{u, 0} (Fin M ⊕ Fin n)))
      (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det)
  have hdet : (jacobianMatrixOfSections k M n q F s).det
      = ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
          (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) := by
    rw [graphJacobianMinorDet_graphCoordinates]
    simp
  have himg2 : ⇑(Spec.map (CommRingCat.ofHom
        ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv.toRingHom))).base ''
        (PrimeSpectrum.basicOpen (jacobianMatrixOfSections k M n q F s).det :
          Set (PrimeSpectrum (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin n)) k)))
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hdet]
    exact image_basicOpen_spec_map_ringEquiv ((graphAlgebraEquiv (graphCoordinates k M n q F)).symm.toRingEquiv)
      (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))
  have hrange : Set.range ⇑(basicOpenToSpecGraphAlgebra k M n q F s).base
      = (PrimeSpectrum.basicOpen
            (graphJacobianMinorDet (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s)) :
          Set (PrimeSpectrum (GraphAlgebra (graphCoordinates k M n q F)))) := by
    rw [hR1, hD, image_base_comp, himg1]
    exact himg2
  exact hL.trans hrange.symm
def specGraphAwayIsoBasicOpen (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ≅
      ((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).basicOpen
        (jacobianDetSection k M n q F s)).toScheme :=
  IsOpenImmersion.isoOfRangeEq (specGraphAwayToSpecGraphAlgebra k M n q F s) (basicOpenToSpecGraphAlgebra k M n q F s)
    (range_specGraphAwayToSpecGraphAlgebra_eq k M n q F s)
def specGraphAwayToAffineSpace (k : Type u) [Field k] (M n q : ℕ)
    (F : Fin q →
      ↑((affineSpaceIndexedBy k (ULift.{u, 0} (Fin M ⊕ Fin n))).presheaf.obj (Opposite.op ⊤)))
    (s : Fin q → Fin n) :
    Spec (CommRingCat.of (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))) ⟶
      Spec (CommRingCat.of (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (ULift.{u, 0} (Fin M ⊕ Fin q)) k)
      (GraphAlgebraAway (graphCoordinates k M n q F) (sumVariableMap.{u} M n q s))))
end FunctorialResolution.EmbeddedResolution
end



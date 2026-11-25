-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductFirstCohomologyComparison
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T00:11:25.7612+00:00
-- url     : https://prove2.me/theorems/ee395295-e0dc-4e07-af0d-a161f1498fbb
-- title:
--   Product First Cohomology Comparison
-- statement:
--   Definitions and structural lemmas for Product First Cohomology Comparison, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductFirstCohomologyComparison.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUniqueIsPullForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbelianSchemeGerms
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_USt
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Glue_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van1_mono
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Van2_mono
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_smul
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_smul
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_TopForm_formMap_dForm
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.TopForm.formMap_dForm
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.CompanionTheory.Axis
open CategoryTheory.Limits
section Fibre
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)
instance affPt_isOpenImmersion {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens) : IsOpenImmersion (affPt s U) :=
  IsAffineOpen.isOpenImmersion_fromSpec U.2
def tensPt (U : X.affineOpens) (V : Y.affineOpens) :
    Sp (Sec f U.1 ⊗[R] Sec g V.1) ⟶ pullback f g :=
  (pullbackSpecIso R (Sec f U.1) (Sec g V.1)).inv ≫
    pullback.map _ _ f g (affPt f U) (affPt g V) (𝟙 _)
      (by rw [affPt_w, Category.comp_id]) (by rw [affPt_w, Category.comp_id])
instance tensPt_isOpenImmersion (U : X.affineOpens) (V : Y.affineOpens) : IsOpenImmersion (tensPt f g U V) := by
  unfold tensPt; infer_instance
theorem range_tensPt (U : X.affineOpens) (V : Y.affineOpens) :
    Set.range (tensPt f g U V) = (pullback.fst f g) ⁻¹' (U.1 : Set X) ∩ (pullback.snd f g) ⁻¹' (V.1 : Set Y) := by
  have e := Scheme.Pullback.range_map _ _ f g (affPt f U) (affPt g V) (𝟙 _)
      (by rw [affPt_w, Category.comp_id]) (by rw [affPt_w, Category.comp_id])
  have hU : Set.range (affPt f U) = (U.1 : Set X) := U.2.range_fromSpec
  have hV : Set.range (affPt g V) = (V.1 : Set Y) := V.2.range_fromSpec
  rw [hU, hV] at e
  rw [← e, tensPt, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, (pullbackSpecIso R _ _).inv.surjective.range_eq, Set.image_univ]
end Fibre
section Fibre2
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Sp R) (g : Y ⟶ Sp R)
theorem isAffineOpen_inf_preimage (U : X.affineOpens) (V : Y.affineOpens) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U.1 ⊓ pullback.snd f g ⁻¹ᵁ V.1) := by
  have h := isAffineOpen_opensRange (tensPt f g U V)
  convert h using 1
  refine TopologicalSpace.Opens.ext ?_
  exact (range_tensPt f g U V).symm
end Fibre2
section Cochain
variable {R : Type} [CommRing R] {P : Type} [SemilatticeInf P]
def Bx (P : Type) : Type := P × P
instance : SemilatticeInf (Bx P) := inferInstanceAs (SemilatticeInf (P × P))
theorem Bx.le_fst {x y : Bx P} (h : x ≤ y) : x.1 ≤ y.1 := (Prod.le_def.1 h).1
theorem Bx.le_snd {x y : Bx P} (h : x ≤ y) : x.2 ≤ y.2 := (Prod.le_def.1 h).2
def boxG (P : Type) [SemilatticeInf P] : (Bx P)ᵒᵖ ⥤ Pᵒᵖ × Pᵒᵖ where
  obj T := (op T.unop.1, op T.unop.2)
  map φ := ((homOfLE (Bx.le_fst (leOfHom φ.unop))).op, (homOfLE (Bx.le_snd (leOfHom φ.unop))).op)
  map_id _ := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  map_comp _ _ := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
def boxGi (P : Type) [SemilatticeInf P] : Pᵒᵖ × Pᵒᵖ ⥤ (Bx P)ᵒᵖ where
  obj T := op (T.1.unop, T.2.unop)
  map φ := (homOfLE (Prod.le_def.2 ⟨leOfHom φ.1.unop, leOfHom φ.2.unop⟩)).op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
end Cochain
section Sys
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]
def boxSys (S : Sys A.left P) : Sys (A ⊗ A).left (Bx P) where
  u q := ⟨(fst A A).left ⁻¹ᵁ (S.u q.1).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u q.2).1,
    isAffineOpen_inf_preimage A.hom A.hom (S.u q.1) (S.u q.2)⟩
  map_inf x y := by
    have h1 : (S.u (x ⊓ y).1).1 = (S.u x.1).1 ⊓ (S.u y.1).1 := S.map_inf x.1 y.1
    have h2 : (S.u (x ⊓ y).2).1 = (S.u x.2).1 ⊓ (S.u y.2).1 := S.map_inf x.2 y.2
    change (fst A A).left ⁻¹ᵁ (S.u (x ⊓ y).1).1 ⊓ (snd A A).left ⁻¹ᵁ (S.u (x ⊓ y).2).1 = _
    rw [h1, h2]
    ext z
    simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Set.mem_inter_iff, Set.mem_preimage,
      SetLike.mem_coe]
    tauto
  cover := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have h : ∀ w : A.left, ∃ a, w ∈ (S.u a).1 := fun w ↦ by
      have : w ∈ ⨆ a, (S.u a).1 := by rw [S.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    obtain ⟨a, ha⟩ := h ((fst A A).left z)
    obtain ⟨b, hb⟩ := h ((snd A A).left z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨((a, b) : Bx P), ha, hb⟩
def pairL (S : Sys A.left P) (q : Bx P) : Pair (fst A A).left := ⟨((boxSys S).u q, S.u q.1), inf_le_left⟩
def pairR (S : Sys A.left P) (q : Bx P) : Pair (snd A A).left := ⟨((boxSys S).u q, S.u q.2), inf_le_right⟩
def gL (S : Sys A.left P) : (Bx P)ᵒᵖ ⥤ (Pair (fst A A).left)ᵒᵖ :=
  (Monotone.functor (f := pairL S) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(boxSys S).mono h, S.mono (Bx.le_fst h)⟩)).op
def gR (S : Sys A.left P) : (Bx P)ᵒᵖ ⥤ (Pair (snd A A).left)ᵒᵖ :=
  (Monotone.functor (f := pairR S) fun _ _ h ↦
    Subtype.coe_le_coe.1 (Prod.le_def.2 ⟨(boxSys S).mono h, S.mono (Bx.le_snd h)⟩)).op
def kL (S : Sys A.left P) :
    CoefMap (RingHom.id R) (OPair (fst A A).left (A ⊗ A).hom) (OSys (A ⊗ A).hom (boxSys S)) where
  G := gL S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
def kR (S : Sys A.left P) :
    CoefMap (RingHom.id R) (OPair (snd A A).left (A ⊗ A).hom) (OSys (A ⊗ A).hom (boxSys S)) where
  G := gR S
  α _ := RingHom.id _
  naturality _ _ := rfl
  smul _ _ _ := rfl
def algOfSemi {B B' : Type} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R B'] (a : B →+* B')
    (h : SemiHom (RingHom.id R) a) : B →ₐ[R] B' :=
  { a with
    commutes' := fun r ↦ by
      have k := h r 1
      simpa [Algebra.algebraMap_eq_smul_one] using k }
def algL (S : Sys A.left P) (T : (Bx P)ᵒᵖ) :
    (OSys A.hom S).obj (op T.unop.1) →ₐ[R] (OSys (A ⊗ A).hom (boxSys S)).obj T :=
  algOfSemi (secPull A.hom (A ⊗ A).hom (pairL S T.unop)) (semiHom_secPull (wOver (fst A A)) (pairL S T.unop))
def algR (S : Sys A.left P) (T : (Bx P)ᵒᵖ) :
    (OSys A.hom S).obj (op T.unop.2) →ₐ[R] (OSys (A ⊗ A).hom (boxSys S)).obj T :=
  algOfSemi (secPull A.hom (A ⊗ A).hom (pairR S T.unop)) (semiHom_secPull (wOver (snd A A)) (pairR S T.unop))
theorem algL_nat (S : Sys A.left P) {T T' : (Bx P)ᵒᵖ} (φ : T ⟶ T') (b : (OSys A.hom S).obj (op T.unop.1)) :
    algL S T' (mp (OSys A.hom S) ((boxG P).map φ).1 b) = mp (OSys (A ⊗ A).hom (boxSys S)) φ (algL S T b) :=
  ((pairPull (wOver (fst A A))).comp (kL S)).naturality φ b
theorem algR_nat (S : Sys A.left P) {T T' : (Bx P)ᵒᵖ} (φ : T ⟶ T') (b : (OSys A.hom S).obj (op T.unop.2)) :
    algR S T' (mp (OSys A.hom S) ((boxG P).map φ).2 b) = mp (OSys (A ⊗ A).hom (boxSys S)) φ (algR S T b) :=
  ((pairPull (wOver (snd A A))).comp (kR S)).naturality φ b
def boxCoef (S : Sys A.left P) :
    CoefMap (RingHom.id R) (box (OSys A.hom S)) (OSys (A ⊗ A).hom (boxSys S)) where
  G := boxG P
  α T := (Algebra.TensorProduct.productMap (algL S T) (algR S T)).toRingHom
  naturality {T T'} φ b := by
    have e : (Algebra.TensorProduct.productMap (algL S T') (algR S T')).comp
        (Algebra.TensorProduct.map (mp (OSys A.hom S) ((boxG P).map φ).1) (mp (OSys A.hom S) ((boxG P).map φ).2)) =
        (mp (OSys (A ⊗ A).hom (boxSys S)) φ).comp (Algebra.TensorProduct.productMap (algL S T) (algR S T)) :=
      Algebra.TensorProduct.ext' fun x y ↦
        (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).trans
          ((congrArg₂ (· * ·) (algL_nat S φ x) (algR_nat S φ y)).trans
            ((map_mul (mp (OSys (A ⊗ A).hom (boxSys S)) φ) _ _).symm.trans
              (congrArg (mp (OSys (A ⊗ A).hom (boxSys S)) φ)
                (Algebra.TensorProduct.productMap_apply_tmul _ _ _ _).symm)))
    exact congrArg (fun t ↦ t b) e
  smul T r b := map_smul (Algebra.TensorProduct.productMap (algL S T) (algR S T)) r b
end Sys
section Main
variable {R : Type} [CommRing R] {A : Over (Sp R)} {P : Type} [SemilatticeInf P]
end Main
end GlobalTheory.CompanionTheory.Axis



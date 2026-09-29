-- Prove2me | solution 1 for AlgebraicCurve.TwoChartIntegralModel.subfieldClosure_range_germToFunctionField_union_range_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/cec87431-35bf-5eda-9516-a0b442080fc4

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite
open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

noncomputable section

namespace ChartDict

universe u

variable (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
  (S : Type u) [CommRing S] [Algebra R S]

abbrev XS : Scheme.{u} := pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))

abbrev CS : Type u := ↥(chartAlgFin R F j) ⊗[R] S

noncomputable def gFin : Spec (CommRingCat.of (CS R F j S)) ⟶ XS R F j S :=
  (pullbackSpecIso R ↥(chartAlgFin R F j) S).inv ≫
    pullback.map _ _ _ _ (ιFin R F j) (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ιFin_toBase]) (by rw [Category.comp_id, Category.id_comp])

scoped instance : IsOpenImmersion (gFin R F j S) := by
  unfold gFin; infer_instance

theorem gFin_fst : gFin R F j S ≫ pullback.fst _ _ =
    Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιFin R F j := by
  unfold gFin
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullbackSpecIso_inv_fst]

theorem gFin_snd : gFin R F j S ≫ pullback.snd _ _ =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := S)).toRingHom) := by
  unfold gFin
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullbackSpecIso_inv_snd, Category.comp_id]
  rfl

theorem range_gFin : Set.range (gFin R F j S).base =
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).base ⁻¹' Set.range (ιFin R F j).base := by
  unfold gFin
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ,
    Scheme.Pullback.range_map]
  · simp
  · exact (pullbackSpecIso R ↥(chartAlgFin R F j) S).inv.homeomorph.surjective

theorem opensRange_gFin : (gFin R F j S).opensRange =
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤) := by
  ext1
  rw [Scheme.Hom.coe_opensRange, range_gFin]
  simp

variable {R F j S}

abbrev UFin : (XS R F j S).Opens :=
  (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)

theorem opensRange_gFin' : (gFin R F j S).opensRange = UFin (R := R) (F := F) (j := j) (S := S) :=
  opensRange_gFin R F j S

theorem preimage_gFin_UFin : (gFin R F j S) ⁻¹ᵁ (UFin : (XS R F j S).Opens) = ⊤ := by
  rw [← opensRange_gFin', Scheme.Hom.preimage_opensRange]

scoped instance isIso_gFin_app : IsIso ((gFin R F j S).app UFin) :=
  Scheme.Hom.isIso_app _ _ (opensRange_gFin' (R := R) (F := F) (j := j) (S := S)).ge

def αhom : CommRingCat.of ↥(chartAlgFin R F j) ⟶ Γ(XS R F j S, UFin) :=
  (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv ≫ ((ιFin R F j).appIso ⊤).inv ≫
    (pullback.fst (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).app ((ιFin R F j) ''ᵁ ⊤)

def βhom : CommRingCat.of S ⟶ Γ(XS R F j S, UFin) :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
    (pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop ≫
      (XS R F j S).presheaf.map (homOfLE le_top).op

def cmp : Γ(XS R F j S, UFin) ⟶ Γ(Spec (CommRingCat.of (CS R F j S)), ⊤) :=
  (gFin R F j S).appLE UFin ⊤ (preimage_gFin_UFin (R := R) (F := F) (j := j) (S := S)).ge

scoped instance isIso_cmp : IsIso (cmp (R := R) (F := F) (j := j) (S := S)) := by
  unfold cmp Scheme.Hom.appLE
  have : IsIso ((Spec (CommRingCat.of (CS R F j S))).presheaf.map
      (homOfLE (preimage_gFin_UFin (R := R) (F := F) (j := j) (S := S)).ge).op) := by
    have h : (homOfLE (preimage_gFin_UFin (R := R) (F := F) (j := j) (S := S)).ge) =
        eqToHom preimage_gFin_UFin.symm := Subsingleton.elim _ _
    rw [h, eqToHom_op]
    infer_instance
  infer_instance

theorem appLE_top_top {P Q : Scheme.{u}} (f : P ⟶ Q) (e : (⊤ : P.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  rw [Scheme.Hom.appLE]
  have : (homOfLE e) = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

theorem α_comm : αhom ≫ cmp (R := R) (F := F) (j := j) (S := S) =
    CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).inv := by

  have key : ∀ (φ : Spec (CommRingCat.of (CS R F j S)) ⟶ AlgebraicCurve.TwoChartIntegralModel R F j)
      (e : (⊤ : (Spec (CommRingCat.of (CS R F j S))).Opens) ≤ φ ⁻¹ᵁ ((ιFin R F j) ''ᵁ ⊤)),
      φ = Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫ ιFin R F j →
      (Scheme.ΓSpecIso (CommRingCat.of ↥(chartAlgFin R F j))).inv ≫ ((ιFin R F j).appIso ⊤).inv ≫
        φ.appLE ((ιFin R F j) ''ᵁ ⊤) ⊤ e =
      CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ (Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).inv := by
    intro φ e hφ
    subst hφ
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.appIso_inv_app_assoc, Scheme.Hom.map_appLE, appLE_top_top,
      ← Scheme.ΓSpecIso_inv_naturality]
  unfold αhom cmp
  simp only [Category.assoc]
  rw [← Scheme.Hom.comp_appLE]
  exact key _ _ (gFin_fst R F j S)

theorem β_comm : βhom ≫ cmp (R := R) (F := F) (j := j) (S := S) =
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := S)).toRingHom ≫
      (Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).inv := by
  have key : ∀ (φ : Spec (CommRingCat.of (CS R F j S)) ⟶ Spec (CommRingCat.of S))
      (e : (⊤ : (Spec (CommRingCat.of (CS R F j S))).Opens) ≤ φ ⁻¹ᵁ ⊤),
      φ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := S)).toRingHom) →
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ φ.appLE ⊤ ⊤ e =
      CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := ↥(chartAlgFin R F j)) (B := S)).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).inv := by
    intro φ e hφ
    subst hφ
    rw [appLE_top_top, ← Scheme.ΓSpecIso_inv_naturality]
  unfold βhom cmp
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE]
  erw [← Scheme.Hom.comp_appLE]
  exact key _ _ (gFin_snd R F j S)

theorem closure_range_α_β :
    Subring.closure (Set.range (αhom (R := R) (F := F) (j := j) (S := S)) ∪ Set.range (βhom (R := R) (F := F) (j := j) (S := S))) = ⊤ := by

  let e : Γ(XS R F j S, UFin) ≃+* CS R F j S :=
    ((asIso (cmp (R := R) (F := F) (j := j) (S := S))) ≪≫ Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).commRingCatIsoToRingEquiv
  have he : ∀ z, e z = (Scheme.ΓSpecIso (CommRingCat.of (CS R F j S))).hom (cmp (R := R) (F := F) (j := j) (S := S) z) := fun z => rfl
  have hα : ∀ a : ↥(chartAlgFin R F j), e (αhom a) = a ⊗ₜ 1 := by
    intro a
    rw [he, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Category.assoc, α_comm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  have hβ : ∀ b : S, e (βhom b) = 1 ⊗ₜ b := by
    intro b
    rw [he, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Category.assoc, β_comm, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [eq_top_iff]
  intro z _

  have hmem : ∀ t : CS R F j S, e.symm t ∈ Subring.closure (Set.range (αhom (R := R) (F := F) (j := j) (S := S)) ∪
      Set.range (βhom (R := R) (F := F) (j := j) (S := S))) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Subring.zero_mem _
    | tmul a b =>
      have : a ⊗ₜ[R] b = e (αhom a) * e (βhom b) := by
        rw [hα, hβ, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [this, ← map_mul, RingEquiv.symm_apply_apply]
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩)) (Subring.subset_closure (Or.inr ⟨b, rfl⟩))
    | add x y hx hy => rw [map_add]; exact Subring.add_mem _ hx hy
  simpa using hmem (e z)

theorem subfieldClosure_eq_top [IsIntegral (XS R F j S)] (x : XS R F j S)
    [Nonempty (Scheme.Opens.toScheme (UFin (R := R) (F := F) (j := j) (S := S)))] :
    Subfield.closure
      (Set.range (fun a : ↥(chartAlgFin R F j) => (XS R F j S).germToFunctionField UFin (αhom a)) ∪
        Set.range (fun s : S =>
          algebraMap ((XS R F j S).presheaf.stalk x) (XS R F j S).functionField
            (((XS R F j S).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ := by
  have hU : IsAffineOpen (UFin : (XS R F j S).Opens) := by
    rw [← opensRange_gFin']; exact isAffineOpen_opensRange _
  haveI := functionField_isFractionRing_of_isAffineOpen (XS R F j S) UFin hU

  have hβgerm : ∀ s : S, (XS R F j S).germToFunctionField UFin (βhom s) =
      algebraMap ((XS R F j S).presheaf.stalk x) (XS R F j S).functionField
        (((XS R F j S).presheaf.germ ⊤ x trivial).hom
          (((pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
            ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))) := by
    have hmor : βhom ≫ (XS R F j S).germToFunctionField UFin =
        (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫
          (pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop ≫
            (XS R F j S).presheaf.germ ⊤ x trivial ≫
              (XS R F j S).presheaf.stalkSpecializes ((genericPoint_spec (XS R F j S)).specializes trivial) := by
      unfold βhom Scheme.germToFunctionField
      simp only [Category.assoc]
      rw [TopCat.Presheaf.germ_res, TopCat.Presheaf.germ_stalkSpecializes]
    intro s
    have h := CommRingCat.hom_ext_iff.mp hmor
    have h' := RingHom.congr_fun h s
    rw [RingHom.algebraMap_toAlgebra]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
    exact h'

  set M := Subfield.closure
      (Set.range (fun a : ↥(chartAlgFin R F j) => (XS R F j S).germToFunctionField UFin (αhom a)) ∪
        Set.range (fun s : S =>
          algebraMap ((XS R F j S).presheaf.stalk x) (XS R F j S).functionField
            (((XS R F j S).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) with hM
  have hgerm : ∀ z : Γ(XS R F j S, UFin), (XS R F j S).germToFunctionField UFin z ∈ M := by
    intro z
    have hz : z ∈ Subring.closure (Set.range (αhom (R := R) (F := F) (j := j) (S := S)) ∪
        Set.range (βhom (R := R) (F := F) (j := j) (S := S))) := by
      rw [closure_range_α_β]; trivial
    refine Subring.closure_induction (fun w hw => ?_) ?_ ?_ (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_)
      (fun a b _ _ ha hb => ?_) hz
    · rcases hw with ⟨a, rfl⟩ | ⟨s, rfl⟩
      · exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
      · rw [hβgerm]; exact Subfield.subset_closure (Or.inr ⟨s, rfl⟩)
    · rw [map_zero]; exact M.zero_mem
    · rw [map_one]; exact M.one_mem
    · rw [map_add]; exact M.add_mem ha hb
    · rw [map_neg]; exact M.neg_mem ha
    · rw [map_mul]; exact M.mul_mem ha hb

  rw [eq_top_iff]
  intro q _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(XS R F j S, UFin)) q
  exact M.div_mem (hgerm a) (hgerm b)

end ChartDict
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top.ChartDict"

end
p2m_reactivate "P2MW.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top.ChartDict"

universe u in
open ChartDict in
theorem solution
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (S : Type u) [CommRing S] [Algebra R S]
    [hint : IsIntegral (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S))))]
    (x : ↥(pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))))
    [hne : Nonempty (Scheme.Opens.toScheme ((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ
      ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)))] :
    Subfield.closure
      (Set.range (fun a : ↥(TwoChartIntegralModel.chartAlgFin R F j) =>
        ((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).germToFunctionField
            ((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))) ⁻¹ᵁ
              ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤))
            (((pullback.fst (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).app
                ((TwoChartIntegralModel.ιFin R F j) ''ᵁ ⊤)).hom
              (((TwoChartIntegralModel.ιFin R F j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(TwoChartIntegralModel.chartAlgFin R F j))).inv a))))) ∪
        Set.range (fun s : S =>
          algebraMap ((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.stalk x)
            (pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).functionField
            (((pullback (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).presheaf.germ ⊤ x trivial).hom
              (((pullback.snd (TwoChartIntegralModel.toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R S)))).appTop).hom
                ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))))) = ⊤ :=
  ChartDict.subfieldClosure_eq_top (R := R) (F := F) (j := j) (S := S) x

end S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top
end P2MW
export P2MW.S_AlgebraicCurve_TwoChartIntegralModel_subfieldClosure_range_germToFunctionField_union_range_eq_top (solution)

-- Prove2me | Definitions.Def_AlgebraicGeometry_SubalgebraStages
-- name    : AlgebraicGeometry_SubalgebraStages
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/ec5b6fef-33bc-5db2-8838-4593c70e101c
-- title:
--   Base-change inverse systems along a monotone family of subalgebras
-- statement:
--   Fix a commutative ring $A_0$, an $A_0$-algebra $A$, a preorder $\iota$, and an order-preserving map $S \colon \iota \to \mathrm{Sub}_{A_0}(A)$ into the $A_0$-subalgebras of $A$. The basic morphisms are $\mathrm{specHom}\,S\,i \colon \operatorname{Spec} S_i \to \operatorname{Spec} A_0$ and $\mathrm{specHomTop} \colon \operatorname{Spec} A \to \operatorname{Spec} A_0$, induced by the structure maps; $\mathrm{specTrans}\,S\,h \colon \operatorname{Spec} S_j \to \operatorname{Spec} S_i$ for $h \colon i \le j$, induced by the inclusion $S_i \subseteq S_j$; and $\mathrm{specLeg}\,S\,i \colon \operatorname{Spec} A \to \operatorname{Spec} S_i$, induced by $S_i \hookrightarrow A$. The accompanying lemmas record the evident triangle identities ($\mathrm{specTrans}$ followed by $\mathrm{specHom}\,S\,i$ is $\mathrm{specHom}\,S\,j$, $\mathrm{specLeg}$ followed by $\mathrm{specHom}$ is $\mathrm{specHomTop}$, $\mathrm{specLeg}\,S\,j$ followed by $\mathrm{specTrans}\,S\,h$ is $\mathrm{specLeg}\,S\,i$) and functoriality of $\mathrm{specTrans}$ in $\le$, which assemble into the functor `specDiagram` $\colon \iota^{\mathrm{op}} \to \mathbf{Sch}$, $i \mapsto \operatorname{Spec} S_i$, and the cone `specCone` over it with vertex $\operatorname{Spec} A$ and legs $\mathrm{specLeg}$.
--
--   Given in addition a scheme $X$ and a morphism $f \colon X \to \operatorname{Spec} A_0$, the stage $\mathrm{obj}\,S\,f\,i$ is the Mathlib pullback of $f$ along $\mathrm{specHom}\,S\,i$, i.e. $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} S_i$; `trans` is the induced transition morphism between stages, characterised by its two components (identity on the projection to $X$, and $\mathrm{specTrans}$ on the projection to the spectra), and `leg` is the analogous morphism from $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ to the $i$-th stage. These give the functor `diagram` $\colon \iota^{\mathrm{op}} \to \mathbf{Sch}$ and the cone `cone` over it with vertex the pullback of $f$ along $\mathrm{specHomTop}$. Further lemmas state that the square formed by `trans`, the two second projections and $\mathrm{specTrans}$ is cartesian, and likewise for `leg` and $\mathrm{specLeg}$; the instances deduce that all transition morphisms and legs are affine, that the second projections are quasi-compact (resp. quasi-separated) when $f$ is, that each stage then has compact (resp. quasi-separated) underlying space, and that $\iota^{\mathrm{op}}$ is cofiltered when $\iota$ is non-empty and directed. No limit property of the cones is asserted here.
--
--   **Relation to Mathlib.** The objects are literally Mathlib's `pullback` of $f$ along `Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(S i)))`, and the affineness, quasi-compactness and quasi-separatedness statements are instances of Mathlib's morphism-property API; the module only packages the subalgebra-indexed diagram and cone so that Mathlib's theory of cofiltered limits of schemes with affine transition morphisms applies to it.
--
--   **Where it is used.** This vocabulary supports the descent arguments in which a property of $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ (finite presentation, separatedness, flatness, properness, or the existence of sections or of morphisms to a scheme locally of finite presentation) is traced back to a single stage $X \times_{\operatorname{Spec} A_0} \operatorname{Spec} S_i$, for instance with $S$ the family of finitely generated $A_0$-subalgebras of $A$, as in Noetherian approximation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_SubalgebraStages.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

namespace SubalgebraStages

variable {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
variable {ι : Type u} [Preorder ι] (S : ι →o Subalgebra A₀ A)

noncomputable abbrev specHom (i : ι) : Spec (CommRingCat.of ↥(S i)) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥(S i)))

noncomputable abbrev specHomTop : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A₀) :=
  Spec.map (CommRingCat.ofHom (algebraMap A₀ A))

noncomputable abbrev specTrans {i j : ι} (h : i ≤ j) : Spec (CommRingCat.of ↥(S j)) ⟶ Spec (CommRingCat.of ↥(S i)) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (S.mono h)).toRingHom)

noncomputable abbrev specLeg (i : ι) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of ↥(S i)) :=
  Spec.map (CommRingCat.ofHom (S i).val.toRingHom)

@[simp] lemma specTrans_specHom {i j : ι} (h : i ≤ j) : specTrans S h ≫ specHom S i = specHom S j := by
  rw [specTrans, specHom, specHom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

@[simp] lemma specLeg_specHom (i : ι) : specLeg S i ≫ specHom S i = specHomTop (A₀ := A₀) (A := A) := by
  rw [specLeg, specHom, specHomTop, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

@[simp] lemma specLeg_specTrans {i j : ι} (h : i ≤ j) : specLeg S j ≫ specTrans S h = specLeg S i := by
  rw [specLeg, specTrans, specLeg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

lemma specTrans_comp {i j k : ι} (h : i ≤ j) (h' : j ≤ k) :
    specTrans S h' ≫ specTrans S h = specTrans S (h.trans h') := by
  rw [specTrans, specTrans, specTrans, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl

@[simp] lemma specTrans_refl (i : ι) : specTrans S (le_refl i) = 𝟙 _ := by
  rw [specTrans, ← Spec.map_id]; rfl

@[reducible] noncomputable def specDiagram : ιᵒᵖ ⥤ Scheme.{u} where
  obj i := Spec (CommRingCat.of ↥(S i.unop))
  map h := specTrans S h.unop.le
  map_id i := specTrans_refl S i.unop
  map_comp h h' := (specTrans_comp S h'.unop.le h.unop.le).symm

@[reducible] noncomputable def specCone : Cone (specDiagram S) where
  pt := Spec (CommRingCat.of A)
  π := { app i := specLeg S i.unop
         naturality {i j} h := by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
           exact (specLeg_specTrans S h.unop.le).symm }

@[simp] lemma specDiagram_obj (i : ιᵒᵖ) : (specDiagram S).obj i = Spec (CommRingCat.of ↥(S i.unop)) := rfl
@[simp] lemma specDiagram_map {i j : ιᵒᵖ} (h : i ⟶ j) : (specDiagram S).map h = specTrans S h.unop.le := rfl
@[simp] lemma specCone_pt : (specCone S).pt = Spec (CommRingCat.of A) := rfl
@[simp] lemma specCone_π_app (i : ιᵒᵖ) : (specCone S).π.app i = specLeg S i.unop := rfl

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A₀))

noncomputable abbrev obj (i : ι) : Scheme.{u} := pullback f (specHom S i)

noncomputable def trans {i j : ι} (h : i ≤ j) : obj S f j ⟶ obj S f i :=
  pullback.lift (pullback.fst f (specHom S j)) (pullback.snd f (specHom S j) ≫ specTrans S h)
    (by rw [pullback.condition, Category.assoc, specTrans_specHom])

@[simp, reassoc] lemma trans_fst {i j : ι} (h : i ≤ j) :
    trans S f h ≫ pullback.fst f (specHom S i) = pullback.fst f (specHom S j) := pullback.lift_fst _ _ _

@[simp, reassoc] lemma trans_snd {i j : ι} (h : i ≤ j) :
    trans S f h ≫ pullback.snd f (specHom S i) = pullback.snd f (specHom S j) ≫ specTrans S h :=
  pullback.lift_snd _ _ _

lemma trans_refl (i : ι) : trans S f (le_refl i) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [trans_fst, Category.id_comp]
  · rw [trans_snd, specTrans_refl, Category.id_comp, Category.comp_id]

lemma trans_comp {i j k : ι} (h : i ≤ j) (h' : j ≤ k) :
    trans S f h' ≫ trans S f h = trans S f (h.trans h') := by
  apply pullback.hom_ext
  · rw [Category.assoc, trans_fst, trans_fst, trans_fst]
  · rw [Category.assoc, trans_snd, trans_snd_assoc, trans_snd, specTrans_comp]

@[reducible] noncomputable def diagram : ιᵒᵖ ⥤ Scheme.{u} where
  obj i := obj S f i.unop
  map h := trans S f h.unop.le
  map_id i := trans_refl S f i.unop
  map_comp h h' := (trans_comp S f h'.unop.le h.unop.le).symm

@[simp] lemma diagram_obj (i : ιᵒᵖ) : (diagram S f).obj i = pullback f (specHom S i.unop) := rfl
@[simp] lemma diagram_map {i j : ιᵒᵖ} (h : i ⟶ j) : (diagram S f).map h = trans S f h.unop.le := rfl

@[reassoc] lemma diagram_map_fst {i j : ιᵒᵖ} (h : i ⟶ j) :
    (diagram S f).map h ≫ pullback.fst f (specHom S j.unop) = pullback.fst f (specHom S i.unop) :=
  trans_fst S f h.unop.le

@[reassoc] lemma diagram_map_snd {i j : ιᵒᵖ} (h : i ⟶ j) :
    (diagram S f).map h ≫ pullback.snd f (specHom S j.unop) = pullback.snd f (specHom S i.unop) ≫ specTrans S h.unop.le :=
  trans_snd S f h.unop.le

noncomputable def leg (i : ι) : pullback f (specHomTop (A₀ := A₀) (A := A)) ⟶ obj S f i :=
  pullback.lift (pullback.fst f specHomTop) (pullback.snd f specHomTop ≫ specLeg S i)
    (by rw [pullback.condition, Category.assoc, specLeg_specHom])

@[simp, reassoc] lemma leg_fst (i : ι) :
    leg S f i ≫ pullback.fst f (specHom S i) = pullback.fst f specHomTop := pullback.lift_fst _ _ _

@[simp, reassoc] lemma leg_snd (i : ι) :
    leg S f i ≫ pullback.snd f (specHom S i) = pullback.snd f specHomTop ≫ specLeg S i :=
  pullback.lift_snd _ _ _

@[simp, reassoc] lemma leg_trans {i j : ι} (h : i ≤ j) : leg S f j ≫ trans S f h = leg S f i := by
  apply pullback.hom_ext
  · rw [Category.assoc, trans_fst, leg_fst, leg_fst]
  · rw [Category.assoc, trans_snd, leg_snd_assoc, leg_snd, specLeg_specTrans]

@[reducible] noncomputable def cone : Cone (diagram S f) where
  pt := pullback f (specHomTop (A₀ := A₀) (A := A))
  π := { app i := leg S f i.unop
         naturality {i j} h := by
           simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
           exact (leg_trans S f h.unop.le).symm }

@[simp] lemma cone_pt : (cone S f).pt = pullback f (specHomTop (A₀ := A₀) (A := A)) := rfl
@[simp] lemma cone_π_app (i : ιᵒᵖ) : (cone S f).π.app i = leg S f i.unop := rfl

@[reassoc] lemma cone_π_app_fst (i : ιᵒᵖ) :
    (cone S f).π.app i ≫ pullback.fst f (specHom S i.unop) = pullback.fst f specHomTop := leg_fst S f i.unop

@[reassoc] lemma cone_π_app_snd (i : ιᵒᵖ) :
    (cone S f).π.app i ≫ pullback.snd f (specHom S i.unop) = pullback.snd f specHomTop ≫ specLeg S i.unop :=
  leg_snd S f i.unop

@[reassoc] lemma specCone_π_app_specHom (i : ιᵒᵖ) :
    (specCone S).π.app i ≫ specHom S i.unop = specHomTop (A₀ := A₀) (A := A) := specLeg_specHom S i.unop

@[reassoc] lemma specDiagram_map_specHom {i j : ιᵒᵖ} (h : i ⟶ j) :
    (specDiagram S).map h ≫ specHom S j.unop = specHom S i.unop := specTrans_specHom S h.unop.le

lemma isPullback_trans {i j : ι} (h : i ≤ j) :
    IsPullback (trans S f h) (pullback.snd f (specHom S j)) (pullback.snd f (specHom S i)) (specTrans S h) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (specHom S i)) (v₁₃ := f) (h₂₂ := specHom S i) ?_ (trans_snd S f h) (IsPullback.of_hasPullback f (specHom S i))
  rw [trans_fst, specTrans_specHom]
  exact IsPullback.of_hasPullback f (specHom S j)

lemma isPullback_leg (i : ι) :
    IsPullback (leg S f i) (pullback.snd f specHomTop) (pullback.snd f (specHom S i)) (specLeg S i) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst f (specHom S i)) (v₁₃ := f) (h₂₂ := specHom S i) ?_ (leg_snd S f i) (IsPullback.of_hasPullback f (specHom S i))
  rw [leg_fst, specLeg_specHom]
  exact IsPullback.of_hasPullback f specHomTop

instance isAffineHom_trans {i j : ι} (h : i ≤ j) : IsAffineHom (trans S f h) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_trans S f h).flip inferInstance

instance isAffineHom_diagram_map {i j : ιᵒᵖ} (h : i ⟶ j) : IsAffineHom ((diagram S f).map h) :=
  isAffineHom_trans S f h.unop.le

instance isAffineHom_leg (i : ι) : IsAffineHom (leg S f i) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_leg S f i).flip inferInstance

instance quasiCompact_snd [QuasiCompact f] (i : ι) : QuasiCompact (pullback.snd f (specHom S i)) :=
  MorphismProperty.pullback_snd (P := @QuasiCompact) _ _ inferInstance

instance quasiSeparated_snd [QuasiSeparated f] (i : ι) : QuasiSeparated (pullback.snd f (specHom S i)) :=
  MorphismProperty.pullback_snd (P := @QuasiSeparated) _ _ inferInstance

instance compactSpace_pullback [QuasiCompact f] (i : ι) : CompactSpace ↥(pullback f (specHom S i)) :=
  @QuasiCompact.compactSpace_of_compactSpace _ _ (pullback.snd f (specHom S i)) (quasiCompact_snd S f i)
    (inferInstance : CompactSpace (PrimeSpectrum ↥(S i)))

instance compactSpace_obj [QuasiCompact f] (i : ιᵒᵖ) : CompactSpace ↥((diagram S f).obj i) :=
  compactSpace_pullback S f i.unop

instance quasiSeparatedSpace_pullback [QuasiSeparated f] (i : ι) : QuasiSeparatedSpace ↥(pullback f (specHom S i)) :=
  @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd f (specHom S i)) inferInstance (quasiSeparated_snd S f i)

instance quasiSeparatedSpace_obj [QuasiSeparated f] (i : ιᵒᵖ) : QuasiSeparatedSpace ↥((diagram S f).obj i) :=
  quasiSeparatedSpace_pullback S f i.unop

instance isCofiltered_op [IsDirected ι (· ≤ ·)] [Nonempty ι] : IsCofiltered ιᵒᵖ := inferInstance

end SubalgebraStages

end AlgebraicGeometry



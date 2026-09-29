-- Prove2me | Definitions.Def_AlgebraicGeometry_FGSubalgebra
-- name    : AlgebraicGeometry_FGSubalgebra
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7e2a011a-77bd-5c33-af7f-4fa01f298c68
-- title:
--   Finitely generated subalgebras as a filtered diagram and its Spec
-- statement:
--   Fix a commutative ring $R$ and a commutative $R$-algebra $A$. The abbreviation `FGSubalgebra R A` is the type of pairs consisting of an $R$-subalgebra $A_0 \subseteq A$ together with a proof that $A_0$ is finitely generated, ordered by inclusion of the underlying subalgebras. Instances record that this poset is nonempty (the bottom subalgebra, the image of $R$, is finitely generated) and directed (the join of two finitely generated subalgebras is finitely generated), hence filtered as a category, with opposite category cofiltered; further instances, together with `nonempty_subtype_le`, record that for a fixed subalgebra $A_0$ the finitely generated subalgebras containing $A_0$ form a directed set, nonempty as soon as $A_0$ is itself finitely generated.
--
--   On this index category two diagrams are defined. `diagram` is the functor from `FGSubalgebra R A` to `CommRingCat` sending $A_0$ to the ring $A_0$ and an inclusion $A_0 \le A_1$ to the induced inclusion homomorphism, and `cocone` is the cocone over it with vertex $A$ whose leg at $A_0$ is the inclusion $A_0 \hookrightarrow A$. Dually, `specDiagram` is the composite of the opposite of `diagram` with $\operatorname{Spec}$, a functor from `FGSubalgebra R A`ᵒᵖ to schemes sending $A_0$ to $\operatorname{Spec} A_0$, and `specCone` is the image under $\operatorname{Spec}$ of the opposite of `cocone`, a cone with vertex $\operatorname{Spec} A$ and legs $\operatorname{Spec} A \to \operatorname{Spec} A_0$. The natural transformation `specOver` from `specDiagram` to the constant functor at $\operatorname{Spec} R$ has component $\operatorname{Spec}$ of the structure map $R \to A_0$ at $A_0$, exhibiting the diagram as one of $R$-schemes; `specCone_π_comp_specOver` states that composing the cone legs with `specOver` gives the constant transformation at $\operatorname{Spec}$ of $R \to A$. Auxiliary lemmas evaluate these functors, cones and transformations on objects and morphisms. Instances record that each $\operatorname{Spec} A_0$ is affine, hence has compact and quasi-separated underlying space, and that every transition morphism in `specDiagram` is affine.
--
--   **Relation to Mathlib.** The constructions are stated in the shape required by Mathlib's theory of inverse limits of quasi-compact quasi-separated schemes with affine transition morphisms; the indexing poset of finitely generated subalgebras and the two diagrams built from it are set up here, Mathlib supplying `Subalgebra.FG`, `CommRingCat`, `Scheme.Spec` and the limit machinery.
--
--   **Where it is used.** These diagrams provide the standard presentation of an arbitrary $R$-algebra as a filtered colimit of its finitely generated subalgebras, and of $\operatorname{Spec} A$ as the corresponding cofiltered limit of affine $R$-schemes of finite type, which is the vehicle for descending statements about schemes or functors locally of finite presentation over $A$ to finitely generated subalgebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FGSubalgebra.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

abbrev FGSubalgebra : Type u := {A₀ : Subalgebra R A // A₀.FG}

namespace FGSubalgebra

instance : Nonempty (FGSubalgebra R A) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

instance : IsDirected (FGSubalgebra R A) (· ≤ ·) :=
  ⟨fun A₀ A₁ ↦ ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩,
    (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1), (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1)⟩⟩

instance : IsFiltered (FGSubalgebra R A) := inferInstance

instance (A₀ : Subalgebra R A) : IsDirected {A₁ : FGSubalgebra R A // A₀ ≤ A₁.1} (· ≤ ·) :=
  ⟨fun A₁ A₂ ↦ ⟨⟨⟨A₁.1.1 ⊔ A₂.1.1, A₁.1.2.sup A₂.1.2⟩, A₁.2.trans (le_sup_left : A₁.1.1 ≤ _)⟩,
    (le_sup_left : A₁.1.1 ≤ A₁.1.1 ⊔ A₂.1.1), (le_sup_right : A₂.1.1 ≤ A₁.1.1 ⊔ A₂.1.1)⟩⟩

instance (A₀ : FGSubalgebra R A) : Nonempty {A₁ : FGSubalgebra R A // A₀.1 ≤ A₁.1} := ⟨⟨A₀, le_rfl⟩⟩

lemma nonempty_subtype_le (A₀ : Subalgebra R A) (h : A₀.FG) :
    Nonempty {A₁ : FGSubalgebra R A // A₀ ≤ A₁.1} := ⟨⟨⟨A₀, h⟩, le_rfl⟩⟩

instance : IsCofiltered (FGSubalgebra R A)ᵒᵖ := inferInstance

noncomputable def diagram : FGSubalgebra R A ⥤ CommRingCat.{u} where
  obj A₀ := CommRingCat.of A₀.1
  map {A₀ A₁} h := CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

noncomputable def cocone : Cocone (diagram R A) where
  pt := CommRingCat.of A
  ι := { app A₀ := CommRingCat.ofHom A₀.1.val.toRingHom
         naturality _ _ _ := by ext; rfl }

lemma diagram_obj (A₀ : FGSubalgebra R A) : (diagram R A).obj A₀ = CommRingCat.of A₀.1 := rfl

lemma diagram_map {A₀ A₁ : FGSubalgebra R A} (h : A₀ ⟶ A₁) :
    (diagram R A).map h =
      CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom := rfl

lemma cocone_pt : (cocone R A).pt = CommRingCat.of A := rfl

lemma cocone_ι_app (A₀ : FGSubalgebra R A) :
    (cocone R A).ι.app A₀ = CommRingCat.ofHom A₀.1.val.toRingHom := rfl

@[simp] lemma cocone_ι_app_apply (A₀ : FGSubalgebra R A) (x : A₀.1) :
    (cocone R A).ι.app A₀ x = (x : A) := rfl

noncomputable def specDiagram : (FGSubalgebra R A)ᵒᵖ ⥤ Scheme.{u} :=
  (diagram R A).op ⋙ Scheme.Spec

noncomputable def specCone : Cone (specDiagram R A) :=
  Scheme.Spec.mapCone (cocone R A).op

noncomputable def specOver :
    specDiagram R A ⟶ (Functor.const _).obj (Spec (CommRingCat.of R)) where
  app i := Spec.map (CommRingCat.ofHom (algebraMap R i.unop.1))
  naturality i j f := by
    obtain ⟨A₁⟩ := i; obtain ⟨A₀⟩ := j
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    change (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (R := R)
        (show A₀.1 ≤ A₁.1 from f.unop.le)).toRingHom) : Spec (CommRingCat.of A₁.1) ⟶ Spec (CommRingCat.of A₀.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) = Spec.map (CommRingCat.ofHom (algebraMap R A₁.1))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

lemma specDiagram_obj (A₀ : FGSubalgebra R A) :
    (specDiagram R A).obj (op A₀) = Spec (CommRingCat.of A₀.1) := rfl

lemma specDiagram_map {A₀ A₁ : FGSubalgebra R A} (h : A₀ ⟶ A₁) :
    (specDiagram R A).map h.op =
      Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (R := R) (show A₀.1 ≤ A₁.1 from h.le)).toRingHom) :=
  rfl

lemma specCone_pt : (specCone R A).pt = Spec (CommRingCat.of A) := rfl

lemma specCone_π_app (A₀ : FGSubalgebra R A) :
    (specCone R A).π.app (op A₀) = Spec.map (CommRingCat.ofHom A₀.1.val.toRingHom) := rfl

lemma specOver_app (A₀ : FGSubalgebra R A) :
    (specOver R A).app (op A₀) = Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) := rfl

lemma specCone_π_comp_specOver :
    (specCone R A).π ≫ specOver R A =
      (Functor.const _).map (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  ext ⟨A₀⟩
  change (Spec.map (CommRingCat.ofHom A₀.1.val.toRingHom) : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A₀.1)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R A₀.1)) = Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

instance (i : (FGSubalgebra R A)ᵒᵖ) : IsAffine ((specDiagram R A).obj i) :=
  inferInstanceAs (IsAffine (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : CompactSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (CompactSpace (Spec _))

instance (i : (FGSubalgebra R A)ᵒᵖ) : QuasiSeparatedSpace ((specDiagram R A).obj i) :=
  inferInstanceAs (QuasiSeparatedSpace (Spec _))

instance {i j : (FGSubalgebra R A)ᵒᵖ} (f : i ⟶ j) : IsAffineHom ((specDiagram R A).map f) :=
  isAffineHom_of_isAffine _

end FGSubalgebra

end AlgebraicGeometry



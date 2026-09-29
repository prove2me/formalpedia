-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nilpPoints.exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/83dd66b4-11ee-5d88-8055-329e3722630c

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType

set_option autoImplicit false

namespace KcSchColim

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld.FormalOmega

universe u

section Index

variable (R : Type) [CommRing R] (B : Type) [CommRing B] [Algebra R B]

def J : Type := {S : Subalgebra R B // S.FG}

scoped instance : Preorder (J R B) := Subtype.preorder _

scoped instance : Nonempty (J R B) := ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

scoped instance : IsDirected (J R B) (· ≤ ·) :=
  ⟨fun S T => ⟨⟨S.1 ⊔ T.1, S.2.sup T.2⟩, le_sup_left (a := S.1), le_sup_right (a := S.1)⟩⟩

def diag : J R B ⥤ CommRingCat.{0} where
  obj S := CommRingCat.of ↥S.1
  map {S T} h := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h)).toRingHom
  map_id S := by apply CommRingCat.hom_ext; ext x; rfl
  map_comp f g := by apply CommRingCat.hom_ext; ext x; rfl

def cocone : Cocone (diag R B) where
  pt := CommRingCat.of B
  ι := { app := fun S => CommRingCat.ofHom S.1.val.toRingHom
         naturality := fun {S T} h => by apply CommRingCat.hom_ext; ext x; rfl }

variable {R B}

noncomputable def jOf (b : B) : J R B := by
  classical
  exact ⟨Algebra.adjoin R (↑({b} : Finset B) : Set B), Subalgebra.fg_adjoin_finset _⟩

theorem mem_jOf (b : B) : b ∈ (jOf (R := R) b).1 := by
  classical
  show b ∈ Algebra.adjoin R (↑({b} : Finset B) : Set B)
  exact Algebra.subset_adjoin (by simp)

section Desc

variable (s : Cocone (diag R B))

noncomputable def descFun (b : B) : s.pt := (s.ι.app (jOf b)).hom ⟨b, mem_jOf b⟩

theorem descFun_spec (S : J R B) (x : ↥S.1) : descFun s (x : B) = (s.ι.app S).hom x := by
  let T : J R B := ⟨S.1 ⊔ (jOf (R := R) (x : B)).1, S.2.sup (jOf (R := R) (x : B)).2⟩
  have hS : S ≤ T := le_sup_left (a := S.1)
  have hj : jOf (R := R) (x : B) ≤ T := le_sup_right (a := S.1)
  have e1 := s.w (homOfLE hS)
  have e2 := s.w (homOfLE hj)
  rw [descFun, ← e2, ← e1]
  rfl

theorem descFun_spec' (S : J R B) (b : B) (hb : b ∈ S.1) : descFun s b = (s.ι.app S).hom ⟨b, hb⟩ :=
  descFun_spec s S ⟨b, hb⟩

theorem exists_mem_mem (a b : B) : ∃ S : J R B, a ∈ S.1 ∧ b ∈ S.1 :=
  ⟨⟨(jOf (R := R) a).1 ⊔ (jOf (R := R) b).1, (jOf a).2.sup (jOf b).2⟩,
    (le_sup_left : (jOf (R := R) a).1 ≤ _) (mem_jOf a), (le_sup_right : (jOf (R := R) b).1 ≤ _) (mem_jOf b)⟩

noncomputable def desc : B →+* s.pt where
  toFun := descFun s
  map_one' := by
    rw [descFun_spec' s (jOf (R := R) (1 : B)) 1 (Subalgebra.one_mem _)]
    exact map_one (s.ι.app (jOf (R := R) (1 : B))).hom
  map_mul' a b := by
    obtain ⟨S, ha, hb⟩ := exists_mem_mem (R := R) a b
    rw [descFun_spec' s S a ha, descFun_spec' s S b hb, descFun_spec' s S (a * b) (Subalgebra.mul_mem _ ha hb)]
    exact map_mul (s.ι.app S).hom ⟨a, ha⟩ ⟨b, hb⟩
  map_zero' := by
    rw [descFun_spec' s (jOf (R := R) (0 : B)) 0 (Subalgebra.zero_mem _)]
    exact map_zero (s.ι.app (jOf (R := R) (0 : B))).hom
  map_add' a b := by
    obtain ⟨S, ha, hb⟩ := exists_mem_mem (R := R) a b
    rw [descFun_spec' s S a ha, descFun_spec' s S b hb, descFun_spec' s S (a + b) (Subalgebra.add_mem _ ha hb)]
    exact map_add (s.ι.app S).hom ⟨a, ha⟩ ⟨b, hb⟩

end Desc

variable (R B) in

noncomputable def isColimit : IsColimit (cocone R B) where
  desc s := CommRingCat.ofHom (desc s)
  fac s S := by
    apply CommRingCat.hom_ext; ext x
    exact descFun_spec s S x
  uniq s m hm := by
    apply CommRingCat.hom_ext; ext b
    show m.hom b = descFun s b
    rw [descFun, ← hm (jOf b)]
    rfl

end Index

section Points

variable {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪] (R : Type) [CommRing R] [Algebra 𝒪 R]
  {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType f]
  (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B]

noncomputable def D : (J R B)ᵒᵖ ⥤ Scheme.{0} := (diag R B).op ⋙ Scheme.Spec

noncomputable def tt : D R B ⟶ (Functor.const (J R B)ᵒᵖ).obj (Spec (CommRingCat.of 𝒪)) where
  app j := Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ↥j.unop.1))
  naturality {j j'} h := by
    show Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (leOfHom h.unop)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ↥j'.unop.1)) = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ↥j.unop.1)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

noncomputable def cone : Cone (D R B) := Scheme.Spec.mapCone (cocone R B).op

noncomputable def isLimit : IsLimit (cone R B) :=
  haveI : PreservesLimitsOfSize.{0, 0} Scheme.Spec.{0} := ΓSpec.adjunction.rightAdjoint_preservesLimits
  isLimitOfPreserves Scheme.Spec (isColimit R B).op

theorem lfp : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  haveI : IsNoetherianRing Γ(Spec (CommRingCat.of 𝒪), U) := IsLocallyNoetherian.component_noetherian U
  exact RingHom.FinitePresentation.of_finiteType.mp
    ((HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)).mp inferInstance U V e)

scoped instance (j : (J R B)ᵒᵖ) : IsAffine ((D R B).obj j) := (inferInstance : IsAffine (Spec _))
scoped instance (j : (J R B)ᵒᵖ) : CompactSpace ((D R B).obj j) := (inferInstance : CompactSpace (Spec _))
scoped instance (j : (J R B)ᵒᵖ) : QuasiSeparatedSpace ((D R B).obj j) := (inferInstance : QuasiSeparatedSpace (Spec _))
scoped instance {i j : (J R B)ᵒᵖ} (h : i ⟶ j) : IsAffineHom ((D R B).map h) := (inferInstance : IsAffineHom (Spec.map _))

theorem cone_π_app (j : (J R B)ᵒᵖ) :
    (cone R B).π.app j = Spec.map (CommRingCat.ofHom (j.unop.1.val).toRingHom) := rfl

theorem tt_app (j : (J R B)ᵒᵖ) : (tt R B).app j = Spec.map (CommRingCat.ofHom (algebraMap 𝒪 ↥j.unop.1)) := rfl

include f in
omit [LocallyOfFiniteType f] in
theorem cone_π_tt (j : (J R B)ᵒᵖ) :
    (cone R B).π.app j ≫ (tt R B).app j = Scheme.specOver (𝒪 := 𝒪) B := by
  have e : CommRingCat.ofHom (algebraMap 𝒪 B) =
      CommRingCat.ofHom (algebraMap 𝒪 ↥j.unop.1) ≫ CommRingCat.ofHom (j.unop.1.val).toRingHom := by
    apply CommRingCat.hom_ext; ext o; rfl
  rw [cone_π_app, tt_app, Scheme.specOver, e, Spec.map_comp]
  rfl

theorem clause₁ (y : (Scheme.nilpPoints f).obj B) :
    ∃ (S : Subalgebra R B) (_ : S.FG) (y₀ : (Scheme.nilpPoints f).obj ↥S),
      (Scheme.nilpPoints f).map ((S.val).restrictScalars 𝒪) y₀ = y := by
  haveI := lfp f
  have ha : (cone R B).π ≫ tt R B = (Functor.const _).map (y.1 ≫ f) := by
    ext j
    rw [NatTrans.comp_app, cone_π_tt R f B j, Functor.const_map_app, y.2]
  obtain ⟨i, g, hg1, hg2⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation (D R B) (tt R B) f (cone R B) (isLimit R B) y.1 ha
  exact ⟨i.unop.1, i.unop.2, ⟨g, hg2⟩, Subtype.ext hg1⟩

omit [IsNoetherianRing 𝒪] in

theorem clause₂ (S₁ S₂ : Subalgebra R B) (h₁ : S₁.FG) (h₂ : S₂.FG)
    (y₁ : (Scheme.nilpPoints f).obj ↥S₁) (y₂ : (Scheme.nilpPoints f).obj ↥S₂)
    (h : (Scheme.nilpPoints f).map ((S₁.val).restrictScalars 𝒪) y₁ = (Scheme.nilpPoints f).map ((S₂.val).restrictScalars 𝒪) y₂) :
    ∃ (S₃ : Subalgebra R B) (_ : S₃.FG) (i₁ : S₁ ≤ S₃) (i₂ : S₂ ≤ S₃),
      (Scheme.nilpPoints f).map ((Subalgebra.inclusion i₁).restrictScalars 𝒪) y₁ =
        (Scheme.nilpPoints f).map ((Subalgebra.inclusion i₂).restrictScalars 𝒪) y₂ := by
  obtain ⟨k, hik, hjk, e⟩ :=
    Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType (D R B) (tt R B) f (cone R B) (isLimit R B)
      (i := Opposite.op ⟨S₁, h₁⟩) y₁.1 y₁.2.symm (j := Opposite.op ⟨S₂, h₂⟩) y₂.1 y₂.2.symm (congrArg Subtype.val h)
  exact ⟨k.unop.1, k.unop.2, leOfHom hik.unop, leOfHom hjk.unop, Subtype.ext e⟩

end Points

end KcSchColim
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType.KcSchColim"

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    (R : Type) [CommRing R] [Algebra 𝒪 R]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of 𝒪)) [LocallyOfFiniteType f] :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B] (y : (Scheme.nilpPoints f).obj B),
        ∃ (S : Subalgebra R B) (_ : S.FG) (y₀ : (Scheme.nilpPoints f).obj ↥S),
          (Scheme.nilpPoints f).map ((S.val).restrictScalars 𝒪) y₀ = y) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra R B] [IsScalarTower 𝒪 R B]
        (S₁ S₂ : Subalgebra R B), S₁.FG → S₂.FG →
        ∀ (y₁ : (Scheme.nilpPoints f).obj ↥S₁) (y₂ : (Scheme.nilpPoints f).obj ↥S₂),
        (Scheme.nilpPoints f).map ((S₁.val).restrictScalars 𝒪) y₁ = (Scheme.nilpPoints f).map ((S₂.val).restrictScalars 𝒪) y₂ →
        ∃ (S₃ : Subalgebra R B) (_ : S₃.FG) (h₁ : S₁ ≤ S₃) (h₂ : S₂ ≤ S₃),
          (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₁).restrictScalars 𝒪) y₁ =
            (Scheme.nilpPoints f).map ((Subalgebra.inclusion h₂).restrictScalars 𝒪) y₂) := by
  exact ⟨fun B _ _ _ _ y => KcSchColim.clause₁ R f B y,
    fun B _ _ _ _ S₁ S₂ h₁ h₂ y₁ y₂ h => KcSchColim.clause₂ R f B S₁ S₂ h₁ h₂ y₁ y₂ h⟩

end S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_nilpPoints_exists_subalgebra_fg_map_eq_of_locallyOfFiniteType (solution)

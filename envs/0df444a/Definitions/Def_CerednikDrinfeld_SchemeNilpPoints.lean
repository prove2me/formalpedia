-- Prove2me | Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
-- name    : CerednikDrinfeld_SchemeNilpPoints
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d76d370e-7fe6-5660-afd9-cb5d6fba2c2e
-- title:
--   Functor of points of a scheme over Spec 𝒪
-- statement:
--   Throughout, $\mathcal{O}$ is a commutative ring. The abbreviation `Scheme.specOver B`, for a commutative $\mathcal{O}$-algebra $B$, is the morphism $\operatorname{Spec} B \to \operatorname{Spec}\mathcal{O}$ obtained by applying $\operatorname{Spec}$ to the structure map $\mathcal{O} \to B$; the lemma `Scheme.specMap_algHom_comp_specOver` records that for an $\mathcal{O}$-algebra homomorphism $g : B \to B'$ the composite of $\operatorname{Spec}(g)$ followed by `Scheme.specOver B` is `Scheme.specOver B'`, i.e. $\operatorname{Spec}(g)$ is a morphism over $\operatorname{Spec}\mathcal{O}$. The principal definition, `Scheme.nilpPoints`, takes a scheme $X$ together with a morphism $f : X \to \operatorname{Spec}\mathcal{O}$ and produces a term of the project's type [`CerednikDrinfeld.FormalOmega.AlgFunctor 𝒪`](../def/CerednikDrinfeld_FormalUpperHalfPlaneCharts.html#L10): its value at a commutative $\mathcal{O}$-algebra $B$ is the type of pairs consisting of a morphism of schemes $\varphi : \operatorname{Spec} B \to X$ together with a proof that $\varphi$ followed by $f$ equals `Scheme.specOver B`, that is, the set of $\operatorname{Spec}\mathcal{O}$-morphisms $\operatorname{Spec} B \to X$; on an $\mathcal{O}$-algebra map $g : B \to B'$ it acts by sending $\varphi$ to $\operatorname{Spec}(g)$ followed by $\varphi$. The identity and composition axioms of `AlgFunctor` are fields of the resulting term, and `Scheme.nilpPoints_map_val` states that the underlying morphism of the transported point is indeed $\operatorname{Spec}(g)$ followed by $\varphi$. Despite the name, no nilpotency condition occurs in the definition: the object map is given on all $\mathcal{O}$-algebras, nilpotency of a chosen $\pi \in \mathcal{O}$ being imposed, where wanted, by the predicates `AlgFunctor.NatTrans.IsIsoOnNilp` and `IsMonoOnNilp`. Two further items are provided: `Scheme.nilpPoints.mapHom`, which turns a morphism $h : X \to Y$ with $h$ followed by $f_Y$ equal to $f_X$ into an `AlgFunctor.NatTrans` from `nilpPoints` of $f_X$ to `nilpPoints` of $f_Y$ by $\varphi \mapsto \varphi$ followed by $h$; and `Scheme.nilpPoints.specPoint`, the tautological $B$-point `Scheme.specOver B` of the functor attached to the identity morphism of $\operatorname{Spec}\mathcal{O}$.
--
--   **Relation to Mathlib.** Mathlib represents points of a scheme by Hom-sets in the category of schemes over a base; the content here is a repackaging of those Hom-sets as a term of the project's own `AlgFunctor` type, whose object map is indexed by bare types carrying `CommRing` and `Algebra 𝒪` instances, so that comparisons with functors defined directly on algebras can be expressed as `AlgFunctor.NatTrans`.
--
--   **Where it is used.** This is the scheme-side input for the Čerednik–Drinfeld comparison: with $X$ a scheme over $\mathcal{O}$ one compares `Scheme.nilpPoints` of its structure morphism with functors on $\mathcal{O}$-algebras built from the charts of Drinfeld's formal upper half plane and the Bruhat–Tits tree, the comparison being a natural transformation that is required to be bijective on algebras in which $\pi$ is nilpotent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_SchemeNilpPoints.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory CerednikDrinfeld.FormalOmega

variable {𝒪 : Type} [CommRing 𝒪]

abbrev Scheme.specOver (B : Type) [CommRing B] [Algebra 𝒪 B] : Spec (.of B) ⟶ Spec (.of 𝒪) :=
  Spec.map (CommRingCat.ofHom (algebraMap 𝒪 B))

theorem Scheme.specMap_algHom_comp_specOver {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B']
    [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Scheme.specOver (𝒪 := 𝒪) B = Scheme.specOver B' := by
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe,
    AlgHom.comp_algebraMap]

def Scheme.nilpPoints {X : Scheme.{0}} (f : X ⟶ Spec (.of 𝒪)) : AlgFunctor 𝒪 where
  obj B _ _ := { φ : Spec (.of B) ⟶ X // φ ≫ f = Scheme.specOver B }
  map g φ := ⟨Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1, by
    rw [Category.assoc, φ.2, Scheme.specMap_algHom_comp_specOver]⟩
  map_id φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ φ.1 = φ.1
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  map_comp g h φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom ((h.comp g).toRingHom)) ≫ φ.1 =
      Spec.map (CommRingCat.ofHom h.toRingHom) ≫ (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1)
    simp only [AlgHom.toRingHom_eq_coe]
    rw [AlgHom.comp_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

@[simp] theorem Scheme.nilpPoints_map_val {X : Scheme.{0}} (f : X ⟶ Spec (.of 𝒪)) {B : Type} [CommRing B]
    [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (g : B →ₐ[𝒪] B') (φ : (Scheme.nilpPoints f).obj B) :
    ((Scheme.nilpPoints f).map g φ).1 = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1 := rfl

def Scheme.nilpPoints.mapHom {X Y : Scheme.{0}} (fX : X ⟶ Spec (.of 𝒪)) (fY : Y ⟶ Spec (.of 𝒪)) (h : X ⟶ Y)
    (w : h ≫ fY = fX) : AlgFunctor.NatTrans (Scheme.nilpPoints fX) (Scheme.nilpPoints fY) where
  app B _ _ φ := ⟨φ.1 ≫ h, by rw [Category.assoc, w, φ.2]⟩
  naturality g φ := by
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (φ.1 ≫ h) = (Spec.map (CommRingCat.ofHom g.toRingHom) ≫ φ.1) ≫ h
    rw [Category.assoc]

def Scheme.nilpPoints.specPoint (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (Scheme.nilpPoints (𝟙 (Spec (CommRingCat.of 𝒪)))).obj B :=
  ⟨Scheme.specOver B, Category.comp_id _⟩

end AlgebraicGeometry

end



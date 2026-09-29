-- Prove2me | Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
-- name    : AlgebraicGeometry_RelativeGroupLawGrpObj
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/b11c92a4-94d6-5406-b86a-b5140e32c00a
-- title:
--   Relative group laws versus group objects over Spec R
-- statement:
--   Fix a commutative ring $R$, a scheme $A$ and a morphism $f \colon A \to \operatorname{Spec} R$. For a test morphism $t \colon T \to \operatorname{Spec} R$ the relative points are `SchemeHomOver t f`, the subtype of morphisms $x \colon T \to A$ with $x$ followed by $f$ equal to $t$; a `RelativeGroupLaw R f` is the project's structure carrying operations `mul`, `one`, `inv` on `SchemeHomOver t f` for every $t$, the fields `mul_assoc`, `one_mul`, `mul_one`, `inv_mul_cancel` (so each `pointGroup` is a group), and a single naturality field `mul_natural`: for $\psi \colon T' \to T$ with $\psi$ followed by $t$ equal to $t'$, precomposition by $\psi$ is multiplicative. This module builds the dictionary with Mathlib's group-object structure `GrpObj` on the object `Over.mk f` of the cartesian monoidal over-category of $\operatorname{Spec} R$. First, `overHomEquivSchemeHomOver` is the bijection sending a morphism $\varphi \colon T \to$ `Over.mk f` in the over-category to its underlying scheme morphism `φ.left`, viewed as a relative point over `T.hom`, with inverse given by `Over.homMk`; `overHomToSchemeHomOver` is correspondingly injective. Next, `relativeGroupLawOfGrpObj` transports the Hom-group structure of a group object through this bijection to a relative group law. Conversely, for a relative group law $G$, `yonedaGrpObjPresheaf` is the functor from the opposite over-category to `GrpCat` sending $T$ to `SchemeHomOver T.hom f` with its point group and a morphism to the precomposition homomorphism; `overMkRepresentableBy` exhibits its underlying set-valued functor as represented by `Over.mk f` via `overHomEquivSchemeHomOver`, and `grpObjOverMk` is the resulting group-object structure, a reducible definition to be activated locally. The unbundling lemmas record that under `grpObjOverMk` the bijection carries $\cdot$, $1$, $(-)^{-1}$ to $G$'s operations, and identify $\mu$, $\eta$, $\iota$ with the law evaluated at the projections, the unit object and the identity; further lemmas show the round trip `relativeGroupLawOfGrpObj` after `grpObjOverMk` returns $G$ on all three operations. Finally, `IsCommMonObj (Over.mk f)` is shown equivalent to pointwise commutativity of the associated relative group law, in both directions of the dictionary, and over a field $K$ with $f$ proper and geometrically integral every relative group law on $f$ is commutative on all relative points.
--
--   **Relation to Mathlib.** `GrpObj`, `IsCommMonObj`, `GrpObj.ofRepresentableBy`, `yonedaGrpObjIsoOfRepresentableBy` and the commutativity of proper geometrically integral group objects are Mathlib's; `RelativeGroupLaw` and the relative-point subtype `SchemeHomOver` are the project's own elementwise presentation, and this module is the translation between the two.
--
--   **Where it is used.** The declarations belong to the Néron-model and good-reduction-of-Jacobians layer, where group laws are produced pointwise on relative points and must be turned into group-scheme structures (and conversely) before the smoothness, separatedness and unique-extension properties of the Néron model bundle are used.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativeGroupLawGrpObj.lean

import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory NeronModelInfra

open scoped CategoryTheory.MonObj

namespace GoodReductionJacobian

def overHomEquivSchemeHomOver {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R)) :
    (T ⟶ Over.mk f) ≃ SchemeHomOver T.hom f where
  toFun φ := ⟨φ.left, by simpa using Over.w φ⟩
  invFun x := Over.homMk x.1 (by simpa using x.2)
  left_inv φ := Over.OverMorphism.ext (by simp)
  right_inv x := Subtype.ext (by simp)

@[simp]
theorem overHomEquivSchemeHomOver_apply_coe {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R))
    (φ : T ⟶ Over.mk f) : (overHomEquivSchemeHomOver T f φ).1 = φ.left :=
  rfl

@[simp]
theorem overHomEquivSchemeHomOver_symm_apply_left {R : Type u} [CommRing R] {A : Scheme.{u}}
    (T : Over (Spec (CommRingCat.of R))) (f : A ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver T.hom f) : ((overHomEquivSchemeHomOver T f).symm x).left = x.1 :=
  rfl

theorem overHomEquivSchemeHomOver_mk_apply {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (h : Over.mk t ⟶ Over.mk f) :
    overHomEquivSchemeHomOver (Over.mk t) f h = overHomToSchemeHomOver h :=
  rfl

theorem overHomEquivSchemeHomOver_mk_symm_apply {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (overHomEquivSchemeHomOver (Over.mk t) f).symm x = schemeHomOverToOverHom x :=
  rfl

theorem overHomToSchemeHomOver_injective {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} :
    Function.Injective
      (overHomToSchemeHomOver : (Over.mk t ⟶ Over.mk f) → SchemeHomOver t f) := by
  intro a b h
  have h2 := congrArg schemeHomOverToOverHom h
  simpa using h2

def relativeGroupLawOfGrpObj (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)] : RelativeGroupLaw R f where
  mul {T} t x y :=
    overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y)
  one {T} t := overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f)
  inv {T} t x := overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹
  mul_assoc {T} t x y z := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_assoc]
  one_mul {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [one_mul, overHomToSchemeHomOver_schemeHomOverToOverHom]
  mul_one {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_one, overHomToSchemeHomOver_schemeHomOverToOverHom]
  inv_mul_cancel {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    have key : ∀ z : SchemeHomOver t f,
        schemeHomOverComp ψ hψ z =
          overHomToSchemeHomOver
            ((Over.homMk ψ (by simpa using hψ) : Over.mk t' ⟶ Over.mk t) ≫
              schemeHomOverToOverHom z) := by
      intro z
      apply Subtype.ext
      simp
    rw [key, key, key]
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [MonObj.comp_mul]

@[simp]
theorem relativeGroupLawOfGrpObj_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).mul t x y =
      overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (relativeGroupLawOfGrpObj R f).one t =
      overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) :=
  rfl

@[simp]
theorem relativeGroupLawOfGrpObj_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).inv t x =
      overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹ :=
  rfl

def RelativeGroupLaw.yonedaGrpObjPresheaf {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ GrpCat.{u} where
  obj T := @GrpCat.of (SchemeHomOver T.unop.hom f) (G.pointGroup T.unop.hom)
  map {S T} χ :=
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    GrpCat.ofHom
      { toFun := fun x => schemeHomOverComp χ.unop.left (Over.w χ.unop) x
        map_one' := G.one_natural _ _ _ _
        map_mul' := fun x y => G.mul_natural _ _ _ _ x y }
  map_id S := by
    letI := G.pointGroup S.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp
  map_comp {S T U} χ χ' := by
    letI := G.pointGroup S.unop.hom
    letI := G.pointGroup T.unop.hom
    letI := G.pointGroup U.unop.hom
    refine GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext ?_)
    simp

def RelativeGroupLaw.overMkRepresentableBy {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (G.yonedaGrpObjPresheaf ⋙ forget GrpCat).RepresentableBy (Over.mk f) where
  homEquiv {T} := overHomEquivSchemeHomOver T f
  homEquiv_comp _ _ := Subtype.ext rfl

@[reducible]
def RelativeGroupLaw.grpObjOverMk {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) : GrpObj (Over.mk f) :=
  GrpObj.ofRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf G.overMkRepresentableBy

theorem RelativeGroupLaw.overHomToSchemeHomOver_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a b : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (a * b) =
      G.mul t (overHomToSchemeHomOver a) (overHomToSchemeHomOver b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_mul a b

theorem RelativeGroupLaw.overHomToSchemeHomOver_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f) = G.one t := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom.map_one

theorem RelativeGroupLaw.overHomToSchemeHomOver_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (a : Over.mk t ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomToSchemeHomOver a⁻¹ = G.inv t (overHomToSchemeHomOver a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup t
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op (Over.mk t))).hom a

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_mul {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) (a b : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (a * b) =
      G.mul T.hom (overHomEquivSchemeHomOver T f a) (overHomEquivSchemeHomOver T f b) := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_mul a b

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_one {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f (1 : T ⟶ Over.mk f) = G.one T.hom := by
  letI := G.grpObjOverMk
  exact ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom.map_one

theorem RelativeGroupLaw.overHomEquivSchemeHomOver_inv {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (T : Over (Spec (CommRingCat.of R))) (a : T ⟶ Over.mk f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver T f a⁻¹ = G.inv T.hom (overHomEquivSchemeHomOver T f a) := by
  letI := G.grpObjOverMk
  letI := G.pointGroup T.hom
  exact map_inv ((yonedaGrpObjIsoOfRepresentableBy (Over.mk f) G.yonedaGrpObjPresheaf
    G.overMkRepresentableBy).hom.app (Opposite.op T)).hom a

theorem RelativeGroupLaw.grpObjOverMk_mul_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f μ[Over.mk f] =
      G.mul (Over.mk f ⊗ Over.mk f).hom
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (fst (Over.mk f) (Over.mk f)))
        (overHomEquivSchemeHomOver (Over.mk f ⊗ Over.mk f) f (snd (Over.mk f) (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [MonObj.mul_eq_mul]
  exact G.overHomEquivSchemeHomOver_mul (Over.mk f ⊗ Over.mk f)
    (fst (Over.mk f) (Over.mk f)) (snd (Over.mk f) (Over.mk f))

theorem RelativeGroupLaw.grpObjOverMk_one_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (𝟙_ (Over (Spec (CommRingCat.of R)))) f η[Over.mk f] =
      G.one (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := by
  letI := G.grpObjOverMk
  rw [MonObj.one_eq_one]
  exact G.overHomEquivSchemeHomOver_one (𝟙_ (Over (Spec (CommRingCat.of R))))

theorem RelativeGroupLaw.grpObjOverMk_inv_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    letI := G.grpObjOverMk
    overHomEquivSchemeHomOver (Over.mk f) f ι[Over.mk f] =
      G.inv (Over.mk f).hom (overHomEquivSchemeHomOver (Over.mk f) f (𝟙 (Over.mk f))) := by
  letI := G.grpObjOverMk
  rw [GrpObj.inv_eq_inv]
  exact G.overHomEquivSchemeHomOver_inv (Over.mk f) (𝟙 (Over.mk f))

theorem relativeGroupLawOfGrpObj_grpObjOverMk_mul {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).mul t x y = G.mul t x y := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_mul t (schemeHomOverToOverHom x)
    (schemeHomOverToOverHom y)
  simpa using h

theorem relativeGroupLawOfGrpObj_grpObjOverMk_one {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).one t = G.one t := by
  letI := G.grpObjOverMk
  exact G.overHomToSchemeHomOver_one t

theorem relativeGroupLawOfGrpObj_grpObjOverMk_inv {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    letI := G.grpObjOverMk
    (relativeGroupLawOfGrpObj R f).inv t x = G.inv t x := by
  letI := G.grpObjOverMk
  have h := G.overHomToSchemeHomOver_inv t (schemeHomOverToOverHom x)
  simpa using h

theorem relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (h : IsCommMonObj (Over.mk f)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver t f) :
    (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x := by
  haveI := (isCommMonObj_iff_isMulCommutative (Over.mk f)).mp h (Over.mk t)
  show overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y) =
    overHomToSchemeHomOver (schemeHomOverToOverHom y * schemeHomOverToOverHom x)
  rw [mul_comm]

theorem isCommMonObj_of_relativeGroupLawOfGrpObj_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)]
    (hc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x) :
    IsCommMonObj (Over.mk f) := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro X
  constructor
  constructor
  intro a b
  have h := hc X.hom (overHomToSchemeHomOver a) (overHomToSchemeHomOver b)
  show a * b = b * a
  simp only [relativeGroupLawOfGrpObj, schemeHomOverToOverHom_overHomToSchemeHomOver] at h
  exact overHomToSchemeHomOver_injective h

theorem isCommMonObj_iff_relativeGroupLawOfGrpObj_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} [GrpObj (Over.mk f)] :
    IsCommMonObj (Over.mk f) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        (relativeGroupLawOfGrpObj R f).mul t x y = (relativeGroupLawOfGrpObj R f).mul t y x :=
  ⟨fun h _ _ x y => relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h _ x y,
    fun hc => isCommMonObj_of_relativeGroupLawOfGrpObj_comm fun t x y => hc t x y⟩

theorem RelativeGroupLaw.isCommMonObj_grpObjOverMk_iff_mul_comm {R : Type u} [CommRing R]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    (letI := G.grpObjOverMk; IsCommMonObj (Over.mk f)) ↔
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
        G.mul t x y = G.mul t y x := by
  letI := G.grpObjOverMk
  constructor
  · intro h T t x y
    rw [← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t x y,
      ← relativeGroupLawOfGrpObj_grpObjOverMk_mul G t y x]
    exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h t x y
  · intro hc
    rw [isCommMonObj_iff_isMulCommutative]
    intro X
    constructor
    constructor
    intro a b
    apply (overHomEquivSchemeHomOver X f).injective
    rw [G.overHomEquivSchemeHomOver_mul X a b, G.overHomEquivSchemeHomOver_mul X b a]
    exact hc X.hom _ _

theorem RelativeGroupLaw.mul_comm_of_isProper_of_geometricallyIntegral {K : Type u} [Field K]
    {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)} [IsProper f] [GeometricallyIntegral f]
    (G : RelativeGroupLaw K f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t f) :
    G.mul t x y = G.mul t y x := by
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  haveI : GeometricallyIntegral (Over.mk f).hom := ‹GeometricallyIntegral f›
  letI := G.grpObjOverMk
  haveI hcomm : IsCommMonObj (Over.mk f) :=
    isCommMonObj_of_isProper_of_geometricallyIntegral (Over.mk f)
  exact G.isCommMonObj_grpObjOverMk_iff_mul_comm.mp hcomm t x y

end GoodReductionJacobian



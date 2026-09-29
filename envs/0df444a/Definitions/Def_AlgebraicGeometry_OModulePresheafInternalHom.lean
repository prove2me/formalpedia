-- Prove2me | Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom
-- name    : AlgebraicGeometry_OModulePresheafInternalHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7cdb32b6-a5fa-5c22-8627-f5fc4098b406
-- title:
--   Internal Hom of module presheaves on affine opens
-- statement:
--   Fix a commutative ring $R$, a scheme $V$, a morphism $\pi\colon V\to\operatorname{Spec} R$, and two `OModulePresheaf` data $F,G$ over $\pi$ (for each open $U\subseteq V$ a module $F(U)$ over $R$ and over $\Gamma(V,U)$, compatibly, together with $R$-linear restriction maps semilinear for restriction of functions). For an open $U$, `AffBelow U` is the type of affine opens $W$ of $V$ with $W\le U$, and `HomPi F G U` is the product $\prod_{W}\operatorname{Hom}_R(F(W),G(W))$ over such $W$. The $R$-submodule `homSub F G U` of this product consists of the families $(\varphi_W)$ satisfying two conditions, recorded again in `mem_homSub_iff`: each $\varphi_W$ is $\Gamma(V,W)$-semilinear, i.e. $\varphi_W(a\cdot x)=a\cdot\varphi_W(x)$ for $a\in\Gamma(V,W)$, and the family commutes with restriction, $\varphi_W\circ F.\mathrm{res} = G.\mathrm{res}\circ\varphi_{W'}$ for affine $W\le W'\le U$. On `homSub F G U` a $\Gamma(V,U)$-action is defined componentwise by $(a\cdot\varphi)_W(x) = (a|_W)\cdot\varphi_W(x)$ (`sectionsSMul`, `smulSections`, `moduleSectionsHomSub`), and for $U\le U'$ the map `homRes` restricts a family by keeping only the components indexed by affine opens inside $U$. The definition `internalHom F G` assembles these into a new `OModulePresheaf` over $\pi$, with sections `homSub F G U`, the above $\Gamma(V,U)$-module structure, the scalar tower over $R$ coming from $\pi$, and `homRes` as restriction. Auxiliary results give the evaluation map `internalHom.eval`, an $R$-linear map from sections over $U$ to $\operatorname{Hom}_R(F(W),G(W))$ for an affine $W\le U$, and mutually inverse maps `toAffHom`, `ofAffHom` identifying the sections of `internalHom F G` over $\top$ with the affine-open morphisms `AffHom F G`. A helper, `smul_comm_sections`, records that the $R$- and $\Gamma(V,W)$-actions on $G(W)$ commute.
--
--   **Relation to Mathlib.** Built on the project's own `OModulePresheaf` datum, which records modules and restrictions indexed by the opens of a scheme rather than using Mathlib's sheaves of modules; the internal Hom constructed here, with sections indexed only by the affine opens contained in a given open, is likewise the project's own.
--
--   **Where it is used.** This supplies the vocabulary of sheaf Hom for the algebraic-geometry layer of the formalisation, where coherence, quasi-coherence and Čech cohomology of module presheaves are formulated on affine opens; the identification of global sections with affine-open morphisms is what makes $\mathcal{H}om(F,G)$ usable for computing $\operatorname{Hom}(F,G)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_OModulePresheafInternalHom.lean

import Mathlib

import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)

abbrev AffBelow (U : V.Opens) : Type u := {W : V.affineOpens // W.1 ≤ U}

abbrev HomPi (U : V.Opens) : Type u := ∀ W : AffBelow U, F.obj W.1.1 →ₗ[R] G.obj W.1.1

def homSub (U : V.Opens) : Submodule R (HomPi F G U) where
  carrier := {φ | (∀ (W : AffBelow U) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), φ W (a • x) = a • φ W x) ∧
    ∀ (W W' : AffBelow U) (h : W.1.1 ≤ W'.1.1) (x : F.obj W'.1.1), φ W (F.res h x) = G.res h (φ W' x)}
  add_mem' {φ ψ} hφ hψ := by
    refine ⟨fun W a x => ?_, fun W W' h x => ?_⟩
    · simp only [Pi.add_apply, LinearMap.add_apply, hφ.1, hψ.1, smul_add]
    · simp only [Pi.add_apply, LinearMap.add_apply, hφ.2 W W' h, hψ.2 W W' h, map_add]
  zero_mem' := ⟨fun W a x => by simp, fun W W' h x => by simp⟩
  smul_mem' r {φ} hφ := by
    refine ⟨fun W a x => ?_, fun W W' h x => ?_⟩
    · simp only [Pi.smul_apply, LinearMap.smul_apply, hφ.1]
      letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1
      rw [← algebraMap_smul (A := Γ(V, W.1.1)) r (a • φ W x), ← algebraMap_smul (A := Γ(V, W.1.1)) r (φ W x),
        smul_smul, smul_smul, mul_comm]
    · simp only [Pi.smul_apply, LinearMap.smul_apply, hφ.2 W W' h, map_smul]

theorem mem_homSub_iff (U : V.Opens) (φ : HomPi F G U) :
    φ ∈ homSub F G U ↔ (∀ (W : AffBelow U) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), φ W (a • x) = a • φ W x) ∧
      ∀ (W W' : AffBelow U) (h : W.1.1 ≤ W'.1.1) (x : F.obj W'.1.1), φ W (F.res h x) = G.res h (φ W' x) :=
  Iff.rfl

theorem smul_comm_sections (W : V.Opens) (c : R) (b : Γ(V, W)) (y : G.obj W) : c • (b • y) = b • (c • y) := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
  rw [← algebraMap_smul (A := Γ(V, W)) c (b • y), ← algebraMap_smul (A := Γ(V, W)) c y, smul_smul, smul_smul,
    mul_comm]

def sectionsSMul (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) : homSub F G U :=
  ⟨fun W =>
    { toFun := fun x => (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x
      map_add' := fun x y => by simp only [map_add, smul_add]
      map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm_sections] }, by
    refine ⟨fun W b x => ?_, fun W W' h x => ?_⟩
    · change (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W (b • x) =
        b • ((V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x)
      rw [φ.2.1, smul_smul, smul_smul, mul_comm]
    · change (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W (F.res h x) =
        G.res h ((V.presheaf.map (homOfLE W'.2).op).hom a • φ.1 W' x)
      rw [φ.2.2 W W' h, G.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
      rfl⟩

theorem sectionsSMul_apply (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) (W : AffBelow U) (x : F.obj W.1.1) :
    (sectionsSMul F G U a φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl

instance smulSections (U : V.Opens) : SMul Γ(V, U) (homSub F G U) := ⟨sectionsSMul F G U⟩

theorem sections_smul_apply (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) (W : AffBelow U) (x : F.obj W.1.1) :
    (a • φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl

instance moduleSectionsHomSub (U : V.Opens) : Module Γ(V, U) (homSub F G U) where
  one_smul φ := by
    ext W x; simp only [sections_smul_apply, map_one, one_smul]
  mul_smul a b φ := by
    ext W x; simp only [sections_smul_apply, map_mul, mul_smul]
  smul_zero a := by
    ext W x
    simp only [sections_smul_apply, Submodule.coe_zero, Pi.zero_apply, LinearMap.zero_apply, smul_zero]
  smul_add a φ ψ := by
    ext W x
    simp only [sections_smul_apply, Submodule.coe_add, Pi.add_apply, LinearMap.add_apply, smul_add]
  add_smul a b φ := by
    ext W x
    simp only [sections_smul_apply, map_add, add_smul, Submodule.coe_add, Pi.add_apply, LinearMap.add_apply]
  zero_smul φ := by
    ext W x
    simp only [sections_smul_apply, map_zero, zero_smul, Submodule.coe_zero, Pi.zero_apply, LinearMap.zero_apply]

def homRes {U U' : V.Opens} (h : U ≤ U') : homSub F G U' →ₗ[R] homSub F G U where
  toFun φ := ⟨fun W => φ.1 ⟨W.1, W.2.trans h⟩, ⟨fun W a x => φ.2.1 ⟨W.1, W.2.trans h⟩ a x,
    fun W W' hW x => φ.2.2 ⟨W.1, W.2.trans h⟩ ⟨W'.1, W'.2.trans h⟩ hW x⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem homRes_apply {U U' : V.Opens} (h : U ≤ U') (φ : homSub F G U') (W : AffBelow U) :
    (homRes F G h φ).1 W = φ.1 ⟨W.1, W.2.trans h⟩ := rfl

def internalHom : OModulePresheaf π where
  obj U := homSub F G U
  module U := inferInstance
  moduleSections U := moduleSectionsHomSub F G U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    refine ⟨fun r a φ => ?_⟩
    ext W x
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1
    have hr : (V.presheaf.map (homOfLE W.2).op).hom (algebraMap R Γ(V, U) r) = algebraMap R Γ(V, W.1.1) r :=
      (Scheme.TwoAffineOpenCover.restrictAlgHom π W.2).commutes r
    simp only [sections_smul_apply, Algebra.smul_def, mul_smul, Submodule.coe_smul, Pi.smul_apply,
      LinearMap.smul_apply, hr, algebraMap_smul]
  res h := homRes F G h
  res_smul h a φ := by
    ext W x
    simp only [homRes_apply, sections_smul_apply]
    congr 1
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl
  res_refl U := rfl
  res_comp h h' := rfl

theorem internalHom_obj (U : V.Opens) : (internalHom F G).obj U = homSub F G U := rfl

theorem internalHom_res_apply {U U' : V.Opens} (h : U ≤ U') (φ : (internalHom F G).obj U') (W : AffBelow U) :
    ((internalHom F G).res h φ).1 W = φ.1 ⟨W.1, W.2.trans h⟩ := rfl

theorem internalHom_smul_apply (U : V.Opens) (a : Γ(V, U)) (φ : (internalHom F G).obj U) (W : AffBelow U)
    (x : F.obj W.1.1) : (a • φ).1 W x = (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x := rfl

namespace internalHom

def eval {U : V.Opens} (W : V.affineOpens) (hW : W.1 ≤ U) : (internalHom F G).obj U →ₗ[R] (F.obj W.1 →ₗ[R] G.obj W.1) where
  toFun φ := φ.1 ⟨W, hW⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem eval_apply {U : V.Opens} (W : V.affineOpens) (hW : W.1 ≤ U) (φ : (internalHom F G).obj U) (x : F.obj W.1) :
    eval F G W hW φ x = φ.1 ⟨W, hW⟩ x := rfl

def toAffHom (φ : (internalHom F G).obj ⊤) : AffHom F G where
  app W := φ.1 ⟨W, le_top⟩
  app_smul W a x := φ.2.1 ⟨W, le_top⟩ a x
  naturality {W W'} h := LinearMap.ext fun x => φ.2.2 ⟨W, le_top⟩ ⟨W', le_top⟩ h x

def ofAffHom (ψ : AffHom F G) : (internalHom F G).obj ⊤ :=
  ⟨fun W => ψ.app W.1, ⟨fun W a x => ψ.app_smul W.1 a x, fun _ _ h x => ψ.naturality_apply h x⟩⟩

@[simp] theorem toAffHom_app (φ : (internalHom F G).obj ⊤) (W : V.affineOpens) (x : F.obj W.1) :
    (toAffHom F G φ).app W x = φ.1 ⟨W, le_top⟩ x := rfl

@[simp] theorem ofAffHom_apply (ψ : AffHom F G) (W : AffBelow (⊤ : V.Opens)) (x : F.obj W.1.1) :
    (ofAffHom F G ψ).1 W x = ψ.app W.1 x := rfl

theorem toAffHom_ofAffHom (ψ : AffHom F G) : toAffHom F G (ofAffHom F G ψ) = ψ := rfl

theorem ofAffHom_toAffHom (φ : (internalHom F G).obj ⊤) : ofAffHom F G (toAffHom F G φ) = φ := rfl

end internalHom

end OModulePresheaf

end AlgebraicGeometry

end



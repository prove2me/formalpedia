-- Prove2me | Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
-- name    : AlgebraicGeometry_TwoAffineOpenCover
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e9c17f1e-2279-50a9-86ea-5504e39573b1
-- title:
--   Two-affine open covers of schemes and their Čech data
-- statement:
--   For a scheme $X$, `Scheme.TwoAffineOpenCover X` is a structure consisting of two opens $U_0,U_1\subseteq X$ together with proofs, carried as fields, that $U_0$ and $U_1$ are affine, that $U_0\sqcup U_1=\top$, and that $U_0\sqcap U_1$ is affine; affineness of the overlap is thus part of the data rather than deduced from separatedness. Fix a commutative ring $R$ and a morphism $c\colon X\to\operatorname{Spec}R$ (where `specMap R A` denotes $\operatorname{Spec}$ applied to the structure map $R\to A$ of an $R$-algebra $A$). For an open $U$, `algebraOfHom c U` is the $R$-algebra structure on $\Gamma(X,U)$ obtained from the inverse of the canonical isomorphism $R\cong\Gamma(\operatorname{Spec}R,\mathcal O)$ followed by $c$ on sections over $U$ (its structure map is recorded pointwise by `algebraMap_algebraOfHom`), and `restrictAlgHom c h` promotes the restriction map $\Gamma(X,U)\to\Gamma(X,V)$, for $V\le U$, to an $R$-algebra homomorphism. From a two-affine open cover $\mathcal V$ and $c$, `cover` builds a [`TwoChartCech.Cover`](../def/AlgebraicGeometry_TwoChartCech.html#L17) over $R$ with $A_0=\Gamma(X,U_0)$, $A_1=\Gamma(X,U_1)$, $A_{01}=\Gamma(X,U_0\cap U_1)$ and $\rho_0,\rho_1$ the two restrictions; short identities identify these components and evaluate $\rho_0,\rho_1$ as presheaf restriction. On this cover, `structureSheafSections` is the sections data with modules $A_0,A_1,A_{01}$ and $r_0=\rho_0$, $r_1=\rho_1$, while `lineBundleSections t`, for a unit $t\in\Gamma(X,U_0\cap U_1)^\times$, twists $r_1$ by multiplication by $t$; their $H^0$ is the kernel of $(s_0,s_1)\mapsto t\,s_1|_{U_0\cap U_1}-s_0|_{U_0\cap U_1}$. The transitivity identity `res_res` for restrictions, `restrict_mem_H0` and the $R$-linear map `toH0`, $s\mapsto (s|_{U_0},s|_{U_1})$, record that global sections land in the degree-zero Čech group of the structure sheaf data. Finally, for an $R$-algebra $A$, `isAffineHom_fst` states that the first projection of the pullback of $c$ along `specMap R A` is an affine morphism, and `pullback` transports $\mathcal V$ to a two-affine open cover of $X\times_{\operatorname{Spec}R}\operatorname{Spec}A$ whose two opens are the preimages of $U_0$ and $U_1$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient notions used here — `IsAffineOpen`, `IsAffineHom` and its stability under base change, `Spec.map`, pullbacks of schemes — and has indexed (affine) open covers; the two-chart structure, with affineness of the intersection as a field, and its bridge to the module-level two-chart Čech formalism are the project's own.
--
--   **Where it is used.** These definitions are the scheme-theoretic interface to the project's two-chart Čech formalism: a cover by two affine opens with affine overlap turns the cohomology of the structure sheaf and of line bundles into the kernel and cokernel of a single map of modules, in a form stable under base change $R\to A$, as needed for computations of $H^0$ and $H^1$ on curves over a base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean

import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Affine

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite

structure Scheme.TwoAffineOpenCover (X : Scheme.{u}) where

  U0 : X.Opens

  U1 : X.Opens
  isAffineOpen_U0 : IsAffineOpen U0
  isAffineOpen_U1 : IsAffineOpen U1
  sup_eq_top : U0 ⊔ U1 = ⊤
  isAffineOpen_inf : IsAffineOpen (U0 ⊓ U1)

namespace Scheme.TwoAffineOpenCover

abbrev specMap (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] : Spec (.of A) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[reducible] def algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.toAlgebra

theorem algebraMap_algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) (r : R) :
    (algebraOfHom c U).algebraMap r = (c.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) :=
  rfl

def restrictAlgHom (c : X ⟶ Spec (.of R)) {U V : X.Opens} (h : V ≤ U) :
    letI := algebraOfHom c U; letI := algebraOfHom c V
    Γ(X, U) →ₐ[R] Γ(X, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => by
      change (c.appLE ⊤ U le_top ≫ X.presheaf.map (homOfLE h).op).hom _ = (c.appLE ⊤ V le_top).hom _
      rw [Scheme.Hom.appLE_map] }

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

def cover : TwoChartCech.Cover.{u, u} R :=
  letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1; letI := algebraOfHom c (𝒱.U0 ⊓ 𝒱.U1)
  { A0 := Γ(X, 𝒱.U0)
    A1 := Γ(X, 𝒱.U1)
    A01 := Γ(X, 𝒱.U0 ⊓ 𝒱.U1)
    ρ0 := restrictAlgHom c inf_le_left
    ρ1 := restrictAlgHom c inf_le_right }

theorem cover_A0 : (𝒱.cover c).A0 = Γ(X, 𝒱.U0) := rfl
theorem cover_A1 : (𝒱.cover c).A1 = Γ(X, 𝒱.U1) := rfl
theorem cover_A01 : (𝒱.cover c).A01 = Γ(X, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem cover_ρ0_apply (x : (𝒱.cover c).A0) :
    (𝒱.cover c).ρ0 x = (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom x := rfl
theorem cover_ρ1_apply (x : (𝒱.cover c).A1) :
    (𝒱.cover c).ρ1 x = (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom x := rfl

abbrev structureSheafSections : TwoChartCech.Sections (𝒱.cover c) := (𝒱.cover c).structureSheaf

abbrev lineBundleSections (t : (𝒱.cover c).A01ˣ) : TwoChartCech.Sections (𝒱.cover c) :=
  (𝒱.cover c).lineBundle t

omit [CommRing R] in
theorem res_res {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem restrict_mem_H0 (s : Γ(X, ⊤)) :
    ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
      (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
      ∈ (𝒱.structureSheafSections c).H0 := by
  refine (TwoChartCech.Sections.mem_H0_iff _ _).mpr ?_
  change (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s)
    = ((1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)ˣ) : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) •
      (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom
        ((X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
  rw [Units.val_one, one_smul, res_res, res_res]

def toH0 : letI := algebraOfHom c ⊤; Γ(X, ⊤) →ₗ[R] (𝒱.structureSheafSections c).H0 :=
  letI := algebraOfHom c ⊤; letI := algebraOfHom c 𝒱.U0; letI := algebraOfHom c 𝒱.U1
  LinearMap.codRestrict _
    (((restrictAlgHom c (le_top : 𝒱.U0 ≤ ⊤)).toLinearMap).prod
      ((restrictAlgHom c (le_top : 𝒱.U1 ≤ ⊤)).toLinearMap))
    (fun s => 𝒱.restrict_mem_H0 c s)

theorem toH0_apply_coe (s : Γ(X, ⊤)) :
    letI := algebraOfHom c ⊤
    ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) =
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
        (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s) := rfl

section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]

theorem isAffineHom_fst : IsAffineHom (Limits.pullback.fst c (specMap R A)) :=
  MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance

def pullback : (Limits.pullback c (specMap R A)).TwoAffineOpenCover :=
  haveI := isAffineHom_fst c A
  { U0 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0
    U1 := (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1
    isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage _
    isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage _
    sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
    isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage _ }

@[simp] theorem pullback_U0 : (𝒱.pullback c A).U0 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0 := rfl
@[simp] theorem pullback_U1 : (𝒱.pullback c A).U1 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1 := rfl

end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end



-- Prove2me | Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
-- name    : AlgebraicGeometry_ModulesProjPresentation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/2331b95d-c7ae-50f1-a3a8-968a2627e107
-- title:
--   Presentations of module sheaves by morphisms to projective space
-- statement:
--   Throughout, $R$ is a commutative ring, $X$ a scheme, and projective space $\mathbb P^N_R$ is $\operatorname{Proj}$ of the total-degree grading on $R[x_0,\dots,x_N]$, with structure morphism `ProjSpace.π R N`, standard charts $D_+(x_i)$ and degree-zero ratios `ProjSpace.ratio R N i j` $= x_j/x_i$.
--
--   The structure `ProjPresentation M f N`, for a sheaf of modules $M$ on $X$ and a morphism $f \colon X \to \operatorname{Spec} R$, carries: a family $\sigma \colon \{0,\dots,N\} \to \Gamma(M,\top)$ of global sections of $M$; a morphism `toProj` $\colon X \to \mathbb P^N_R$; the equation that `toProj` followed by `ProjSpace.π R N` is $f$; the field `frame`, asserting that for every index $i$ and every open $V \le$ `toProj`$^{-1}(D_+(x_i))$ the scalar-multiplication map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective; and the field `app_ratio_smul`, asserting that on $U_i :=$ `toProj`$^{-1}(D_+(x_i))$ the pullback under `toProj` of the section of the structure sheaf of $\mathbb P^N_R$ over $D_+(x_i)$ determined by $x_j/x_i$ (via `Proj.awayToSection`) multiplies $\sigma_i|_{U_i}$ into $\sigma_j|_{U_i}$, for all $i,j$. So the two geometric conditions — that $\sigma_i$ frames $M$ over every open inside the $i$-th chart preimage, and that pulled-back coordinate ratios are ratios of the $\sigma$'s — are fields of the structure rather than consequences.
--
--   Two predicates are then defined: `FiniteBySections M f` asserts the existence of some $N$ and some such presentation whose `toProj` is finite, and `ClosedImmersionBySections M f` the existence of one whose `toProj` is a closed immersion.
--
--   The remaining declarations supply the case $N = 0$. `awayZeroEval` is the ring homomorphism from the degree-zero homogeneous localisation of $R[x_0]$ away from $x_0$ to $R$ induced by $x_0 \mapsto 1$; `pointOfProjZero` is the resulting $R$-point $\operatorname{Spec} R \to \mathbb P^0_R$, factoring through the chart $D_+(x_0)$. It is shown to be a section of `ProjSpace.π R 0` (the composite is the identity of $\operatorname{Spec} R$) and to have the whole of $\operatorname{Spec} R$ as preimage of $D_+(x_0)$. Finally `unitOne` is the global section $1$ of the unit sheaf of modules on $X$, and `ProjPresentation.unitSpec` is the presentation of the unit sheaf of modules on $\operatorname{Spec} R$ over the identity morphism with $N = 0$, all $\sigma_i$ equal to $1$ and `toProj` $=$ `pointOfProjZero`.
--
--   **Relation to Mathlib.** Mathlib supplies $\operatorname{Proj}$ of a graded ring with its charts `Proj.awayι`, `Proj.basicOpen` and `Proj.awayToSection`, the unit sheaf of modules `SheafOfModules.unit`, and the classes `IsFinite` and `IsClosedImmersion`; the structure `ProjPresentation` and the predicates `FiniteBySections` and `ClosedImmersionBySections` are the project's own vocabulary.
--
--   **Where it is used.** These notions form part of the project's projective-geometry layer, alongside the data structures `ChowDatum` and `ChowDatumProj` for proper schemes admitting a proper cover that closed-immerses into a product of projective spaces over $\operatorname{Spec} R$; `FiniteBySections` is the form in which a family of global sections is used to produce a finite morphism to projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesProjPresentation.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

structure ProjPresentation (M : X.Modules) (f : X ⟶ Spec (.of R)) (N : ℕ) where

  σ : Fin (N + 1) → Γ(M, ⊤)

  toProj : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

  toProj_π : toProj ≫ ProjSpace.π R N = f

  frame : ∀ (i : Fin (N + 1)) (V : X.Opens),
    V ≤ toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) →
    Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))

  app_ratio_smul : ∀ i j : Fin (N + 1),
    (toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
        (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) •
        M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ i)
      = M.presheaf.map (homOfLE (le_top : toProj ⁻¹ᵁ
          Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i) ≤ ⊤)).op (σ j)

def FiniteBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsFinite 𝔓.toProj

def ClosedImmersionBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsClosedImmersion 𝔓.toProj

end Scheme.Modules

namespace ProjSpace

variable (R : Type u) [CommRing R]

def awayZeroEval :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R) →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away (X 0 : MvPolynomial (Fin 1) R))
      (X 0 : MvPolynomial (Fin 1) R)
      (g := (MvPolynomial.aeval (R := R) (fun _ : Fin 1 => (1 : R))).toRingHom)
      (by simp)).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R))
      (Localization.Away (X 0 : MvPolynomial (Fin 1) R)))

def pointOfProjZero : Spec (.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R) :=
  Spec.map (CommRingCat.ofHom (awayZeroEval R)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos

theorem pointOfProjZero_π : pointOfProjZero R ≫ π R 0 = 𝟙 _ := by
  rw [pointOfProjZero, Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r : 2
  change awayZeroEval R (algebraMap R _ r) = r
  simp only [awayZeroEval, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply, val_algebraMap, IsLocalization.Away.lift_eq]
  simp

theorem pointOfProjZero_preimage_basicOpen :
    pointOfProjZero R ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
  rw [pointOfProjZero, Scheme.Hom.comp_preimage]
  have : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
    rw [← Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos]
    exact Scheme.Hom.preimage_opensRange _
  rw [this]
  rfl

end ProjSpace

variable (R : Type u) [CommRing R]

def Scheme.Modules.unitOne (X : Scheme.{u}) :
    Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), (⊤ : X.Opens)) :=
  (show Γ(X, ⊤) from 1)

def Scheme.Modules.ProjPresentation.unitSpec :
    Scheme.Modules.ProjPresentation (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)
      (𝟙 (Spec (.of R))) 0 where
  σ := fun _ => Scheme.Modules.unitOne (Spec (.of R))
  toProj := ProjSpace.pointOfProjZero R
  toProj_π := ProjSpace.pointOfProjZero_π R
  frame := fun i V _ => by
    have h : (Scheme.Modules.presheaf (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)).map
        (homOfLE (le_top : V ≤ ⊤)).op (Scheme.Modules.unitOne (Spec (.of R)))
        = (show Γ(Spec (.of R), V) from 1) := by
      change ((Spec (.of R)).ringCatSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom 1 = 1
      exact map_one _
    rw [h]
    change Function.Bijective fun g : Γ(Spec (.of R), V) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  app_ratio_smul := fun i j => by
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi hj
    rw [ProjSpace.ratio_self, map_one, map_one, one_smul]

end AlgebraicGeometry

end



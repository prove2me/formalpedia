-- Prove2me | Definitions.Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec
-- name    : AlgebraicGeometry_PicDualNumberDeformationClassSpec
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/f4411970-d24f-5f67-9a6b-4f472286dd43
-- title:
--   Dual-number deformation classes in two-chart Čech H1
-- statement:
--   Throughout: a commutative ring $R$, a scheme $C$ with a morphism $c\colon C\to\operatorname{Spec}R$, a rigidifying datum $\varepsilon$ (a morphism over the identity of $\operatorname{Spec}R$ relative to $c$), a commutative $R$-algebra $A$, and a two-affine open cover $\mathcal V=(U_0,U_1)$ of $C$; $A[\epsilon]$ denotes the dual numbers `DualNumber A`. Three auxiliary notions are named. `dualNumberThickening` is the cover morphism `HomOver.stage` attached to the structure map $A\to A[\epsilon]$: a morphism of two-affine covers lying over that ring homomorphism, whose underlying scheme map is the projection $C\times_{\operatorname{Spec}R}\operatorname{Spec}A[\epsilon]\to C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ and which induces semilinear pullback maps `map0`, `map1`, `map01` on sections of the structure sheaf over the charts and their intersection. For $f$ a function on the intersection of the two charts of the $A$-pullback, `oneAddEpsMul` is the section $1+\epsilon\cdot\iota(f)$ on the intersection of the charts of the $A[\epsilon]$-pullback, $\iota$ being `map01` of that thickening. `H1StructureSheaf` is the two-chart Čech $H^1$ of the structure sheaf of $C\times_{\operatorname{Spec}R}\operatorname{Spec}A$ with the pulled-back cover, i.e. functions on the intersection modulo the image of $(s_0,s_1)\mapsto s_1|-s_0|$.
--
--   The main declaration `IsDeformationClassMap` is a predicate on a map $\delta$ from `RigKerDualNumber c ε A` — classes of rigidified line bundles on the $A[\epsilon]$-stage whose pullback along the reduction $\operatorname{Spec}A\to\operatorname{Spec}A[\epsilon]$ has underlying module isomorphic to the unit, taken modulo the equivalence of rigidified line bundles — to `H1StructureSheaf`. It asserts: for every representative $M$, every sections $e_0,e_1$ of $M$ over the two charts of the $A[\epsilon]$-pullback which are frames there in the sense of `Scheme.Modules.IsFrameOn` (on each smaller open set, multiplication by the restricted section is a bijection from functions to sections), and every $f$ on the intersection of the $A$-charts such that the restriction of $e_1$ equals $(1+\epsilon\,\iota f)$ times the restriction of $e_0$, one has $\delta$ of the class of $M$ equal to the class of $f$. This is thus a specification of $\delta$ by its behaviour on normalised frames, not a construction of it: existence, uniqueness, additivity and naturality in $A$ are the subject of separate statements.
--
--   **Relation to Mathlib.** Mathlib supplies the dual numbers (`DualNumber`/`TrivSqZeroExt`) and sheaves of modules on a scheme; the two-chart Čech complex and its $H^1$, cover morphisms over a ring map, frames for a sheaf of modules, the rigidified relative Picard kernel and the deformation class map itself are project notions with no Mathlib counterpart.
--
--   **Where it is used.** These definitions pin down the chart-level identification of the kernel of $\operatorname{Pic}(C_{A[\epsilon]})\to\operatorname{Pic}(C_A)$ with $H^1$ of the structure sheaf, a deformation of the trivial bundle being glued by the unit $1+\epsilon f_{01}$. They serve the analysis of the relative Picard functor of a curve over a base, used in the treatment of Jacobians of modular curves and their Néron models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_PicDualNumberDeformationClassSpec.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigKerDualNumber
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace AlgebraicGeometry.RelPicard

section Thickening

variable {R : Type u} [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))

abbrev dualNumberThickening :
    HomOver (IsScalarTower.toAlgHom R A (DualNumber A)).toRingHom (𝒱.pullback c A) (pullback.snd c (specMap R A))
      (𝒱.pullback c (DualNumber A)) (pullback.snd c (specMap R (DualNumber A))) :=
  HomOver.stage 𝒱 c (IsScalarTower.toAlgHom R A (DualNumber A))

def oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    ((𝒱.pullback c (DualNumber A)).cover (pullback.snd c (specMap R (DualNumber A)))).A01 :=
  1 + algebraMap (DualNumber A) _ DualNumber.eps * (dualNumberThickening A 𝒱 c).map01 f

end Thickening

section Spec

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A] (𝒱 : C.TwoAffineOpenCover)

abbrev H1StructureSheaf : Type u :=
  ((𝒱.pullback c A).structureSheafSections (pullback.snd c (specMap R A))).H1

def IsDeformationClassMap (δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱) : Prop :=
  ∀ (M : RigKerDualNumber.Carrier c ε A)
    (e₀ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U0)) (e₁ : Γ(M.1.L, (𝒱.pullback c (DualNumber A)).U1))
    (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01),
    Scheme.Modules.IsFrameOn e₀ (𝒱.pullback c (DualNumber A)).U0 →
    Scheme.Modules.IsFrameOn e₁ (𝒱.pullback c (DualNumber A)).U1 →
    M.1.L.presheaf.map (homOfLE inf_le_right).op e₁ =
      (show Γ(Limits.pullback c (specMap R (DualNumber A)),
              (𝒱.pullback c (DualNumber A)).U0 ⊓ (𝒱.pullback c (DualNumber A)).U1)
          from oneAddEpsMul A 𝒱 c f) •
        M.1.L.presheaf.map (homOfLE inf_le_left).op e₀ →
    δ (Quotient.mk _ M) = Submodule.Quotient.mk f

end Spec

end AlgebraicGeometry.RelPicard

end



-- Prove2me | Definitions.Def_ModularCurve_DRModelLegTwoInputV2
-- name    : ModularCurve_DRModelLegTwoInputV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/e2a2bc3e-acbd-597b-ab95-fadd092458b5
-- title:
--   Degeneration input block, version two, for the Deligne–Rapoport model
-- statement:
--   For a prime $p$ and a package $\mathfrak X : \mathrm{DRModelPackage}\ p$ of data on the two-chart integral model `DRModel p` of $X_0(p)$ over $\mathbb Z$, the structure `DRModelPackage.LegTwoInputV2` extends `DRModelPackage.LegTwoInput` (which carries a two-affine open cover of the model, bijectivity of $A \to \Gamma$ of the base change, affine neighbourhoods inside the smooth locus of finite sets of points, triviality of fibrewise algebraically-trivial invertible modules with a nonzero section, reducedness of geometric fibres, a genus integer with its Čech $H^1$ computation, the split-pool field `hpool`, and a degeneration field `hbad`) by a single extra field `hbadV5`. Its content: for every algebraically closed field $k$ and every $s : \operatorname{Spec} k \to \operatorname{Spec}\mathbb Z$ for which the fibre $\mathfrak X_s$, i.e. the base change `pullback.snd (DRModel.toBase p) s`, is not smooth, there exist two curve models $M_1,M_2$ over $k$ with function field $k(T)$, closed immersions $i_1,i_2$ of $M_1.C$, $M_2.C$ into $\mathfrak X_s$ over $\operatorname{Spec} k$, an $n$, an injective $a : \mathrm{Fin}\,n \to k^\times$, a further $b : \mathrm{Fin}\,n \to k^\times$, and a two-affine open cover $\mathcal W_0$ of $\mathfrak X_s$, such that: the two images cover $\mathfrak X_s$; $i_1$ of the place of $a_i$ equals $i_2$ of the place of $b_i$, and these are the only coincidences of points of the two components; $M_1.C \times_{\mathfrak X_s} M_2.C$ is reduced; the $i_j$-preimages of $\mathcal W_0.U0$ and $\mathcal W_0.U1$ are the complements of the point at infinity, respectively of the zero point, on each component; $i_1$ of the point at infinity is the point of $\mathfrak X_s$ cut out by $\mathfrak X.\varepsilon_{\inf}$; the image of $i_1$ meets the smooth locus exactly in the connected component of that point; each $i_1(a_i)$ lies outside the smooth locus; every point of $\mathfrak X_s$ other than the $i_1(a_i)$ lies in the smooth locus; and the complement of the image of $i_2$ is an open subset along which $i_1$ restricts to an open immersion.
--
--   The only difference from the inherited `hbad` is the clause that all points off the finite set $\{i_1(a_i)\}$ are smooth; `hbad` remains available as a component, so consumers of the weaker block apply unchanged. The structure carries no proof obligations beyond these fields.
--
--   **Relation to Mathlib.** Mathlib has no Deligne–Rapoport integral model, relative Picard functor, `CurveModel` or `TwoAffineOpenCover`; all of these, and both input blocks, are the project's own notions, built on Mathlib's schemes, smooth and proper morphisms, and sheaves of modules.
--
--   **Where it is used.** The bundle packages the geometric input needed to represent the fibrewise algebraically-trivial part of the relative Picard functor of the model of $X_0(p)$ over $\mathbb Z$, thereby producing $J_0(p)$ together with control of its reduction; the degeneration clause describes the semistable geometric fibres as two rational components crossing transversally at the supersingular points. This feeds the good-reduction and level-lowering part of the route to Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRModelLegTwoInputV2.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
  AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing

noncomputable section

namespace ModularCurve

variable {p : ℕ} [Fact p.Prime]

structure DRModelPackage.LegTwoInputV2 (𝔛 : DRModelPackage p) extends 𝔛.LegTwoInput where
  hbadV5 : ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)), ¬ Smooth (pullback.snd (DRModel.toBase p) s) →
    ∃ (M₁ M₂ : CurveModel k (RatFunc k)) (i₁ : M₁.C ⟶ pullback (DRModel.toBase p) s) (i₂ : M₂.C ⟶ pullback (DRModel.toBase p) s)
      (_ : IsClosedImmersion i₁) (_ : IsClosedImmersion i₂)
      (n : ℕ) (a b : Fin n → kˣ) (𝒲₀ : (pullback (DRModel.toBase p) s).TwoAffineOpenCover),
      i₁ ≫ pullback.snd (DRModel.toBase p) s = M₁.toBase ∧ i₂ ≫ pullback.snd (DRModel.toBase p) s = M₂.toBase ∧
      Set.range i₁.base ∪ Set.range i₂.base = Set.univ ∧
      Function.Injective a ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 =
        i₂.base (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      (∀ (P₁ : M₁.C) (Q₂ : M₂.C), i₁.base P₁ = i₂.base Q₂ →
        ∃ i, P₁ = (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∧
          Q₂ = (M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k (b i : k))).1) ∧
      IsReduced (pullback i₁ i₂) ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U0 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U0 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeInfty k)).1}ᶜ ∧
      ((i₁ ⁻¹ᵁ 𝒲₀.U1 : M₁.C.Opens) : Set M₁.C) =
        {(M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      ((i₂ ⁻¹ᵁ 𝒲₀.U1 : M₂.C.Opens) : Set M₂.C) =
        {(M₂.placeEquiv.symm (RationalFunctionField.placeOfPoint k 0)).1}ᶜ ∧
      i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeInfty k)).1 = ((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k) ∧
      Set.range i₁.base ∩ ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) =
        connectedComponentIn ((pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens) : Set ↥(pullback (DRModel.toBase p) s)) (((sectionFibrePoint 𝔛.εinf s).1).base (IsLocalRing.closedPoint k)) ∧
      (∀ i, i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1 ∉
        (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∀ y : ↥(pullback (DRModel.toBase p) s),
        (∀ i, y ≠ i₁.base (M₁.placeEquiv.symm (RationalFunctionField.placeOfPoint k (a i : k))).1) →
          y ∈ (pullback.fst (DRModel.toBase p) s ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) s).Opens)) ∧
      (∃ W₁ : (pullback (DRModel.toBase p) s).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) s)) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

end ModularCurve

end



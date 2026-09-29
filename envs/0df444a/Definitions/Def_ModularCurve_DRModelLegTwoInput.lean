-- Prove2me | Definitions.Def_ModularCurve_DRModelLegTwoInput
-- name    : ModularCurve_DRModelLegTwoInput
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/45a6ed63-137b-5c7e-8d89-9a92b87d67e6
-- title:
--   Input bundle for the relative Picard functor of `DRModel`
-- statement:
--   For a prime $p$ and a Deligne–Rapoport package $\mathfrak X$ of the integral two-chart model $X=$ `DRModel p` with structure morphism $x=$ `DRModel.toBase p` to $\operatorname{Spec}\mathbf Z$, smooth locus $U=\mathfrak X.\mathtt{smoothLocus}$ and section $\varepsilon_\infty=\mathfrak X.\mathtt{εinf}$, the structure `DRModelPackage.LegTwoInput 𝔛` bundles data and hypotheses about $x$; it carries no conclusion of its own. Its fields are: a two-affine open cover $\mathcal V$ of $X$ (two affine opens with affine intersection covering $X$); `hH0`, asserting that for every $\mathbf Z$-algebra $A$ the structure map $A \to \Gamma(X\times_{\mathbf Z}\operatorname{Spec}A,\mathcal O)$ is bijective; `hcov`, that any finite subset of $U$ lying over an affine open $V\subseteq\operatorname{Spec}\mathbf Z$ is contained in an affine open of $U$ inside the preimage of $V$; `hfib`, that on each geometric fibre $X_k$ ($k$ algebraically closed, $x$-point $\operatorname{Spec}k\to\operatorname{Spec}\mathbf Z$) an invertible module which is algebraically equivalent to zero — trivialised and realised by an invertible module on a geometrically integral finite-type family over $k$ along two $k$-sections — and admits a nonzero map from the unit is isomorphic to the unit; `hgred`, that all geometric fibres are reduced; a natural number `genus` together with `hg`, that for every geometric fibre and every two-affine cover of it the $k$-dimension of the two-chart Čech $H^1$ of the structure sheaf equals `genus`; `hpool`, producing, for every prime $\mathfrak p$ of $\mathbf Z$ and all $A_0,B_0,n_0$, some $f\notin\mathfrak p$, bounds $b$ and $M>A_0b^{n_0}+B_0$, a finite étale faithfully flat $\mathbf Z[1/f]$-algebra $R'$ and $M$ finite étale $\mathbf Z[1/f]$-algebras $B_i$ of degree in $[1,b]$, all split by $R'$, together with closed immersions $\operatorname{Spec}B_i\to X_{\mathbf Z[1/f]}$ over $\mathbf Z[1/f]$ with pairwise disjoint images inside the preimage of $U$, each meeting every geometric fibre inside the connected component of the $\varepsilon_\infty$-point in the preimage of $U$; and `hbad`, describing every non-smooth geometric fibre $X_k$ as the union of the images of closed immersions of two smooth proper models $M_1,M_2$ of $k(T)$ over $k$, glued at the finitely many pairs of points with coordinates $a_i\in k^\times$ (the $a_i$ distinct) and $b_i\in k^\times$ and at no other pairs, with reduced intersection scheme, with a two-affine cover $\mathcal W_0$ of $X_k$ pulling back on each model to the complements of $T=\infty$ and of $T=0$, with $\infty\in M_1$ mapping to the $\varepsilon_\infty$-point, with the image of $M_1$ meeting the preimage of $U$ exactly in the connected component of that point, with all glueing points outside the preimage of $U$, and with the part of $M_1$ over the complement of the image of $M_2$ an open immersion into $X_k$.
--
--   **Relation to Mathlib.** Mathlib provides the ambient notions used here (proper, smooth and étale morphisms, étale algebras, sheaves of modules), but it has no relative Picard functor; the invertibility predicate for sheaves of modules, algebraic equivalence to zero, two-chart Čech sections and the notion of a curve model over a base field are project definitions, and this hypothesis bundle has no Mathlib counterpart.
--
--   **Where it is used.** These fields are exactly the hypotheses consumed by the representability result for the subfunctor of the relative Picard functor of `DRModel p` over $\operatorname{Spec}\mathbf Z$ cut out by fibrewise algebraic equivalence to zero, rigidified along $\varepsilon_\infty$; that is, they are the input for constructing the relative $\mathrm{Pic}^0$ of the Deligne–Rapoport model of $X_0(p)$, which carries the Galois representations used in the level-lowering part of the argument. Keeping the bundle as a separate structure isolates the model from the shape of that theorem's hypothesis block.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_DRModelLegTwoInput.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
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

variable (p : ℕ) [Fact p.Prime]

variable {p} in

structure DRModelPackage.LegTwoInput (𝔛 : DRModelPackage p) where

  𝒱 : (DRModel p).TwoAffineOpenCover
  hH0 : ∀ (A : Type) [CommRing A] [Algebra ℤ A],
    letI := Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd (DRModel.toBase p) (Scheme.TwoAffineOpenCover.specMap ℤ A)) ⊤
    Function.Bijective (algebraMap A Γ(Limits.pullback (DRModel.toBase p) (Scheme.TwoAffineOpenCover.specMap ℤ A), ⊤))
  hcov : ∀ (V : (Spec (CommRingCat.of ℤ)).affineOpens) (F : Finset ↥𝔛.smoothLocus),
    (∀ x ∈ F, (𝔛.smoothLocus.ι ≫ (DRModel.toBase p)).base x ∈ (V : (Spec (CommRingCat.of ℤ)).Opens)) →
    ∃ W : (𝔛.smoothLocus : Scheme.{0}).Opens, IsAffineOpen W ∧
      W ≤ (𝔛.smoothLocus.ι ≫ (DRModel.toBase p)) ⁻¹ᵁ (V : (Spec (CommRingCat.of ℤ)).Opens) ∧ ∀ x ∈ F, x ∈ W
  hfib : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (L : (pullback (DRModel.toBase p) x).Modules), Scheme.Modules.IsInvertible L →
    IsAlgEquivZero (pullback.snd (DRModel.toBase p) x) L →
    ∀ s : 𝟙_ (pullback (DRModel.toBase p) x).Modules ⟶ L, s ≠ 0 → Nonempty (L ≅ 𝟙_ (pullback (DRModel.toBase p) x).Modules)
  hgred : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ)), IsReduced (pullback (DRModel.toBase p) x)

  genus : ℕ
  hg : ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ℤ))
    (𝒲 : (pullback (pullback.snd (DRModel.toBase p) (𝟙 (Spec (CommRingCat.of ℤ)))) x).TwoAffineOpenCover),
    Module.finrank k (𝒲.sectionsOf (fibreAt (DRModel.toBase p) (𝟙 _) x)
      (SheafOfModules.unit (pullback (pullback.snd (DRModel.toBase p) (𝟙 (Spec (CommRingCat.of ℤ)))) x).ringCatSheaf)).H1 = genus
  hpool : ∀ (𝔭 : PrimeSpectrum ℤ) (A₀ B₀ n₀ : ℕ), ∃ (f : ℤ) (_ : f ∉ 𝔭.asIdeal) (b M : ℕ) (_ : A₀ * b ^ n₀ + B₀ < M)
    (R' : Type) (_ : CommRing R') (aZ : Algebra ℤ R')
    (aL : Algebra (Localization.Away f) R')

    (_ : @IsScalarTower ℤ (Localization.Away f) R' OreLocalization.instSMulOfIsScalarTower aL.toSMul aZ.toSMul)
    (_ : Module.Finite (Localization.Away f) R') (_ : Algebra.Etale (Localization.Away f) R')
    (_ : Module.FaithfullyFlat (Localization.Away f) R')
    (B : Fin M → Type) (_ : ∀ i, CommRing (B i)) (_ : ∀ i, Algebra (Localization.Away f) (B i))
    (_ : ∀ i, Module.Finite (Localization.Away f) (B i)) (_ : ∀ i, Algebra.Etale (Localization.Away f) (B i))
    (deg : Fin M → ℕ) (_ : ∀ i, 1 ≤ deg i) (_ : ∀ i, deg i ≤ b)
    (_φ : ∀ i, TensorProduct (Localization.Away f) R' (B i) ≃ₐ[R'] (Fin (deg i) → R'))
    (z : ∀ i, Spec (CommRingCat.of (B i)) ⟶ pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f)))
    (_ : ∀ i, IsClosedImmersion (z i)),
    (∀ i, z i ≫ baseChange ℤ (DRModel.toBase p) (Localization.Away f) = specMap (Localization.Away f) (B i)) ∧
    (∀ i, Set.range (z i).base ⊆
      ((pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f)) ⁻¹ᵁ 𝔛.smoothLocus : (pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))).Opens) :
        Set ↥(pullback (DRModel.toBase p) (specMap ℤ (Localization.Away f))))) ∧
    (Pairwise fun i j => Disjoint (Set.range (z i).base) (Set.range (z j).base)) ∧
    (∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away f)))
      (i : Fin M),
      (pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).base ⁻¹' Set.range (z i).base ⊆
        connectedComponentIn
          (((pullback.fst (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s ≫ pullback.fst (DRModel.toBase p) (specMap ℤ (Localization.Away f))) ⁻¹ᵁ 𝔛.smoothLocus :
              (pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s).Opens) : Set ↥(pullback (baseChange ℤ (DRModel.toBase p) (Localization.Away f)) s))
          (((sectionFibrePoint (sectionBaseChange (Localization.Away f) 𝔛.εinf) s).1).base (IsLocalRing.closedPoint k)))
  hbad : ∀ (k : Type) [Field k] [IsAlgClosed k] [DecidableEq (RatFunc k)]
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
      (∃ W₁ : (pullback (DRModel.toBase p) s).Opens, (W₁ : Set ↥(pullback (DRModel.toBase p) s)) = (Set.range i₂.base)ᶜ ∧
        IsOpenImmersion ((i₁ ⁻¹ᵁ W₁).ι ≫ i₁))

end ModularCurve

end



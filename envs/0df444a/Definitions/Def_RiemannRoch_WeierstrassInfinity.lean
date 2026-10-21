-- Prove2me | Definitions.Def_RiemannRoch_WeierstrassInfinity
-- name    : RiemannRoch_WeierstrassInfinity
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T13:25:25.131844+00:00
-- url     : https://prove2.me/theorems/ca08a8e1-dcf3-4c26-b700-09d23d56e706
-- title:
--   Places of a Weierstrass function field in the chart presentation: the place at infinity and the places of points
-- statement:
--   Let $k$ be a field and $W$ a Weierstrass curve over $k$, given by
--   $$y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,\qquad a_i\in k,$$
--   elliptic (nonzero discriminant) where stated. Let $k[W]$ be its affine coordinate ring and $K$ a fraction field of $k[W]$, with compatible embeddings $k[X]\subset k[W]$, $k[X]\subset k(X)\subset K$ such that $K/k(X)$ is finite separable. Let $\mathcal O_\infty\subset k(X)$ be the valuation ring at infinity with maximal ideal $\mathfrak m_\infty$, $\mathcal O_K$ and $\mathcal O_{K,\infty}$ the integral closures of $k[X]$ and $\mathcal O_\infty$ in $K$, $\mathbb P^{\mathrm{ch}}_K=\operatorname{Spec}^1(\mathcal O_K)\sqcup\operatorname{Spec}^1(\mathcal O_{K,\infty})$ the chart places, and $W(k)=\{O\}\cup\{(x_0,y_0)\in k^2\text{ on }W\text{ and nonsingular}\}$ the set of points of $W$.
--
--   This file introduces:
--
--   1. **Coordinates at infinity.** With $t=1/x$, the element $z=y\,t^2\in K$ satisfies the monic equation
--   $$z^2+(a_1t+a_3t^2)\,z-(t+a_2t^2+a_4t^3+a_6t^4)=0,$$
--   so $z$ and $t$ lie in $\mathcal O_{K,\infty}$.
--   2. **The place at infinity** $\infty$: a height-one prime of $\mathcal O_{K,\infty}$ lying over $\mathfrak m_\infty$, chosen among those that exist, viewed as an infinite chart place.
--   3. **Finite places of points.** For elliptic $W$, the isomorphism $k[W]\cong\mathcal O_K$ of $k[X]$-algebras; for a nonsingular point $(x_0,y_0)$, the maximal ideal $(X-x_0,\,Y-y_0)$ of $k[W]$ as a height-one prime and the corresponding finite chart place.
--   4. **The point–place map** $W(k)\to\mathbb P^{\mathrm{ch}}_K$, sending $O\mapsto\infty$ and $(x_0,y_0)\mapsto$ the place of $(X-x_0,Y-y_0)$.
--
--   The file also contains the structural lemmas these definitions need: the class of $X$ in $K$ is the chart variable $x_K$, $(x_K,y)$ satisfies the Weierstrass equation in $K$, $z$ is integral over $\mathcal O_\infty$, and $(X-x_0,Y-y_0)$ is a nonzero maximal ideal.
--
--   This is the chart half of the dictionary between points of a Weierstrass curve and places of its function field. The accompanying theorems `WeierstrassCurve.Affine.Chart.infinity_ramificationIdx_eq_two` and `WeierstrassCurve.Affine.Chart.infinity_heightOne_unique` show that every prime of $\mathcal O_{K,\infty}$ has ramification index $2$ over $\mathfrak m_\infty$ and that $\infty$ is the only one. In the chain of definition files it imports `RiemannRoch_WeierstrassDedekind` and is imported by `RiemannRoch_WeierstrassGenus`.
--
--   **Formalization Note** The curve is `W : WeierstrassCurve.Affine k`, with `[W.IsElliptic]` declared for the file and omitted from the lemmas on $z$ and the equation; its points are Mathlib's `W.Point` (constructors `zero` and `some`). $K$ is an abstract field with `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`, together with `Algebra k[X] K`, `IsScalarTower k[X] W.CoordinateRing K`, `Algebra k⟮X⟯ K`, `IsScalarTower k[X] k⟮X⟯ K`, `FunctionField k K` and `Algebra.IsSeparable k⟮X⟯ K`; the algebra $k\to K$ is the local instance obtained through $k[X]$. The place at infinity `Chart.infinityHeightOne` is selected with `Classical.choose` from the existence of a maximal ideal lying over $\mathfrak m_\infty$ (it does not depend on $W$), and `Chart.infinityPlace` is the corresponding element of `PlaceA k K`; the isomorphism $k[W]\cong\mathcal O_K$ is `IsIntegralClosure.equiv`, which uses the Dedekind (integrally closed) property of `RiemannRoch_WeierstrassDedekind`.
-- source:
--   J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, III.1 (Weierstrass equations, discriminant, the point $O$ at infinity) and III.3 (points of an elliptic curve, cf.); H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 6.1 (elliptic function fields, cf.); the explicit choice of $z=y/x^2$ at infinity and the chart bookkeeping are auxiliary constructions of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/Infinity.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/PlaceDictionary.lean

import Mathlib
import Definitions.Def_RiemannRoch_WeierstrassDedekind

/-
Contains code from riemann-roch-function-fields
(https://github.com/vaca22/riemann-roch-function-fields, commit dbca5bee),
Copyright (c) 2026 Guanghao Li, released under the Apache License 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
Modified: ported to Lean v4.33.1 / Mathlib 0df444a (module headers converted, some proofs
adapted to this Mathlib, a few names qualified, `picTorsor` omitted; statements unchanged), then
split into prove2.me definitions and theorems, with comments removed.
-/

set_option linter.style.haveILetI false

section
section
open FunctionField
open FunctionField.Chart
open Polynomial
open scoped Polynomial RatFunc
namespace WeierstrassCurve.Affine.Chart
noncomputable section
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K]
  [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
local instance instAlgebraConstants : Algebra k K := FunctionField.algebraConstants k K
local instance instConstantsTower : IsScalarTower k k[X] K :=
  FunctionField.algebraConstants_isScalarTower k K
local instance instCoordinateConstantsTower : IsScalarTower k W.CoordinateRing K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing,
      ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]
local notation "A∞" => inftyValuationSubring k
local notation "S∞" => infiniteIntegers k K
local instance instFaithfulInfinity : FaithfulSMul A∞ S∞ :=
  FaithfulSMul.of_field_isFractionRing A∞ S∞ k⟮X⟯ K
local instance instInfinityConstantsTower : IsScalarTower k A∞ K :=
  IsScalarTower.of_algebraMap_eq fun c => by
    change algebraMap k K c = algebraMap k⟮X⟯ K (RatFunc.C c)
    rw [IsScalarTower.algebraMap_apply k k[X] K,
      IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
    rfl
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma xCoord_eq_XK :
    algebraMap W.CoordinateRing K (CoordinateRing.mk W (Polynomial.C Polynomial.X)) =
      XK k K := by
  have hx : CoordinateRing.mk W (Polynomial.C Polynomial.X) =
      algebraMap k[X] W.CoordinateRing Polynomial.X := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply k[X] W.CoordinateRing K]
  change algebraMap k[X] K Polynomial.X = XK k K
  rw [IsScalarTower.algebraMap_apply k[X] k⟮X⟯ K]
  exact congrArg (algebraMap k⟮X⟯ K) (RatFunc.algebraMap_X (K := k))
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma yCoord_equation :
    (W⁄K).Equation (XK k K) (W.yCoord K) := by
  have h := (coordinate_equation W).map (algebraMap W.CoordinateRing K)
  convert h using 1
  · ext <;> simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map]
    all_goals exact IsScalarTower.algebraMap_apply k W.CoordinateRing K _
  · exact (xCoord_eq_XK W K).symm
  · rfl
noncomputable def infinityZ : K := W.yCoord K * (tK k K) ^ 2
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZ_equation :
    (infinityZ W K) ^ 2 +
        (algebraMap k K W.a₁ * tK k K + algebraMap k K W.a₃ * (tK k K) ^ 2) *
          infinityZ W K -
      (tK k K + algebraMap k K W.a₂ * (tK k K) ^ 2 +
        algebraMap k K W.a₄ * (tK k K) ^ 3 +
        algebraMap k K W.a₆ * (tK k K) ^ 4) = 0 := by
  have heq := (W⁄K).equation_iff (XK k K) (W.yCoord K) |>.mp
    (yCoord_equation W K)
  change W.yCoord K ^ 2 + algebraMap k K W.a₁ * XK k K * W.yCoord K +
      algebraMap k K W.a₃ * W.yCoord K =
    XK k K ^ 3 + algebraMap k K W.a₂ * XK k K ^ 2 +
      algebraMap k K W.a₄ * XK k K + algebraMap k K W.a₆ at heq
  have hxt : XK k K * tK k K = 1 := XK_mul_tK k K
  dsimp [infinityZ]
  linear_combination (tK k K) ^ 4 * heq +
    (-(algebraMap k K W.a₁) * W.yCoord K * (tK k K) ^ 3 +
      tK k K * ((XK k K * tK k K) ^ 2 + XK k K * tK k K + 1) +
      algebraMap k K W.a₂ * (tK k K) ^ 2 * (XK k K * tK k K + 1) +
      algebraMap k K W.a₄ * (tK k K) ^ 3) * hxt
omit [WeierstrassCurve.IsElliptic W] [IsFractionRing W.CoordinateRing K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] in
lemma infinityZ_isIntegral : _root_.IsIntegral A∞ (infinityZ W K) := by
  let t : A∞ := tA k
  let c : k →+* A∞ := algebraMap k A∞
  let p : A∞[X] :=
    X ^ 2 + C (c W.a₁ * t + c W.a₃ * t ^ 2) * X -
      C (t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4)
  refine ⟨p, ?_, ?_⟩
  · dsimp [p]
    simpa only [sub_eq_add_neg, ← Polynomial.C_neg] using
      (isMonicOfDegree_add_add_two
        (c W.a₁ * t + c W.a₃ * t ^ 2)
        (-(t + c W.a₂ * t ^ 2 + c W.a₄ * t ^ 3 + c W.a₆ * t ^ 4))).monic
  · simp only [p, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
    dsimp [t, c]
    have htmap : algebraMap A∞ K (tA k) = tK k K := rfl
    simp only [map_add, map_mul, map_pow, htmap]
    rw [← IsScalarTower.algebraMap_apply k A∞ K W.a₁,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₃,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₂,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₄,
      ← IsScalarTower.algebraMap_apply k A∞ K W.a₆]
    exact infinityZ_equation W K
noncomputable def infinityZInt : S∞ :=
  ⟨infinityZ W K, (mem_integralClosure_iff (R := A∞) (A := K)).2
    (infinityZ_isIntegral W K)⟩
noncomputable def infinityTInt : S∞ := algebraMap A∞ S∞ (tA k)
noncomputable def infinityHeightOne : IsDedekindDomain.HeightOneSpectrum S∞ := by
  let p := IsLocalRing.maximalIdeal A∞
  have hp0 : p ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField (IsLocalRing.maximalIdeal.isMaximal A∞)
      (IsDiscreteValuationRing.not_isField A∞)
  let hex := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := S∞) p
  let P : Ideal S∞ := Classical.choose hex
  have hP : P.IsMaximal ∧ P.LiesOver p := Classical.choose_spec hex
  letI : P.LiesOver p := hP.2
  exact ⟨P, hP.1.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩
noncomputable def infinityPlace : PlaceA k K := Sum.inr (infinityHeightOne (k := k) K)
end
end WeierstrassCurve.Affine.Chart
end
end

section
section
open FunctionField
open FunctionField.Chart
open scoped Polynomial RatFunc
namespace WeierstrassCurve.Affine.Chart
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
  [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
  [_root_.FunctionField k K] [Algebra.IsSeparable k⟮X⟯ K]
noncomputable def coordinateRingEquivIntegers :
    W.CoordinateRing ≃ₐ[k[X]] ringOfIntegers k K :=
  IsIntegralClosure.equiv k[X] W.CoordinateRing K (ringOfIntegers k K)
omit [W.IsElliptic] in
lemma XYIdeal_isMaximal {x y : k} (h : W.Nonsingular x y) :
    (CoordinateRing.XYIdeal W x (Polynomial.C y)).IsMaximal := by
  let e := CoordinateRing.quotientXYIdealEquiv (W' := W) (x := x)
    (y := Polynomial.C y) h.1
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
    (e.toRingEquiv.isField (Field.toIsField k))
omit [W.IsElliptic] in
lemma XYIdeal_ne_bot {x y : k} (_h : W.Nonsingular x y) :
    CoordinateRing.XYIdeal W x (Polynomial.C y) ≠ ⊥ := by
  intro hbot
  apply CoordinateRing.XClass_ne_zero (W' := W) x
  rw [← Ideal.mem_bot, ← hbot]
  exact Ideal.subset_span (Set.mem_insert _ _)
noncomputable def affineHeightOne {x y : k} (h : W.Nonsingular x y) :
    IsDedekindDomain.HeightOneSpectrum W.CoordinateRing :=
  ⟨CoordinateRing.XYIdeal W x (Polynomial.C y),
    (XYIdeal_isMaximal W h).isPrime, XYIdeal_ne_bot W h⟩
noncomputable def finitePlaceOfAffine {x y : k} (h : W.Nonsingular x y) : PlaceA k K :=
  Sum.inl (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv
    (coordinateRingEquivIntegers W K).toRingEquiv (affineHeightOne W h))
noncomputable def placeOfPoint : W.Point → PlaceA k K
  | .zero => infinityPlace K
  | .some _ _ h => finitePlaceOfAffine W K h
end WeierstrassCurve.Affine.Chart
end
end



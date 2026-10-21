-- Prove2me | Definitions.Def_RiemannRoch_WeierstrassDedekind
-- name    : RiemannRoch_WeierstrassDedekind
-- status  : Definition
-- author  : @Idealson
-- created : 2026-10-20T13:23:56.345206+00:00
-- url     : https://prove2.me/theorems/a8e77698-f708-4924-ac4c-b713c8b4b0fc
-- title:
--   Function field of a Weierstrass curve and the Dedekind property of its coordinate ring
-- statement:
--   Let $k$ be a field and $W$ a Weierstrass curve over $k$,
--   $$W:\ y^2+a_1xy+a_3y=x^3+a_2x^2+a_4x+a_6,\qquad a_i\in k,$$
--   with affine coordinate ring $k[W]=k[X,Y]/(W)$, and let $K$ be a field of fractions of $k[W]$. The curve is called elliptic if its discriminant is nonzero.
--
--   This file sets up the function field of $W$ in the form required by the Riemann–Roch library and proves that $k[W]$ is a Dedekind domain. It introduces:
--
--   1. **Algebra structures.** $k[W]$ is a finite, hence integral, $k[X]$-module; the induced maps $k[X]\to K$ (injective), $k(X)\to K$ and $k\to K$ (through $k[X]$), with the corresponding compatibility.
--   2. **The coordinate $y$.** The element $y\in K$, the $k(X)$-basis $\{1,y\}$ of $K$ (so $[K:k(X)]=2$), and $y\notin k(X)$.
--   3. **The equation as a cubic in $x$.** The polynomial
--   $$x^3+a_2x^2+(a_4-a_1y)\,x+(a_6-y^2-a_3y)\in k[y][x],$$
--   which is monic, and the $k$-algebra isomorphism $k[y][x]/(\text{this cubic})\cong k[W]$ obtained by exchanging the two variables.
--
--   It also contains the structural lemmas these constructions need: the Weierstrass equation and its partial derivatives evaluated at the classes of $X,Y$ in $k[W]$; if $W$ is elliptic, the classes of $\partial W/\partial X$ and $\partial W/\partial Y$ are not both in any prime ideal of $k[W]$; for a monic polynomial $f$ over a commutative ring $R$ and a prime $\mathfrak P$ of $R[x]/(f)$ not containing the class of $f'$, $R[x]/(f)$ is unramified over $R$ at $\mathfrak P$, and if moreover $R$ is a Noetherian principal ideal ring, $R[x]/(f)$ is a domain and $\mathfrak P\ne0$, the localization at $\mathfrak P$ is a discrete valuation ring; transport of this property along ring isomorphisms; hence the localization of $k[W]$ at a nonzero prime $\mathfrak P$ is a discrete valuation ring as soon as $\partial W/\partial X\notin\mathfrak P$ or $\partial W/\partial Y\notin\mathfrak P$, and
--   $$W\ \text{elliptic}\ \Longrightarrow\ k[W]\ \text{is a Dedekind domain.}$$
--
--   This is the input that identifies $k[W]$ with the integral closure of $k[X]$ in $K$, so that the places of $K$ can be compared with the points of $W$. In the chain of definition files it imports `RiemannRoch_WeilDifferentials` and is imported by `RiemannRoch_WeierstrassInfinity`.
--
--   **Formalization Note** The curve is Mathlib's `W : WeierstrassCurve.Affine k`, with coordinate ring `W.CoordinateRing`; `W.IsElliptic` means that the discriminant is a unit. $K$ is an abstract field with `[Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]`. The algebra structures `algebraPolynomial`, `algebraRatFunc` and `FunctionField.algebraConstants` are definitions, not global instances; the later statements take `Algebra k[X] K`, `Algebra k⟮X⟯ K` with scalar-tower hypotheses instead. $y$ is `yCoord`, the basis is `basisRatFunc`, the cubic is `xPolynomial` in `k[X][Y]` (outer variable playing the role of $x$, inner variable that of $y$) and the isomorphism is `xAdjoinRootEquiv : AdjoinRoot (xPolynomial W) ≃ₐ[k] W.CoordinateRing`. The Dedekind property is the instance `instIsDedekindDomainCoordinateRing` under `[W.IsElliptic]`, proved through Mathlib's `IsDedekindDomainDvr`.
-- source:
--   J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., GTM 106, Springer 2009, III.1 (Weierstrass equations, discriminant) and II.1 (the local ring at a smooth point is a discrete valuation ring, cf.); H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer 2009, Section 6.1 (elliptic function fields, cf.); the Jacobian-criterion lemmas for $R[x]/(f)$ are auxiliary lemmas of the formalization. Lean: riemann-roch-function-fields by Guanghao Li (Apache 2.0), ported to Mathlib 0df444a: https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/Instances.lean, https://github.com/vaca22/riemann-roch-function-fields/blob/dbca5beed1da77e2ecd1eec207d0451fa57e8aa6/RiemannRoch/EllipticCurve/Dedekind.lean

import Mathlib
import Definitions.Def_RiemannRoch_WeilDifferentials

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
open Polynomial
open scoped Polynomial.Bivariate RatFunc nonZeroDivisors
noncomputable section
namespace WeierstrassCurve.Affine
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k)
namespace CoordinateRing
instance : Module.Finite k[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)
theorem algebraMap_polynomial_injective' :
    Function.Injective (algebraMap k[X] W.CoordinateRing) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (by rw [degree_polynomial]; exact (by decide : (2 : WithBot ℕ) ≠ 0))
instance : FaithfulSMul k[X] W.CoordinateRing :=
  (faithfulSMul_iff_algebraMap_injective k[X] W.CoordinateRing).mpr
    (algebraMap_polynomial_injective' W)
instance : Algebra.IsIntegral k[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite k[X] W.CoordinateRing
end CoordinateRing
variable (K : Type*) [Field K] [Algebra W.CoordinateRing K] [IsFractionRing W.CoordinateRing K]
@[reducible]
def algebraPolynomial : Algebra k[X] K :=
  ((algebraMap W.CoordinateRing K).comp (algebraMap k[X] W.CoordinateRing)).toAlgebra
section AbstractPolynomialAlgebra
variable [Algebra k[X] K] [IsScalarTower k[X] W.CoordinateRing K]
include W in
theorem algebraMap_polynomial_injective :
    Function.Injective (algebraMap k[X] K) := by
  rw [IsScalarTower.algebraMap_eq k[X] W.CoordinateRing K]
  exact (IsFractionRing.injective W.CoordinateRing K).comp
    (CoordinateRing.algebraMap_polynomial_injective' W)
@[reducible]
def algebraRatFunc : Algebra k⟮X⟯ K :=
  (IsFractionRing.lift (W.algebraMap_polynomial_injective K)).toAlgebra
section AbstractRatFuncAlgebra
variable [Algebra k⟮X⟯ K] [IsScalarTower k[X] k⟮X⟯ K]
def yCoord : K := algebraMap W.CoordinateRing K (CoordinateRing.mk W Y)
def basisRatFunc : Module.Basis (Fin 2) k⟮X⟯ K :=
  (CoordinateRing.basis W).localizationLocalization k⟮X⟯ k[X]⁰ K
@[simp]
theorem basisRatFunc_zero : W.basisRatFunc K 0 = 1 := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, CoordinateRing.basis_zero,
    map_one]
@[simp]
theorem basisRatFunc_one : W.basisRatFunc K 1 = W.yCoord K := by
  rw [basisRatFunc, Module.Basis.localizationLocalization_apply, CoordinateRing.basis_one,
    yCoord]
theorem yCoord_notMem_range :
    W.yCoord K ∉ Set.range (algebraMap k⟮X⟯ K) := by
  rintro ⟨c, hc⟩
  have h := Fintype.linearIndependent_iff.mp (W.basisRatFunc K).linearIndependent ![c, -1]
  have h1 : (![c, -1] : Fin 2 → k⟮X⟯) 1 = 0 := by
    refine h ?_ 1
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, basisRatFunc_zero, basisRatFunc_one]
    rw [← hc, Algebra.smul_def, mul_one, neg_one_smul, add_neg_cancel]
  norm_num at h1
end AbstractRatFuncAlgebra
end AbstractPolynomialAlgebra
end WeierstrassCurve.Affine
namespace FunctionField
open scoped Polynomial
variable (k K : Type*) [Field k] [Field K] [Algebra k[X] K]
@[reducible]
noncomputable def algebraConstants : Algebra k K :=
  ((algebraMap k[X] K).comp (algebraMap k k[X])).toAlgebra
theorem algebraConstants_isScalarTower :
    letI := algebraConstants k K
    IsScalarTower k k[X] K :=
  letI := algebraConstants k K
  IsScalarTower.of_algebraMap_eq fun _ => rfl
end FunctionField
end
end
end

section
section
open Polynomial
open scoped Polynomial.Bivariate
namespace WeierstrassCurve.Affine
variable {k : Type*} [Field k]
noncomputable def xPolynomial (W : WeierstrassCurve.Affine k) : k[X][Y] :=
  Cubic.toPoly
    ⟨1, C W.a₂, C W.a₄ - C W.a₁ * X,
      C W.a₆ - X ^ 2 - C W.a₃ * X⟩
lemma xPolynomial_eq_neg_swap (W : WeierstrassCurve.Affine k) :
    xPolynomial W = -Polynomial.Bivariate.swap W.polynomial := by
  rw [xPolynomial, polynomial, Cubic.toPoly]
  simp only [map_add, map_sub, map_mul, map_pow, map_one, one_mul,
    Polynomial.Bivariate.swap_Y, Polynomial.Bivariate.swap_C,
    Polynomial.map_C, Polynomial.map_X]
  ring
lemma xPolynomial_monic (W : WeierstrassCurve.Affine k) : (xPolynomial W).Monic := by
  rw [xPolynomial]
  exact Cubic.monic_of_a_eq_one'
noncomputable def xAdjoinRootEquiv (W : WeierstrassCurve.Affine k) :
    AdjoinRoot (xPolynomial W) ≃ₐ[k] W.CoordinateRing :=
  { Ideal.quotientEquiv
      (Ideal.span {xPolynomial W}) (Ideal.span {W.polynomial})
      Polynomial.Bivariate.swap.toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton, xPolynomial_eq_neg_swap,
        map_neg, Ideal.span_singleton_neg]
      exact congrArg (fun p => Ideal.span ({p} : Set k[X][Y]))
        (Polynomial.Bivariate.swap_swap_apply W.polynomial).symm) with
    commutes' := fun r => by
      rw [IsScalarTower.algebraMap_apply k k[X] (AdjoinRoot (xPolynomial W)),
        IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing]
      change (Ideal.quotientEquiv _ _ Polynomial.Bivariate.swap.toRingEquiv _)
        (Ideal.Quotient.mk _ (C (C r))) = Ideal.Quotient.mk _ (C (C r))
      rw [Ideal.quotientEquiv_mk]
      exact congrArg (Ideal.Quotient.mk (Ideal.span {W.polynomial}))
        (Polynomial.Bivariate.swap_C_C r) }
lemma xAdjoinRootEquiv_mk (W : WeierstrassCurve.Affine k) (q : k[X][Y]) :
    xAdjoinRootEquiv W (AdjoinRoot.mk (xPolynomial W) q) =
      CoordinateRing.mk W (Polynomial.Bivariate.swap q) := by
  rfl
noncomputable instance instIsDomainXAdjoinRoot (W : WeierstrassCurve.Affine k) :
    IsDomain (AdjoinRoot (xPolynomial W)) :=
  (xAdjoinRootEquiv W).injective.isDomain (xAdjoinRootEquiv W).toRingHom
lemma coordinate_mk_eq_eval₂ (W : WeierstrassCurve.Affine k) (q : k[X][Y]) :
    CoordinateRing.mk W q =
      eval₂ (eval₂RingHom (algebraMap k W.CoordinateRing)
        (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y) q := by
  change (CoordinateRing.mk W) q =
    (eval₂RingHom (eval₂RingHom (algebraMap k W.CoordinateRing)
      (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y)) q
  apply congrArg (fun f : k[X][Y] →+* W.CoordinateRing => f q)
  apply Polynomial.ringHom_ext
  · intro p
    rw [AdjoinRoot.mk_C]
    change (AdjoinRoot.of W.polynomial) p =
      eval₂ (eval₂RingHom (algebraMap k W.CoordinateRing)
        (CoordinateRing.mk W (C X))) (CoordinateRing.mk W Y) (C p)
    rw [eval₂_C]
    apply congrArg (fun f : k[X] →+* W.CoordinateRing => f p)
    apply Polynomial.ringHom_ext
    · intro a
      simp [CoordinateRing.mk,
        IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing]
    · simp [CoordinateRing.mk]
  · simp [CoordinateRing.mk]
lemma coordinate_polynomialX_eval (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).polynomialX.evalEval
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) =
        CoordinateRing.mk W W.polynomialX := by
  change (W.map (algebraMap k W.CoordinateRing)).polynomialX.evalEval _ _ = _
  rw [map_polynomialX]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  exact (coordinate_mk_eq_eval₂ W W.polynomialX).symm
lemma coordinate_polynomialY_eval (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).polynomialY.evalEval
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) =
        CoordinateRing.mk W W.polynomialY := by
  change (W.map (algebraMap k W.CoordinateRing)).polynomialY.evalEval _ _ = _
  rw [map_polynomialY]
  rw [← Polynomial.eval₂_eval₂RingHom_apply]
  exact (coordinate_mk_eq_eval₂ W W.polynomialY).symm
lemma coordinate_equation (W : WeierstrassCurve.Affine k) :
    (W⁄W.CoordinateRing).Equation
      (CoordinateRing.mk W (C X)) (CoordinateRing.mk W Y) := by
  rw [equation_iff]
  have h : CoordinateRing.mk W W.polynomial = 0 := AdjoinRoot.mk_self
  simp only [polynomial, map_add, map_sub, map_mul, map_pow] at h
  convert sub_eq_zero.mp h using 1 <;>
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.map,
      IsScalarTower.algebraMap_apply k k[X] W.CoordinateRing] ; ring
lemma derivative_polynomial_eq (W : WeierstrassCurve.Affine k) :
    W.polynomial.derivative = W.polynomialY := by
  rw [polynomial, polynomialY]
  simp only [derivative_add, derivative_sub, derivative_pow, derivative_X,
    derivative_mul, derivative_C, zero_mul]
  norm_num
  have h2 : (2 : k[X]) = C (2 : k) := (map_ofNat C 2).symm
  exact h2
lemma xPolynomial_derivative_eq (W : WeierstrassCurve.Affine k) :
    (xPolynomial W).derivative = -Polynomial.Bivariate.swap W.polynomialX := by
  rw [xPolynomial, polynomialX, Cubic.toPoly]
  simp only [derivative_add, derivative_pow, derivative_X,
    derivative_mul, derivative_C, zero_mul, add_zero]
  simp only [map_ofNat, C_1, one_mul, map_add, map_sub, map_mul, map_pow,
    Polynomial.Bivariate.swap_C, Polynomial.Bivariate.swap_Y,
    Polynomial.map_C, Polynomial.map_X]
  norm_num
  have h2 : (2 : k[X][Y]) = C (2 : k[X]) := (map_ofNat C 2).symm
  have h3 : (3 : k[X][Y]) = C (3 : k[X]) := (map_ofNat C 3).symm
  rw [h2, h3]
  ring
lemma xAdjoinRootEquiv_neg_swap_polynomialX (W : WeierstrassCurve.Affine k) :
    xAdjoinRootEquiv W (AdjoinRoot.mk (xPolynomial W)
      (-Polynomial.Bivariate.swap W.polynomialX)) =
      -CoordinateRing.mk W W.polynomialX := by
  have hcore : xAdjoinRootEquiv W
      (AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX)) =
        CoordinateRing.mk W W.polynomialX := by
    rw [xAdjoinRootEquiv_mk, Polynomial.Bivariate.swap_swap_apply]
  calc
    xAdjoinRootEquiv W
        (AdjoinRoot.mk (xPolynomial W) (-Polynomial.Bivariate.swap W.polynomialX)) =
      xAdjoinRootEquiv W
        (-(AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX))) := by
          rw [map_neg]
    _ = -xAdjoinRootEquiv W
        (AdjoinRoot.mk (xPolynomial W) (Polynomial.Bivariate.swap W.polynomialX)) := map_neg _ _
    _ = -CoordinateRing.mk W W.polynomialX := congrArg Neg.neg hcore
lemma coordinate_derivatives_not_both_mem (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (P : Ideal W.CoordinateRing) [P.IsPrime] :
    CoordinateRing.mk W W.polynomialX ∉ P ∨ CoordinateRing.mk W W.polynomialY ∉ P := by
  let L := P.ResidueField
  let f : W.CoordinateRing →+* L := algebraMap W.CoordinateRing L
  let x : L := algebraMap W.CoordinateRing L (CoordinateRing.mk W (C X))
  let y : L := algebraMap W.CoordinateRing L (CoordinateRing.mk W Y)
  letI : (W⁄W.CoordinateRing).IsElliptic := by
    change (W.map (algebraMap k W.CoordinateRing)).IsElliptic
    infer_instance
  letI : ((W⁄W.CoordinateRing).map f).IsElliptic := by infer_instance
  have hEq : ((W⁄W.CoordinateRing).map f).Equation x y := by
    simpa [x, y, f] using (coordinate_equation W).map f
  have hns : ((W⁄W.CoordinateRing).map f).Nonsingular x y :=
    (((W⁄W.CoordinateRing).map f).equation_iff_nonsingular).mp hEq
  rw [Nonsingular] at hns
  rcases hns.2 with hx | hy
  · left
    intro hmem
    apply hx
    rw [map_polynomialX, map_mapRingHom_evalEval, coordinate_polynomialX_eval]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
  · right
    intro hmem
    apply hy
    rw [map_polynomialY, map_mapRingHom_evalEval, coordinate_polynomialY_eval]
    exact Ideal.algebraMap_residueField_eq_zero.mpr hmem
end WeierstrassCurve.Affine
namespace AdjoinRoot
variable {R : Type*} [CommRing R]
theorem isUnramifiedAt_of_monic_derivative_not_mem (f : R[X]) (hf : f.Monic)
    (P : Ideal (AdjoinRoot f)) [P.IsPrime]
    (hP : AdjoinRoot.mk f f.derivative ∉ P) :
    Algebra.IsUnramifiedAt R P := by
  let Q : StandardEtalePair R :=
    ⟨f, hf, f.derivative, 1, 0, 1, by simp⟩
  have hfu : Algebra.FormallyUnramified R
      (Localization.Away (AdjoinRoot.mk f f.derivative)) := by
    exact Algebra.FormallyUnramified.of_equiv Q.equivAwayAdjoinRoot
  have hopen := (Algebra.basicOpen_subset_unramifiedLocus_iff (R := R)
    (A := AdjoinRoot f) (f := AdjoinRoot.mk f f.derivative)).mpr hfu
  have hmem : (⟨P, inferInstance⟩ : PrimeSpectrum (AdjoinRoot f)) ∈
      PrimeSpectrum.basicOpen (AdjoinRoot.mk f f.derivative) := by
    simpa using hP
  exact hopen hmem
theorem isDiscreteValuationRing_atPrime_of_derivative_not_mem
    [IsNoetherianRing R] [IsPrincipalIdealRing R]
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot f)]
    (P : Ideal (AdjoinRoot f)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : AdjoinRoot.mk f f.derivative ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  letI : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite R _
  letI : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  letI : Algebra.IsUnramifiedAt R P :=
    isUnramifiedAt_of_monic_derivative_not_mem f hf P hP
  let p := P.under R
  letI := Localization.AtPrime.algebraOfLiesOver p P
  have hmap : p.map (algebraMap R (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R p P).mp inferInstance).2
  haveI : p.IsPrincipal := IsPrincipalIdealRing.principal p
  have hprincipal : (IsLocalRing.maximalIdeal (Localization.AtPrime P)).IsPrincipal := by
    rw [← hmap]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P)
    (IsLocalization.AtPrime.not_isField (AdjoinRoot f) hP0
      (Localization.AtPrime P))).out 4 0).mp hprincipal
theorem isDiscreteValuationRing_atPrime_of_derivative_eq_not_mem
    [IsNoetherianRing R] [IsPrincipalIdealRing R]
    (f : R[X]) (hf : f.Monic) [IsDomain (AdjoinRoot f)]
    (q : R[X]) (hder : f.derivative = q)
    (P : Ideal (AdjoinRoot f)) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hP : AdjoinRoot.mk f q ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  apply isDiscreteValuationRing_atPrime_of_derivative_not_mem f hf P hP0
  rwa [hder]
end AdjoinRoot
namespace IsDiscreteValuationRing
theorem of_ringEquiv_of_not_isField {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsLocalRing B]
    (e : A ≃+* B) (hB : ¬IsField B) : IsDiscreteValuationRing B := by
  letI : IsPrincipalIdealRing B :=
    { principal := fun I => by
        let J := I.comap e.toRingHom
        haveI : J.IsPrincipal := IsPrincipalIdealRing.principal J
        have hJI : J.map e.toRingHom = I :=
          Ideal.map_comap_eq_self_of_equiv e I
        rw [← hJI]
        infer_instance }
  exact { not_a_field' := IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hB }
theorem atPrime_of_comap_ringEquiv {A B : Type*}
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    (e : A ≃+* B) (P : Ideal B) [P.IsPrime] (hP0 : P ≠ ⊥)
    [IsDiscreteValuationRing (Localization.AtPrime (P.comap e.toRingHom))] :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  have hmon : Submonoid.map e.toMonoidHom (P.comap e.toRingHom).primeCompl =
      P.primeCompl := e.map_primeCompl_comap_eq P
  let eLoc : Localization.AtPrime (P.comap e.toRingHom) ≃+* Localization.AtPrime P :=
    IsLocalization.ringEquivOfRingEquiv
      (M := (P.comap e.toRingHom).primeCompl) (T := P.primeCompl)
      _ _ e hmon
  exact of_ringEquiv_of_not_isField eLoc
    (IsLocalization.AtPrime.not_isField B hP0 _)
end IsDiscreteValuationRing
 theorem not_mem_comap_of_image_eq {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (P : Ideal B) (x : A) (y : B) (hxy : e x = y) (hy : y ∉ P) :
    x ∉ P.comap e.toRingHom := by
  intro hx
  exact hy (hxy ▸ hx)
namespace WeierstrassCurve.Affine.CoordinateRing
variable {k : Type*} [Field k] (W : WeierstrassCurve.Affine k) [W.IsElliptic]
omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_of_polynomialY_not_mem
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hY : CoordinateRing.mk W W.polynomialY ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  apply AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_not_mem
    W.polynomial W.monic_polynomial P hP0
  rwa [derivative_polynomial_eq]
omit [WeierstrassCurve.IsElliptic W] in
theorem x_comap_ne_bot (P : Ideal W.CoordinateRing) (hP0 : P ≠ ⊥) :
    P.comap (xAdjoinRootEquiv W).toRingHom ≠ ⊥ := by
  intro hQ
  apply hP0
  have hmap : (P.comap (xAdjoinRootEquiv W).toRingHom).map
      (xAdjoinRootEquiv W).toRingHom = P :=
    Ideal.map_comap_eq_self_of_equiv (xAdjoinRootEquiv W).toRingEquiv P
  rw [← hmap, hQ, Ideal.map_bot]
omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_x_comap
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hX : CoordinateRing.mk W W.polynomialX ∉ P) :
    IsDiscreteValuationRing
      (Localization.AtPrime (P.comap (xAdjoinRootEquiv W).toRingHom)) := by
  letI : (P.comap (xAdjoinRootEquiv W).toRingHom).IsPrime :=
    Ideal.IsPrime.comap (xAdjoinRootEquiv W).toRingHom
  exact AdjoinRoot.isDiscreteValuationRing_atPrime_of_derivative_eq_not_mem
    (xPolynomial W) (xPolynomial_monic W)
    (-Polynomial.Bivariate.swap W.polynomialX) (xPolynomial_derivative_eq W)
    (P.comap (xAdjoinRootEquiv W).toRingHom) (x_comap_ne_bot W P hP0)
    (not_mem_comap_of_image_eq (xAdjoinRootEquiv W).toRingEquiv P _ _
      (xAdjoinRootEquiv_neg_swap_polynomialX W) (by simpa using hX))
omit [WeierstrassCurve.IsElliptic W] in
theorem isDiscreteValuationRing_atPrime_of_polynomialX_not_mem
    (P : Ideal W.CoordinateRing) [P.IsPrime] (hP0 : P ≠ ⊥)
    (hX : CoordinateRing.mk W W.polynomialX ∉ P) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by
  letI : IsDiscreteValuationRing
      (Localization.AtPrime (P.comap (xAdjoinRootEquiv W).toRingHom)) :=
    isDiscreteValuationRing_atPrime_x_comap W P hP0 hX
  exact IsDiscreteValuationRing.atPrime_of_comap_ringEquiv
    (xAdjoinRootEquiv W).toRingEquiv P hP0
theorem isDedekindDomainDvr : IsDedekindDomainDvr W.CoordinateRing := by
  letI : IsNoetherianRing W.CoordinateRing := IsNoetherianRing.of_finite k[X] _
  refine { is_dvr_at_nonzero_prime := ?_ }
  intro P hP0 hPprime
  rcases coordinate_derivatives_not_both_mem W P with hX | hY
  · exact isDiscreteValuationRing_atPrime_of_polynomialX_not_mem W P hP0 hX
  · exact isDiscreteValuationRing_atPrime_of_polynomialY_not_mem W P hP0 hY
theorem isDedekindDomain : IsDedekindDomain W.CoordinateRing := by
  letI := isDedekindDomainDvr W
  infer_instance
noncomputable instance instIsDedekindDomainCoordinateRing :
    IsDedekindDomain W.CoordinateRing := isDedekindDomain W
end WeierstrassCurve.Affine.CoordinateRing
end
end



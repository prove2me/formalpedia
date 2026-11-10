-- Prove2me | Definitions.Def_APSCounting893_Main_LineGeometry
-- name    : APSCounting893_Main_LineGeometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:01:35.052299+00:00
-- url     : https://prove2.me/theorems/894c130a-471c-4786-b21f-b91d8dab6484
-- title:
--   The reduced map, graph curve, line equations and zero fiber
-- statement:
--   The reduced map has $m=n+1$, $n\ge1$, image dimension $n$ and degree bound $d\ge\max(2,\deg f_i)$. A chosen normalization $\pi_c$ and good nonempty relative open set $U\subseteq Y$ determine $V=\mathbb C^n\setminus\pi_c(Y\setminus U)$. A nonzero direction $\alpha$ is admissible when its entire line $L=\{t\alpha:t\in\mathbb C\}$ meets $V$.
--
--   Through the graph isomorphism $x\mapsto(x,F(x))$, the curve is represented by
--
--   $$D=\overline{(\pi_c\circ F)^{-1}(L\cap V)}^{\,\mathrm{Zar}}.$$
--
--   The zero fiber is $Y_0=Y\cap\pi_c^{-1}(0)$. Actual Puiseux solutions satisfy $y_i=f_i(x)$ and $\pi_c(y)=t\alpha$; their input coordinates may have negative valuation. Function-field finiteness refers to the fraction field of the actual component coordinate ring, with the map from $\mathbb C(t)$ pinned by the line parameter. Local finiteness over an open set is expressed through localization on principal opens. No residue coverage or finite-extension conclusion is built into the input data.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §§4.1–4.2, equation (4.1), p. 16, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_Geometry

set_option autoImplicit false

namespace APSCounting893.Main

/-- The reduced map has the exact dimensions and degree bound of (3.2), §4 and (4.4). -/
structure RawMap where
  n : ℕ
  F : PolynomialMap ℂ n (n + 1)
  d : ℕ

structure ReducedMap extends RawMap where
  positive : 0 < n
  degree_ge_two : 2 ≤ d
  degree_bound : ∀ i, (F i).totalDegree ≤ d
  dimension : RSCapacity.algDim (imageClosure F) = ((n : ℕ∞) : WithBot ℕ∞)

instance : Coe ReducedMap RawMap := ⟨ReducedMap.toRawMap⟩

noncomputable def betaPolynomials (F : ReducedMap) (c : Affine ℂ F.n) :
    PolynomialMap ℂ F.n F.n :=
  fun j => MvPolynomial.eval₂Hom MvPolynomial.C F.F (normalizationPolynomials c j)

/-- A finite morphism over an open subset is locally a finite module after localization.
The exponents below only express localization at the selected principal open. -/
noncomputable def FiniteOverOpen {K : Type} [Field K] {n m : ℕ}
    (X : Set (Affine K n)) (F : PolynomialMap K n m) (U : Set (Affine K m)) : Prop :=
  ∀ y ∈ U, ∃ b : Polynomials K m,
    MvPolynomial.eval y b ≠ 0 ∧
    (∀ y' ∈ evaluate F '' X, MvPolynomial.eval y' b ≠ 0 → y' ∈ U) ∧
    ∃ (s : ℕ) (generators : Fin s → Polynomials K n),
      ∀ f : Polynomials K n, ∃ (coefficients : Fin s → Polynomials K m) (exponents : Fin s → ℕ),
        ∀ x ∈ X, MvPolynomial.eval (evaluate F x) b ≠ 0 →
          MvPolynomial.eval x f = ∑ i,
            (MvPolynomial.eval (evaluate F x) (coefficients i) /
              MvPolynomial.eval (evaluate F x) b ^ exponents i) *
                MvPolynomial.eval x (generators i)

noncomputable def GoodOpen (F : ReducedMap) (U : Set (Affine ℂ (F.n + 1))) : Prop :=
  RelativeOpen (imageClosure F.F) U ∧ U.Nonempty ∧
    U ⊆ Set.range (evaluate F.F) ∧ FiniteOverOpen Set.univ F.F U

noncomputable def normalizationOpen (F : ReducedMap) (c : Affine ℂ F.n)
    (U : Set (Affine ℂ (F.n + 1))) : Set (Affine ℂ F.n) :=
  (normalization c '' (imageClosure F.F \ U))ᶜ

/-- D is represented in x coordinates through the graph isomorphism x↦(x,F(x)).
In particular it is the closure of the open inverse image, not just that inverse image. -/
noncomputable def closedGraphCurve (F : ReducedMap) (c alpha : Affine ℂ F.n)
    (U : Set (Affine ℂ (F.n + 1))) : Set (Affine ℂ F.n) :=
  RSCapacity.zClosure {x | evaluate (betaPolynomials F c) x ∈
    affineLine 0 alpha ∩ normalizationOpen F c U}

noncomputable def zeroFiber (F : ReducedMap) (c : Affine ℂ F.n) : Set (Affine ℂ (F.n + 1)) :=
  {y | y ∈ imageClosure F.F ∧ normalization c y = 0}

/-- All the data specified before Proposition 4.2, excluding its conclusions. -/
structure LineData (F : ReducedMap) where
  c : Affine ℂ F.n
  normalization : IsNormalization (imageClosure F.F) c
  U : Set (Affine ℂ (F.n + 1))
  goodOpen : GoodOpen F U
  alpha : Affine ℂ F.n
  nonzero : alpha ≠ 0
  meetsOpen : (affineLine 0 alpha ∩ normalizationOpen F c U).Nonempty

/-- The actual function-field extension, with t pulled back to β/α along the fixed line.
Its algebra structure is pinned on constants and on t. Domainhood and module finiteness are
conclusions, never hypotheses declaring the component's function field finite. -/
noncomputable def FiniteLineFunctionField (F : ReducedMap) (D : LineData F)
    (W : Set (Affine ℂ F.n)) : Prop :=
  ∃ h : IsDomain (CoordinateRing W),
    letI := h
    ∃ a : Algebra (RatFunc ℂ) (FractionRing (CoordinateRing W)),
      letI := a
      IsScalarTower ℂ (RatFunc ℂ) (FractionRing (CoordinateRing W)) ∧
      Module.Finite (RatFunc ℂ) (FractionRing (CoordinateRing W)) ∧
      ∀ i : Fin F.n,
        algebraMap (CoordinateRing W) (FractionRing (CoordinateRing W))
            (Ideal.Quotient.mk _ (betaPolynomials F D.c i)) =
          algebraMap ℂ (FractionRing (CoordinateRing W)) (D.alpha i) *
            algebraMap (RatFunc ℂ) (FractionRing (CoordinateRing W))
              (algebraMap (Polynomial ℂ) (RatFunc ℂ) Polynomial.X)

/-- The n+m affine variables are ordered x then y. -/
noncomputable def lineSolutions (F : ReducedMap) (D : LineData F) :
    Set (Affine PuiseuxAmbient (F.n + (F.n + 1))) :=
  {z | (∀ i, IsPuiseux (z i)) ∧
    (∀ j : Fin (F.n + 1), z (j.natAdd F.n) =
      MvPolynomial.eval₂ HahnSeries.C (fun i : Fin F.n => z (i.castAdd (F.n + 1))) (F.F j)) ∧
    (∀ j : Fin F.n,
      z (j.castSucc.natAdd F.n) - HahnSeries.C (D.c j) * z ((Fin.last F.n).natAdd F.n) =
        HahnSeries.C (D.alpha j) * HahnSeries.single (1 : ℚ) (1 : ℂ))}

noncomputable def outputResidue (F : ReducedMap)
    (z : Affine PuiseuxAmbient (F.n + (F.n + 1))) : Affine ℂ (F.n + 1) :=
  fun j => residue (z (j.natAdd F.n))

/-- A polynomial over C[t] in the n+m z variables: t remains a coefficient variable. -/
noncomputable def affineLineEquations (F : RawMap) (c alpha : Affine ℂ F.n) :
    Fin ((F.n + 1) + F.n) →
      MvPolynomial (Fin (F.n + (F.n + 1))) (Polynomial ℂ) :=
  Fin.addCases
    (fun j => MvPolynomial.X (j.natAdd F.n) -
      MvPolynomial.rename (fun i : Fin F.n => i.castAdd (F.n + 1))
        (MvPolynomial.map Polynomial.C (F.F j)))
    (fun j => MvPolynomial.X (j.castSucc.natAdd F.n) -
      MvPolynomial.C (Polynomial.C (c j)) * MvPolynomial.X ((Fin.last F.n).natAdd F.n) -
      MvPolynomial.C (Polynomial.C (alpha j) * Polynomial.X))

end APSCounting893.Main



-- Prove2me | Definitions.Def_HilbertSixteenth_PolyFields
-- name    : HilbertSixteenth_PolyFields
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-30T19:45:54.790989+00:00
-- url     : https://prove2.me/theorems/4697324f-f882-4862-bd8c-a1abfb8f1371
-- title:
--   Polynomial vector fields, invariant algebraic curves, algebraic limit cycles and $H_a(d)$
-- statement:
--   Write $\mathbb R[x,y]$ for real polynomials in two variables.
--
--   1. A **polynomial vector field** is a pair $V=(P,Q)$ with $P,Q\in\mathbb R[x,y]$, i.e. the system $\dot x = P(x,y)$, $\dot y=Q(x,y)$. Its **degree** is $\max(\deg P,\deg Q)$ (total degrees).
--   2. For $f\in\mathbb R[x,y]$ write $Xf = P f_x + Q f_y$. The curve $f=0$ is an **invariant algebraic curve** with **cofactor** $K\in\mathbb R[x,y]$ if $Xf = Kf$.
--   3. A limit cycle of $V$ is **algebraic** if it is contained in the real zero set $\{f=0\}$ of a non-zero polynomial $f$.
--   4. The **number of algebraic limit cycles** of $V$ is the cardinality of the set of its algebraic limit cycles, in $\mathbb N\cup\{\infty\}$.
--   5. The **algebraic Hilbert number** is
--   $$H_a(d) = \sup\{\#\text{algebraic limit cycles of } V : \deg V\le d\}\in\mathbb N\cup\{\infty\}.$$
--   6. A family $S$ of polynomials is **generic** if, with points of the affine plane taken in $\mathbb C^2$ and "distinct" meaning "not scalar multiples of each other":
--      (i) no $f\in S$ has a point where $f=f_x=f_y=0$;
--      (ii) the highest-degree homogeneous part of each $f\in S$ is square-free;
--      (iii) at every common zero of two distinct $f,g\in S$ the gradients are linearly independent, $f_xg_y-f_yg_x\ne0$;
--      (iv) no point is a common zero of three pairwise distinct members of $S$;
--      (v) the highest-degree homogeneous parts of two distinct members of $S$ have no common non-unit factor.
--      $V$ **has generic invariant curves** if the set of its irreducible invariant algebraic curves is generic.
--   7. The **generic bound** is $1+\frac{(d-1)(d-2)}2$ for even $d$ and $\frac{(d-1)(d-2)}2$ for odd $d$.
--   8. The **bounded components** of $f=0$ are the bounded connected components of its real zero set.
--
--   These objects are the language of Problems 6–7, Theorem 4, the conjectures and Christopher's theorem.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin 2) ℝ` with variable `0` as $x$ and `1` as $y$. The zero polynomial has degree $0$. Counts are `Set.encard` values in `ℕ∞` and $H_a(d)$ is an `iSup` in `ℕ∞`, so unbounded or infinite counts give $\infty$. The source's genericity conditions do not specify real or complex points; complex points are used here, which makes the genericity hypothesis of Theorem 4 stronger (hence Theorem 4 weaker).
-- source:
--   J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015), no. 3, pp. 543–554: equation (1); Problems 6–7 (algebraic limit cycle, algebraic Hilbert number $H_a(d)$); §7 equations (3)–(4) (invariant algebraic curve, cofactor); conditions (i)–(v) (generic curves) and Theorem 4 (bound); Theorem 2 (bounded components).

import Definitions.Def_HilbertSixteenth_Dynamics

/-!
# Polynomial vector fields, invariant algebraic curves and algebraic limit cycles

Source: J. Llibre, *Sobre el problema 16 de Hilbert*, La Gaceta de la RSME 18 (2015),
no. 3, 543–554: equation (1), Problems 6–7 (algebraic limit cycles, algebraic Hilbert
number), §7 equations (3)–(4) (invariant algebraic curves, cofactor), conditions (i)–(v)
(generic invariant curves), and Theorem 2 (bounded components of an algebraic curve).

Polynomials in `x, y` are elements of `MvPolynomial (Fin 2) ℝ`, with variable `0` playing
the role of `x` and variable `1` the role of `y`.
-/

namespace HilbertSixteenth

/-- Real polynomials in the two variables `x = X 0`, `y = X 1`. -/
abbrev Poly2 := MvPolynomial (Fin 2) ℝ

/-- Evaluation of a polynomial `f(x, y)` at the point `p = (x, y)`. -/
noncomputable def evalAt (f : Poly2) (p : ℝ × ℝ) : ℝ := MvPolynomial.eval ![p.1, p.2] f

/-- The real zero set `{(x, y) ∈ ℝ² : f(x, y) = 0}`. -/
def zeroSet (f : Poly2) : Set (ℝ × ℝ) := {p | evalAt f p = 0}

/-- A polynomial vector field `P ∂/∂x + Q ∂/∂y`, i.e. the system `ẋ = P(x,y), ẏ = Q(x,y)`. -/
structure PolyField where
  /-- The `x`-component `P`. -/
  P : Poly2
  /-- The `y`-component `Q`. -/
  Q : Poly2

/-- The degree of the polynomial vector field: the maximum of the degrees of `P` and `Q`. -/
noncomputable def PolyField.degree (V : PolyField) : ℕ :=
  max V.P.totalDegree V.Q.totalDegree

/-- The polynomial vector field as a map `ℝ² → ℝ²`. -/
noncomputable def PolyField.toField (V : PolyField) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (evalAt V.P p, evalAt V.Q p)

/-- The action of the vector field on polynomials: `X f = P ∂f/∂x + Q ∂f/∂y`. -/
noncomputable def PolyField.derivation (V : PolyField) (f : Poly2) : Poly2 :=
  V.P * MvPolynomial.pderiv 0 f + V.Q * MvPolynomial.pderiv 1 f

/-- `f = 0` is an invariant algebraic curve of `V` with cofactor `K`: `X f = K f`
(equation (4) of the source). -/
def IsInvariantCurve (V : PolyField) (f K : Poly2) : Prop :=
  V.derivation f = K * f

/-- An algebraic limit cycle: a limit cycle contained in the zero set of a non-zero
polynomial. -/
def IsAlgebraicLimitCycle (V : PolyField) (O : Set (ℝ × ℝ)) : Prop :=
  IsLimitCycle V.toField O ∧ ∃ f : Poly2, f ≠ 0 ∧ O ⊆ zeroSet f

/-- The number of algebraic limit cycles of `V` (in `ℕ∞`; `⊤` if there are infinitely many). -/
noncomputable def numAlgebraicLimitCycles (V : PolyField) : ℕ∞ :=
  {O : Set (ℝ × ℝ) | IsAlgebraicLimitCycle V O}.encard

/-- The algebraic Hilbert number `Hₐ(d)`: the supremum, over all polynomial vector fields of
degree at most `d`, of the number of algebraic limit cycles (`⊤` if unbounded). -/
noncomputable def algebraicHilbertNumber (d : ℕ) : ℕ∞ :=
  ⨆ (V : PolyField) (_ : V.degree ≤ d), numAlgebraicLimitCycles V

/-- The homogeneous part of highest degree of `f`. -/
noncomputable def topForm (f : Poly2) : Poly2 :=
  MvPolynomial.homogeneousComponent f.totalDegree f

/-- Evaluation of a real polynomial at a complex point `z = (z₀, z₁) ∈ ℂ²`. -/
noncomputable def cEval (f : Poly2) (z : Fin 2 → ℂ) : ℂ := MvPolynomial.aeval z f

/-- A family `S` of algebraic curves is *generic* (conditions (i)–(v) of the source, with
points of the affine plane taken in `ℂ²`; curves are distinct when they are not
associated, i.e. not scalar multiples of each other):
(i) no curve has a singular point;
(ii) the highest-degree homogeneous part of each curve is square-free;
(iii) two distinct curves meet transversally (their gradients are independent at every
common point);
(iv) no point lies on three distinct curves;
(v) the highest-degree homogeneous parts of two distinct curves have no common factor. -/
def IsGenericFamily (S : Set Poly2) : Prop :=
  (∀ f ∈ S, ∀ z : Fin 2 → ℂ,
      ¬ (cEval f z = 0 ∧ cEval (MvPolynomial.pderiv 0 f) z = 0 ∧
          cEval (MvPolynomial.pderiv 1 f) z = 0)) ∧
  (∀ f ∈ S, Squarefree (topForm f)) ∧
  (∀ f ∈ S, ∀ g ∈ S, ¬ Associated f g → ∀ z : Fin 2 → ℂ, cEval f z = 0 → cEval g z = 0 →
      cEval (MvPolynomial.pderiv 0 f) z * cEval (MvPolynomial.pderiv 1 g) z -
        cEval (MvPolynomial.pderiv 1 f) z * cEval (MvPolynomial.pderiv 0 g) z ≠ 0) ∧
  (∀ f ∈ S, ∀ g ∈ S, ∀ h ∈ S, ¬ Associated f g → ¬ Associated f h → ¬ Associated g h →
      ∀ z : Fin 2 → ℂ, ¬ (cEval f z = 0 ∧ cEval g z = 0 ∧ cEval h z = 0)) ∧
  (∀ f ∈ S, ∀ g ∈ S, ¬ Associated f g → IsRelPrime (topForm f) (topForm g))

/-- The irreducible invariant algebraic curves of `V`. -/
def invariantIrreducibleCurves (V : PolyField) : Set Poly2 :=
  {f | Irreducible f ∧ ∃ K : Poly2, IsInvariantCurve V f K}

/-- All invariant algebraic curves of `V` are generic. -/
def HasGenericInvariantCurves (V : PolyField) : Prop :=
  IsGenericFamily (invariantIrreducibleCurves V)

/-- The bound of Theorem 4: `1 + (d-1)(d-2)/2` for even `d`, `(d-1)(d-2)/2` for odd `d`. -/
def genericAlgebraicBound (d : ℕ) : ℕ :=
  if Even d then 1 + (d - 1) * (d - 2) / 2 else (d - 1) * (d - 2) / 2

/-- The bounded connected components of the real algebraic curve `f = 0`. -/
def boundedComponents (f : Poly2) : Set (Set (ℝ × ℝ)) :=
  {C | ∃ p ∈ zeroSet f, C = connectedComponentIn (zeroSet f) p ∧ Bornology.IsBounded C}

end HilbertSixteenth



-- Prove2me | Definitions.Def_HodgeComputerReflectionChart
-- name    : HodgeComputerReflectionChart
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T04:56:58.456184+00:00
-- url     : https://prove2.me/theorems/4c393496-8d4f-4c2a-bebe-51b77cc74925
-- title:
--   Reflection-chart cubic threefold and cleared relative primitive interface
-- statement:
--   This module establishes the shared polynomial interface for descending a six-variable projective sextic fourfold $V(F) \subset \mathbb{P}^5$ with a $(01)$-reflection symmetry $(X_0, Y_0) \leftrightarrow (X_1, Y_1)$ to a family of affine cubic threefolds.
--
--   Write $(\lambda, b, c, d, v)$ for five affine chart coordinates and embed them into $\mathbb{C}^6$ along the reflection-adapted affine slice
--
--   $$
--   (X_0, X_1, X_2, Y_0, Y_1, Y_2) = (1 + v,\; 1 - v,\; b,\; c + \lambda v,\; c - \lambda v,\; d).
--   $$
--
--   When $F$ and a degree-$6$ source $A$ are invariant under $(X_0, Y_0) \leftrightarrow (X_1, Y_1)$, their pullbacks depend on $v$ only through $u = v^2$, giving polynomials $f(\lambda, b, c, d, u)$ and $P(\lambda, b, c, d, u)$ with $F|_{\mathrm{chart}} = f(\lambda, b, c, d, v^2)$ and $A|_{\mathrm{chart}} = P(\lambda, b, c, d, v^2)$. After accounting for the Jacobian factor $4 v$, Poincare residue elimination along $f = 0$ asks for a cleared relative two-form primitive $\beta_j = C_j / D$ ($j \in \{b, c, d\}$) with $D \neq 0$ coprime to $f$ satisfying
--
--   $$
--   f_u^2 \sum_{j \in \{b,c,d\}} \Bigl[ f_u (D \partial_j C_j - C_j \partial_j D) - f_j (D \partial_u C_j - C_j \partial_u D) \Bigr] - 2 D^2 (f_u P_u - f_{uu} P) \equiv 0 \pmod{f}.
--   $$
--
--   For a cubic equation $f = \ell u^3 + c_2 u^2 + c_1 u + c_0$ and a source $P = p_0 + p_1 u + p_2 u^2 + p_3 u^3$ of degree at most $3$ in $u$, the cleared canonical trace coefficients
--
--   $$
--   K_0 = 6 \ell^2 p_0 - 2 \ell c_1 p_2 + (3 \ell c_0 + c_2 c_1) p_3, \qquad K_1 = 6 \ell^2 p_1 - 4 \ell c_2 p_2 + 2 c_2^2 p_3
--   $$
--
--   give the unique linear-in-$u$ representative $K_0 + K_1 u$ of $6 \ell^2 P$ after subtracting the first-order pole and trace-zero branch multiple of $f_u$ modulo $f$.
--
--   This shared definition supports reusable transport and trace-reduction theorems across reflection-invariant sextic targets such as `symmetric-sextic-residual` and `diagonal-permutation`.
--
--   **Formalization Note** Coordinates in `ChartPoly := MvPolynomial (Fin 5) ℂ` are ordered $(\lambda, b, c, d, u)$ (or $(\lambda, b, c, d, v)$ after applying the ring homomorphism `squareLift` sending $X_4 \mapsto X_4^2$). The smooth test point `normalPoint` is $(0, 0, 0, 0, i)$.
-- source:
--   Hodge.computer Sextic Fourfold Atlas, Chapter 3B (Weighted Threefolds and Reflection Charts) and Discussion #117 / #177, https://hodge.computer/#book/03b-weighted-threefolds and https://github.com/hodge-computer/sextics/discussions/117

import Definitions.Def_DiamondCertificate

set_option autoImplicit false
noncomputable section

namespace HodgeComputer.ReflectionChart
open MvPolynomial
open scoped BigOperators

/-- Five-variable chart polynomial ring in coordinates `(λ, b, c, d, u)` or `(λ, b, c, d, v)`. -/
abbrev ChartPoly := MvPolynomial (Fin 5) ℂ

/-- Reflection cover substitution `u ↦ v²` on the last coordinate (`Fin 5` index `4`). -/
def squareLift : ChartPoly →+* ChartPoly :=
  eval₂Hom C (fun i : Fin 5 => if i = 4 then X i ^ 2 else X i)

/-- Transformed double-pole source numerator `4 v P(λ, b, c, d, v²)` on the reflection chart. -/
def reflectedSource (P : ChartPoly) : ChartPoly :=
  C 4 * X 4 * squareLift P

/-- Pullback of a six-variable polynomial along the affine reflection chart
`(X₀, X₁, X₂, Y₀, Y₁, Y₂) = (1 + v, 1 - v, b, c + λ v, c - λ v, d)`. -/
def affinePullback : AmbientPoly 5 →+* ChartPoly :=
  eval₂Hom C ![1 + X 4, 1 - X 4, X 1, X 2 + X 0 * X 4, X 2 - X 0 * X 4, X 3]

/-- Canonical smooth test point `(0, 0, 0, 0, i)` on the affine reflection chart. -/
def normalPoint : Fin 5 → ℂ := ![0, 0, 0, 0, Complex.I]

/-- Cleared relative-primitive polynomial defect on the weighted cubic threefold `f(λ, b, c, d, u) = 0`:
`f_u² ∑_{j ∈ {b,c,d}} [f_u (D ∂_j C_j - C_j ∂_j D) - f_j (D ∂_u C_j - C_j ∂_u D)] - 2 D² (f_u P_u - f_{uu} P)`. -/
def cubicResidueDefect (f P D : ChartPoly) (Cvec : Fin 3 → ChartPoly) : ChartPoly :=
  (pderiv 4 f) ^ 2 *
    (∑ j : Fin 3,
      (pderiv 4 f * (D * pderiv j.succ.castSucc (Cvec j) - Cvec j * pderiv j.succ.castSucc D) -
        pderiv j.succ.castSucc f * (D * pderiv 4 (Cvec j) - Cvec j * pderiv 4 D))) -
    C 2 * D ^ 2 * (pderiv 4 f * pderiv 4 P - pderiv 4 (pderiv 4 f) * P)

/-- Existence of a cleared relative two-form primitive `β_j = C_j / D` (`j ∈ {b, c, d}`)
on the weighted threefold `f(λ, b, c, d, u) = 0` for the residue density `2(f_u P_u - f_{uu} P) / f_u³`. -/
def RelativePrimitive (f P : ChartPoly) : Prop :=
  ∃ (D : ChartPoly) (Cvec : Fin 3 → ChartPoly) (Q : ChartPoly),
    D ≠ 0 ∧ IsRelPrime f D ∧ cubicResidueDefect f P D Cvec = f * Q

/-- Cleared constant-in-`u` canonical trace coefficient `K₀` for a cubic equation
`f = ℓ u³ + c₂ u² + c₁ u + c₀` and cubic source `P = p₀ + p₁ u + p₂ u² + p₃ u³`. -/
def cubicTraceK0 (ell c2 c1 c0 p0 p2 p3 : ChartPoly) : ChartPoly :=
  C 6 * ell ^ 2 * p0 - C 2 * ell * c1 * p2 + (C 3 * ell * c0 + c2 * c1) * p3

/-- Cleared linear-in-`u` canonical trace coefficient `K₁` for a cubic equation
`f = ℓ u³ + c₂ u² + c₁ u + c₀` and cubic source `P = p₀ + p₁ u + p₂ u² + p₃ u³`. -/
def cubicTraceK1 (ell c2 p1 p2 p3 : ChartPoly) : ChartPoly :=
  C 6 * ell ^ 2 * p1 - C 4 * ell * c2 * p2 + C 2 * c2 ^ 2 * p3

end HodgeComputer.ReflectionChart



-- Prove2me | Definitions.Def_DetPermanentApprox_Main_PolynomialComputation
-- name    : DetPermanentApprox_Main_PolynomialComputation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:27:27.874939+00:00
-- url     : https://prove2.me/theorems/d78e117e-e5b2-4d0b-85fe-9f3289bf9116
-- title:
--   Explicit graph inputs and polynomial output tables
-- statement:
--   A finite graph input gives its vertex and edge counts followed by its zero-one incidence table. A constructed polynomial is represented by a table of distinct nonzero monomials, each row holding a rational coefficient and all nonnegative integer exponents. Reconstructing that table must give the specified multivariate polynomial; the row order is immaterial.
--
--   A logarithmic edge derivative is the Euler operator $w_e\,\partial/\partial w_e$ applied to a rational polynomial. Iterating this operator according to an edge list represents any fixed-order mixed logarithmic derivative, including the empty list for the value itself. Construction and evaluation input layouts expose only graph data, rational $K$, truncation degree or accuracy, supplied weights, and derivative indices. No coefficient or derivative oracle occurs in the machine syntax.
-- source:
--   Vishesh Jain, Dingding Dong, STOC 2027 submission #704 (October 2026), §3.1, pp. 11–12, Lemma 3.2 and proof (PDF pp. 11–12); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/704.pdf

import Mathlib
import Definitions.Def_DetPermanentApprox_Main_Computation
import Definitions.Def_DetPermanentApprox_Main_Surrogate

open scoped BigOperators

namespace DetPermanentApprox.Main

open Classical in
/-- Explicit incidence-table input: N, d, then d rows of N zero/one entries.
Vertex and edge enumerations are input labels, with no matching/counting oracle. -/
noncomputable def graphInput {N d : ℕ} (G : Graph (Fin N) (Fin d)) : List ℝ :=
  [(N : ℝ), (d : ℝ)] ++
    (List.ofFn fun e : Fin d =>
      List.ofFn fun v : Fin N => if Incident G v e then (1 : ℝ) else 0).flatten

/-- Output table: cell 0 is the number L of distinct nonzero monomials.
Row j, starting at 1+j(d+1), stores the coefficient followed by d exponents.
The row order is immaterial; reconstruction must give the specified polynomial. -/
def polynomialOutput {d : ℕ} (c : Configuration) (P : Poly (Fin d)) : Prop :=
  ∃ L : ℕ, ∃ coeff : Fin L → ℚ, ∃ exponent : Fin L → (Fin d → ℕ),
    c.mem 0 = (L : ℝ) ∧ Function.Injective exponent ∧
    (∀ j, coeff j ≠ 0 ∧ c.mem (1 + (j : ℤ) * (d + 1)) = (coeff j : ℝ) ∧
      ∀ e : Fin d, c.mem (2 + (j : ℤ) * (d + 1) + (e : ℤ)) = (exponent j e : ℝ)) ∧
    P = ∑ j, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm (exponent j)) (coeff j)

noncomputable def eulerDerivative {E : Type} [DecidableEq E] (e : E) (P : Poly E) : Poly E :=
  MvPolynomial.X e * MvPolynomial.pderiv e P

noncomputable def logDerivativePolynomial {E : Type} [DecidableEq E]
    (P : Poly E) (edges : List E) : Poly E :=
  edges.foldl (fun Q e => eulerDerivative e Q) P

noncomputable def taylorConstructionInput {N d : ℕ} (G : Graph (Fin N) (Fin d))
    (K : ℚ) (m : ℕ) : List ℝ :=
  graphInput G ++ [(K : ℝ), (m : ℝ)]

noncomputable def surrogateConstructionInput {N d : ℕ} (G : Graph (Fin N) (Fin d))
    (K : ℚ) (η : ℝ) : List ℝ :=
  graphInput G ++ [(K : ℝ), η]

noncomputable def evaluationInput {N d : ℕ} (G : Graph (Fin N) (Fin d))
    (K : ℚ) (m : ℕ) (w : Fin d → ℝ) (edges : List (Fin d)) : List ℝ :=
  taylorConstructionInput G K m ++ List.ofFn w ++ edges.map (fun e => (e.val : ℝ))

noncomputable def surrogateEvaluationInput {N d : ℕ} (G : Graph (Fin N) (Fin d))
    (K : ℚ) (η : ℝ) (w : Fin d → ℝ) (edges : List (Fin d)) : List ℝ :=
  surrogateConstructionInput G K η ++ List.ofFn w ++ edges.map (fun e => (e.val : ℝ))

end DetPermanentApprox.Main



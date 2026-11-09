-- Prove2me | Definitions.Def_CatalyticMatching_General_WeightedPfaffian
-- name    : CatalyticMatching_General_WeightedPfaffian
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:38.996637+00:00
-- url     : https://prove2.me/theorems/ee008f4f-8f78-4905-b2e0-6b2af057c6ab
-- title:
--   Weighted Pfaffians, edge components, and matching coefficients
-- statement:
--   Given a rational evaluation $T'$ and natural edge weights $W$, set $A_{ij}=T'_{ij}z^{W(\{i,j\})}$. For a selected edge $e$, replace its two entries by $T'_{ij}y$ and $T'_{ji}y$ to obtain $A_e$ over $\mathbb Q[z][y]$. Define $P_{0,e}$ and $P_{1,e}$ as its Pfaffian's coefficients of $y^0$ and $y^1$.
--
--   $$c_M=[\prod_{e\in M}x_e]\operatorname{Pf}(T'_X),\quad c_w=\sum_{M:W(M)=w}c_M,\quad c_w^{\bar e}=\sum_{M:W(M)=w,e\notin M}c_M,\quad c_w^e=c_w-c_w^{\bar e}.$$
--
--   All sums range over the referenced finite family of perfect matchings. The selected edge set is $\{e:c_w^{\bar e}=0\}$. Zero evaluated entries and cancellation are allowed. This supplies actual algebraic objects for the threshold dichotomy, without assuming nonzero component polynomials or isolation.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §3.2.1 pp.17–18

import Definitions.Def_CatalyticMatching_General_Tutte
import Definitions.Def_CatalyticMatching_General_Pfaffian

namespace CatalyticMatching.General

/-- A=T'∘W over ℚ[z], §3.2.1 p.17. -/
noncomputable def weightedMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) :
    Matrix (Fin n) (Fin n) (Polynomial ℚ) :=
  tutteEval G (fun e => Polynomial.monomial (W e) (a e))

/-- A_e over ℚ[z][y]; the selected edge loses its z weight. -/
noncomputable def edgeMatrix {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (e : G.edgeSet) :
    Matrix (Fin n) (Fin n) (Polynomial (Polynomial ℚ)) := by
  classical
  exact tutteEval G (fun f => if f = e then
    Polynomial.C (Polynomial.C (a f)) * Polynomial.X
    else Polynomial.C (Polynomial.monomial (W f) (a f)))

noncomputable def P0 {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (e : G.edgeSet) : Polynomial ℚ :=
  (pfaffian (edgeMatrix G a W e)).coeff 0

noncomputable def P1 {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (e : G.edgeSet) : Polynomial ℚ :=
  (pfaffian (edgeMatrix G a W e)).coeff 1

/-- c_M is the actual multivariate Pfaffian coefficient of ∏_{e∈M} x_e. -/
noncomputable def matchingCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (M : Finset G.edgeSet) : ℚ := by
  classical
  exact MvPolynomial.coeff (∑ e ∈ M, Finsupp.single e 1)
    (pfaffian (tutteEval G (fun e => MvPolynomial.C (a e) * MvPolynomial.X e)))

/-- c_w, including all cancellations and zero evaluated edges. -/
noncomputable def weightCoefficient {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (w : ℕ) : ℚ := by
  classical
  exact ∑ M ∈ ((MulmuleyVV.Matching.perfectMatchings G).filter
    (fun M => (∑ f ∈ M, W f) = w)), matchingCoefficient G a M

noncomputable def coefficientWithout {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (e : G.edgeSet) (w : ℕ) : ℚ := by
  classical
  exact ∑ M ∈ ((MulmuleyVV.Matching.perfectMatchings G).filter
    (fun M => (∑ f ∈ M, W f) = w ∧ e ∉ M)), matchingCoefficient G a M

/-- c_w^e = c_w - c_w^{bar e}. -/
noncomputable def coefficientWith {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (e : G.edgeSet) (w : ℕ) : ℚ :=
  weightCoefficient G a W w - coefficientWithout G a W e w

noncomputable def coefficientMatching {n : ℕ} (G : SimpleGraph (Fin n))
    (a : G.edgeSet → ℚ) (W : G.edgeSet → ℕ) (w : ℕ) : Finset G.edgeSet := by
  classical
  exact Finset.univ.filter (fun e => coefficientWithout G a W e w = 0)

end CatalyticMatching.General



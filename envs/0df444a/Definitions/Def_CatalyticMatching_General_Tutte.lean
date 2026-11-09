-- Prove2me | Definitions.Def_CatalyticMatching_General_Tutte
-- name    : CatalyticMatching_General_Tutte
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:43.749038+00:00
-- url     : https://prove2.me/theorems/ffb9a7dc-cd09-49e3-ac3d-3a70b6cb6ae4
-- title:
--   Rational Tutte evaluations, generic rank, and rank deficiency
-- statement:
--   For each edge $e=\{i,j\}$ with $i<j$, a Tutte evaluation has entry $a_e$ at $(i,j)$ and $-a_e$ at $(j,i)$; every other entry is zero. The generic matrix replaces $a_e$ by independent variables and computes rank over $\mathbb Q(x_e:e\in E)$. A perturbation updates one edge assignment, hence both skew entries.
--
--   $$D(B)=\{u:\operatorname{rank}(B\setminus\{u\})=\operatorname{rank}B\}.$$
--
--   Deletion removes the same row and column. The finite test range is the rational image of $\{1,\ldots,n^{10}\}$. These objects are computed from the graph and assignment; neither maximum rank nor the identity with $2\nu(G)$ is assumed.
-- source:
--   Srijan Chakraborty, Samir Datta, Aryan Kusre, Partha Mukhopadhyay, Amit Sinhababu, Maximum Matching and Related Problems in Catalytic Logspace, STOC 2027 submission #479 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/479.pdf, §1 pp.4–6; §3.1 p.11

import Definitions.Def_CatalyticMatching_General_Encoding

namespace CatalyticMatching.General

/-- Rational or symbolic Tutte evaluation; changing an edge changes both entries. -/
noncomputable def tutteEval {n : ℕ} (G : SimpleGraph (Fin n))
    {R : Type} [Ring R] (a : G.edgeSet → R) : Matrix (Fin n) (Fin n) R := by
  classical
  exact fun i j => if h : G.Adj i j then
    if i < j then a ⟨s(i,j), G.mem_edgeSet.mpr h⟩
    else -a ⟨s(i,j), G.mem_edgeSet.mpr h⟩ else 0

abbrev TutteField {n : ℕ} (G : SimpleGraph (Fin n)) :=
  FractionRing (MvPolynomial G.edgeSet ℚ)

noncomputable def genericTutte {n : ℕ} (G : SimpleGraph (Fin n)) :
    Matrix (Fin n) (Fin n) (TutteField G) :=
  tutteEval G (fun e => algebraMap (MvPolynomial G.edgeSet ℚ) (TutteField G)
    (MvPolynomial.X e))

/-- Delete the same row and column; no unproved algebraic identity is assumed. -/
noncomputable def deficiency {n : ℕ} {K : Type} [Field K]
    (B : Matrix (Fin n) (Fin n) K) : Set (Fin n) := by
  classical
  exact {u | (B.submatrix (fun v : {v : Fin n // v ≠ u} => v.val)
    (fun v : {v : Fin n // v ≠ u} => v.val)).rank = B.rank}

noncomputable def perturb {n : ℕ} {G : SimpleGraph (Fin n)}
    (a : G.edgeSet → ℚ) (e : G.edgeSet) (b : ℚ) : G.edgeSet → ℚ := by
  classical
  exact Function.update a e b

/-- The printed [n¹⁰] is {1,...,n¹⁰}, embedded in ℚ. -/
def TestValue (n : ℕ) (a : ℚ) : Prop := ∃ j : ℕ, 1 ≤ j ∧ j ≤ n^10 ∧ a = j

end CatalyticMatching.General



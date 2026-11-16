-- Prove2me | Definitions.Def_OddPermSum_Evaluation_Supplement_generatingPolynomial
-- name    : OddPermSum_Evaluation_Supplement_generatingPolynomial
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:34:32.86114+00:00
-- url     : https://prove2.me/theorems/0a0fa093-fb6d-4b61-837b-d398281f9329
-- title:
--   The cycle polynomial and its arc derivatives
-- statement:
--   Over a field $F$, assign an independent variable $w_e$ to each arc of $D$. With $W(w)_{u,v}=w_{(u,v)}$ on arcs and zero elsewhere, define
--   $$Q(z,w)=\Phi(I+zW(w)),\qquad Q_e(z,w)=w_e\frac{\partial Q}{\partial w_e}(z,w).$$
--   The coefficient ring is $F[w_e:e\in E]$, and $z$ is a separate polynomial variable. The monomial of a cycle is the product of its arc variables, each occurring once.
--
--   The published permutation polynomial defines $\Phi$ independently of the graph, while coefficientwise formal differentiation defines $Q_e$.
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 13, Eqs. (5.1), (5.3)

import Definitions.Def_OddPermSum_Evaluation_Supplement_digraph
import Definitions.Def_OddPermSum_Evaluation_gradient

set_option autoImplicit false

namespace OddPermSum.Evaluation.Supplement

noncomputable def cycleMonomial {F : Type*} [Field F] {n : ℕ} (D : Digraph n)
    (C : Finset (Fin n × Fin n)) : MvPolynomial D.Arc F := by
  classical
  exact ∏ e : D.Arc, if e.val ∈ C then MvPolynomial.X e else 1

noncomputable def symbolicAdjacency {F : Type*} [Field F] {n : ℕ} (D : Digraph n) :
    Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial D.Arc F)) := by
  classical
  exact fun i j => if h : (i,j) ∈ D.arcs then Polynomial.C (MvPolynomial.X ⟨(i,j),h⟩) else 0

noncomputable def generatingQ {F : Type*} [Field F] {n : ℕ} (D : Digraph n) :
    Polynomial (MvPolynomial D.Arc F) :=
  phi (1 + (Polynomial.X : Polynomial (MvPolynomial D.Arc F)) • symbolicAdjacency (F := F) D)

/-- Coefficientwise formal differentiation in an arc variable, followed by multiplication by it. -/
noncomputable def arcQ {F : Type*} [Field F] {n : ℕ} (D : Digraph n) (e : D.Arc) :
    Polynomial (MvPolynomial D.Arc F) :=
  (generatingQ (F := F) D).sum fun r c =>
    Polynomial.monomial r (MvPolynomial.X e * MvPolynomial.pderiv e c)

end OddPermSum.Evaluation.Supplement



-- Prove2me | Definitions.Def_MonoABPWidth_Hierarchy_Supplement_formulas
-- name    : MonoABPWidth_Hierarchy_Supplement_formulas
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:33:18.554199+00:00
-- url     : https://prove2.me/theorems/2f45f754-b2d5-4038-b4e8-4a72f2a8b955
-- title:
--   Real monotone formula trees and their exact resources
-- statement:
--   A real monotone formula is a finite rooted tree. Each leaf is either a nonnegative real constant or a nonnegative real scalar multiple of a variable. Each internal gate adds or multiplies a positive finite number of children; unary gates are permitted. Evaluation uses polynomial sum and product. Leaves have depth zero and count as one gate and one leaf. For an internal gate with children $F_i$,
--   $$s(F)=1+\sum_i s(F_i),\qquad \lambda(F)=\sum_i\lambda(F_i),\qquad d(F)=1+\max_i d(F_i).$$
--   Addition depth and multiplication depth count their respective gates along the longest path. Alternation forbids adjacent internal gates of the same type. Root predicates distinguish the two operations. This generic tree model imposes neither homogeneity nor an order on variables.
--
--   Two numerical functions also record the IMM leaf bounds: the lower expression $n k^{d(n^{1/d}-1)}$ for $d>0$, extended to $n$ at $d=0,n\le1$ and $+\infty$ at $d=0,n\ge2$, and the integer upper count $n k^{d(\lceil n^{1/d}\rceil-1)}$ for $d\ge1$. These functions do not constrain formula trees or their evaluation.
-- source:
--   Julian Dörfler, Alexander Rogovskyy, STOC 2027 submission #927 (October 2026), §2.3, p.5, PDF6; Lemma 5.4 and Theorem 5.6, p.14, PDF15; depth-zero extension p.21, PDF22

import Definitions.Def_MonoABPWidth_Hierarchy_polynomials

open scoped BigOperators ENNReal

namespace MonoABPWidth.Hierarchy.Supplement

/-- §2.3: finite arbitrary-fan-in monotone formula trees. Internal gates have
positive fan-in, including unary gates. Constants include zero. A scalar-variable
leaf counts as one leaf and has depth zero. -/
inductive Formula (σ : Type) where
  | constant (c : NNReal)
  | variable (c : NNReal) (x : σ)
  | add (arity : ℕ) (child : Fin (arity + 1) → Formula σ)
  | mul (arity : ℕ) (child : Fin (arity + 1) → Formula σ)

noncomputable def Formula.eval {σ : Type} : Formula σ → MvPolynomial σ ℝ
  | .constant c => MvPolynomial.C (c : ℝ)
  | .variable c x => MvPolynomial.C (c : ℝ) * MvPolynomial.X x
  | .add _ f => ∑ i, (f i).eval
  | .mul _ f => ∏ i, (f i).eval

def Formula.leaves {σ : Type} : Formula σ → ℕ
  | .constant _ | .variable _ _ => 1
  | .add _ f | .mul _ f => ∑ i, (f i).leaves

def Formula.size {σ : Type} : Formula σ → ℕ
  | .constant _ | .variable _ _ => 1
  | .add _ f | .mul _ f => 1 + ∑ i, (f i).size

def Formula.depth {σ : Type} : Formula σ → ℕ
  | .constant _ | .variable _ _ => 0
  | .add _ f | .mul _ f => 1 + Finset.univ.sup (fun i => (f i).depth)

def Formula.addDepth {σ : Type} : Formula σ → ℕ
  | .constant _ | .variable _ _ => 0
  | .add _ f => 1 + Finset.univ.sup (fun i => (f i).addDepth)
  | .mul _ f => Finset.univ.sup (fun i => (f i).addDepth)

def Formula.mulDepth {σ : Type} : Formula σ → ℕ
  | .constant _ | .variable _ _ => 0
  | .add _ f => Finset.univ.sup (fun i => (f i).mulDepth)
  | .mul _ f => 1 + Finset.univ.sup (fun i => (f i).mulDepth)

def Formula.addRoot {σ : Type} : Formula σ → Prop
  | .add _ _ => True
  | _ => False

def Formula.mulRoot {σ : Type} : Formula σ → Prop
  | .mul _ _ => True
  | _ => False

/-- Alternation of adjacent internal gate types; leaves have no gate type. -/
def Formula.Alternating {σ : Type} : Formula σ → Prop
  | .constant _ | .variable _ _ => True
  | .add _ f => ∀ i, ¬ (f i).addRoot ∧ (f i).Alternating
  | .mul _ f => ∀ i, ¬ (f i).mulRoot ∧ (f i).Alternating

/-- The exact positive-depth expression of Theorem 5.6, extended as in its proof
on p.21 to depth zero: n for n≤1, and infinity otherwise. -/
noncomputable def immLeafLower (k n d : ℕ) : ℝ≥0∞ :=
  if d = 0 then (if n ≤ 1 then (n : ℝ≥0∞) else ⊤)
  else ENNReal.ofReal ((n : ℝ) * (k : ℝ) ^
    ((d : ℝ) * ((n : ℝ) ^ (1 / (d : ℝ)) - 1)))

/-- Exact integer leaf count of Lemma 5.4; d≥1 is its domain. -/
noncomputable def immLeafUpper (k n d : ℕ) : ℕ :=
  n * k ^ (d * (Nat.ceil ((n : ℝ) ^ (1 / (d : ℝ))) - 1))

end MonoABPWidth.Hierarchy.Supplement



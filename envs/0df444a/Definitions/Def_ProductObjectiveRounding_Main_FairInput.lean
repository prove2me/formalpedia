-- Prove2me | Definitions.Def_ProductObjectiveRounding_Main_FairInput
-- name    : ProductObjectiveRounding_Main_FairInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:59.081731+00:00
-- url     : https://prove2.me/theorems/0ce0004d-6fd0-47c1-b438-9fe097feb05b
-- title:
--   Fair-sign products and prepared sparse incidence views
-- statement:
--   For nonnegative weights and real coefficients with $|b_{ij}|\le1$, a fair-sign objective is
--   $$F(x)=\sum_i w_i\prod_{j\in S_i}(1+b_{ij}x_j),\qquad x_j\in\{-1,1\}.$$
--   Supports are nonempty and cover the variable labels. The support size $m$ counts incidences. An explicit ambient $n$ bounds the number of rows plus variables and remains fixed for auxiliary calls. Prepared views contain the row and variable permutations of common incidence identifiers and their segment boundaries; the cross-pointers are inverse permutation compositions. Legality checks their ordering and boundaries. The fractional extension is the same polynomial on real vectors; mass bounds sum $|b_{ij}|^p$ over each row.
--
--   These data describe the internal fair-sign setting of all four milestones. They impose no fair-sign or mass restriction on the goal's arbitrary-marginal input. A Boolean represents a sign by false $\mapsto-1$ and true $\mapsto1$.
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, §4, (5), pp.12–13, fair-sign instances and input representation

import Definitions.Def_ProductObjectiveRounding_Main_Input

open scoped BigOperators
noncomputable section

namespace ProductObjectiveRounding.Main

/-- Prepared views are permutations of the same incidence identifiers (p.13). -/
structure IncidenceViews (s : SparseShape) where
  rowOrder : Equiv.Perm (Fin s.m)
  variableOrder : Equiv.Perm (Fin s.m)
  rowStart : Fin (s.k + 1) → ℕ
  variableStart : Fin (s.u + 1) → ℕ

def IncidenceViews.Valid {s : SparseShape} (v : IncidenceViews s) : Prop :=
  (∀ a b, a < b →
    (s.row (v.rowOrder a) < s.row (v.rowOrder b) ∨
      (s.row (v.rowOrder a) = s.row (v.rowOrder b) ∧
        s.varIndex (v.rowOrder a) < s.varIndex (v.rowOrder b)))) ∧
  (∀ a b, a < b →
    (s.varIndex (v.variableOrder a) < s.varIndex (v.variableOrder b) ∨
      (s.varIndex (v.variableOrder a) = s.varIndex (v.variableOrder b) ∧
        s.row (v.variableOrder a) < s.row (v.variableOrder b)))) ∧
  (∀ i, v.rowStart i = (Finset.univ.filter (fun e => (s.row e).val < i.val)).card) ∧
  (∀ j, v.variableStart j =
    (Finset.univ.filter (fun e => (s.varIndex e).val < j.val)).card)

def IncidenceViews.rowToVariable {s : SparseShape} (v : IncidenceViews s)
    (a : Fin s.m) : Fin s.m := v.variableOrder.symm (v.rowOrder a)

def IncidenceViews.variableToRow {s : SparseShape} (v : IncidenceViews s)
    (a : Fin s.m) : Fin s.m := v.rowOrder.symm (v.variableOrder a)

/-- Ambient n remains fixed for auxiliary calls, and need not equal local u+k. -/
structure FairInput where
  shape : SparseShape
  ambient : ℕ
  weight : Fin shape.k → ℝ
  coefficient : Fin shape.m → ℝ
  views : IncidenceViews shape

def FairInput.Legal (I : FairInput) : Prop :=
  I.shape.Simple ∧ I.shape.n ≤ I.ambient ∧
  (∀ i, (I.shape.rowEntries i).Nonempty) ∧
  (∀ j, ∃ e, I.shape.varIndex e = j) ∧
  (∀ i, 0 ≤ I.weight i) ∧ (∀ e, |I.coefficient e| ≤ 1) ∧ I.views.Valid

def FairInput.W (I : FairInput) : ℝ := ∑ i, I.weight i

def sign (b : Bool) : ℝ := if b then 1 else -1

def FairInput.fractionalF (I : FairInput) (y : Fin I.shape.u → ℝ) : ℝ :=
  ∑ i, I.weight i * ∏ e ∈ I.shape.rowEntries i,
    (1 + I.coefficient e * y (I.shape.varIndex e))

def FairInput.F (I : FairInput) (x : Fin I.shape.u → Bool) : ℝ :=
  I.fractionalF (fun j => sign (x j))

def FairInput.MassBound (I : FairInput) (power : ℕ) (B : ℝ) : Prop :=
  ∀ i, ∑ e ∈ I.shape.rowEntries i, |I.coefficient e| ^ power ≤ B

end ProductObjectiveRounding.Main



-- Prove2me | Definitions.Def_ProductObjectiveRounding_Main_Input
-- name    : ProductObjectiveRounding_Main_Input
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:21.281628+00:00
-- url     : https://prove2.me/theorems/71c09eee-009a-4a41-99bf-8e6a8a550c03
-- title:
--   Normalized sparse product inputs and finite Bernoulli expectations
-- statement:
--   A finite sparse input explicitly lists its variable and row counts, incidence identifiers, nonnegative real weights, binary marginals and two nonnegative real endpoints per incidence. Incidence pairs are distinct within a row. Legality requires $p_j\in[0,1]$ and $(1-p_j)f_{ij}(0)+p_jf_{ij}(1)=1$ for every incidence.
--
--   The objective and expectation baseline are
--   $$F(x)=\sum_i w_i\prod_{j\in S_i}f_{ij}(x_j),\qquad W=\sum_iw_i.$$
--   The finite product probability mass is $\prod_jp_j^{x_j}(1-p_j)^{1-x_j}$, interpreted directly as a choice of $p_j$ or $1-p_j$, including endpoints. The expectation is the finite sum against this mass. The fractional extension replaces each endpoint by its affine interpolation. This package supplies the data shared by every theorem, with $n=u+k$ and $N=n+m$, and retains empty rows, isolated variables and zero weights.
-- source:
--   Chase Hutton, Adam Melrod, STOC 2027 submission #1466 (October 2026); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1466.pdf, §1.1, (1), p.3; §1.2, p.4; §4.5, p.21

import Mathlib

open scoped BigOperators
noncomputable section

namespace ProductObjectiveRounding.Main

/-- Sparse incidence labels; input order is unrestricted. Source (1), p.3, and p.13. -/
structure SparseShape where
  u : ℕ
  k : ℕ
  m : ℕ
  row : Fin m → Fin k
  varIndex : Fin m → Fin u

def SparseShape.Simple (s : SparseShape) : Prop :=
  Function.Injective (fun e => (s.row e, s.varIndex e))

def SparseShape.rowEntries (s : SparseShape) (i : Fin s.k) : Finset (Fin s.m) :=
  Finset.univ.filter (fun e => s.row e = i)

def SparseShape.n (s : SparseShape) : ℕ := s.u + s.k

def SparseShape.size (s : SparseShape) : ℕ := s.n + s.m

/-- All numerical data are real; legality is a separate predicate, not an algorithm certificate. -/
structure ProductInput where
  shape : SparseShape
  weight : Fin shape.k → ℝ
  marginal : Fin shape.u → ℝ
  endpoint : Fin shape.m → Bool → ℝ

def ProductInput.Legal (I : ProductInput) : Prop :=
  I.shape.Simple ∧ (∀ i, 0 ≤ I.weight i) ∧
  (∀ j, 0 ≤ I.marginal j ∧ I.marginal j ≤ 1) ∧
  (∀ e b, 0 ≤ I.endpoint e b) ∧
  ∀ e, (1 - I.marginal (I.shape.varIndex e)) * I.endpoint e false +
    I.marginal (I.shape.varIndex e) * I.endpoint e true = 1

def ProductInput.W (I : ProductInput) : ℝ := ∑ i, I.weight i

def ProductInput.F (I : ProductInput) (x : Fin I.shape.u → Bool) : ℝ :=
  ∑ i, I.weight i * ∏ e ∈ I.shape.rowEntries i, I.endpoint e (x (I.shape.varIndex e))

/-- Elementary finite Bernoulli product mass, on every binary assignment, including zero-probability assignments. -/
def binaryProductMass {u : ℕ} (p : Fin u → ℝ) (x : Fin u → Bool) : ℝ :=
  ∏ j, if x j then p j else 1 - p j

def ProductInput.expectation (I : ProductInput) : ℝ :=
  ∑ x : Fin I.shape.u → Bool, binaryProductMass I.marginal x * I.F x

/-- Fractional multilinear extension in §4.5, p.21. -/
def ProductInput.fractionalF (I : ProductInput) (q : Fin I.shape.u → ℝ) : ℝ :=
  ∑ i, I.weight i * ∏ e ∈ I.shape.rowEntries i,
    ((1 - q (I.shape.varIndex e)) * I.endpoint e false +
      q (I.shape.varIndex e) * I.endpoint e true)

end ProductObjectiveRounding.Main



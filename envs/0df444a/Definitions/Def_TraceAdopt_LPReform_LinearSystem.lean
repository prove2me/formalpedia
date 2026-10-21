-- Prove2me | Definitions.Def_TraceAdopt_LPReform_LinearSystem
-- name    : TraceAdopt_LPReform_LinearSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:42.777995+00:00
-- url     : https://prove2.me/theorems/d46fecb7-720e-4bde-bd4d-ad143a69546b
-- title:
--   Finite linear systems and intersection graphs
-- statement:
--   For a finite real linear system $Az\ge b$, split the coordinates as $z=(x,y)$, where $x\in\mathbb R^n$ are visible and $y\in\mathbb R^N$ are auxiliary. A pair $(x,y)$ is feasible exactly when
--
--   $$b_k\le\sum_v A_{kv}z_v\qquad\text{for every row }k.$$
--
--   The **intersection graph** of a family of finite row supports has one vertex per variable, with two distinct variables adjacent exactly when they occur together in at least one row. This general linear-programming interface is shared by the generic treewidth formulation and the paper's target formulation.
--
--   **Formalization Note** Equalities can be expressed as two inequalities. Both variables and constraints count toward formulation size.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 15, equation (3), Definition 4; p. 19, equation (7)

import Mathlib

namespace TraceAdopt.LPReform

/-- Feasibility of a finite linear system `Az ≥ b`, with visible coordinates `x` and
auxiliary coordinates `y`. This is the generic LP object used in Proposition 4 and Theorem 2. -/
def LinFeasible {n N K : ℕ}
    (A : Matrix (Fin K) (Fin n ⊕ Fin N) ℝ) (b : Fin K → ℝ)
    (x : Fin n → ℝ) (y : Fin N → ℝ) : Prop :=
  ∀ k, b k ≤ ∑ v, A k v * Sum.elim x y v

/-- Definition 4, p. 15: variables are adjacent when they occur together in a row. -/
def intersectionGraph {V ι : Type} (supp : ι → Finset V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ k, u ∈ supp k ∧ v ∈ supp k
  symm := by
    constructor
    intro u v h
    obtain ⟨hne, k, hu, hv⟩ := h
    exact ⟨Ne.symm hne, k, hv, hu⟩
  loopless := by
    constructor
    intro u h
    exact h.1 rfl

end TraceAdopt.LPReform



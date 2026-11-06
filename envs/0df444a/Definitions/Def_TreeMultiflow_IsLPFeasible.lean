-- Prove2me | Definitions.Def_TreeMultiflow_IsLPFeasible
-- name    : TreeMultiflow_IsLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:56.339753+00:00
-- url     : https://prove2.me/theorems/10789c27-7e2c-4eae-a6c6-1be53c41e735
-- title:
--   Feasible solution of the LP relaxation (1)
-- statement:
--   A vector $x\in\mathbb R^F$ is a **feasible solution of (1)** if
--   $$
--   \sum_{f\in F:\ e\in\mathrm{Path}(f)} x_f\le u_e\quad\text{for every edge } e,\qquad 0\le x_f\le 1\quad\text{for every request } f.
--   $$
--
--   This is the constraint system of the natural LP relaxation of unit-demand multicommodity flow on trees; the same system with capacities $c_e$ is the hypothesis of Theorem 2.1.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Section 1, p.2, LP (1)

import Mathlib
import Definitions.Def_TreeMultiflow_OnPath

namespace TreeMultiflow

open Classical in
/-- **Feasible solution of the LP relaxation (1).**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Section 1,
p.2, LP (1): "subject to Σ_{f∈F : e∈Path(f)} x_f ≤ uₑ for every edge e, 0 ≤ x_f ≤ 1 for every
request f."

`IsLPFeasible G u src dst x` says `0 ≤ x f ≤ 1` for every request `f`, and for every edge `e` of
the tree the sum of `x f` over the requests whose path uses `e` is at most `u e`.

**Formalization Note.** Requests form a finite index type `F`; `x : F → ℝ`. Capacities are
natural numbers cast to `ℝ`; only edges of `G` are constrained. -/
def IsLPFeasible {V F : Type*} [Fintype F] (G : SimpleGraph V) (u : Sym2 V → ℕ)
    (src dst : F → V) (x : F → ℝ) : Prop :=
  (∀ f, 0 ≤ x f ∧ x f ≤ 1) ∧
    ∀ e ∈ G.edgeSet,
      ∑ f ∈ Finset.univ.filter (fun f => OnPath G (src f) (dst f) e), x f ≤ (u e : ℝ)

end TreeMultiflow



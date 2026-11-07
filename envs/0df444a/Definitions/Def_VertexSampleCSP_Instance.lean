-- Prove2me | Definitions.Def_VertexSampleCSP_Instance
-- name    : VertexSampleCSP_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:28.036993+00:00
-- url     : https://prove2.me/theorems/9ab4ac82-cdfb-4e79-a527-582ee3b19b06
-- title:
--   Instance of a constraint satisfaction problem of arity $r$ over $[q]$, and its value $F_{\mathcal I}(\sigma)$
-- statement:
--   An **instance** $\mathcal I$ of arity $r$ over the alphabet $[q]$ on a finite set $V$ of variables consists of a real payoff table $f_e:[q]^e\to\mathbb R$ for each $r$-subset $e\subseteq V$. Its **value** at an assignment $\sigma\in[q]^V$ is
--
--   $$F_{\mathcal I}(\sigma)=\sum_e f_e(\sigma_e),$$
--
--   the sum over the $r$-subsets $e\subseteq V$, where $\sigma_e$ is the restriction of $\sigma$ to $e$.
--
--   This is the model of the whole mission: it contains Max-$r$-SAT, Max-$r$-CSP with arbitrary predicates, Max-$q$-Cut and Max-Cut of $r$-uniform hypergraphs. Several constraints on one set are merged into one table, so there is exactly one table per $r$-subset.
--
--   **Formalization Note** The alphabet is `Fin q`. The structure carries a table for every finite subset of $V$, but only the tables on $r$-subsets are ever read: every sum in the mission runs over the $r$-subsets, so tables on sets of another size have no effect.
-- source:
--   Chang, Optimal Vertex Sampling for Constraint Satisfaction Problems, STOC 2027 submission (manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4); Appendix A, "Instances", p.13 (PDF p.15)

import Mathlib

namespace VertexSampleCSP

/-- **Instance of a constraint satisfaction problem of arity `r` over `[q]`.**
Chang, *Optimal Vertex Sampling for Constraint Satisfaction Problems*, STOC 2027 submission
(manuscript sha256 1e0edd23…), §1.1, p.2 (PDF p.4), and Appendix A, "Instances", p.13 (PDF p.15):
"An instance I of arity r ≥ 2 over [q] on a finite set V of variables consists of real tables
fe : [q]^e → ℝ, one for each r-subset e ⊆ V."

`I.f e a` is the payoff of the table on the set `e` at the assignment `a : e → Fin q`.

**Formalization Note.** The alphabet `[q] = {1, …, q}` is `Fin q = {0, …, q − 1}`. The field `f`
carries a table for every finite subset `e` of `V`, but only the tables on the `r`-subsets are ever
used: the value, the number of constraints, the scale `Γ` and the payoff tensor all sum over
`Finset.powersetCard r Finset.univ`. The tables on sets of another size are ignored (so the model has
exactly one table per `r`-subset, as in footnote 1, p.2). -/
structure Instance (V : Type*) [Fintype V] [DecidableEq V] (r q : ℕ) where
  /-- The payoff table `f_e : [q]^e → ℝ` of the set `e`. -/
  f : (e : Finset V) → (e → Fin q) → ℝ

/-- **Value `F_I(σ)` of an assignment.** Chang, STOC 2027 submission (manuscript sha256 1e0edd23…),
Appendix A, "Instances", p.13 (PDF p.15): `F_I(σ) = Σ_e f_e(σ_e)`, the sum over the `r`-subsets
`e ⊆ V` of the payoff of the table of `e` at the restriction `σ_e` of `σ` to `e`. -/
noncomputable def Instance.value {V : Type*} [Fintype V] [DecidableEq V] {r q : ℕ}
    (I : Instance V r q) (σ : V → Fin q) : ℝ :=
  ∑ e ∈ Finset.powersetCard r Finset.univ, I.f e (fun i => σ i)

end VertexSampleCSP



-- Prove2me | Definitions.Def_DDROFB_HasIndepComponents
-- name    : DDROFB_HasIndepComponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:04:31.903088+00:00
-- url     : https://prove2.me/theorems/973a6978-e90b-4a53-97ca-4c7524babe44
-- title:
--   A law on $\mathbb R^d$ with independent components
-- statement:
--   A measure $\mathbb P$ on $\mathbb R^d$, the law of $\tilde u = (\tilde u_1,\dots,\tilde u_d)$, **has independent components** if the coordinates $\tilde u_1,\dots,\tilde u_d$ are mutually independent under $\mathbb P$:
--
--   $$
--   \mathbb P\bigl(\tilde u_{i_1} \in A_1, \dots, \tilde u_{i_k} \in A_k\bigr) \;=\; \prod_{j=1}^k \mathbb P(\tilde u_{i_j} \in A_j)
--   $$
--
--   for all distinct indices $i_1,\dots,i_k$ and Borel sets $A_1,\dots,A_k \subseteq \mathbb R$.
--
--   Independence is the structural assumption under which the deviation bound of Chen, Sim and Sun applies, and it is the hypothesis of Theorem 6.
--
--   **Formalization Note** Mutual independence is Mathlib's `ProbabilityTheory.iIndepFun` applied to the family of coordinate maps of `EuclideanSpace ℝ (Fin d)`.
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 2 and Theorem 6, p. 19 ("P∗ has independent components")

import Mathlib
open MeasureTheory

namespace DDROFB

/-- **A law with independent components.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, p. 2 and
Theorem 6, p. 19 (unnumbered): "`P∗` has independent components".

`HasIndepComponents P` says the coordinate maps `u ↦ u_1, …, u ↦ u_d` are mutually independent
under `P`.

**Formalization Note.** Mutual independence is Mathlib's `ProbabilityTheory.iIndepFun` of the
family of coordinate maps of `EuclideanSpace ℝ (Fin d)`. -/
def HasIndepComponents {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  ProbabilityTheory.iIndepFun (fun (i : Fin d) (u : EuclideanSpace ℝ (Fin d)) => u i) P

end DDROFB



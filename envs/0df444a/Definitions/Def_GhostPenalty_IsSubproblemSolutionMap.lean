-- Prove2me | Definitions.Def_GhostPenalty_IsSubproblemSolutionMap
-- name    : GhostPenalty_IsSubproblemSolutionMap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:28.647213+00:00
-- url     : https://prove2.me/theorems/a555c043-14e2-4cee-9b12-0b2dd0240778
-- title:
--   The direction map $d(\cdot)$ solves $(\mathrm P_x)$ on $K$
-- statement:
--   A map $d:\mathbb R^n\to\mathbb R^n$ is the **direction map** of the method if, for every $x\in K$,
--   $$d(x)\in\widetilde X(x)\quad\text{and}\quad \tilde f(d(x);x)\le\tilde f(u;x)\ \text{ for all } u\in\widetilde X(x),$$
--   that is, $d(x)=\arg\min_d\{\tilde f(d;x)\mid d\in\widetilde X(x)\}$.
--
--   **Formalization Note** $d$ is a function characterised by minimality rather than a choice function: under Assumption A the minimizer exists and is unique, so $d$ is determined on $K$; values off $K$ are never used.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, p.7

import Mathlib
import Definitions.Def_GhostPenalty_Xt

namespace GhostPenalty

/-- **The direction map `d(·)`**: `d(x)` solves the subproblem (Pₓ) at every `x ∈ K`.
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §3, p.7: "`d(x) ≜ arg min_d { f̃(d;x) | d ∈ X̃(x) }`", the unique solution of the
strongly convex subproblem (Pₓ) (p.6).

`IsSubproblemSolutionMap ft g gt K lam ρ β d` says that for every `x ∈ K`, `d x` lies in
`X̃(x)` and minimizes `f̃(·;x)` (`ft · x`) over `X̃(x)`.

**Formalization Note.** `d` is a function hypothesis characterised by minimality, not a
`Classical.choose`: under Assumption A the minimizer exists and is unique (milestone
`GhostPenalty.subproblem_well_posed`), so this pins `d` down on `K`; its values off `K` are
never used. -/
def IsSubproblemSolutionMap {n m : ℕ}
    (ft : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (gt : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (lam ρ β : ℝ)
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x ∈ K, d x ∈ Xt g gt K lam ρ β x ∧ ∀ u ∈ Xt g gt K lam ρ β x, ft (d x) x ≤ ft u x

end GhostPenalty



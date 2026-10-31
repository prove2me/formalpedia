-- Prove2me | Definitions.Def_NieYangPareto_ParetoNotions
-- name    : NieYangPareto_ParetoNotions
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:01.810348+00:00
-- url     : https://prove2.me/theorems/6d24311e-07db-4041-83ca-f97a095df604
-- title:
--   Pareto and weakly Pareto points and values (Definition 1.1)
-- statement:
--   Let $K$ and $f$ be as in (1.1). A point $x^*\in K$ is a **Pareto point** if there is no $x\in K$ with $f_i(x)\le f_i(x^*)$ for all $i=1,\dots,m$ and $f_j(x)<f_j(x^*)$ for at least one $j$. It is a **weakly Pareto point** if there is no $x\in K$ with $f_i(x)<f_i(x^*)$ for all $i=1,\dots,m$.
--
--   A vector $v$ is a **Pareto value** (resp. **weakly Pareto value**) if $v=f(x^*)$ for some Pareto point (resp. weakly Pareto point) $x^*$.
--
--   These are the optimality notions of multi-objective optimization. The mission characterizes the weakly Pareto values geometrically.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, Definition 1.1, p.1, and pp.1–2, 6 (Pareto values)

import Mathlib
import Definitions.Def_NieYangPareto_MOP

namespace NieYangPareto

variable {n m : ℕ} {E I : Type*}

/-- **Pareto point.** Nie–Yang, arXiv:2108.04336v2, Definition 1.1, p.1: `x* ∈ K` is a Pareto point
if there is no `x ∈ K` with `f_i(x) ≤ f_i(x*)` for all `i` and `f_j(x) < f_j(x*)` for at least
one `j`. -/
def MOP.IsParetoPoint (P : MOP n m E I) (xs : Fin n → ℝ) : Prop :=
  xs ∈ P.K ∧ ¬ ∃ x ∈ P.K, (∀ i, P.obj x i ≤ P.obj xs i) ∧ ∃ j, P.obj x j < P.obj xs j

/-- **Weakly Pareto point.** Nie–Yang, arXiv:2108.04336v2, Definition 1.1, p.1: `x* ∈ K` is a weakly
Pareto point if there is no `x ∈ K` with `f_i(x) < f_i(x*)` for all `i`. -/
def MOP.IsWeaklyParetoPoint (P : MOP n m E I) (xs : Fin n → ℝ) : Prop :=
  xs ∈ P.K ∧ ¬ ∃ x ∈ P.K, ∀ i, P.obj x i < P.obj xs i

/-- **Pareto value (PV).** Nie–Yang, arXiv:2108.04336v2, pp.1–2 and p.6: `v = f(x*)` for a Pareto
point `x*`. -/
def MOP.IsParetoValue (P : MOP n m E I) (v : Fin m → ℝ) : Prop :=
  ∃ xs, P.IsParetoPoint xs ∧ v = P.obj xs

/-- **Weakly Pareto value (WPV).** Nie–Yang, arXiv:2108.04336v2, pp.1–2 and p.6: `v = f(x*)` for a
weakly Pareto point `x*`. -/
def MOP.IsWeaklyParetoValue (P : MOP n m E I) (v : Fin m → ℝ) : Prop :=
  ∃ xs, P.IsWeaklyParetoPoint xs ∧ v = P.obj xs

end NieYangPareto



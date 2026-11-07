-- Prove2me | Definitions.Def_ClusterDecomp_IsFairCut
-- name    : ClusterDecomp_IsFairCut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:07:26.277068+00:00
-- url     : https://prove2.me/theorems/91010f75-41c6-4f74-9772-e8796b0893b6
-- title:
--   $\alpha$-fair $s,t$-cut
-- statement:
--   Let $c$ be capacities on a finite vertex set with terminals $s,t$. A cut $(S,T)$ with $s\in S$, $t\in T$ is $\alpha$-fair if there is a feasible signed $s,t$-flow $f$, that is $f(u,v)=-f(v,u)$, $|f(u,v)|\le c(u,v)$ and $\sum_v f(x,v)=0$ for $x\ne s,t$, such that
--   $$f(u,v)\ge\frac{c(u,v)}{\alpha}\qquad\text{for all }u\in S,\ v\in T.$$
--
--   Fair cuts were introduced by Li, Nanongkai, Panigrahi and Saranurak; they are the only access this paper's algorithms have to flows.
--
--   **Formalization Note** Capacities are a raw function, $0$ on non-edges. Skew symmetry makes loops carry no flow.
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), §3, p.9 (PDF p.11); [LNPS23]

import Mathlib
import Definitions.Def_ClusterDecomp_WGraph

open Finset

namespace ClusterDecomp

/-- An `α`-fair `s,t`-cut (§3, p.9, PDF p.11; [LNPS23]): "an `s,t`-cut admitting a feasible signed `s,t`-flow `f`
such that, for every cut edge `(u, v)` oriented from `S` to `T`, `f(u, v) ≥ c(u, v)/α`".

`S` is the source side and `Sᶜ` the sink side.

**Formalization Note.** `c` is a raw capacity function, `0` on non-edges. A signed flow is skew symmetric, feasible
(`|f u v| ≤ c u v`), and conserved at every vertex other than `s`, `t`. Skew symmetry makes loops carry no flow.
The condition is one-way: it constrains `f u v` for `u ∈ S`, `v ∉ S`; together with feasibility it forces `f` to be
nonnegative across the cut in that direction. Feasibility forces `c ≥ 0`, so a negative capacity admits no flow. -/
def IsFairCut {W : Type*} [Fintype W] [DecidableEq W] (c : W → W → ℝ) (s t : W) (S : Finset W)
    (α : ℝ) : Prop :=
  s ∈ S ∧ t ∉ S ∧ ∃ f : W → W → ℝ,
    (∀ u v, f u v = -f v u) ∧
    (∀ u v, |f u v| ≤ c u v) ∧
    (∀ x, x ≠ s → x ≠ t → ∑ v, f x v = 0) ∧
    (∀ u ∈ S, ∀ v ∉ S, c u v / α ≤ f u v)

end ClusterDecomp



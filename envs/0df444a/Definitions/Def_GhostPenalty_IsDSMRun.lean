-- Prove2me | Definitions.Def_GhostPenalty_IsDSMRun
-- name    : GhostPenalty_IsDSMRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:10.199189+00:00
-- url     : https://prove2.me/theorems/ea0fe7b2-fae3-44fa-8533-9e8b2ee79455
-- title:
--   A non-terminating run of Algorithm 1 (DSM)
-- statement:
--   **Algorithm 1 (DSM).** Data: stepsizes $\gamma^\nu\in(0,1]$ with
--   $$\lim_{\nu\to\infty}\gamma^\nu=0,\qquad\sum_{\nu=0}^\infty\gamma^\nu=\infty, \tag{3}$$
--   and $x^0\in K$. At iteration $\nu$: (S.1) if $x^\nu$ is generalized stationary for (P), stop; (S.2) compute $\kappa(x^\nu)$ and the solution $d(x^\nu)$ of $(\mathrm P_{x^\nu})$; (S.3) set
--   $$x^{\nu+1}=x^\nu+\gamma^\nu d(x^\nu). \tag{2}$$
--
--   A **non-terminating run** is a pair of sequences $(x^\nu)$, $(\gamma^\nu)$ satisfying the data conditions and (2) for every $\nu$, in which no iterate is generalized stationary, so (S.1) never stops the method.
--
--   **Formalization Note** $\sum\gamma^\nu=\infty$ is "the partial sums tend to $+\infty$". The direction map $d$ is a parameter; that it solves $(\mathrm P_x)$ is the separate hypothesis on $d$.
-- source:
--   Facchinei, Kungurtsev, Lampariello & Scutari, Ghost Penalties in Nonconvex Constrained Optimization, arXiv:1709.03384v3, (2), (3), p.2; Algorithm 1, p.13

import Mathlib
import Definitions.Def_GhostPenalty_IsGenStationary

namespace GhostPenalty

open Filter Topology

/-- **A non-terminating run of Algorithm 1 (DSM Algorithm for (P)).**
Facchinei, Kungurtsev, Lampariello & Scutari, *Ghost Penalties in Nonconvex Constrained
Optimization*, arXiv:1709.03384v3, §1, (2), (3), p.2, and §4, Algorithm 1, p.13:
"`x^{ν+1} = x^ν + γ^ν d(x^ν)`. (2)", "`lim_{ν→∞} γ^ν = 0` and `Σ_{ν=0}^∞ γ^ν = ∞`, (3)", and
"Algorithm 1: DSM Algorithm for (P). Data: `γ^ν ∈ (0,1]` such that (3) holds, `x⁰ ∈ K`,
`ν ← 0`; repeat (S.1) if `x^ν` is generalized stationary for (P) then stop and return `x^ν`;
end (S.2) compute `κ(x^ν)` and the solution `d(x^ν)` of problem `(P_{x^ν})`;
(S.3) set `x^{ν+1} = x^ν + γ^ν d(x^ν)`, `ν ← ν + 1`; end".

`IsDSMRun f g K d x γ` says that the sequence `x` with stepsizes `γ` is produced by
Algorithm 1 with direction map `d` and never stops at (S.1).

**Formalization Note.** The run is infinite: the test (S.1) fails at every iterate
(`¬ IsGenStationary`). This is the sequence Theorem 1 speaks about (it concerns limit points);
a run that stops returns a generalized stationary point. `Σ γ^ν = ∞` is "the partial sums tend
to `+∞`". That `d` is the solution of (Pₓ) is the separate hypothesis
`IsSubproblemSolutionMap`. -/
def IsDSMRun {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (K : Set (EuclideanSpace ℝ (Fin n)))
    (d : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (γ : ℕ → ℝ) : Prop :=
  (∀ ν, γ ν ∈ Set.Ioc (0 : ℝ) 1) ∧ Tendsto γ atTop (𝓝 0) ∧
    Tendsto (fun N => ∑ ν ∈ Finset.range N, γ ν) atTop atTop ∧
    x 0 ∈ K ∧ (∀ ν, ¬ IsGenStationary f g K (x ν)) ∧
    ∀ ν, x (ν + 1) = x ν + γ ν • d (x ν)

end GhostPenalty



-- Prove2me | Definitions.Def_AbelianCayleyHDX_IsTwoSidedSpectralExpander
-- name    : AbelianCayleyHDX_IsTwoSidedSpectralExpander
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:38.420478+00:00
-- url     : https://prove2.me/theorems/4a1fcc47-469b-435d-9c48-bd4d42afc9dc
-- title:
--   Two-sided $\lambda$-spectral expander (weighted graph)
-- statement:
--   Let $G = (U, w)$ be a finite undirected graph without isolated vertices and with nonnegative symmetric weights $w(u,v) = w(v,u)$ (an edge is a pair of positive weight, no loops). Let $d(u) = \sum_{v \in U} w(u,v)$, let $P$ be the random-walk operator $(Pf)(u) = \sum_{v} w(u,v) f(v)/d(u)$, and let $\pi(u) = d(u)/\sum_v d(v)$ be its stationary measure. $G$ is a **two-sided $\lambda$-spectral expander** if it is connected and
--   $$\big\|P|_{\mathbf 1^{\perp_\pi}}\big\|_\pi \le \lambda,$$
--   that is, $\|Pf\|_\pi \le \lambda \|f\|_\pi$ for every $f$ with $\sum_u \pi(u) f(u) = 0$, where $\|f\|_\pi^2 = \sum_u \pi(u) f(u)^2$. Since $P$ is self-adjoint for $\langle\cdot,\cdot\rangle_\pi$, this says that every nontrivial eigenvalue of $P$ lies in $[-\lambda, \lambda]$.
--
--   **Formalization Note** The vertex set is a nonempty `Finset` $U$ of an ambient type, and only values on $U$ matter. The measure $\pi$ is replaced by the degree $d$, which changes both sides by the same factor. The norm inequality is stated with square roots; since $U$ has at least two vertices, it forces $\lambda \ge 0$.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8

import Mathlib

namespace AbelianCayleyHDX

/-- **Two-sided `λ`-spectral expander** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.2, p.8). A finite undirected weighted
graph `G = (U, w)` without isolated vertices, with nonnegative symmetric weights (an edge is a pair
with positive weight), degrees `d(u) = ∑_{v ∈ U} w(u, v)`, random-walk operator
`(P f)(u) = ∑_{v ∈ U} w(u, v) f(v) / d(u)` and stationary measure `π(u) ∝ d(u)`, is a two-sided
`λ`-spectral expander if it is connected and `‖P|_{1^⊥π}‖_π ≤ λ`, i.e.
`‖P f‖_π ≤ λ ‖f‖_π` for every `f` with `∑_u π(u) f(u) = 0`.

The clauses: `U` is nonempty; `w` is symmetric, nonnegative and zero on the diagonal (no loops) on
`U`; every vertex has positive degree; the graph `u ~ v ⟺ w(u, v) > 0` on `U` is connected; and
for every `f : α → ℝ` with `∑_{u ∈ U} d(u) f(u) = 0`,
`√(∑_{u ∈ U} d(u) (P f)(u)²) ≤ λ √(∑_{u ∈ U} d(u) f(u)²)`.

**Formalization Note** The vertex set is a `Finset` `U` of an ambient type; values of `w` and `f`
off `U` are ignored. The normalization `π = d / ∑ d` cancels from both sides, so `d` is used in
place of `π`. Since `U` has at least two vertices, the mean-zero space is nonzero and the
inequality forces `0 ≤ λ`. -/
noncomputable def IsTwoSidedSpectralExpander {α : Type*} (U : Finset α) (w : α → α → ℝ) (lam : ℝ) :
    Prop :=
  U.Nonempty ∧
  (∀ u ∈ U, ∀ v ∈ U, w u v = w v u) ∧
  (∀ u ∈ U, ∀ v ∈ U, 0 ≤ w u v) ∧
  (∀ u ∈ U, w u u = 0) ∧
  (∀ u ∈ U, 0 < ∑ v ∈ U, w u v) ∧
  (∀ u ∈ U, ∀ v ∈ U, Relation.ReflTransGen (fun a b => a ∈ U ∧ b ∈ U ∧ 0 < w a b) u v) ∧
  (∀ f : α → ℝ, ∑ u ∈ U, (∑ v ∈ U, w u v) * f u = 0 →
    Real.sqrt (∑ u ∈ U, (∑ v ∈ U, w u v) *
        ((∑ v ∈ U, w u v * f v) / (∑ v ∈ U, w u v)) ^ 2) ≤
      lam * Real.sqrt (∑ u ∈ U, (∑ v ∈ U, w u v) * f u ^ 2))

end AbelianCayleyHDX



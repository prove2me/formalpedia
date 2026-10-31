-- Prove2me | Definitions.Def_LeGallBrownianMap_IsBDGSubseqLimit
-- name    : LeGallBrownianMap_IsBDGSubseqLimit
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:43:41.433686+00:00
-- url     : https://prove2.me/theorems/fde9f533-a3c9-4fb7-a276-0803f6dc1d03
-- title:
--   Subsequential limits $(e,Z,D)$ of the convergence (5)
-- statement:
--   Let $(n_k)$ be strictly increasing and $(e,Z,D)$ random processes on a probability space, with $e,Z$ indexed by $[0,1]$ and $D$ by $[0,1]^2$. The triple is a **subsequential limit of (5)** along $(n_k)$ if the coordinates are measurable, the paths are almost surely continuous, and
--
--   $$
--   \Big(\lambda_p n^{-1/2} C^n_{pnt},\ \kappa_p n^{-1/4}\Lambda^n_{pnt},\ \kappa_p n^{-1/4} d_n(pns,pnt)\Big)\xrightarrow[n=n_k\to\infty]{(d)}(e_t,Z_t,D(s,t))
--   $$
--
--   for $\theta_n$ uniform on $\mathbb T^p_n$, as continuous processes with the uniform topology. Sections 3–7 of the paper work "in the setting of Theorem 2.3", i.e. with such a limit.
--
--   **Formalization Note** Convergence in distribution is convergence of $\mathbb E[F(\cdot)]$ for all bounded $F$ continuous for the uniform topology on functions. The predicate depends only on the joint law of $(e,Z,D)$.
-- source:
--   Le Gall, Uniqueness and universality of the Brownian map, arXiv:1105.4842v2, Theorem 2.3, eq. (5), p.16

import Mathlib
import Definitions.Def_LeGallBrownianMap_rescaledTriple
import Definitions.Def_LeGallBrownianMap_uniformTreeExpectation

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace LeGallBrownianMap

/-- Le Gall, *Uniqueness and universality of the Brownian map*, arXiv:1105.4842v2, Theorem 2.3,
eq. (5), p.16: "we can extract a subsequence (n_k)_{k≥1} along which the following convergence in
distribution of continuous processes holds: (λ_p n^{−1/2} C^n_{pnt}, κ_p n^{−1/4} Λ^n_{pnt},
κ_p n^{−1/4} d_n(pns, pnt)) −(d)→ (e_t, Z_t, D(s, t))". Sections 3–7 work "in the setting of
Theorem 2.3", i.e. with `(e, Z, D)` such a subsequential limit.

`IsBDGSubseqLimit p φ e Z D P` says that `φ` is strictly increasing, that `(e, Z, D)` is a random
triple of processes on `(Ω, P)` with measurable coordinates and almost surely continuous paths,
and that along `n = φ(k)` the rescaled triple (5) of `θ_n` uniform on `T^p_n` converges in
distribution to `(e, Z, D)`: `E[F(triple_n)] → E[F(e, Z, D)]` for every bounded `F` continuous for
the uniform topology.

**Formalization Note.** This is a property of the joint law of `(e, Z, D)` only. Convergence in
distribution of continuous processes (sup norm) is stated with test functions on the spaces of
functions with uniform convergence (`UniformFun`); since all processes involved are continuous
and the space of continuous functions is closed there, this is the paper's convergence. -/
def IsBDGSubseqLimit (p : ℕ) (φ : ℕ → ℕ) {Ω : Type} [MeasurableSpace Ω]
    (e Z : Ω → unitInterval → ℝ) (D : Ω → unitInterval → unitInterval → ℝ)
    (P : Measure Ω) : Prop :=
  StrictMono φ ∧
  (∀ t, Measurable (fun ω => e ω t)) ∧ (∀ t, Measurable (fun ω => Z ω t)) ∧
  (∀ s t, Measurable (fun ω => D ω s t)) ∧
  (∀ᵐ ω ∂P, Continuous (e ω) ∧ Continuous (Z ω) ∧
    Continuous (fun x : unitInterval × unitInterval => D ω x.1 x.2)) ∧
  ∀ F : (UniformFun unitInterval ℝ × UniformFun unitInterval ℝ ×
      UniformFun (unitInterval × unitInterval) ℝ) →ᵇ ℝ,
    Tendsto (fun k => uniformTreeExpectation p (φ k) (fun θ => F (rescaledTriple p (φ k) θ)))
      atTop
      (𝓝 (∫ ω, F (UniformFun.ofFun (e ω), UniformFun.ofFun (Z ω),
        UniformFun.ofFun (fun x : unitInterval × unitInterval => D ω x.1 x.2)) ∂P))

end LeGallBrownianMap



-- Prove2me | Definitions.Def_UnionVolEst_Supplement_hitRunLaw
-- name    : UnionVolEst_Supplement_hitRunLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:08:39.365197+00:00
-- url     : https://prove2.me/theorems/bc5b0a2e-68b1-41ca-a387-38879b1363c7
-- title:
--   Law $D_t$ of Hit-and-Run after $t$ steps from a point start (§3.2, App. C)
-- statement:
--   Let $K\subseteq\mathbb R^n$ and $x_0\in K$. **Hit-and-Run** generates a Markov chain $(X_t)_{t\ge0}$ with $X_0=x_0$. At each step it draws a direction $u$ uniformly from the unit sphere $S^{n-1}$ and picks $X_{t+1}$ uniformly from the chord
--   $$
--   C_K(X_t,u)=K\cap\{X_t+su:s\in\mathbb R\}.
--   $$
--   The law of $X_t$ is $D_t$:
--   $$
--   D_0=\delta_{x_0},\qquad D_{t+1}(B)=\int P(x,B)\,D_t(dx),
--   $$
--   where $P$ is the one-step Hit-and-Run kernel.
--
--   The guarantees of Theorems 21 and 32 are statements about $D_t$: its exceptional set $\mathrm{Bad}_{t,\eta}$ is small under both $D_t$ and the uniform distribution.
--
--   **Formalization Note** The kernel $P$ is the published Random Directions kernel `SmithHitAndRun.RandomDir.rdKernel K`: a uniform direction on the unit sphere, then a uniform point on the line set. That kernel is the identity at points outside $K$ and for non-measurable $K$. Neither case arises for a compact convex body and a start in $K$.
-- source:
--   Banerjee, Bal, Basu, Chakraborty, Chanda, Sarkar, Estimating the Volume of a Union of Convex Bodies, arXiv:2611.06364 (held version, sha256 15de4f2e…26bd24), §3.2, p.12 (PDF p.14); App. C, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_SmithHitAndRun_RandomDir_RandomDirectionsKernel

open MeasureTheory

namespace UnionVolEst.Supplement

/-- The law `D_t` of the Hit-and-Run chain after `t` steps (Banerjee–Bal–Basu–Chakraborty–Chanda–Sarkar,
*Estimating the Volume of a Union of Convex Bodies*, arXiv:2611.06364 (held version, sha256
15de4f2e…26bd24), §3.2, printed p.12, PDF p.14; App. C, printed p.43, PDF p.45): started at
`X₀ = x₀`, each step draws a direction `u` uniformly from the unit sphere `S^{n−1}` and moves to a
uniform point of the chord `K ∩ {X_t + s u : s ∈ ℝ}`. So `D_0 = δ_{x₀}` and
`D_{t+1} = ∫ P(x, ·) D_t(dx)`.

**Formalization Note** The one-step kernel `P` is the published Random Directions kernel
`SmithHitAndRun.RandomDir.rdKernel K` (uniform direction on the unit sphere, then uniform point
on the line set). It is the identity off `K` and for non-measurable `K`; neither case arises for a
compact convex `K` and a start `x₀ ∈ K`. -/
noncomputable def hitRunLaw {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n)) : ℕ → Measure (EuclideanSpace ℝ (Fin n))
  | 0 => Measure.dirac x₀
  | t + 1 => (hitRunLaw K x₀ t).bind (SmithHitAndRun.RandomDir.rdKernel K)

end UnionVolEst.Supplement



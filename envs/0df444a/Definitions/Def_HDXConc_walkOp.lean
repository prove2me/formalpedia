-- Prove2me | Definitions.Def_HDXConc_walkOp
-- name    : HDXConc_walkOp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:11.986504+00:00
-- url     : https://prove2.me/theorems/ad176dee-75de-47a5-8abc-d8249f204aa8
-- title:
--   Vertex mean, variance, inner product, and the walk operator of the underlying graph
-- statement:
--   Let $\rho$ be a density on $X(d)$, with induced measures $\pi_1,\pi_2$. For functions on the vertices,
--
--   $$\mathbb E_{\pi_1}[f]=\sum_{v\in X(1)}\pi_1(v)f(v),\qquad \mathrm{Var}_{\pi_1}(f)=\sum_{v\in X(1)}\pi_1(v)\big(f(v)-\mathbb E_{\pi_1}[f]\big)^2,\qquad \langle f,g\rangle_{\pi_1}=\sum_{v\in X(1)}\pi_1(v)f(v)g(v).$$
--
--   The **normalized adjacency operator** of the underlying graph is
--
--   $$Ah(v)=\frac{1}{2\pi_1(v)}\sum_{u\sim v}\pi_2(\{u,v\})\,h(u),$$
--
--   where $u\sim v$ means $u\ne v$ and $\{u,v\}\in X$. With $\rho=\pi_{d,t}$ these are the paper's $\pi_{1,t}$, $\pi_{2,t}$ and $A_t$.
--
--   **Formalization Note.** The operator is only read at vertices of $X$, where $\pi_1>0$.
-- source:
--   Das, Hopkins, Ray, Tung, Concentration on HDX: Simplified and Optimized, STOC 2027 submission (manuscript sha256 ea5bee5f…), §2.1 "Expansion", p.11; proof of Theorem 1.1, p.15

import Mathlib
import Definitions.Def_HDXConc_IsTopDensity
import Definitions.Def_HDXConc_linkWeight

namespace HDXConc

/-!
# Vertex means and the walk operator of the underlying graph of `X`

Das, Hopkins, Ray, Tung, *Concentration on HDX: Simplified and Optimized*, STOC 2027 submission
(manuscript sha256 ea5bee5f…), §2.1 "Expansion", p.11, and proof of Theorem 1.1, p.15.

**Formalization Note.** Here `ρ` is a density on `X(d)`; the paper's `π_{1,t}`, `π_{2,t}`, `A_t` are the instances
at `ρ = π_{d,t}`. The neighbours `u ∼ v` of p.11 are the `u ∈ X(1)` with `u ≠ v` and `{u, v} ∈ X`. The operator is
only read at vertices of `X`, where `π₁ > 0`.
-/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `E_{π₁}[f] = ∑_{v ∈ X(1)} π₁(v) f(v)`, with `π₁` induced by `ρ`. -/
noncomputable def vertexMean (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * f v

/-- `Var_{π₁}(f) = ∑_{v ∈ X(1)} π₁(v) (f(v) - E_{π₁}[f])²`, with `π₁` induced by `ρ`. -/
noncomputable def vertexVar (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * (f v - vertexMean X d ρ f) ^ 2

/-- The inner product `⟨f, g⟩_{π₁} = ∑_{v ∈ X(1)} π₁(v) f(v) g(v)` of p.11, with `π₁` induced by `ρ`. -/
noncomputable def vertexInner (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (f g : V → ℝ) : ℝ :=
  ∑ v ∈ vertices X, faceMeasure X d ρ 1 {v} * f v * g v

/-- The normalized adjacency operator of p.11 on the underlying graph of `X`,
`A h (v) = (1 / (2 π₁(v))) ∑_{u ∼ v} π₂({u, v}) h(u)`, with `π₁`, `π₂` induced by `ρ`. -/
noncomputable def walkOp (X : Finset (Finset V)) (d : ℕ) (ρ : Finset V → ℝ) (h : V → ℝ) (v : V) : ℝ :=
  (1 / (2 * faceMeasure X d ρ 1 {v})) *
    ∑ u ∈ (vertices X).filter (fun u => u ≠ v ∧ ({u, v} : Finset V) ∈ X),
      faceMeasure X d ρ 2 {u, v} * h u

end HDXConc



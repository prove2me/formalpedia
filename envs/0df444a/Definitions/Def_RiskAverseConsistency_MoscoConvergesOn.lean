-- Prove2me | Definitions.Def_RiskAverseConsistency_MoscoConvergesOn
-- name    : RiskAverseConsistency_MoscoConvergesOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:21:35.611769+00:00
-- url     : https://prove2.me/theorems/1a5b4ceb-22f1-46df-8c07-4befee4f57b6
-- title:
--   Mosco-epiconvergence (Definition 3)
-- statement:
--   Let $V$ be a normed space and $V_0\subseteq V$. A sequence $\phi_k:V_0\to(-\infty,\infty]$ **Mosco-epiconverges** to $\phi:V_0\to(-\infty,\infty]$ if for each $v\in V_0$
--
--   1. for each $(v_k)\subset V_0$ with $v_k\rightharpoonup v$ (weakly), $\liminf_{k\to\infty}\phi_k(v_k)\ge\phi(v)$, and
--   2. there exists $(v_k)\subset V_0$ with $v_k\to v$ (in norm) such that $\limsup_{k\to\infty}\phi_k(v_k)\le\phi(v)$.
--
--   **Formalization Note** Weak convergence is the published `QuasiHemiVI.Existence.WeakConv`. The paper's standing hypotheses ($V$ reflexive Banach, $V_0$ closed, nonempty, convex) and the exclusion of $-\infty$ are hypotheses of each theorem that uses the notion.
-- source:
--   Milz, Surowiec, Asymptotic consistency for nonconvex risk-averse stochastic optimization with infinite dimensional decision spaces, arXiv:2207.14756v2, p.5, Definition 3

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_WeakConv

open Filter Topology QuasiHemiVI.Existence

namespace RiskAverseConsistency

/-- **Mosco-epiconvergence** (Definition 3) of `φₖ : V₀ → (−∞, ∞]` to `φ : V₀ → (−∞, ∞]`: for each
`v ∈ V₀`,
1. for each `(vₖ) ⊂ V₀` with `vₖ ⇀ v` (weakly), `liminf φₖ(vₖ) ≥ φ(v)`, and
2. there exists `(vₖ) ⊂ V₀` with `vₖ → v` (in norm) such that `limsup φₖ(vₖ) ≤ φ(v)`.

Milz, Surowiec, arXiv:2207.14756v2, Definition 3, p.5.

Formalization Note: weak convergence `⇀` is the published `QuasiHemiVI.Existence.WeakConv`
(`ℓ(vₖ) → ℓ(v)` for every continuous linear functional `ℓ`). Functions "on `V₀`" are `EReal`-valued
functions on `V` whose values off `V₀` are never used. The standing hypotheses of Definition 3
(`V` reflexive Banach, `V₀` closed, nonempty and convex) and the exclusion of `−∞` are hypotheses
of every theorem that uses this notion. -/
def MoscoConvergesOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (V₀ : Set V)
    (φk : ℕ → V → EReal) (φ : V → EReal) : Prop :=
  ∀ v ∈ V₀,
    (∀ u : ℕ → V, (∀ k, u k ∈ V₀) → WeakConv u v →
      φ v ≤ liminf (fun k => φk k (u k)) atTop) ∧
    (∃ u : ℕ → V, (∀ k, u k ∈ V₀) ∧ Tendsto u atTop (𝓝 v) ∧
      limsup (fun k => φk k (u k)) atTop ≤ φ v)

end RiskAverseConsistency



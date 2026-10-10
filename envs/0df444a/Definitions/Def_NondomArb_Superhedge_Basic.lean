-- Prove2me | Definitions.Def_NondomArb_Superhedge_Basic
-- name    : NondomArb_Superhedge_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T14:21:48.327315+00:00
-- url     : https://prove2.me/theorems/1676f27e-d1eb-406d-9d35-63d5257da1c7
-- title:
--   §1.1: the extended expectation (1.1), 𝒫-polar sets and 𝒫-q.s., Q ⋘ 𝒫, upper semianalytic functions
-- statement:
--   These are the measure-theoretic conventions of §1.1 of Bouchard–Nutz, used throughout the paper.
--
--   1. **Extended expectation (1.1).** For a measure $P$ on a measurable space $(\Omega,\mathcal F)$ and a measurable $f:\Omega\to\overline{\mathbb R}=[-\infty,\infty]$,
--   $$E_P[f] := E_P[f^+] - E_P[f^-]\qquad\text{with the convention } \infty-\infty := -\infty .$$
--   2. **Polar sets and quasi-sure properties.** For a family $\mathcal P$ of measures, a set $A\subseteq\Omega$ is *$\mathcal P$-polar* if $A\subseteq A'$ for some $A'\in\mathcal F$ with $P(A')=0$ for all $P\in\mathcal P$; a property holds *$\mathcal P$-quasi surely* ($\mathcal P$-q.s.) if it holds outside a $\mathcal P$-polar set.
--   3. **Domination by a family.** $Q\lll\mathcal P$ means that $Q\ll P$ for some $P\in\mathcal P$.
--   4. **Upper semianalytic functions.** On a topological (in the paper: Polish) space $X$, a function $f:X\to\overline{\mathbb R}$ is *upper semianalytic* if every super-level set $\{f>c\}$, $c\in\mathbb R$, is analytic.
--
--   The convention $\infty-\infty=-\infty$ makes $E_P[f]$ well defined for every measurable $f$, which is what allows the paper to take suprema of expectations over sets of measures without integrability assumptions.
--
--   **Formalization Note** $E_P[f]$ is computed in `EReal` as the difference of the lower integrals of $f^+$ and $f^-$; Mathlib's `EReal` arithmetic gives $\top-\top=\bot$, which is the paper's convention. Polar sets use the paper's literal definition with a measurable superset $A'$. Analytic sets are Mathlib's `AnalyticSet`.
-- source:
--   Bouchard, Nutz, Arbitrage and duality in nondominated discrete-time models, arXiv:1305.6008v3, p. 3, §1.1, (1.1); p. 6, definition of Q ⋘ 𝒫

import Mathlib

namespace NondomArb.Superhedge

open MeasureTheory

/-- **(1.1)** (Bouchard–Nutz, p. 3). The extended expectation of a measurable function
`f : Ω → [−∞, ∞]` under a measure `P`: `E_P[f] := E_P[f⁺] − E_P[f⁻]`, computed in `EReal`.
Mathlib's `EReal` has `⊤ - ⊤ = ⊤ + ⊥ = ⊥`, which is exactly the paper's convention
`∞ − ∞ := −∞`. -/
noncomputable def extExp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → EReal) : EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂P : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂P : ENNReal) : EReal)

/-- §1.1 (p. 3). A subset `A ⊆ Ω` is `𝒫`-*polar* if `A ⊆ A'` for some measurable `A'` with
`P(A') = 0` for all `P ∈ 𝒫` (the paper's literal definition, for a general measurable space). -/
def IsPolar {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) (A : Set Ω) : Prop :=
  ∃ A' : Set Ω, MeasurableSet A' ∧ A ⊆ A' ∧ ∀ P ∈ Pset, P A' = 0

/-- §1.1 (p. 3). A property holds `𝒫`-*quasi surely* if it holds outside a `𝒫`-polar set. -/
def QS {Ω : Type*} [MeasurableSpace Ω] (Pset : Set (Measure Ω)) (p : Ω → Prop) : Prop :=
  IsPolar Pset {ω | ¬ p ω}

/-- p. 6. `Q ⋘ 𝒫`: there exists `P ∈ 𝒫` such that `Q ≪ P`. -/
def AbsContSet {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) (Pset : Set (Measure Ω)) : Prop :=
  ∃ P ∈ Pset, Q ≪ P

/-- §1.1 (p. 3). A function `f : X → [−∞, ∞]` on a topological space is *upper semianalytic* if
every super-level set `{f > c}`, `c ∈ ℝ`, is analytic. -/
def IsUpperSemianalytic {X : Type*} [TopologicalSpace X] (f : X → EReal) : Prop :=
  ∀ c : ℝ, AnalyticSet {x | (c : EReal) < f x}

end NondomArb.Superhedge



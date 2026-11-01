-- Prove2me | Definitions.Def_LearningBasedRO_Model
-- name    : LearningBasedRO_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:30:20.143989+00:00
-- url     : https://prove2.me/theorems/84772c60-759a-4571-a1fb-52ea7cae53c3
-- title:
--   Chance-constrained and robust feasibility, requirement (3), order statistics, the index $i^*$ of (4) and the learned uncertainty set $U(D)$
-- statement:
--   This module fixes the objects of the basic statistical guarantee of Hong, Huang and Lam.
--
--   Let $(E,\mathcal E)$ be the space of the random parameter $\xi$ (the paper: $\mathbb R^m$), $P$ a measure on it (the law of $\xi$), $X$ a set of decisions, $\Omega$ a set of outcomes, $g:X\times E\to\Omega$ and $A\subseteq\Omega$, and $\epsilon,\delta$ the tolerance and confidence parameters.
--
--   1. **Chance-constrained feasibility (1).** A decision $x$ is feasible for the chance-constrained program (1) if $P(g(x;\xi)\in A)\ge 1-\epsilon$.
--   2. **Robust feasibility (2).** For an uncertainty set $U\subseteq E$, $x$ is feasible for the robust program (2) if $g(x;\xi)\in A$ for every $\xi\in U$.
--   3. **Content.** $U$ is a $(1-\epsilon)$-content set if $P(\xi\in U)\ge 1-\epsilon$.
--   4. **Requirement (3).** A data-driven set $U(D)$, where the data $D$ has law $P_D$, satisfies (3) if
--   $$P_D\big(P(\xi\in U(D))\ge 1-\epsilon\big)\ge 1-\delta .$$
--   5. **Split sample.** The data are $D=(D_1,D_2)$ with $D_1=(\xi^1_1,\dots,\xi^1_{n_1})$ and $D_2=(\xi^2_1,\dots,\xi^2_{n_2})$, all i.i.d. from $P$; their law is the product $P^{n_1}\otimes P^{n_2}$.
--   6. **Order statistics.** For reals $y_1,\dots,y_n$ and $1\le r\le n$, $y_{(r)}$ is the $r$-th smallest value, counted with multiplicity.
--   7. **The index (4).** With $b_k=\binom{n_2}{k}(1-\epsilon)^k\epsilon^{n_2-k}$,
--   $$i^*=\min\Big\{r:\ \sum_{k=0}^{r-1}b_k\ge 1-\delta,\ 1\le r\le n_2\Big\},\qquad i_*=\max\Big\{r:\ \sum_{k=r}^{n_2}b_k\ge 1-\delta,\ 1\le r\le n_2\Big\}$$
--   ($i_*$ is the lower index of Lemma 3).
--   8. **The learned set.** For a score map $t$ built from $D_1$,
--   $$U(D)=\{\xi:\ t(\xi)\le t(\xi^2_{(i^*)})\},$$
--   where $t(\xi^2_{(i^*)})$ is the $i^*$-th smallest of the scores $t(\xi^2_1),\dots,t(\xi^2_{n_2})$.
--
--   These are the objects every statement of the mission is about: Lemmas 1 and 2 relate (1), (2) and (3), Lemma 3 is about order statistics and $i^*$, and Theorem 1 shows that $U(D)$ satisfies (3).
--
--   **Formalization Note** Observations are indexed by `Fin n` (0-based) while ranks $r$ and $i^*$ are 1-based naturals: $y_{(r)}$ is `y (Tuple.sort y ⟨r - 1, _⟩)`, with junk value $0$ outside $1\le r\le n$. Ties are kept (the paper's strict ranking holds almost surely for continuous data). $i^*$ is `sInf` and $i_*$ is `sSup` on $\mathbb N$, both $0$ (not a valid rank) when their set is empty; every statement either assumes the set nonempty or carries the paper's sample-size condition. The score map is a function $t(D_1,\xi)$ of $D_1$ and $\xi$ only. Probabilities $1-\epsilon$, $1-\delta$ enter through `ENNReal.ofReal`; the measure of a possibly non-measurable set is its outer measure.
-- source:
--   Hong–Huang–Lam, arXiv:1704.04342v2, (1) p.1; (2), Lemma 1, (3) p.5; Phase 1–2 split pp.6–7; ranked observations and (4) p.7; Lemma 3 (i_*) p.8; U(D) in Theorem 1, p.9

import Mathlib

open MeasureTheory

namespace LearningBasedRO

/-- Feasibility for the chance-constrained program (1): the decision `x` satisfies
`P(g(x; ξ) ∈ A) ≥ 1 - ϵ`.
Hong–Huang–Lam, arXiv:1704.04342v2, §1, (1), p.1.

**Formalization Note** The objective `f` of (1) plays no role in feasibility and is omitted.
`P {ξ | g x ξ ∈ A}` is the (outer) measure of the set; `1 - ϵ` enters through `ENNReal.ofReal`. -/
def CCPFeasible {X E Ω : Type*} [MeasurableSpace E] (P : Measure E) (g : X → E → Ω)
    (A : Set Ω) (ϵ : ℝ) (x : X) : Prop :=
  ENNReal.ofReal (1 - ϵ) ≤ P {ξ | g x ξ ∈ A}

/-- Feasibility for the robust program (2) with uncertainty set `U`:
`g(x; ξ) ∈ A` for every `ξ ∈ U`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2, (2), p.5. -/
def ROFeasible {X E Ω : Type*} (g : X → E → Ω) (A : Set Ω) (U : Set E) (x : X) : Prop :=
  ∀ ξ ∈ U, g x ξ ∈ A

/-- `U` is a `(1 - ϵ)`-content set for `P`: `P(ξ ∈ U) ≥ 1 - ϵ`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2, p.5 (text before Lemma 1). -/
def IsContentSet {E : Type*} [MeasurableSpace E] (P : Measure E) (ϵ : ℝ) (U : Set E) : Prop :=
  ENNReal.ofReal (1 - ϵ) ≤ P U

/-- Requirement (3) for a data-driven set `U : Ω_D → Set E`, where the data `D` has law `μD`:
`P_D(P(ξ ∈ U(D)) ≥ 1 - ϵ) ≥ 1 - δ`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.1, (3), p.5.

**Formalization Note** `μD` of the event is its outer measure; the goal theorem proves in addition
that the event is measurable for the paper's set. -/
def SatisfiesReq3 {ΩD E : Type*} [MeasurableSpace ΩD] [MeasurableSpace E] (μD : Measure ΩD)
    (P : Measure E) (ϵ δ : ℝ) (U : ΩD → Set E) : Prop :=
  ENNReal.ofReal (1 - δ) ≤ μD {D | IsContentSet P ϵ (U D)}

/-- The law of the split i.i.d. sample `D = (D₁, D₂)`, `D₁ = (ξ¹₁, …, ξ¹ₙ₁)`,
`D₂ = (ξ²₁, …, ξ²ₙ₂)`: the product `P^{n₁} ⊗ P^{n₂}`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.1, p.6, and Theorem 1, p.9.

**Formalization Note** The partition of the i.i.d. sample `D` into `D₁` and `D₂` is fixed in
advance, so `(D₁, D₂)` has the product law. Observations are indexed by `Fin n₁`, `Fin n₂`
(0-based). `n₁ = 0` is allowed. -/
noncomputable def splitLaw {E : Type*} [MeasurableSpace E] (P : Measure E) (n₁ n₂ : ℕ) :
    Measure ((Fin n₁ → E) × (Fin n₂ → E)) :=
  (Measure.pi fun _ : Fin n₁ => P).prod (Measure.pi fun _ : Fin n₂ => P)

/-- The `r`-th order statistic `y₍ᵣ₎` (the `r`-th smallest value, counted with multiplicity) of a
tuple `y = (y₁, …, yₙ)` of reals, for `1 ≤ r ≤ n`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.1, p.7 (ranked observations), Lemma 3, p.8.

**Formalization Note** The rank `r` is 1-based as on the page; positions of `Tuple.sort` are
0-based, so `y₍ᵣ₎ = y (Tuple.sort y ⟨r - 1, _⟩)`. Ties are kept (the paper's strict ranking
`y₍₁₎ < ⋯ < y₍ₙ₎` holds almost surely for continuous data). Outside `1 ≤ r ≤ n` the value is the
junk `0`; every statement uses it only for `1 ≤ r ≤ n` or with a hypothesis forcing that. -/
noncomputable def orderStat {n : ℕ} (y : Fin n → ℝ) (r : ℕ) : ℝ :=
  if h : 1 ≤ r ∧ r ≤ n then y (Tuple.sort y ⟨r - 1, by omega⟩) else 0

/-- The binomial term `C(n,k) (1 - ϵ)^k ϵ^(n-k)`, used in (4) and Lemma 3.
Hong–Huang–Lam, arXiv:1704.04342v2, (4), p.7; Lemma 3, p.8.

**Formalization Note** Only used with `k ≤ n`, so the natural subtraction `n - k` is exact. -/
noncomputable def binomTerm (n : ℕ) (ϵ : ℝ) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (1 - ϵ) ^ k * ϵ ^ (n - k)

/-- The set over which (4) minimizes:
`{r : Σ_{k=0}^{r-1} C(n,k)(1-ϵ)^k ϵ^(n-k) ≥ 1 - δ, 1 ≤ r ≤ n}`.
Hong–Huang–Lam, arXiv:1704.04342v2, (4), p.7; Lemma 3, p.8. -/
def iStarSet (n : ℕ) (ϵ δ : ℝ) : Set ℕ :=
  {r | 1 ≤ r ∧ r ≤ n ∧ 1 - δ ≤ ∑ k ∈ Finset.range r, binomTerm n ϵ k}

/-- The calibration index `i*` of (4):
`i* = min{r : Σ_{k=0}^{r-1} C(n,k)(1-ϵ)^k ϵ^(n-k) ≥ 1 - δ, 1 ≤ r ≤ n}`.
Hong–Huang–Lam, arXiv:1704.04342v2, (4), p.7; Lemma 3, p.8.

**Formalization Note** `sInf` on `ℕ`; when the set is empty (the procedure is not valid) the value
is the junk `0`, which is not a valid rank. Every statement using `iStar` either assumes the set
nonempty or carries the paper's sample-size condition, which makes it nonempty. -/
noncomputable def iStar (n : ℕ) (ϵ δ : ℝ) : ℕ :=
  sInf (iStarSet n ϵ δ)

/-- The set over which the lower index `i_*` of Lemma 3 maximizes:
`{r : Σ_{k=r}^{n} C(n,k)(1-ϵ)^k ϵ^(n-k) ≥ 1 - δ, 1 ≤ r ≤ n}`.
Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 3, p.8. -/
def iLowerStarSet (n : ℕ) (ϵ δ : ℝ) : Set ℕ :=
  {r | 1 ≤ r ∧ r ≤ n ∧ 1 - δ ≤ ∑ k ∈ Finset.Icc r n, binomTerm n ϵ k}

/-- The lower index `i_*` of Lemma 3:
`i_* = max{r : Σ_{k=r}^{n} C(n,k)(1-ϵ)^k ϵ^(n-k) ≥ 1 - δ, 1 ≤ r ≤ n}`.
Hong–Huang–Lam, arXiv:1704.04342v2, Lemma 3, p.8 (printed with a subscript star).

**Formalization Note** `sSup` on `ℕ` of a set bounded by `n`; junk `0` when the set is empty.
Every statement using it assumes the set nonempty. -/
noncomputable def iLowerStar (n : ℕ) (ϵ δ : ℝ) : ℕ :=
  sSup (iLowerStarSet n ϵ δ)

/-- The learned uncertainty set `U(D) = {ξ : t(ξ) ≤ s}` with `s = t(ξ²₍ᵢ*₎)`, the `i*`-th smallest
of the scores `t(ξ²₁), …, t(ξ²ₙ₂)` of the Phase-2 data, where the score map `t` is built from the
Phase-1 data `D₁`.
Hong–Huang–Lam, arXiv:1704.04342v2, §2.1 Phase 2, p.7; Theorem 1, p.9.

**Formalization Note** The score map is a function `t : (Fin n₁ → E) → E → ℝ` of `D₁` and `ξ`
("a map constructed from D₁"); it never sees `D₂`. `D = (D₁, D₂)`. -/
noncomputable def uncertaintySet {E : Type*} {n₁ n₂ : ℕ} (t : (Fin n₁ → E) → E → ℝ)
    (ϵ δ : ℝ) (D : (Fin n₁ → E) × (Fin n₂ → E)) : Set E :=
  {ξ | t D.1 ξ ≤ orderStat (fun i => t D.1 (D.2 i)) (iStar n₂ ϵ δ)}

end LearningBasedRO



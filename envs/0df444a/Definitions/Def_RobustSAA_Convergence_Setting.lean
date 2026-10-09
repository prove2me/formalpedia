-- Prove2me | Definitions.Def_RobustSAA_Convergence_Setting
-- name    : RobustSAA_Convergence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T14:16:48.08095+00:00
-- url     : https://prove2.me/theorems/c6dd009a-2c03-4cd1-9489-d64b712e6be6
-- title:
--   §1.2, (4), (7), Definitions 1, 3, Assumptions 1–3, (18)–(20) — DUS maps, worst-case expectation, uniform consistency, convergence conditions
-- statement:
--   This file fixes the setting of Robust Sample Average Approximation (Robust SAA) and the objects in which its convergence theory is stated.
--
--   **Data.** The uncertain parameter $\xi$ takes values in a closed set $\Xi\subseteq\mathbb R^d$, and $\mathcal P(\Xi)$ denotes the Borel probability distributions on $\Xi$, with the topology of weak convergence. The data $\xi^1,\xi^2,\dots$ are i.i.d. draws from an unknown distribution $F\in\mathcal P(\Xi)$; they are modelled as one point $\omega=(\xi^1,\xi^2,\dots)$ of the infinite product space $\Xi^{\mathbb N}$ under the product law $F^{\otimes\mathbb N}$, and the first $N$ of them form the sample of size $N$.
--
--   **Data-driven uncertainty sets.** A DUS map assigns to every sample size $N$ and sample $(\xi^1,\dots,\xi^N)$ a set $\mathcal F_N\subseteq\mathcal P(\Xi)$. Every goodness-of-fit (GoF) test is identified with its confidence region (7): the test rejects a hypothetical $F_0$ exactly when $F_0\notin\mathcal F_N$.
--
--   **Worst-case expectation.** For a cost $c(x;\xi)$ with decisions $x\in X\subseteq\mathbb R^{d_x}$, the robust objective (4) is
--   $$\mathcal C(x;\mathcal F_N)=\sup_{F_0\in\mathcal F_N}\mathbb E_{F_0}[c(x;\xi)],$$
--   computed in the extended reals; an expectation $\mathbb E_{F_0}[f(\xi)]$ is the integral when $f$ is $F_0$-integrable and $+\infty$ otherwise. The supremum over the empty set is $-\infty$.
--
--   **Uniform consistency (Definition 3).** A test is uniformly consistent if, for every data-generating $F$, almost surely every sequence $F_N$ that does not converge weakly to $F$ satisfies $F_N\notin\mathcal F_N$ for infinitely many $N$:
--   $$\mathbb P\big(F_N\not\to F\implies F_N\notin\mathcal F_N\ \text{i.o.}\big)=1 .$$
--   The almost-sure event quantifies over all sequences $(F_N)$ at once.
--
--   **Standing assumptions (§1.2).** $X$ is closed and $c(x;\cdot)$ is $F$-integrable for each $x\in X$ (so $\mathbb E_F[c(x;\xi)]$ is finite), and $c(x;\cdot)$ is continuous on $\Xi$.
--
--   **Assumption 1.** The family $\{c(\cdot;\xi):\xi\in\Xi\}$ is equicontinuous on the whole decision space (Definition 1).
--
--   **Assumption 2.** $X$ is closed and either (a) $X$ is bounded, or (b) there is an open $D\subseteq\Xi$ with $F(D)>0$ such that $c(x;\xi)\to\infty$ as $\|x\|\to\infty$ in the whole decision space, uniformly over $\xi\in D$, and $\liminf_{\|x\|\to\infty}\inf_{\xi\notin D}c(x;\xi)>-\infty$.
--
--   **Assumption 3.** Either (a) $\Xi$ is bounded, or (b) there is a continuous $\phi:\Xi\to\mathbb R_+$ with $\mathbb E_F[\phi(\xi)]<\infty$ such that, almost surely,
--   $$\sup_{F_0\in\mathcal F_N}\Big|\mathbb E_{F_0}\phi(\xi)-\frac1N\sum_{i=1}^N\phi(\xi^i)\Big|\to0,$$
--   and $c(x;\xi)=O(\phi(\xi))$ for each $x\in X$, i.e. $|c(x;\xi)|\le\nu+\eta\,\phi(\xi)$ for some constants $\nu,\eta$.
--
--   **Convergence conditions (18)–(20)**, stated for an arbitrary sequence of sets $\mathcal G_N$ (applied to $\mathcal G_N=\mathcal F_N$):
--   1. (18) $\mathcal C(x;\mathcal G_N)\to\mathbb E_F[c(x;\xi)]$ uniformly over every compact subset of $X$;
--   2. (19) $\inf_{x\in X}\mathcal C(x;\mathcal G_N)\to\inf_{x\in X}\mathbb E_F[c(x;\xi)]$ in the extended reals;
--   3. (20) every sequence $x_N$ that eventually minimizes $\mathcal C(\cdot;\mathcal G_N)$ over $X$ has at least one limit point, and all of its limit points minimize $\mathbb E_F[c(\cdot;\xi)]$ over $X$.
--
--   These objects are shared by every statement of the mission: Theorem 2 characterizes uniform consistency as exactly the property of the DUS under which (18)–(20) hold almost surely for every admissible instance.
--
--   **Formalization Note** Points of $\mathbb R^d$ are `EuclideanSpace ℝ (Fin d)`; distributions are `ProbabilityMeasure ↥Ξ`, whose topology is weak convergence. Data are 0-indexed (`ω 0` is $\xi^1$). Expectations over members of the DUS return $+\infty$ (not Lean's default $0$) on non-integrable functions. Three hypotheses are added to the page, each needed by the paper's own proof: continuity of $c(x;\cdot)$ (portmanteau and Billingsley's Theorem 3.5 in Proposition 8), openness of $D$ in Assumption 2b (to get $\liminf F_N(D)\ge F(D)$ from weak convergence, p. 37), and continuity of $\phi$ in Assumption 3b (Billingsley's Theorem 3.6 in Proposition 8). $\mathbb E_F\phi<\infty$ is the convention fixed on p. 10. Equicontinuity holds on the whole decision space; "min" in (19)–(20) is read as an infimum in the extended reals, so neither side needs $X\neq\emptyset$ or attainment; (20) applies to sequences that are minimizers for all large $N$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, (3)–(4) p. 2, §1.2 p. 4, Definition 1 p. 5, (7) and §2.2 p. 7, φ convention p. 10, (18)–(20) p. 12, Definition 3 and Assumptions 1–3 p. 13

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace RobustSAA.Convergence

/-- Euclidean space `ℝ^d`. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ} {Ξ : Set (Pt d)}

/-- Law of the iid data sequence `ξ¹, ξ², …` drawn from `F`, on the canonical product space
`ℕ → Ξ` (0-based: `ω 0` is the paper's `ξ¹`). -/
noncomputable def dataLaw (F : ProbabilityMeasure ↥Ξ) : Measure (ℕ → ↥Ξ) :=
  Measure.infinitePi (fun _ : ℕ => (F : Measure ↥Ξ))

/-- The first `N` data points `ξ¹, …, ξᴺ` of a data sequence. -/
def sample (ω : ℕ → ↥Ξ) (N : ℕ) : Fin N → ↥Ξ := fun i => ω i

/-- A data-driven uncertainty set (DUS) map: to each sample size `N` and sample
`(ξ¹, …, ξᴺ)` it assigns a set `𝓕_N` of distributions on `Ξ` (the confidence region (7) of a
goodness-of-fit test, which rejects `F₀` iff `F₀ ∉ 𝓕_N`). -/
abbrev DUS (Ξ : Set (Pt d)) := (N : ℕ) → (Fin N → ↥Ξ) → Set (ProbabilityMeasure ↥Ξ)

/-- Expectation `E_G[f(ξ)]` in `EReal`: the Bochner integral when `f` is `G`-integrable, and `+∞`
otherwise (so a non-integrable member can never lower a worst case). -/
noncomputable def expect (G : ProbabilityMeasure ↥Ξ) (f : ↥Ξ → ℝ) : EReal := by
  classical
  exact if Integrable f (G : Measure ↥Ξ) then ((∫ ξ, f ξ ∂(G : Measure ↥Ξ) : ℝ) : EReal) else ⊤

/-- Worst-case expectation (4): `C(x; 𝒢) = sup_{G ∈ 𝒢} E_G[c(x; ξ)]`, with `f = c(x; ·)`. -/
noncomputable def worstCase (𝒢 : Set (ProbabilityMeasure ↥Ξ)) (f : ↥Ξ → ℝ) : EReal :=
  ⨆ G ∈ 𝒢, expect G f

/-- Full-information objective `E_F[c(x; ξ)]` (a real number; integrable by `Standing`). -/
noncomputable def trueObj {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (c : Pt dx → ↥Ξ → ℝ)
    (x : Pt dx) : ℝ :=
  ∫ ξ, c x ξ ∂(F : Measure ↥Ξ)

/-- Definition 3 (p. 13): the test with confidence regions `𝓕` is uniformly consistent if for
every data-generating `F`, almost surely, every sequence `F_N` that does not converge weakly to
`F` is rejected infinitely often. -/
def IsUniformlyConsistent (𝓕 : DUS Ξ) : Prop :=
  ∀ F : ProbabilityMeasure ↥Ξ, ∀ᵐ ω ∂(dataLaw F), ∀ G : ℕ → ProbabilityMeasure ↥Ξ,
    ¬ Tendsto G atTop (𝓝 F) → ∃ᶠ N in atTop, G N ∉ 𝓕 N (sample ω N)

/-- Standing assumptions of §1.2 (p. 4): `X` is closed and, for every `x ∈ X`, the cost
`c(x; ·)` is `F`-integrable; plus (disclosed addition) `c(x; ·)` is continuous on `Ξ`. -/
def Standing {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ) :
    Prop :=
  IsClosed X ∧ ∀ x ∈ X, Integrable (c x) (F : Measure ↥Ξ) ∧ Continuous (c x)

/-- Assumption 1 (p. 13), with Definition 1 (p. 5): the family `{c(·; ξ) : ξ ∈ Ξ}` is
equicontinuous on the whole decision space. -/
def Assumption1 {dx : ℕ} (_X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ) : Prop :=
  EquicontinuousOn (fun ξ : ↥Ξ => fun x : Pt dx => c x ξ) Set.univ

/-- Assumption 2 (p. 13): `X` is closed and either (a) `X` is bounded, or (b) for some set
`D ⊆ Ξ` with `F(D) > 0` (taken open: disclosed addition), `c(x; ξ) → ∞` as `‖x‖ → ∞`
uniformly over `ξ ∈ D`, and `liminf_{‖x‖→∞} inf_{ξ ∉ D} c(x; ξ) > -∞`. -/
def Assumption2 {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx))
    (c : Pt dx → ↥Ξ → ℝ) : Prop :=
  IsClosed X ∧
    (Bornology.IsBounded X ∨
      ∃ D : Set ↥Ξ, IsOpen D ∧ 0 < (F : Measure ↥Ξ) D ∧
        (∀ M : ℝ, ∀ᶠ x in Bornology.cobounded (Pt dx), ∀ ξ ∈ D, M ≤ c x ξ) ∧
        ∃ B : ℝ, ∀ᶠ x in Bornology.cobounded (Pt dx), ∀ ξ ∉ D, B ≤ c x ξ)

/-- Sample mean `(1/N) ∑_{i=1}^N φ(ξⁱ)` of a nonnegative function (equals `0` when `N = 0`). -/
noncomputable def sampleMean {N : ℕ} (φ : ↥Ξ → ℝ≥0) (s : Fin N → ↥Ξ) : ℝ≥0∞ :=
  (N : ℝ≥0∞)⁻¹ * ∑ i, (φ (s i) : ℝ≥0∞)

/-- `|E_G φ(ξ) − (1/N) ∑ φ(ξⁱ)|` in `ℝ≥0∞`: equal to the real absolute difference when
`E_G φ < ∞`, and `∞` when `E_G φ = ∞`. -/
noncomputable def phiDev {N : ℕ} (φ : ↥Ξ → ℝ≥0) (G : ProbabilityMeasure ↥Ξ)
    (s : Fin N → ↥Ξ) : ℝ≥0∞ :=
  ((∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G : Measure ↥Ξ)) - sampleMean φ s) +
    (sampleMean φ s - ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(G : Measure ↥Ξ))

/-- Assumption 3 (p. 13): either (a) `Ξ` is bounded, or (b) there is `φ : Ξ → ℝ₊` with
`E_F φ < ∞` (convention of p. 10) and continuous (disclosed addition) such that, almost surely,
`sup_{F₀ ∈ 𝓕_N} |E_{F₀} φ(ξ) − (1/N) ∑ φ(ξⁱ)| → 0`, and `c(x; ξ) = O(φ(ξ))` for each `x ∈ X`,
read as on p. 10: `|c(x; ξ)| ≤ ν + η φ(ξ)`. -/
def Assumption3 {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (𝓕 : DUS Ξ) (X : Set (Pt dx))
    (c : Pt dx → ↥Ξ → ℝ) : Prop :=
  Bornology.IsBounded Ξ ∨
    ∃ φ : ↥Ξ → ℝ≥0, Continuous φ ∧ ∫⁻ ξ, (φ ξ : ℝ≥0∞) ∂(F : Measure ↥Ξ) < ⊤ ∧
      (∀ᵐ ω ∂(dataLaw F),
        Tendsto (fun N => ⨆ G ∈ 𝓕 N (sample ω N), phiDev φ G (sample ω N)) atTop (𝓝 0)) ∧
      ∀ x ∈ X, ∃ ν η : ℝ, ∀ ξ, |c x ξ| ≤ ν + η * (φ ξ : ℝ)

/-- Condition (18) for a sequence of sets `𝒢 N`: `C(x; 𝒢_N) → E_F[c(x; ξ)]` uniformly over every
compact subset of `X`. -/
def ObjConv {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)) : Prop :=
  ∀ K ⊆ X, IsCompact K → ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ x ∈ K,
    worstCase (𝒢 N) (c x) ≤ ((trueObj F c x + ε : ℝ) : EReal) ∧
      ((trueObj F c x - ε : ℝ) : EReal) ≤ worstCase (𝒢 N) (c x)

/-- Condition (19): `inf_{x ∈ X} C(x; 𝒢_N) → inf_{x ∈ X} E_F[c(x; ξ)]`, both infima in `EReal`. -/
def ValConv {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)) : Prop :=
  Tendsto (fun N => ⨅ x ∈ X, worstCase (𝒢 N) (c x)) atTop
    (𝓝 (⨅ x ∈ X, ((trueObj F c x : ℝ) : EReal)))

/-- Condition (20): every sequence `x_N` that (eventually) minimizes `C(·; 𝒢_N)` over `X` has at
least one limit point, and all its limit points minimize `E_F[c(·; ξ)]` over `X`. -/
def SolConv {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)) : Prop :=
  ∀ xs : ℕ → Pt dx,
    (∀ᶠ N in atTop, xs N ∈ X ∧ worstCase (𝒢 N) (c (xs N)) = ⨅ y ∈ X, worstCase (𝒢 N) (c y)) →
      (∃ y, MapClusterPt y atTop xs) ∧
        ∀ y, MapClusterPt y atTop xs → y ∈ X ∧ ∀ z ∈ X, trueObj F c y ≤ trueObj F c z

/-- Conditions (18)–(20) together, for a sequence of sets `𝒢 N`. -/
def Conditions {dx : ℕ} (F : ProbabilityMeasure ↥Ξ) (X : Set (Pt dx)) (c : Pt dx → ↥Ξ → ℝ)
    (𝒢 : ℕ → Set (ProbabilityMeasure ↥Ξ)) : Prop :=
  ObjConv F X c 𝒢 ∧ ValConv F X c 𝒢 ∧ SolConv F X c 𝒢

end RobustSAA.Convergence



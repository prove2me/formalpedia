-- Prove2me | Definitions.Def_MultiperiodRisk_Bellman_TestSet
-- name    : MultiperiodRisk_Bellman_TestSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T18:01:15.294019+00:00
-- url     : https://prove2.me/theorems/b55aa31a-4e7a-44c4-8a79-253980ef10a8
-- title:
--   Test probabilities on $(\Omega,\mathcal F_N)$, value processes, pasting and stability (Definition 3.1)
-- statement:
--   This file sets up the objects of Sections 3–4 of Artzner, Delbaen, Eber, Heath and Ku.
--
--   Let $(\Omega,\mathcal F,\mathbb P_0)$ be a probability space with a filtration $(\mathcal F_n)_{n\ge 0}$, and fix a horizon $N$ (only the times $0,\dots,N$ are used).
--
--   1. A **bounded stopping time** is a stopping time $\tau$ of $(\mathcal F_n)$ with $\tau(\omega)\le N$ for every $\omega$.
--   2. A **value process** is a process $X=(X_n)_{0\le n\le N}$ with $X_n$ $\mathcal F_n$-measurable and $\sup_{n\le N}\|X_n\|_{L^\infty(\mathbb P_0)}<\infty$. The class of value processes is written $\mathcal G$.
--   3. A **set of test probabilities** $\mathcal P$ is a closed convex set of probabilities on $(\Omega,\mathcal F_N)$ that are absolutely continuous with respect to $\mathbb P_0$. It is represented by the set $D$ of its densities $f=d\mathbb Q/d\mathbb P_0$: each $f\in D$ is $\mathcal F_N$-measurable, $f\ge 0$ a.s., $f$ is integrable and $\mathbb E_{\mathbb P_0}[f]=1$; $D$ is convex; $D$ is closed in $L^1(\Omega,\mathcal F_N,\mathbb P_0)$; and membership in $D$ depends only on the a.s. class of $f$. The probability with density $f$ is written $\mathbb Q_f$.
--   4. $\mathcal P^e$ is the set of $f\in D$ with $f>0$ a.s., i.e. the test probabilities equivalent to $\mathbb P_0$.
--   5. The **density martingale** of $f$ is $Z^f_n=\mathbb E_{\mathbb P_0}[f\mid\mathcal F_n]$.
--   6. For $f_0,f\in\mathcal P^e$ and a bounded stopping time $\tau$, the **result of pasting** $\mathbb Q_{f_0}$ and $\mathbb Q_f$ at $\tau$ is the probability with density
--   $$
--   L_N=\frac{Z^{f_0}_\tau\, f}{Z^{f}_\tau}.
--   $$
--   7. (Definition 3.1) $\mathcal P$ is **stable** if for all $f_0,f\in\mathcal P^e$ and every bounded stopping time $\tau$, the result of pasting lies in $D$.
--
--   The martingale $L$ of Definition 3.1 ($L_n=Z^{0}_n$ for $n\le\tau$, $L_n=Z^0_\tau Z_n/Z_\tau$ for $n\ge\tau$) is the density martingale of $L_N$, so membership of $L_N$ in $D$ is exactly the paper's condition. Stability is the hypothesis under which the two constructions of risk-adjusted values in Section 4 agree.
--
--   **Formalization Note** Time is $\mathbb N$ and processes are read only on $0,\dots,N$; Mathlib stopping times take values in $\mathbb N\cup\{\top\}$, so every stopping time used is required to satisfy $\tau\le N$. "Closed" is sequential closedness in the $L^1(\mathbb P_0)$ seminorm among $\mathcal F_N$-measurable functions (for convex sets this coincides with weak closedness). Nonnegativity of densities is required only almost surely. The division in $L_N$ returns $0$ where $Z^f_\tau=0$, which is a null set for $f\in\mathcal P^e$.
-- source:
--   Artzner, Delbaen, Eber, Heath, Ku, Coherent Multiperiod Risk Adjusted Values and Bellman's Principle, Ann. Oper. Res. 152 (2007); manuscript of Nov. 16, 2004, p. 5, §2.1 Notation (value processes); p. 9, §3 Notation and §3.1 (test probabilities, 𝒫ᵉ, density martingales); p. 10, Definition 3.1 (pasting, stability)

import Mathlib

namespace MultiperiodRisk.Bellman

open MeasureTheory Filter Topology

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A stopping time of the filtration `ℱ` taking values in `{0, …, N}`. -/
def IsBddStoppingTime (ℱ : Filtration ℕ m) (N : ℕ) (τ : Ω → WithTop ℕ) : Prop :=
  IsStoppingTime ℱ τ ∧ ∀ ω, τ ω ≤ (N : WithTop ℕ)

/-- A value process on the times `0, …, N`: adapted to `ℱ` and essentially bounded
under the reference probability `P₀`. Values at times `n > N` are never read. -/
def IsValueProcess (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) (X : ℕ → Ω → ℝ) : Prop :=
  (∀ n ≤ N, StronglyMeasurable[ℱ n] (X n)) ∧
    ∃ C : ℝ, ∀ n ≤ N, ∀ᵐ ω ∂P₀, |X n ω| ≤ C

/-- A closed convex set of test probabilities on `(Ω, ℱ_N)`, absolutely continuous with
respect to `P₀`, represented by the set of their densities `dℚ/dP₀`. -/
structure TestSet (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (N : ℕ) where
  /-- The densities `dℚ/dP₀` of the test probabilities. -/
  set : Set (Ω → ℝ)
  stronglyMeasurable : ∀ f ∈ set, StronglyMeasurable[ℱ N] f
  nonneg : ∀ f ∈ set, 0 ≤ᵐ[P₀] f
  integrable : ∀ f ∈ set, Integrable f P₀
  integral_eq_one : ∀ f ∈ set, ∫ ω, f ω ∂P₀ = 1
  convex : Convex ℝ set
  /-- Closed in `L¹(Ω, ℱ_N, P₀)`. -/
  closed : ∀ (g : ℕ → Ω → ℝ) (f : Ω → ℝ), (∀ k, g k ∈ set) → StronglyMeasurable[ℱ N] f →
    Tendsto (fun k => eLpNorm (g k - f) 1 P₀) atTop (𝓝 0) → f ∈ set
  /-- Membership depends only on the `P₀`-a.e. class of the density. -/
  ae_saturated : ∀ f ∈ set, ∀ g : Ω → ℝ, StronglyMeasurable[ℱ N] g → g =ᵐ[P₀] f → g ∈ set

/-- The test probability `ℚ` with density `f` with respect to `P₀`. -/
noncomputable def Q (P₀ : Measure Ω) (f : Ω → ℝ) : Measure Ω :=
  P₀.withDensity (fun ω => ENNReal.ofReal (f ω))

/-- `𝒫ᵉ`: the densities of the test probabilities equivalent to `P₀` on `ℱ_N`. -/
def Pe {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ} (D : TestSet P₀ ℱ N) : Set (Ω → ℝ) :=
  {f | f ∈ D.set ∧ ∀ᵐ ω ∂P₀, 0 < f ω}

/-- The density martingale `Z^ℚ_n = 𝐄_{P₀}[dℚ/dP₀ | ℱ_n]`. -/
noncomputable def Z (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (f : Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  P₀[f | ℱ n]

/-- The terminal density of the result of pasting `ℚ⁰` (density `f₀`) and `ℚ` (density `f`)
at the stopping time `τ`: `L_N = Z⁰_τ · Z_N / Z_τ`, with `Z_N = f`. -/
noncomputable def pasteDensity (P₀ : Measure Ω) (ℱ : Filtration ℕ m) (f₀ f : Ω → ℝ)
    (τ : Ω → WithTop ℕ) : Ω → ℝ :=
  fun ω => stoppedValue (Z P₀ ℱ f₀) τ ω * f ω / stoppedValue (Z P₀ ℱ f) τ ω

/-- Definition 3.1: the set of test probabilities is stable under pasting. -/
def IsStable {P₀ : Measure Ω} {ℱ : Filtration ℕ m} {N : ℕ} (D : TestSet P₀ ℱ N) : Prop :=
  ∀ f₀ ∈ Pe D, ∀ f ∈ Pe D, ∀ τ : Ω → WithTop ℕ, IsBddStoppingTime ℱ N τ →
    pasteDensity P₀ ℱ f₀ f τ ∈ D.set

end MultiperiodRisk.Bellman



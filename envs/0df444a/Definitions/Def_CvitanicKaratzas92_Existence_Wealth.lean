-- Prove2me | Definitions.Def_CvitanicKaratzas92_Existence_Wealth
-- name    : CvitanicKaratzas92_Existence_Wealth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:45.342978+00:00
-- url     : https://prove2.me/theorems/a401eab0-0057-4366-803c-6d09c2d8fcd0
-- title:
--   Sections 3, 6, and 8 — admissible wealth triples and primal value functions
-- statement:
--   A policy triple $(\pi,c,X)$ consists of a progressively measurable portfolio and nonnegative consumption process, together with its adapted continuous wealth process solving the market's stochastic integral equation (3.1). Admissibility requires $X_t\geq0$ almost surely on $[0,T]$. The classes $\mathcal A_0'(x)$ and $\mathcal A'(x)$ additionally require finite expected negative utility, and the latter requires $\pi_t\in K$ for Lebesgue-time times probability almost every $(t,\omega)$. The auxiliary-market classes use the drift correction $\delta_K(\nu)+\pi\cdot\nu$ of (8.10).
--
--   The expected utility and constrained value are
--
--   $$J(\pi,c,X)=\mathbb E\!\left[\int_0^T U_1(t,c_t)\,dt+U_2(X_T)\right],\qquad V(x)=\sup_{(\pi,c,X)\in\mathcal A'(x)}J(\pi,c,X).$$
--
--   The definitions also provide $V_0$, $V_\nu$, the budget map $\mathcal X_\nu$, its finiteness class $\mathcal D'$, and the auxiliary optimal consumption, terminal wealth, and conditional-expectation wealth processes.
--
--   **Formalization Note** Extended-real positive and negative parts define expectations; the negative part is finite on each admissible utility class. An Itô integrand in a wealth equation must be in the operator's square-integrable domain. The triple representation makes the paper's unique wealth solution explicit.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 770–771, 773–774, 777–778, (3.1)–(3.3), (6.1)–(6.5), (8.10)–(8.19); https://doi.org/10.1214/aoap/1177005576

import Definitions.Def_CvitanicKaratzas92_Existence_Utility

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

structure Policy (d : ℕ) (Ω : Type*) where
  π : VProc d Ω
  c : RProc Ω
  X : RProc Ω

def IsPortfolio {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (π : VProc d Ω) : Prop := IsLocallySquareIntegrable P 𝓕 T π

def IsConsumption {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (c : RProc Ω) : Prop :=
  IsStronglyProgressive 𝓕 c ∧ (∀ t ω, 0 ≤ c t ω) ∧
  (∀ᵐ ω ∂P, Integrable (fun s : ℝ => c s.toNNReal ω) (timeMeasure T))

def IsWealth {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (x : ℝ) (p : Policy d Ω) : Prop :=
  IsLocallySquareIntegrable P 𝓕 T
    (fun s ω => p.X s ω •
      Matrix.toEuclideanLin ((M.σ s ω).transpose) (p.π s ω)) ∧
  StronglyAdapted 𝓕 p.X ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => p.X t ω) (Set.Icc 0 T)) ∧
  ∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P,
    p.X t ω = x +
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        M.r s.toNNReal ω * p.X s.toNNReal ω - p.c s.toNNReal ω +
          p.X s.toNNReal ω *
            inner ℝ (Matrix.toEuclideanLin ((M.σ s.toNNReal ω).transpose)
              (p.π s.toNNReal ω)) (theta M s.toNNReal ω)) +
      I (fun s ω => p.X s ω •
        Matrix.toEuclideanLin ((M.σ s ω).transpose) (p.π s ω)) t ω

def IsWealthNu {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (ν : VProc d Ω) (x : ℝ) (p : Policy d Ω) : Prop :=
  IsLocallySquareIntegrable P 𝓕 T
    (fun s ω => p.X s ω •
      Matrix.toEuclideanLin ((M.σ s ω).transpose) (p.π s ω)) ∧
  StronglyAdapted 𝓕 p.X ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => p.X t ω) (Set.Icc 0 T)) ∧
  ∀ t : ℝ≥0, t ≤ T → ∀ᵐ ω ∂P,
    p.X t ω = x +
      (∫ s in Set.Icc (0 : ℝ) (t : ℝ),
        M.r s.toNNReal ω * p.X s.toNNReal ω - p.c s.toNNReal ω +
          p.X s.toNNReal ω *
            (inner ℝ (Matrix.toEuclideanLin ((M.σ s.toNNReal ω).transpose)
              (p.π s.toNNReal ω)) (theta M s.toNNReal ω) +
             (delta K (ν s.toNNReal ω)).toReal +
             inner ℝ (p.π s.toNNReal ω) (ν s.toNNReal ω))) +
      I (fun s ω => p.X s ω •
        Matrix.toEuclideanLin ((M.σ s ω).transpose) (p.π s ω)) t ω

def A0 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (x : ℝ) (p : Policy d Ω) : Prop :=
  IsPortfolio P 𝓕 T p.π ∧ IsConsumption P 𝓕 T p.c ∧
  IsWealth P 𝓕 T M I x p ∧
  (∀ᵐ ω ∂P, ∀ t ≤ T, 0 ≤ p.X t ω)

/-- Positive and negative parts of an extended real, including ±∞. -/
noncomputable def epos (z : EReal) : ℝ≥0∞ :=
  if z = ⊤ then ⊤ else ENNReal.ofReal z.toReal

noncomputable def eneg (z : EReal) : ℝ≥0∞ :=
  if z = ⊥ then ⊤ else ENNReal.ofReal (-z.toReal)

noncomputable def expectExtended {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → EReal) : EReal :=
  ((∫⁻ a, epos (f a) ∂μ : ℝ≥0∞) : EReal) -
    ((∫⁻ a, eneg (f a) ∂μ : ℝ≥0∞) : EReal)

def A0' {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω)
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (x : ℝ) (p : Policy d Ω) : Prop :=
  A0 P 𝓕 T M I x p ∧
  (∫⁻ q, eneg (uExt (U1 q.1.toNNReal) (p.c q.1.toNNReal q.2))
    ∂(spaceTime P T)) < ⊤ ∧
  (∫⁻ ω, eneg (uExt U2 (p.X T ω)) ∂P) < ⊤

def A' {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (x : ℝ) (p : Policy d Ω) : Prop :=
  A0' P 𝓕 T M I U1 U2 x p ∧
  ∀ᵐ q ∂(spaceTime P T), p.π q.1.toNNReal q.2 ∈ K

def Anu {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (ν : VProc d Ω) (x : ℝ) (p : Policy d Ω) : Prop :=
  IsPortfolio P 𝓕 T p.π ∧ IsConsumption P 𝓕 T p.c ∧
  IsWealthNu P 𝓕 T M I K ν x p ∧
  (∀ᵐ ω ∂P, ∀ t ≤ T, 0 ≤ p.X t ω)

def Anu' {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (ν : VProc d Ω) (x : ℝ) (p : Policy d Ω) : Prop :=
  Anu P 𝓕 T M I K ν x p ∧
  (∫⁻ q, eneg (uExt (U1 q.1.toNNReal) (p.c q.1.toNNReal q.2))
    ∂(spaceTime P T)) < ⊤ ∧
  (∫⁻ ω, eneg (uExt U2 (p.X T ω)) ∂P) < ⊤

noncomputable def J {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (U1 : ℝ≥0 → ℝ → ℝ)
    (U2 : ℝ → ℝ) (p : Policy d Ω) : EReal :=
  expectExtended (spaceTime P T)
      (fun q => uExt (U1 q.1.toNNReal) (p.c q.1.toNNReal q.2)) +
    expectExtended P (fun ω => uExt U2 (p.X T ω))

noncomputable def V0 {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω)
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) (x : ℝ) : EReal :=
  ⨆ p : {p : Policy d Ω // A0' P 𝓕 T M I U1 U2 x p}, J P T U1 U2 p.val

noncomputable def V {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) (x : ℝ) : EReal :=
  ⨆ p : {p : Policy d Ω // A' P 𝓕 T M I K U1 U2 x p}, J P T U1 U2 p.val

noncomputable def Vnu {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (ν : VProc d Ω) (x : ℝ) : EReal :=
  ⨆ p : {p : Policy d Ω // Anu' P 𝓕 T M I K U1 U2 ν x p}, J P T U1 U2 p.val

noncomputable def calX {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) (M : Market d Ω)
    (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (ν : VProc d Ω) (y : ℝ) : ℝ≥0∞ :=
  (∫⁻ q, ENNReal.ofReal
      (HNu M I K ν q.1.toNNReal q.2 *
        CvitanicKaratzas92.Optimality.invMarginal (U1 q.1.toNNReal) (y * HNu M I K ν q.1.toNNReal q.2))
      ∂(spaceTime P T)) +
  (∫⁻ ω, ENNReal.ofReal
      (HNu M I K ν T ω * CvitanicKaratzas92.Optimality.invMarginal U2 (y * HNu M I K ν T ω)) ∂P)

def IsD' {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ) (ν : VProc d Ω) : Prop :=
  IsD P 𝓕 T K ν ∧
  ∀ y : ℝ, 0 < y → calX P T M I K U1 U2 ν y < ⊤

noncomputable def cNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (ν : VProc d Ω) (y : ℝ) : RProc Ω :=
  fun t ω => CvitanicKaratzas92.Optimality.invMarginal (U1 t) (y * HNu M I K ν t ω)

noncomputable def xiNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (K : Set (Vec d))
    (U2 : ℝ → ℝ) (ν : VProc d Ω) (y : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  CvitanicKaratzas92.Optimality.invMarginal U2 (y * HNu M I K ν T ω)

/-- The conditional-expectation wealth process (8.19), used with ν ∈ 𝒟' and y > 0. -/
noncomputable def XNu {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) (I : ItoOperator d Ω) (K : Set (Vec d))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (ν : VProc d Ω) (y : ℝ) : RProc Ω :=
  fun t ω => (HNu M I K ν t ω)⁻¹ *
    (P[(fun ω =>
      (∫ s in Set.Icc (t : ℝ) (T : ℝ),
        HNu M I K ν s.toNNReal ω * cNu M I K U1 ν y s.toNNReal ω) +
      HNu M I K ν T ω * xiNu M I K U2 ν y T ω) | 𝓕 t]) ω

end CvitanicKaratzas92.Existence



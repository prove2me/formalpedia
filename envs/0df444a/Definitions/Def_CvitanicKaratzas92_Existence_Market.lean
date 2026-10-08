-- Prove2me | Definitions.Def_CvitanicKaratzas92_Existence_Market
-- name    : CvitanicKaratzas92_Existence_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:14:45.18487+00:00
-- url     : https://prove2.me/theorems/c9e19575-3263-4355-8e67-034da2b3d2bf
-- title:
--   Sections 2–4 and 8 — Brownian market, Itô integral, support function, and auxiliary deflators
-- statement:
--   The market has a bond rate $r$, stock appreciation vector $b$, volatility matrix $\sigma$, a standard $d$-dimensional Brownian motion $W$, and its augmented natural filtration. The local stochastic integral is characterized by bounded predictable step approximations and convergence in probability. The market assumptions are (2.3)–(2.7), including progressive measurability, a lower bound on $r$, uniform nondegeneracy of $\sigma\sigma^{\mathsf T}$, finite expected absolute interest-rate integral, and finite expected energy of $\theta=\sigma^{-1}(b-r\mathbf1)$.
--
--   For a nonempty closed convex constraint set $K\subseteq\mathbb R^d$, the support function and its effective domain are
--
--   $$\delta_K(v)=\sup_{\pi\in K}(-\pi\cdot v)\in(-\infty,+\infty],\qquad \widetilde K=\{v:\delta_K(v)<+\infty\}.$$
--
--   The definitions also give the unconstrained and auxiliary discount factors $\gamma_0,Z_0,H_0$ and $\gamma_\nu,Z_\nu,H_\nu$. They are reusable for stochastic control problems with portfolio constraints.
--
--   **Formalization Note** Time is restricted to $[0,T]$. The stochastic integral operator is required to satisfy the local Itô integral relation on every progressively measurable, almost-surely square-integrable integrand. Extended-real support values prevent the unbounded-set default of a real supremum. In (8.1), the paper prints $\leq\infty$; the finite condition used elsewhere in the paper is encoded as $<\infty$.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), pp. 769–772 and 776–778, (2.3)–(2.10), (4.1)–(4.4), (8.1)–(8.8); https://doi.org/10.1214/aoap/1177005576

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_EthierKurtz_itoStepSum

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Existence

abbrev Vec (d : ℕ) := EthierKurtz.SDEState d
abbrev VProc (d : ℕ) (Ω : Type*) := ℝ≥0 → Ω → Vec d
abbrev RProc (Ω : Type*) := ℝ≥0 → Ω → ℝ
abbrev ItoOperator (d : ℕ) (Ω : Type*) := VProc d Ω → RProc Ω

noncomputable def timeMeasure (T : ℝ≥0) : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) (T : ℝ))

noncomputable def spaceTime {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (T : ℝ≥0) : Measure (ℝ × Ω) :=
  (timeMeasure T).prod P

/-- The probability augmentation of the natural filtration of the Brownian motion. -/
def IsAugmentedBrownianFiltration {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (W : VProc d Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) : Prop :=
  ∀ t, 𝓕 t =
    (⨆ s : {s : ℝ≥0 // s ≤ t}, MeasurableSpace.comap (W s.val) inferInstance) ⊔
      MeasurableSpace.generateFrom {N : Set Ω | P N = 0}

def IsLocallySquareIntegrable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (φ : VProc d Ω) : Prop :=
  IsStronglyProgressive 𝓕 φ ∧
    ∀ᵐ ω ∂P, Integrable (fun s : ℝ => ‖φ s.toNNReal ω‖ ^ 2) (timeMeasure T)

/-- A local, almost-sure square-integrable Itô integral, characterized by bounded
predictable dyadic approximations in probability. -/
def IsItoIntegral {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (W φ : VProc d Ω) (J : RProc Ω) : Prop :=
  IsLocallySquareIntegrable P 𝓕 T φ ∧
  StronglyAdapted 𝓕 J ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun t => J t ω) (Set.Icc 0 T)) ∧
  ∀ t : ℝ≥0, t ≤ T →
    ∃ a : Fin d → ℕ → ℕ → Ω → ℝ,
      (∀ (j : Fin d) (n k : ℕ), k < 2 ^ n →
        Measurable[𝓕 ((k : ℝ≥0) * t / (2 : ℝ≥0) ^ n)] (a j n k)) ∧
      (∀ (j : Fin d) (n : ℕ), ∃ C : ℝ, ∀ (k : ℕ), k < 2 ^ n → ∀ ω, |a j n k ω| ≤ C) ∧
      (∀ j, TendstoInMeasure P
        (fun n ω => ∫ s in (0 : ℝ)..(t : ℝ),
          (EthierKurtz.itoStepValue t n (a j n) s ω - φ s.toNNReal ω j) ^ 2)
        atTop (fun _ => (0 : ℝ))) ∧
      TendstoInMeasure P
        (fun n ω => ∑ j : Fin d,
          EthierKurtz.itoStepSum (fun s ω => W s ω j) t n (a j n) ω)
        atTop (J t)

def IsItoIntegralOperator {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (W : VProc d Ω) (I : ItoOperator d Ω) : Prop :=
  ∀ φ, IsLocallySquareIntegrable P 𝓕 T φ → IsItoIntegral P 𝓕 T W φ (I φ)

structure Market (d : ℕ) (Ω : Type*) where
  r : RProc Ω
  b : VProc d Ω
  σ : ℝ≥0 → Ω → Matrix (Fin d) (Fin d) ℝ

noncomputable def theta {d : ℕ} {Ω : Type*} (M : Market d Ω) : VProc d Ω :=
  fun t ω => Matrix.toEuclideanLin ((M.σ t ω)⁻¹)
    (M.b t ω - M.r t ω • (WithLp.toLp 2 (fun _ : Fin d => (1 : ℝ))))

def Market.Standing {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (M : Market d Ω) : Prop :=
  0 < d ∧ 0 < T ∧
  IsStronglyProgressive 𝓕 M.r ∧
  IsStronglyProgressive 𝓕 M.b ∧
  IsStronglyProgressive 𝓕 M.σ ∧
  (∃ η : ℝ, 0 ≤ η ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, -η ≤ M.r t ω) ∧
  (∃ ε : ℝ, 0 < ε ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, ∀ ξ : Vec d,
    ε * ‖ξ‖ ^ 2 ≤
      inner ℝ (Matrix.toEuclideanLin (M.σ t ω * (M.σ t ω).transpose) ξ) ξ) ∧
  (∫⁻ q, ENNReal.ofReal |M.r q.1.toNNReal q.2| ∂(spaceTime P T)) < ⊤ ∧
  (∫⁻ q, ENNReal.ofReal (‖theta M q.1.toNNReal q.2‖ ^ 2) ∂(spaceTime P T)) < ⊤

noncomputable def delta {d : ℕ} (K : Set (Vec d)) (x : Vec d) : EReal :=
  ⨆ π : {π : Vec d // π ∈ K}, ((-inner ℝ π.val x : ℝ) : EReal)

def barrierCone {d : ℕ} (K : Set (Vec d)) : Set (Vec d) :=
  {x | delta K x < ⊤}

def ConstraintStanding {d : ℕ} (K : Set (Vec d)) : Prop :=
  K.Nonempty ∧ IsClosed K ∧ Convex ℝ K ∧
  ContinuousOn (fun x => (delta K x).toReal) (barrierCone K) ∧
  ∃ δ₀ : ℝ, ∀ x, (δ₀ : EReal) ≤ delta K x

noncomputable def gamma0 {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(∫ s in Set.Icc (0 : ℝ) (t : ℝ), M.r s.toNNReal ω))

noncomputable def Z0 {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(I (theta M) t ω) -
    (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      ‖theta M s.toNNReal ω‖ ^ 2)

noncomputable def H0 {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gamma0 M t ω * Z0 M I t ω

def IsH {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (ν : VProc d Ω) : Prop :=
  IsStronglyProgressive 𝓕 ν ∧
  (∫⁻ q, ENNReal.ofReal (‖ν q.1.toNNReal q.2‖ ^ 2) ∂(spaceTime P T)) < ⊤

def IsD {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (T : ℝ≥0)
    (K : Set (Vec d)) (ν : VProc d Ω) : Prop :=
  IsH P 𝓕 T ν ∧
  (∀ᵐ q ∂(spaceTime P T), ν q.1.toNNReal q.2 ∈ barrierCone K) ∧
  (∫⁻ q, ENNReal.ofReal ((delta K (ν q.1.toNNReal q.2)).toReal)
    ∂(spaceTime P T)) < ⊤

noncomputable def thetaNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (ν : VProc d Ω) : VProc d Ω :=
  fun t ω => theta M t ω + Matrix.toEuclideanLin ((M.σ t ω)⁻¹) (ν t ω)

noncomputable def gammaNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (K : Set (Vec d)) (ν : VProc d Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(∫ s in Set.Icc (0 : ℝ) (t : ℝ),
    M.r s.toNNReal ω + (delta K (ν s.toNNReal ω)).toReal))

noncomputable def ZNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (ν : VProc d Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp (-(I (thetaNu M ν) t ω) -
    (1 / 2 : ℝ) * ∫ s in Set.Icc (0 : ℝ) (t : ℝ),
      ‖thetaNu M ν s.toNNReal ω‖ ^ 2)

noncomputable def HNu {d : ℕ} {Ω : Type*} (M : Market d Ω)
    (I : ItoOperator d Ω) (K : Set (Vec d))
    (ν : VProc d Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  gammaNu M K ν t ω * ZNu M I ν t ω

end CvitanicKaratzas92.Existence



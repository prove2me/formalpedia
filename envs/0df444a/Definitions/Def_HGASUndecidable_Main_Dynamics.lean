-- Prove2me | Definitions.Def_HGASUndecidable_Main_Dynamics
-- name    : HGASUndecidable_Main_Dynamics
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:13:52.984549+00:00
-- url     : https://prove2.me/theorems/de628f1d-f33f-447b-81da-9274220d5fed
-- title:
--   Polynomial dynamics, stability, angular flows, and maximal averages
-- statement:
--   States are Euclidean vectors with zero-based finite coordinates. Real and rational multivariate polynomial fields are evaluated coordinatewise. Homogeneity means f(ax)=a^d f(x) for positive real a. A forward solution has the prescribed derivative on [0,∞), one-sided at zero. Lyapunov stability includes existence from all sufficiently small initial states and the ε–δ bound for every forward solution. GAS additionally includes forward existence from every initial state and convergence of every forward solution to zero. Entire solutions have derivatives at every real time. Continuous flows are Mathlib Flow ℝ; FlowSolves relates their orbits to the field without postulating existence. Invariant measures are Borel probability measures invariant under every real time map. β is the supremum of their integrals, M(T) the supremum of orbit integrals, and M* the EReal supremum over T≥0. The general quadratic form, its ellipsoid, radial rate, angular field, and degree/dimension padding are explicit. Padding multiplies the entire vector (H(x),−z³) by the j-th power of the squared Euclidean norm.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §§3.3–4.2 and Lemma 6.1, printed pp. 14–22,35 (PDF 16–24,37)

import Mathlib

noncomputable section
open Filter Topology MeasureTheory
open scoped BigOperators

namespace HGASUndecidable.Main

abbrev State (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev RPoly (n : ℕ) := MvPolynomial (Fin n) ℝ
abbrev QPoly (n : ℕ) := MvPolynomial (Fin n) ℚ

def evalField {n : ℕ} (p : Fin n → RPoly n) (x : State n) : State n :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval x (p i))

def evalQField {n : ℕ} (p : Fin n → QPoly n) (x : State n) : State n :=
  WithLp.toLp 2 (fun i => MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (p i))

def Homogeneous {n : ℕ} (d : ℕ) (f : State n → State n) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ x, f (a • x) = a ^ d • f x

def PolynomialField {n : ℕ} (f : State n → State n) : Prop :=
  ∃ p : Fin n → RPoly n, f = evalField p

def ForwardSolution {n : ℕ} (f : State n → State n) (x : ℝ → State n) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt x (f (x t)) (Set.Ici 0) t

def EntireSolution {n : ℕ} (f : State n → State n) (x : ℝ → State n) : Prop :=
  ∀ t, HasDerivAt x (f (x t)) t

def ForwardComplete {n : ℕ} (f : State n → State n) : Prop :=
  ∀ x₀, ∃ x, ForwardSolution f x ∧ x 0 = x₀

def LyapunovStable {n : ℕ} (f : State n → State n) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    (∀ x₀ : State n, ‖x₀‖ < δ → ∃ x, ForwardSolution f x ∧ x 0 = x₀) ∧
    ∀ x, ForwardSolution f x → ‖x 0‖ < δ → ∀ t, 0 ≤ t → ‖x t‖ < ε

def GAS {n : ℕ} (f : State n → State n) : Prop :=
  LyapunovStable f ∧ ForwardComplete f ∧
    ∀ x, ForwardSolution f x → Tendsto x atTop (𝓝 0)

def FlowSolves {n : ℕ} (S : Set (State n)) (f : State n → State n)
    (Φ : Flow ℝ S) : Prop :=
  ∀ x : S, ∀ t : ℝ, HasDerivAt (fun s => (Φ s x).val) (f (Φ t x).val) t

def invariantMeasures {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    (Φ : Flow ℝ K) : Set (ProbabilityMeasure K) :=
  {μ | ∀ t : ℝ, (μ : Measure K).map (Φ t) = (μ : Measure K)}

def beta {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    (Φ : Flow ℝ K) (a : K → ℝ) : ℝ :=
  sSup {v | ∃ μ ∈ invariantMeasures Φ, v = ∫ x, a x ∂(μ : Measure K)}

def orbitIntegral {K : Type*} [TopologicalSpace K]
    (Φ : Flow ℝ K) (a : K → ℝ) (x : K) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, a (Φ t x)

def maxIntegral {K : Type*} [TopologicalSpace K]
    (Φ : Flow ℝ K) (a : K → ℝ) (T : ℝ) : ℝ :=
  sSup (Set.range (fun x => orbitIntegral Φ a x T))

def maxIntegralStar {K : Type*} [TopologicalSpace K]
    (Φ : Flow ℝ K) (a : K → ℝ) : EReal :=
  ⨆ (T : ℝ) (_ : 0 ≤ T), (maxIntegral Φ a T : EReal)

def qInner {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v w : State n) : ℝ :=
  ∑ i, ∑ j, v i * M i j * w j

def qNorm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : State n) : ℝ :=
  Real.sqrt (qInner M v v)

def qSphere {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Set (State n) :=
  {v | qInner M v v = 1}

def radialRate {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (P : State n → State n)
    (v : State n) : ℝ := qInner M v (P v)

def angularField {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (P : State n → State n)
    (v : State n) : State n := P v - radialRate M P v • v

def padding {m n : ℕ} (h : m ≤ n) (j : ℕ) (H : State m → State m)
    (v : State n) : State n :=
  (∑ i, v i ^ 2) ^ j • WithLp.toLp 2 (fun i =>
    if hi : i.val < m then H (WithLp.toLp 2 (fun a => v (Fin.castLE h a))) ⟨i.val, hi⟩
    else -(v i) ^ 3)

end HGASUndecidable.Main



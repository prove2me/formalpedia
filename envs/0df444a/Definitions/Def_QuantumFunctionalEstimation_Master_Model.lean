-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Model
-- name    : QuantumFunctionalEstimation_Master_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T16:27:24.776685+00:00
-- url     : https://prove2.me/theorems/9636dd3f-0185-4389-a75b-56113dc1675e
-- title:
--   States, moment matching, collective estimation, and intervals
-- statement:
--   A state of dimension $d$ is a complex $d\times d$ positive semidefinite matrix of trace one. It carries the Borel sigma algebra induced from matrices. For arbitrary Borel probability laws $\mu_0,\mu_1$ on the real line, matching $K$ moments means that the following integrals exist and agree:
--   $$\int x^j\,d\mu_0(x)=\int x^j\,d\mu_1(x),\qquad 0\le j\le K.$$
--   Support on a set means almost-sure membership. The average of $n$ copies under a state prior $P$ is $\int\rho^{\otimes n}\,dP(\rho)$, with the same state in all tensor factors.
--
--   A collective estimator is a normalized countably additive positive operator-valued measure $E$ with real outcomes, acting on all $n$ copies. It succeeds for a real functional $F$ at additive error $\varepsilon$ when
--   $$\Pr_E[|Y-F(\rho)|\le\varepsilon\mid\rho^{\otimes n}]\ge 2/3$$
--   for every state $\rho$. The Born law and tensor powers are the published generic definitions. The direct sum is the actual block diagonal matrix $p\rho\oplus(1-p)\sigma$. A real interval is a nonempty order-connected set, and its distance to another interval is $\inf\{|x-y|:x\in I,y\in J\}$.
--
--   This interface permits continuous input laws, arbitrary collective measurements, and arbitrary real intervals. It imposes no rank or qubit restriction.
--
--   Differences from the source:
--   - encoding: expectations and interval distance → Bochner integrals with finite moment existence and infimum over two nonempty intervals; reason: these are the same quantities with their domains made explicit
--   - encoding: quantum states and collective estimators → density-matrix subtype and published real-outcome OperatorPOVM/copyLaw on Fin n → Fin d; reason: the register has dimension d^n and real output includes measurable classical post-processing
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), Definition 2.1, printed p. 12 (PDF p. 14); §4, Theorem 4.2, printed pp. 18–20 (PDF pp. 20–22); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/451.pdf

import Mathlib
import Definitions.Def_KnownFidelity_Rank_copyLaw
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal BigOperators Matrix ComplexOrder Matrix.Norms.Elementwise
noncomputable section

namespace QuantumFunctionalEstimation.Master

instance matrixMeasurable (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℂ) := borel _

instance matrixBorel (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℂ) := ⟨rfl⟩

/-- Actual density matrices, with the induced Borel sigma algebra. -/
abbrev State (d : ℕ) := {ρ : Matrix (Fin d) (Fin d) ℂ // QAlgorithms.IsDensityMatrix ρ}

/-- Definition 2.1: moments zero through K, for arbitrary Borel laws. -/
def MomentMatching (K : ℕ) (μ₀ μ₁ : ProbabilityMeasure ℝ) : Prop :=
  ∀ j : ℕ, j ≤ K →
    Integrable (fun x : ℝ => x ^ j) (μ₀ : Measure ℝ) ∧
    Integrable (fun x : ℝ => x ^ j) (μ₁ : Measure ℝ) ∧
    (∫ x, x ^ j ∂(μ₀ : Measure ℝ)) = ∫ x, x ^ j ∂(μ₁ : Measure ℝ)

/-- Almost-sure support, including continuous and atomic laws. -/
def Supported (μ : ProbabilityMeasure ℝ) (s : Set ℝ) : Prop :=
  ∀ᵐ x ∂(μ : Measure ℝ), x ∈ s

/-- Average of tensor powers of the SAME sampled state. -/
def averageCopies {d : ℕ} (prior : Measure (State d)) (n : ℕ) :
    Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ :=
  ∫ ρ, QAlgorithms.piKron n ρ.val ∂prior

/-- Real-outcome collective measurement, successful uniformly on ALL states. -/
def Successful {ι : Type} [Fintype ι] [DecidableEq ι]
    (F : Matrix ι ι ℂ → ℝ) (ε : ℝ) (n : ℕ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin n → ι) ℝ) : Prop :=
  ∀ (ρ : Matrix ι ι ℂ) (hρ : QAlgorithms.IsDensityMatrix ρ),
    (2 / 3 : ℝ≥0∞) ≤ KnownFidelity.Rank.copyLaw n E ρ hρ (Set.Icc (F ρ - ε) (F ρ + ε))

/-- Actual direct sum on the disjoint union of the two registers. -/
def directSum {d d' : ℕ} (p : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ)
    (σ : Matrix (Fin d') (Fin d') ℂ) :
    Matrix (Fin d ⊕ Fin d') (Fin d ⊕ Fin d') ℂ :=
  Matrix.fromBlocks ((p : ℂ) • ρ) 0 0 (((1 - p : ℝ) : ℂ) • σ)

/-- Nonempty intervals, allowing any endpoint conventions and unbounded intervals. -/
structure RealInterval where
  carrier : Set ℝ
  nonempty : carrier.Nonempty
  connected : carrier.OrdConnected

/-- The distance of two nonempty sets; its defining set is nonempty and bounded below by zero. -/
def intervalDistance (I J : RealInterval) : ℝ :=
  sInf {t : ℝ | ∃ x ∈ I.carrier, ∃ y ∈ J.carrier, t = |x - y|}

end QuantumFunctionalEstimation.Master



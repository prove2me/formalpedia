-- Prove2me | Definitions.Def_SingleCopyMoments_Adaptive_Estimation
-- name    : SingleCopyMoments_Adaptive_Estimation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T09:45:43.240794+00:00
-- url     : https://prove2.me/theorems/a3430651-6298-41c8-8044-22e1c5a463cd
-- title:
--   Additive success, moment rates, and matrix conventions
-- statement:
--   A state is any positive semidefinite complex $d\times d$ matrix of trace one. A protocol uses the published arbitrary-measurable POVM and seeded adaptive Born-kernel model, with a fixed worst-case budget $T$. Its additive success predicate is
--
--   $$\Pr_\rho\{|\widehat p-p_t(\rho)|\le\varepsilon\}\ge1-\delta\quad\text{for every state }\rho,\qquad p_t(\rho)=\operatorname{Tr}(\rho^t).$$
--
--   The transcript law is also required to be a probability measure and the success event measurable. The same protocol precedes the quantification over states. The integer level is $h=\lceil\log_2t\rceil$, and its exponent is the real number $h/(h+1)$. Estimability means a dimension-uniform constant at each fixed accuracy and failure tolerance, including every positive dimension. A simultaneous readout estimates all orders from $m$ through $2m$ on one joint success event.
--
--   These interfaces express both operational complexity bounds without a default-valued infimum. Operator norm means the Euclidean operator norm; squared Hilbert–Schmidt norm is $\operatorname{Re}\operatorname{Tr}(A^\dagger A)$. A total state normalizer returns the normalized matrix when it is a density matrix and an explicitly supplied dummy otherwise; uses of its formula are restricted to positive-trace PSD inputs.
-- source:
--   Zhenhuan Liu, STOC 2027 submission #41 (October 2026), §5 asymptotic and state conventions, printed pp. 13–14 (PDF pp. 15–16); §5.4 protocol and transcript model, printed pp. 19–20 (PDF pp. 21–22); Theorem 1, printed p. 2 (PDF p. 4); Lemma 24, printed pp. 25–26 (PDF pp. 27–28). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/41.pdf

import Definitions.Def_IncoherentPurity_Adaptive_Measurements

open scoped Matrix.Norms.L2Operator

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ENNReal ComplexOrder Topology
noncomputable section

namespace SingleCopyMoments.Adaptive

abbrev Op := IncoherentPurity.Adaptive.Op
abbrev State := IncoherentPurity.Adaptive.State
abbrev Protocol := IncoherentPurity.Adaptive.Protocol
abbrev moment := @IncoherentPurity.Adaptive.powerSum
abbrev Record {d : ℕ} (P : Protocol d) := P.Seed × (ℕ → (Unit ⊕ P.Outcome))
abbrev law := @IncoherentPurity.Adaptive.transcriptLaw

def AdditiveSucceeds {d : ℕ} (P : Protocol d) (T t : ℕ) (ε δ : ℝ) : Prop :=
  ∀ ρ : State d, IsProbabilityMeasure (law P ρ T) ∧
    MeasurableSet {H | |P.output H - moment ρ.val t| ≤ ε} ∧
    ENNReal.ofReal (1 - δ) ≤ (law P ρ T) {H | |P.output H - moment ρ.val t| ≤ ε}

/-- Least integer h with t ≤ 2^h, with its harmless t=0 default. -/
def level (t : ℕ) : ℕ := Nat.clog 2 t

def exponent (t : ℕ) : ℝ := (level t : ℝ) / ((level t : ℝ) + 1)

def Estimable (t : ℕ) (a : ℝ) : Prop :=
  ∀ ε ∈ Set.Ioo (0 : ℝ) 1, ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
    ∃ C > 0, ∀ d : ℕ, 0 < d → ∃ T : ℕ, ∃ P : Protocol d,
      (T : ℝ) ≤ C * (d : ℝ) ^ a ∧ AdditiveSucceeds P T t ε δ

/-- One classical transcript, with a jointly successful measurable vector readout. -/
def SimultaneousSucceeds {d : ℕ} (P : Protocol d) (T m : ℕ)
    (out : Record P → ℕ → ℝ) (ε δ : ℝ) : Prop :=
  (∀ k, Measurable (fun H => out H k)) ∧
  ∀ ρ : State d, IsProbabilityMeasure (law P ρ T) ∧
    ENNReal.ofReal (1 - δ) ≤ (law P ρ T)
      {H | ∀ k ∈ Finset.Icc m (2*m), |out H k - moment ρ.val k| ≤ ε}

/-- L2 operator norm, explicitly distinguished from the entrywise matrix norm. -/
def opNorm {d : ℕ} (A : Op d) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

def hsSq {d : ℕ} (A : Op d) : ℝ := (A.conjTranspose * A).trace.re

def Loewner {d : ℕ} (A B : Op d) : Prop := (B - A).PosSemidef

def unitOp (d : ℕ) : Op d := (1 / (d : ℝ)) • (1 : Op d)

def canonicalState (d : ℕ) (hd : 0 < d) : State d := by
  refine ⟨unitOp d, ?_, ?_⟩
  · exact Matrix.PosSemidef.one.smul (show (0 : ℝ) ≤ 1 / (d : ℝ) by positivity)
  · simp [unitOp, Matrix.trace_smul, Matrix.trace_one, ne_of_gt hd]

/-- A total normalizer. It is used only on positive-trace PSD inputs; outside that
specified domain it returns the supplied dummy state. -/
def normalizedState {d : ℕ} (A : Op d) (dummy : State d) : State d := by
  classical
  exact if h : ProjectiveMeasurementEquilibration.IsDensityMatrix
      ((1 / A.trace.re) • A) then ⟨(1 / A.trace.re) • A, h⟩ else dummy

end SingleCopyMoments.Adaptive



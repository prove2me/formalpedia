-- Prove2me | Definitions.Def_QuantumFunctionalEstimation_Master_Supplement_Observables
-- name    : QuantumFunctionalEstimation_Master_Supplement_Observables
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:54:49.232864+00:00
-- url     : https://prove2.me/theorems/bfab05a1-2531-4970-88d4-53f8f0172089
-- title:
--   Entropy, ordered spectrum, and distances to the maximally mixed state
-- statement:
--   For a $d$-dimensional density matrix $\rho$, write $\lambda_1\ge\cdots\ge\lambda_d\ge0$ for its eigenvalues, including zero eigenvalues with multiplicity. The power trace, von Neumann entropy, Rényi entropy and Tsallis entropy are
--   $$P_\alpha(\rho)=\sum_i\lambda_i^\alpha,\quad S(\rho)=-\sum_i\lambda_i\log\lambda_i,\quad S^R_\alpha(\rho)=\frac{\log P_\alpha(\rho)}{1-\alpha},\quad S^T_\alpha(\rho)=\frac{P_\alpha(\rho)-1}{1-\alpha}.$$
--   Here $\alpha>0$, $\alpha\ne1$ for the entropy quotients, logarithms are natural, and $0\log0=0$. The known reference is $I_d/d$. Trace distance uses one half the trace norm; fidelity is unsquared Uhlmann fidelity. Quantum Hellinger distance is the square root of $\operatorname{tr}(\sqrt\rho-\sqrt\sigma)^2$, including for noncommuting arguments. The spectrum estimator has arbitrary real vector outcomes and error $\frac12\sum_i|\widehat\lambda_i-\lambda_i|$, without optimizing over permutations. The rank tail is $\Delta_r(\rho)=\sum_{i>r}\lambda_i$.
--
--   These observables and success events share the published density-matrix, eigenvalue and collective-POVM primitives. They apply to all positive dimensions and introduce no full-rank promise.
-- source:
--   Qisheng Wang, STOC 2027 submission #451 (October 2026), printed pp. 1–7, 31–33 (PDF pp. 3–9, 33–35), §§1.1–1.2, 5.4–5.7, equation (38)

import Definitions.Def_QuantumFunctionalEstimation_Master_Functionals
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Matrix ComplexOrder ENNReal
noncomputable section

namespace QuantumFunctionalEstimation.Master.Supplement

/-- Unscaled eigenvalues, in decreasing order, including every zero with multiplicity. -/
def spectrum {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) (i : Fin d) : ℝ :=
  QAlgorithms.ascEigenvalues ρ (Fin.rev (Fin.cast (by simp) i))

def powerTrace {d : ℕ} (α : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i : Fin d, (spectrum ρ i) ^ α

def entropy {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i : Fin d, -(spectrum ρ i) * Real.log (spectrum ρ i)

def renyi {d : ℕ} (α : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.log (powerTrace α ρ) / (1 - α)

def tsallis {d : ℕ} (α : ℝ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (powerTrace α ρ - 1) / (1 - α)

def mixed (d : ℕ) : Matrix (Fin d) (Fin d) ℂ := (1 / (d : ℂ)) • 1

def traceToMixed {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  QAlgorithms.traceDistance ρ (mixed d)

def fidelityToMixed {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  QAlgorithms.rootFidelity (mixed d) ρ

/-- The Hilbert--Schmidt square-root metric, also on noncommuting arguments. -/
def hellingerSquared {ι : Type} [Fintype ι] [DecidableEq ι]
    (ρ σ : Matrix ι ι ℂ) : ℝ :=
  ((cfc Real.sqrt ρ - cfc Real.sqrt σ) ^ 2).trace.re

def hellingerToMixed {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  Real.sqrt (hellingerSquared ρ (mixed d))

def hellingerSquaredToMixed {d : ℕ} (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  hellingerSquared ρ (mixed d)

def vectorTV {d : ℕ} (x y : Fin d → ℝ) : ℝ := (∑ i, |x i - y i|) / 2

def SpectrumSuccessful (d N : ℕ) (ε : ℝ)
    (E : QAlgorithms.Measurements.OperatorPOVM (Fin N → Fin d) (Fin d → ℝ)) : Prop :=
  ∀ ρ : State d, (2 / 3 : ℝ≥0∞) ≤ KnownFidelity.Rank.copyLaw N E ρ.val ρ.property
    {x | vectorTV x (spectrum ρ.val) ≤ ε}

/-- Equation (38), using its finite spectral-sum expression rather than a real infimum. -/
def rankTail {d : ℕ} (r : ℕ) (ρ : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  ∑ i : Fin d, if r ≤ i.val then spectrum ρ i else 0

end QuantumFunctionalEstimation.Master.Supplement



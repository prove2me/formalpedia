-- Prove2me | Definitions.Def_QCopyMono_FourierSampling
-- name    : QCopyMono_FourierSampling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:59.075377+00:00
-- url     : https://prove2.me/theorems/d4cafb84-7d78-430a-b4a7-06546f122f9b
-- title:
--   The one-copy measurements of the Fourier tester: Fourier sampling ($Y$) and computational-basis sampling ($Z$)
-- statement:
--   Two one-copy measurements of $|\psi_f\rangle$ are used by the Fourier tester.
--
--   1. **Fourier sampling.** Apply $H^{\otimes(n+1)}$, with $\langle s,b|H^{\otimes(n+1)}|x,c\rangle=2^{-(n+1)/2}(-1)^{s\cdot x+bc}$, and measure in the computational basis; the outcome $(s,b)$ is read as the set $S=\{i:s_i=1\}$ and the last qubit $b$. The estimator is $Y=2|S|$ if $b=1$ and $Y=0$ otherwise.
--   2. **Computational-basis sampling.** Measure $|\psi_f\rangle$ in the computational basis, obtaining $(x,c)$; with $z_i=(-1)^{x_i}$ and $g(z)=(-1)^c$, the estimator is $Z=g(z)\sum_{i=1}^n z_i$.
--
--   Each outcome law is given by its probability mass function $|\langle\text{outcome}|\cdot\rangle|^2$ on the finite outcome set.
--
--   **Formalization Note** The function-value qubit is the `Bool` of `X n = Qubits n × Bool`. Bit addition in the sign of $H^{\otimes(n+1)}$ is exclusive or.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), proof of Proposition 1, pp.7–8 (Y, Z)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_Influence

namespace QCopyMono

open QAlgorithms Matrix

/-! # The two one-copy measurements of the Fourier tester

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), proof of Proposition 1, pp.7–8.

**Formalization Note.** The `n + 1` qubits of one copy are `X n = Qubits n × Bool`, the last
qubit (the function value) being the `Bool`. `H^{⊗(n+1)}` has entries
`⟨s, b| H^{⊗(n+1)} |x, c⟩ = 2^{-(n+1)/2} (−1)^{s·x + b c}`. A computational-basis outcome
`(s, b)` has probability `|⟨s, b| H^{⊗(n+1)} |ψ_f⟩|²`, and `s` is read as the set
`S = {i : sᵢ = 1}`. Outcome laws are given by their probability mass functions on the finite
outcome set, so expectations are finite sums. -/

/-- The Hadamard transform `H^{⊗(n+1)}` on one copy. -/
noncomputable def hadMat (n : ℕ) : Matrix (X n) (X n) ℂ :=
  fun a b => (((Real.sqrt (2 ^ (n + 1)))⁻¹ : ℝ) : ℂ) *
    ((sgn (dotBits a.1 b.1 + (a.2 && b.2)) : ℝ) : ℂ)

/-- p.7: "Apply `H^{⊗(n+1)}` to a quantum function state and measure in the computational
basis": the probability of outcome `(s, b)`. -/
noncomputable def fourierProb {n : ℕ} (f : Qubits n → Bool) (a : X n) : ℝ :=
  Complex.normSq ((hadMat n *ᵥ fnState f) a)

/-- The set `S = {i : sᵢ = 1}` read off the first `n` measured qubits. -/
def outSet {n : ℕ} (s : Qubits n) : Finset (Fin n) :=
  Finset.univ.filter fun i => s i = true

/-- p.8: "Define `Y = 2|S|` when the last qubit is 1, and `Y = 0` otherwise." -/
def fourierY {n : ℕ} (a : X n) : ℝ :=
  if a.2 then 2 * ((outSet a.1).card : ℝ) else 0

/-- p.8: measuring `|ψ_f⟩` in the computational basis: the probability of outcome `(x, c)`. -/
noncomputable def compProb {n : ℕ} (f : Qubits n → Bool) (a : X n) : ℝ :=
  Complex.normSq (fnState f a)

/-- p.8: `Z := g(z) ∑ᵢ zᵢ` for the labeled example `(z, g(z))` in the sign representation, read
from the computational-basis outcome `(x, c)` as `z = (−1)^x` and `g(z) = (−1)^c`. -/
def estZ {n : ℕ} (a : X n) : ℝ :=
  sgn a.2 * ∑ i : Fin n, sgn (a.1 i)

end QCopyMono



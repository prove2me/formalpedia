-- Prove2me | Definitions.Def_HO1D_basic
-- name    : HO1D_basic
-- status  : Definition
-- author  : @LG
-- created : 2026-11-25T01:21:03.607925+00:00
-- url     : https://prove2.me/theorems/3064b987-a453-4802-bc9e-7648f8a7c8c7
-- title:
--   1D harmonic oscillator: oscillator, characteristic length, Schrödinger and parity operators
-- statement:
--   This bundle defines the basic objects of the one-dimensional quantum harmonic oscillator.
--
--   A **harmonic oscillator** `HarmonicOscillator` is a record of three positive real parameters: the mass $m$, the reduced Planck constant $\hbar$, and the angular frequency $\omega$. Its **characteristic length** is $\xi=\sqrt{\hbar/(m\omega)}$. The **Schrödinger operator** maps a wavefunction $\psi:\mathbb R\to\mathbb C$ to $-\frac{\hbar^{2}}{2m}\psi''+\frac12 m\omega^{2}x^{2}\psi$, using Mathlib's `deriv` for differentiation. The **parity operator** maps $\psi$ to $x\mapsto\psi(-x)$. The bundle also provides the projection positivity lemmas for the three parameters.
--
--   **Formalization Note.** The source (physlib) fixes $\hbar$ to the physical constant `Constants.ℏ`; here $\hbar$ is a positive parameter of the oscillator, matching the source's docstring ("specified by three real parameters $m,\hbar,\omega$"). The source packages parity as a $\mathbb C$-linear map; here it is its underlying action, which is all the statements use. `Real.sqrt` is written explicitly for `√`.
-- source:
--   https://github.com/leanprover-community/physlib/blob/85bb8f5df598f6701be57a70f06e08069e30589c/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean#L63-L154

import Mathlib

namespace HarmonicOscillator1D

/-- A quantum harmonic oscillator specified by three positive real parameters: the mass `m` of the
particle, the reduced Planck constant `ℏ`, and the angular frequency `ω`. -/
structure HarmonicOscillator where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The angular frequency of the harmonic oscillator. -/
  ω : ℝ
  /-- The reduced Planck constant. -/
  ℏ : ℝ
  hω : 0 < ω
  hm : 0 < m
  hℏ : 0 < ℏ

namespace HarmonicOscillator

variable (Q : HarmonicOscillator)

@[simp] lemma m_pos : 0 < Q.m := Q.hm
@[simp] lemma m_nonneg : 0 ≤ Q.m := Q.hm.le
@[simp] lemma m_ne_zero : Q.m ≠ 0 := Q.hm.ne'
@[simp] lemma ω_pos : 0 < Q.ω := Q.hω
@[simp] lemma ω_nonneg : 0 ≤ Q.ω := Q.hω.le
@[simp] lemma ω_ne_zero : Q.ω ≠ 0 := Q.hω.ne'
@[simp] lemma ℏ_pos : 0 < Q.ℏ := Q.hℏ
@[simp] lemma ℏ_nonneg : 0 ≤ Q.ℏ := Q.hℏ.le
@[simp] lemma ℏ_ne_zero : Q.ℏ ≠ 0 := Q.hℏ.ne'

/-- The characteristic length `ξ` of the harmonic oscillator, defined as `√(ℏ / (m ω))`. -/
noncomputable def ξ : ℝ := Real.sqrt (Q.ℏ / (Q.m * Q.ω))

/-- The Schrödinger operator of the harmonic oscillator: the map from `ℝ → ℂ` to `ℝ → ℂ` sending
`ψ ↦ -ℏ²/(2m) · ψ'' + (1/2) m ω² x² ψ`. -/
noncomputable def schrodingerOperator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => - Q.ℏ ^ 2 / (2 * Q.m) * (deriv (deriv ψ) x) + 1/2 * Q.m * Q.ω^2 * x^2 * ψ x

end HarmonicOscillator

/-- The parity operator on functions `ℝ → ℂ`, sending `ψ` to `fun x => ψ (-x)`. -/
def parityOperator (ψ : ℝ → ℂ) : ℝ → ℂ := fun x => ψ (-x)

end HarmonicOscillator1D



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P50
-- name    : QAlgorithms_Papers_Independent_Extend50_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T21:26:30.73525+00:00
-- url     : https://prove2.me/theorems/d5e1d9bb-1ae9-442f-9259-6c32d3f2c9f2
-- title:
--   Definitions for Optical quantum memory
-- statement:
--   The objects the formalized statements of *Optical quantum memory* (arXiv:1002.4659) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `transverseForwardEfficiency`: PDF p.7, II.D.2, unnumbered display: the transverse forward-recall model as a function of the dimensionless optical depth, used on nonnegative depths.
--   - `atomicExcitationConfiguration`: PDF p.6, Eq.(5): atom `j` is excited (`a = true`); every other atom is in the ground level (`b = false`). The atom ordering is the shared qubit ordering.
--   - `singleExcitationWave`: PDF p.6, Eq.(5): the explicitly constructed single-excitation vector. Coefficients include the time-independent carrier factor `exp(i k z_j)`. Normalization is `∑ j, Complex.normSq (a j) = 1` whenever this vector is a state.
--   - `detuningPhaseWave`: PDF p.6, Eq.(5): computed detuning evolution with the source's negative phase sign, keeping the same joint single-excitation configurations.
--   - `idealCombDetuning`: PDF p.8, II.D.3: ideal tooth-center detunings at integer multiples of the common spacing. The recurrence theorem requires strictly positive spacing. This definition does not describe teeth of finite width.
--   - `linearizedFaradayOutputs`: PDF p.10, Eqs.(7),(8): the effective linearized Faraday outputs, grouped as ((atomic y, atomic z), (optical 2, optical 3)). `V` is the real vector space of operators on a common joint light-atom domain; only addition and real scalar multiplication enter these equations. This model incorporates the far-detuned, z-propagating, y-polarized light and x-polarized spin setting, small-angle approximation and replacement of macroscopic components by numbers. It supplies no error estimate comparing this model with the physical dynamics.
--   - `faradayFeedbackOutput`: PDF p.11, Eq.(9): compute the post-feedback atomic pair by subtracting `beta⁻¹` times the outgoing Stokes-2 quantity from the outgoing atomic z quantity. This is the source's algebraic effective feedback rule; it does not model quantum measurement back-action or its physical implementation.
-- source:
--   Optical quantum memory, arXiv:1002.4659v3, https://arxiv.org/abs/1002.4659v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

/-!
# Optical quantum memory: three exact consequences of the displayed models

A. I. Lvovsky, B. C. Sanders and W. Tittel, arXiv:1002.4659v3.
PDF pages are used throughout. Physical derivations of the effective models are
not assumed to be exact device theorems. The review overview is deferred.
-/

namespace QAlgorithms.Papers.Independent.Extend50.P50

/-- PDF p.7, II.D.2, unnumbered display: the transverse forward-recall model
as a function of the dimensionless optical depth, used on nonnegative depths. -/
noncomputable def transverseForwardEfficiency (d : ℝ) : ℝ :=
  d ^ 2 * Real.exp (-d)

example : transverseForwardEfficiency 0 = 0 := by
  simp [transverseForwardEfficiency]

/-- PDF p.6, Eq.(5): atom `j` is excited (`a = true`); every other atom is
in the ground level (`b = false`). The atom ordering is the shared qubit ordering. -/
def atomicExcitationConfiguration {N : ℕ} (j : Fin N) : QAlgorithms.Qubits N :=
  fun k => if k = j then true else false

example {N : ℕ} (j : Fin N) : atomicExcitationConfiguration j j = true := by
  simp [atomicExcitationConfiguration]

/-- PDF p.6, Eq.(5): the explicitly constructed single-excitation vector.
Coefficients include the time-independent carrier factor `exp(i k z_j)`.
Normalization is `∑ j, Complex.normSq (a j) = 1` whenever this vector is a state. -/
noncomputable def singleExcitationWave {N : ℕ} (a : Fin N → ℂ) :
    EuclideanSpace ℂ (QAlgorithms.Qubits N) :=
  ∑ j : Fin N, a j • QAlgorithms.ket (atomicExcitationConfiguration j)

example (a : Fin 1 → ℂ) :
    singleExcitationWave a =
      a 0 • QAlgorithms.ket (atomicExcitationConfiguration (0 : Fin 1)) := by
  simp [singleExcitationWave]

/-- PDF p.6, Eq.(5): computed detuning evolution with the source's negative
phase sign, keeping the same joint single-excitation configurations. -/
noncomputable def detuningPhaseWave {N : ℕ} (a : Fin N → ℂ)
    (detuning : Fin N → ℝ) (t : ℝ) : EuclideanSpace ℂ (QAlgorithms.Qubits N) :=
  singleExcitationWave (fun j =>
    a j * Complex.exp (-(Complex.I * ((detuning j * t : ℝ) : ℂ))))

example {N : ℕ} (a : Fin N → ℂ) (detuning : Fin N → ℝ) :
    detuningPhaseWave a detuning 0 = singleExcitationWave a := by
  simp [detuningPhaseWave]

/-- PDF p.8, II.D.3: ideal tooth-center detunings at integer multiples of the
common spacing. The recurrence theorem requires strictly positive spacing.
This definition does not describe teeth of finite width. -/
noncomputable def idealCombDetuning {N : ℕ} (r : Fin N → ℤ) (spacing : ℝ) :
    Fin N → ℝ :=
  fun j => (r j : ℝ) * spacing

example {N : ℕ} (spacing : ℝ) (j : Fin N) :
    idealCombDetuning (fun _ => 0) spacing j = 0 := by
  simp [idealCombDetuning]

/-- PDF p.10, Eqs.(7),(8): the effective linearized Faraday outputs, grouped
as ((atomic y, atomic z), (optical 2, optical 3)). `V` is the real vector
space of operators on a common joint light-atom domain; only addition and
real scalar multiplication enter these equations. This model incorporates the
far-detuned, z-propagating, y-polarized light and x-polarized spin setting,
small-angle approximation and replacement of macroscopic components by numbers.
It supplies no error estimate comparing this model with the physical dynamics. -/
noncomputable def linearizedFaradayOutputs {V : Type*} [AddCommGroup V] [Module ℝ V]
    (alpha beta : ℝ) (jy jz s2 s3 : V) : (V × V) × (V × V) :=
  ((jy + alpha • s3, jz), (s2 + beta • jz, s3))

example {V : Type*} [AddCommGroup V] [Module ℝ V]
    (alpha beta : ℝ) (jy jz s2 s3 : V) :
    (linearizedFaradayOutputs alpha beta jy jz s2 s3).2.2 = s3 := by
  rfl

/-- PDF p.11, Eq.(9): compute the post-feedback atomic pair by subtracting
`beta⁻¹` times the outgoing Stokes-2 quantity from the outgoing atomic z
quantity. This is the source's algebraic effective feedback rule; it does not
model quantum measurement back-action or its physical implementation. -/
noncomputable def faradayFeedbackOutput {V : Type*} [AddCommGroup V] [Module ℝ V]
    (alpha beta : ℝ) (jy jz s2 s3 : V) : V × V :=
  let outputs := linearizedFaradayOutputs alpha beta jy jz s2 s3
  (outputs.1.1, outputs.1.2 - beta⁻¹ • outputs.2.1)

example {V : Type*} [AddCommGroup V] [Module ℝ V]
    (alpha beta : ℝ) (jy jz s2 s3 : V) :
    (faradayFeedbackOutput alpha beta jy jz s2 s3).1 = jy + alpha • s3 := by
  rfl

end QAlgorithms.Papers.Independent.Extend50.P50



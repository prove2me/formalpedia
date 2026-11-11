-- Prove2me | Definitions.Def_QMAvsQCMAH_Normalized
-- name    : QMAvsQCMAH_Normalized
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:30.107614+00:00
-- url     : https://prove2.me/theorems/d1a6ec5e-1d2a-47fc-a910-ef3a714640c9
-- title:
--   Pure states, expectations, density operators and POVMs
-- statement:
--   A vector $\psi\in\mathbb C^\iota$ is a **pure state** if $\sum_i|\psi(i)|^2=1$. For a matrix $E$, the **expectation** $\langle\psi|E|\psi\rangle$ (its real part) is the probability of the outcome of $E$ when $E$ is a POVM element. A **density operator** is a positive semidefinite matrix of trace one, and a **POVM** with outcomes $\Omega$ is a family of positive semidefinite matrices summing to the identity.
--
--   Witnesses of quantum verifiers are pure states wherever the paper quantifies over states: acceptance is linear in the witness density operator, so pure witnesses attain both the maximum and the minimum.
-- source:
--   Cakan, Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography Even When P = QCMA, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18; Definition 1, p.19

import Mathlib

set_option autoImplicit false

namespace QMAvsQCMAH

open ComplexOrder
/-- A vector `ψ ∈ ℂ^ι` is a **pure state** (unit vector): `∑_i |ψ(i)|² = 1`.

Cakan, *Classical Oracle Separation of QMA from the QCMA Hierarchy and Quantum Cryptography
Even When P = QCMA*, STOC 2027 submission (held version, sha256 336ce016…c897), Section 3.1, p.18 (PDF p.21); Definition 1, p.19 (PDF p.22).

**Formalization Note.** Witnesses are normalized wherever the paper quantifies over states;
acceptance is linear in the witness density operator, so pure witnesses attain every value of
the existential and universal witness conditions (paper.md decision 6). -/
def Normalized {ι : Type} [Fintype ι] (ψ : ι → ℂ) : Prop := ∑ i, Complex.normSq (ψ i) = 1

/-- The expectation `⟨ψ|E|ψ⟩` (real part) of a matrix `E` in a vector `ψ`; for a POVM element
`E` and a unit vector `ψ` it is the probability of the outcome of `E`. -/
noncomputable def expect {ι : Type} [Fintype ι] (E : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℝ :=
  (dotProduct (star ψ) (E.mulVec ψ)).re

/-- A matrix `σ` is a **density operator**: positive semidefinite with trace `1`. -/
def IsDensity {ι : Type} [Fintype ι] (σ : Matrix ι ι ℂ) : Prop := σ.PosSemidef ∧ σ.trace = 1

/-- A family `E : Ω → Matrix ι ι ℂ` is a **POVM** with outcomes `Ω`: every element is positive
semidefinite and the elements sum to the identity. -/
def IsPOVM {ι Ω : Type} [Fintype ι] [DecidableEq ι] [Fintype Ω] (E : Ω → Matrix ι ι ℂ) : Prop :=
  (∀ o, (E o).PosSemidef) ∧ ∑ o, E o = 1

end QMAvsQCMAH



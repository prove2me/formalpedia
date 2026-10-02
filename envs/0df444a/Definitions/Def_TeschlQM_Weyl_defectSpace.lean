-- Prove2me | Definitions.Def_TeschlQM_Weyl_defectSpace
-- name    : TeschlQM_Weyl_defectSpace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T23:07:59.688122+00:00
-- url     : https://prove2.me/theorems/f7feaa03-26e0-4a16-8ed9-f63acf2ed02d
-- title:
--   Defect spaces K± = Ran(A ± i)^⊥ and equal finite defect indices (2.101)
-- statement:
--   Let $A$ be a linear operator in a complex Hilbert space $\mathfrak H$. The **defect spaces** are
--   $$K_\pm = \operatorname{Ran}(A \pm i)^\perp, \qquad \operatorname{Ran}(A \pm i) = \{A\psi \pm i\psi \mid \psi \in \mathfrak D(A)\},$$
--   and the **defect indices** are $d_\pm(A) = \dim K_\pm$. $A$ has **equal finite defect indices** if $d_+(A) = d_-(A) < \infty$.
--
--   **Formalization Note.** "Equal finite" is stated as: both $K_+$ and $K_-$ are finite dimensional and their `Module.finrank` agree.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 81, Section 2.6, Eq. (2.101)

import Mathlib

namespace TeschlQM.Weyl

/-- Teschl (2.101), p. 81: the defect space `K₊ = Ran(A + i)^⊥`, where
`Ran(A + i) = {Aψ + iψ | ψ ∈ 𝔇(A)}`. -/
noncomputable def defectPlus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (A.toFun + Complex.I • A.domain.subtype))ᗮ

/-- Teschl (2.101), p. 81: the defect space `K₋ = Ran(A - i)^⊥`, where
`Ran(A - i) = {Aψ - iψ | ψ ∈ 𝔇(A)}`. -/
noncomputable def defectMinus {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (A.toFun - Complex.I • A.domain.subtype))ᗮ

/-- Teschl (2.101), p. 81, and Theorem 6.20, p. 147: `A` has **equal finite defect indices**,
`d₊(A) = dim K₊` and `d₋(A) = dim K₋` are finite and equal. -/
def HasEqualFiniteDefectIndices {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ.[ℂ] H) : Prop :=
  FiniteDimensional ℂ (defectPlus A) ∧ FiniteDimensional ℂ (defectMinus A) ∧
    Module.finrank ℂ (defectPlus A) = Module.finrank ℂ (defectMinus A)

end TeschlQM.Weyl



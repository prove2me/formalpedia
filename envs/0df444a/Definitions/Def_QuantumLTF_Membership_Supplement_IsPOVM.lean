-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_IsPOVM
-- name    : QuantumLTF_Membership_Supplement_IsPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T10:34:32.246221+00:00
-- url     : https://prove2.me/theorems/30a19853-79b7-439e-a27c-42e976ab7256
-- title:
--   General quantum measurement (POVM)
-- statement:
--   A map $P$ assigning to every vector $\psi$ of a complex Hilbert space $H$ a measure $P_\psi$ on an outcome space $O$ is a **POVM** if:
--
--   1. for every unit vector $\psi$, $P_\psi$ is a probability measure;
--   2. for every measurable set $S\subseteq O$ there is a positive operator $E_S$ with $P_\psi(S)=\langle\psi,E_S\psi\rangle$ for all unit $\psi$.
--
--   It is the final measurement of the general learners of Theorems 3.5 and 5.12. Every projective measurement, and every measurement with a continuous outcome space, is of this form.
--
--   **Formalization Note** Only unit vectors are ever measured. Countable additivity of the $P_\psi$ makes $S\mapsto E_S$ a positive-operator-valued measure, and $E_O=I$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Theorems 3.5 and 5.12, pp. 38, 78 (PDF pp. 39, 79)

import Mathlib

namespace QuantumLTF.Membership.Supplement

open MeasureTheory

/-- **A general quantum measurement (POVM) on a Hilbert space.** Krivcenko, Nguyen, de Wolf, *Fast Quantum Algorithms for Learning Linear Threshold Functions*,
arXiv:2609.40331, Theorems 3.5 and 5.12,
pp. 38, 78 (PDF pp. 39, 79): the learner's final measurement, whose outcome labels a classical
hypothesis. `P ψ` is the outcome distribution on the measurable space `O` when the state `ψ` is
measured. It is a POVM: for every unit `ψ`, `P ψ` is a probability measure, and for every measurable
outcome set `S` there is a positive operator `E_S` with `P ψ (S) = ⟨ψ, E_S ψ⟩` for all unit `ψ`.

**Formalization Note.** Only unit vectors are ever measured; `P` is unconstrained elsewhere. Since
`P ψ` is a probability measure for every unit `ψ`, `E_O = I`; countable additivity of the `P ψ` makes
`S ↦ E_S` a positive-operator-valued measure (weakly, by polarization). Every projective measurement,
and every measurement with a continuous outcome space, is of this form. -/
def IsPOVM {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {O : Type} [MeasurableSpace O]
    (P : H → Measure O) : Prop :=
  (∀ ψ : H, ‖ψ‖ = 1 → IsProbabilityMeasure (P ψ)) ∧
  ∀ S : Set O, MeasurableSet S → ∃ E : H →L[ℂ] H, E.IsPositive ∧
    ∀ ψ : H, ‖ψ‖ = 1 → (P ψ S).toReal = RCLike.re (inner ℂ ψ (E ψ))

end QuantumLTF.Membership.Supplement



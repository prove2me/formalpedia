-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Operators
-- name    : PauliUnclonable531_Pauli_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:35.351385+00:00
-- url     : https://prove2.me/theorems/70ebf987-a746-44c8-9704-8fb95be14342
-- title:
--   Finite complex operators and spectral conventions
-- statement:
--   Operators on a finite register A are complex square matrices. A density operator is positive semidefinite with trace one. The Born pairing of an effect Q and a state ρ is
--
--   $$\operatorname{Born}(Q,\rho)=\operatorname{Re}\operatorname{Tr}(Q\rho).$$
--
--   Loewner order means positivity of the difference. The norm is the Euclidean spectral operator norm from Mathlib. For a Hermitian operator on a nonzero register, the largest eigenvalue is the maximum of its finite real eigenvalue family, with its sign retained. The unused non-Hermitian branch returns zero. These conventions supply the operator language shared by the construction and security statements. Density validity reuses the published QAlgorithms predicate imported by the channel definition.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), §2, pp.9–10, Eq. (12)

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Finite complex operators, §2, pp.9–10. All tensor products below use the displayed
ordered product of computational-basis indices. -/
abbrev Op (A : Type) := Matrix A A ℂ

abbrev Density {A : Type} [Fintype A] (M : Op A) : Prop :=
  QAlgorithms.IsDensityMatrix M

/-- The Euclidean operator norm, not the entrywise matrix norm (§2, p.9). -/
noncomputable def spectralNorm {A : Type} [Fintype A] [DecidableEq A] (M : Op A) : ℝ := ‖M‖

/-- Loewner order; no positive-definiteness requirement. -/
def Below {A : Type} [Fintype A] (M N : Op A) : Prop := (N - M).PosSemidef

/-- Largest signed eigenvalue. The non-Hermitian fallback is never used in this mission. -/
noncomputable def largestEigenvalue {A : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    (M : Op A) : ℝ :=
  by
    classical
    exact if h : M.IsHermitian then Finset.univ.sup' Finset.univ_nonempty h.eigenvalues else 0

/-- Born pairing is real on the physical inputs used here. -/
def born {A : Type} [Fintype A] (Q ρ : Op A) : ℝ := (Q * ρ).trace.re

end PauliUnclonable531.Pauli



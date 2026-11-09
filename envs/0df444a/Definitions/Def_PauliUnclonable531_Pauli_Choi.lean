-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Choi
-- name    : PauliUnclonable531_Pauli_Choi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:19.576692+00:00
-- url     : https://prove2.me/theorems/0020b628-ed35-4aa6-ae6d-21ab5f30266e
-- title:
--   Normalized maximally entangled density and Choi operator
-- statement:
--   For a finite register A, let Ω=|A|⁻¹ᐟ²∑ⱼ|j,j⟩. Its density matrix and the normalized Choi operator of a channel Φ are
--
--   $$|\Omega\rangle\langle\Omega|=|A|^{-1}\sum_{i,j}|i,i\rangle\langle j,j|,\qquad \tau=(\mathrm{id}_A\otimes\Phi)(|\Omega\rangle\langle\Omega|).$$
--
--   The identity extension applies Φ to each computational-basis block using the existing published idTensorSuperop. The channel output may have any finite dimension. The theorem using this definition requires A to be nonempty, excluding the empty-register inverse default. No unnormalized Choi convention is introduced.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Theorem 2.1, pp.10–11; §4.1, p.18

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Operators

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Normalized |Ω⟩⟨Ω| on A⊗A, with ordinary computational-basis ordering (Thm 2.1). -/
noncomputable def omegaDensity (A : Type) [Fintype A] [DecidableEq A] : Op (A × A) :=
  fun i j => if i.1 = i.2 ∧ j.1 = j.2 then (Fintype.card A : ℂ)⁻¹ else 0

noncomputable def choi {A O : Type} [Fintype A] [DecidableEq A]
    (Φ : Op A →ₗ[ℂ] Op O) : Op (A × O) :=
  QAlgorithms.idTensorSuperop Φ (omegaDensity A)

end PauliUnclonable531.Pauli



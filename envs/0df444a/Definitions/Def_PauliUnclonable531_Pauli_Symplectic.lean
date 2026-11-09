-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Symplectic
-- name    : PauliUnclonable531_Pauli_Symplectic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:04:52.526831+00:00
-- url     : https://prove2.me/theorems/f9a8a32d-45ed-436a-9692-e0306db9b44a
-- title:
--   Full Pauli symplectic character matrix
-- statement:
--   For labels k=(x,z) and l=(x′,z′), form the following sum in the field with two elements:
--
--   $$[k,l]=\sum_j(x_jz'_j+z_jx'_j),\qquad \Xi_{k,l}=(-1)^{[k,l]}.$$
--
--   The square matrix Ξ is indexed by all 4ⁿ labels, including the zero label in both rows and columns. This is the full matrix of Definition 2.6; deleting its identity row and column is a later proof operation. The encoding uses addition and multiplication modulo two on Fin 2, so the sign agrees with the paper's symplectic form, including n=0.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), Definitions 2.4, 2.6, pp.12–13

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Keys

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- The symplectic sum is formed in F₂; Fin 2 has addition modulo 2. -/
def symplectic {n : ℕ} (k l : Label n) : Fin 2 :=
  ∑ j, (k.1 j * l.2 j + k.2 j * l.1 j)

/-- Includes the identity row and column (Definition 2.6). -/
def character (n : ℕ) : Op (Label n) := fun k l => sign (symplectic k l)

end PauliUnclonable531.Pauli



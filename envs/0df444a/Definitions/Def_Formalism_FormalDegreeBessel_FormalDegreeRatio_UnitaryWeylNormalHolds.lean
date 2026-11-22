-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:43.846583+00:00
-- url     : https://prove2.me/theorems/9311170b-a547-4b5f-8419-93463d4278c3
-- title:
--   Unitary Weyl Normal Holds
-- statement:
--   Definitions and structural lemmas for Unitary Weyl Normal Holds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/UnitaryWeylNormalHolds.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
namespace Formalism.QuantumDeterminants
namespace WeylGroupFacts
variable {k r : ℕ}
def col (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j : Fin (2 * r + k + 1), j.val ≤ r + k → (j.val ≤ i.val ∨ r ≤ i.val) →
    g i j = if i = j then 1 else 0
def block (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  (∀ i j : Fin (2 * r + k + 1), (j.val < r ∨ r + k < j.val) → g i j = if i = j then 1 else 0) ∧
  (∀ i j : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → g i j = if i = j then 1 else 0)
def tau (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  ⟨if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val, by split_ifs <;> omega⟩
def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
end WeylGroupFacts
namespace WeylGroupFacts
variable {k r : ℕ}
end WeylGroupFacts
namespace WeylGroupFacts
variable {k r : ℕ}
end WeylGroupFacts
end Formalism.QuantumDeterminants



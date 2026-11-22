-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- name    : Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:05:25.021015+00:00
-- url     : https://prove2.me/theorems/dbdba49f-79c1-446a-a893-b00f7c15111d
-- title:
--   GBasic
-- statement:
--   Definitions and structural lemmas for GBasic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GBasic.lean

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
namespace GBasic
def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i
def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
def epsK (k r : ℕ) (i : Fin (2 * r + k + 1)) : Bool := decide (i.val < r + k)
def dK (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if epsK k r i then 1 else -1
def c1 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then 1 else if r + k < i.val then -1 / 2 else 1
def c2 (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then 1 / 2 else if r + k < i.val then 1 else 0
def Pk (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  (if j = i then c1 k r i else 0) + (if i = sig k r j then c2 k r i else 0)
end GBasic
end Formalism.QuantumDeterminants



-- Prove2me | Definitions.Def_GroundTheory_Brauer_Degree
-- name    : GroundTheory_Brauer_Degree
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:22.317814+00:00
-- url     : https://prove2.me/theorems/6a5723d5-3d28-403a-ab0d-f1c1e70bf874
-- title:
--   Degree
-- statement:
--   Definitions and structural lemmas for Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Degree.lean

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Brauer
open Module TensorProduct
universe u v w
section Degree
variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
noncomputable def degree : ℕ := Nat.sqrt (finrank K A)
end Degree
section CSA
variable {K : Type u} [Field K]
end CSA
section Index
variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
noncomputable def index : ℕ :=
  sInf {d : ℕ | ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra K D),
    Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) ∧ degree K D = d}
variable {K A}
variable (K A)
variable {K A}
variable (K A)
end Index
end GroundTheory.Brauer



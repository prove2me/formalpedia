-- Prove2me | Definitions.Def_SizeRamsey_Upper
-- name    : SizeRamsey_Upper
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T23:22:05.035621+00:00
-- url     : https://prove2.me/theorems/79abc15b-90e5-5613-bf60-6fae5fd79171
-- title:
--   Upper
-- statement:
--   Definitions and structural lemmas for Upper, from benkeene (benkeene/size-ramsey; see pinned Apache-2.0 LICENSE and source headers)'s pinned Connected size-Ramsey number of a four-edge matching versus a quadrilateral equals 17 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/benkeene/size-ramsey/blob/3233dcdd4807cbc808f68582d913c4f463047de2/SizeRamsey/Upper.lean

module
public import Definitions.Def_SizeRamsey_AInterface
set_option autoImplicit false
@[expose] public section
@[expose] public section
namespace SizeRamsey
def HasMatching2 {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 4 → V, Function.Injective f ∧ G.Adj (f 0) (f 1) ∧ G.Adj (f 2) (f 3)
end SizeRamsey
namespace SizeRamsey.Plan
def leftCopy (i : Fin 6) : Fin 12 :=
  ⟨i.val, by omega⟩
def rightCopy (i : Fin 6) : Fin 12 :=
  ⟨i.val + 6, by omega⟩
end SizeRamsey.Plan
namespace SizeRamsey
namespace Proof
end Proof
end SizeRamsey



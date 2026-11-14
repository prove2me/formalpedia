-- Prove2me | Definitions.Def_CatalyticTreeEval_DecoderTensor
-- name    : CatalyticTreeEval_DecoderTensor
-- status  : Definition
-- author  : @sragavan
-- created : 2026-11-14T01:40:39.007557+00:00
-- url     : https://prove2.me/theorems/c8aec5c5-ff04-4fce-9729-d8379e45269b
-- title:
--   Explicit ternary tensor-product decoder
-- statement:
--   Base-three indexing enumerates exactly the ternary tuples. The global kernel is the product of local integer-valued kernels, reduced only after multiplication; an abstract CRT lift combines the local shifts.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Sections 3.1/4 and Appendix B. Native composition adapts the shared-tape halting-redirection construction of tcslib/cslib.

import Definitions.Def_CatalyticTreeEval_DecoderConstruction

set_option autoImplicit false

namespace CatalyticTreeEval.DecoderConstruction

/-- The decoder's index set is exactly the ternary tuples, in finite indexing. -/
def ternaryIndex (t : ℕ) : Fin (3 ^ t) ≃ (Fin t → Fin 3) :=
  finFunctionFinEquiv.symm

/-- Product of local integer-valued kernels, before the final reduction. -/
noncomputable def tensorValue {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (β : Fin t → Fin 3) (z : ZMod m) : ℤ :=
  ∏ i, localTerm (β i) (proj i z)

/-- CRT combines ternary local shifts; integer kernel products are reduced only
after multiplying. Correctness needs the right-inverse law for `lift`, not its
particular implementation. -/
noncomputable def tensorDecoder {t m : ℕ} {p : Fin t → ℕ}
    (proj : (i : Fin t) → ZMod m →+* ZMod (p i))
    (lift : ((i : Fin t) → ZMod (p i)) → ZMod m) : Main.Decoder m (3 ^ t) where
  shift j := lift (fun i => ((ternaryIndex t j i).val : ZMod (p i)))
  term j z := (tensorValue proj (ternaryIndex t j) z : ZMod m)

end CatalyticTreeEval.DecoderConstruction



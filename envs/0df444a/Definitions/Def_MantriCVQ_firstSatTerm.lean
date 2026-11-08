-- Prove2me | Definitions.Def_MantriCVQ_firstSatTerm
-- name    : MantriCVQ_firstSatTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:21.941076+00:00
-- url     : https://prove2.me/theorems/c4a3f711-fe36-465b-a7b8-66580eddf40d
-- title:
--   The first satisfied term of a DNF
-- statement:
--   At an input that a DNF accepts, the **first satisfied term** is the first term, in the order of the list, whose literals all hold. The paper fixes an order of the terms; here that order is the list order.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §6.1, p. 23 (PDF p. 25)

import Mathlib
import Definitions.Def_SamplingAC0_DNF

open SamplingAC0

namespace MantriCVQ

/-- The first satisfied term of a DNF at the input `x`, in list order (Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), §6.1, p. 23 (PDF p. 25): "fix an order of its terms … At an accepting input
we consider the first satisfied term"). It is `none` when the DNF rejects. -/
def firstSatTerm {V : Type} (φ : DNF V) (x : V → Bool) : Option (Term V) :=
  φ.find? fun t => t.all fun l => x l.1 == l.2

end MantriCVQ



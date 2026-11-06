-- Prove2me | Definitions.Def_ConstrSOSP_encMCode
-- name    : ConstrSOSP_encMCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:06.550379+00:00
-- url     : https://prove2.me/theorems/68927ee0-2760-4d05-8607-8497eeb88725
-- title:
--   Binary code of a machine description
-- statement:
--   A machine description is written as a bit string: the numbers of symbols and states, the special states and bit symbols, then the transition table entry by entry (new state, written symbol, move), every number in self-delimiting binary. This is the "description" handed to the solver in the white-box model.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_ConstrSOSP_MCode

namespace ConstrSOSP

open QAlgorithms.LocalHamiltonian

/-- **Binary code of a Turing machine description** (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17:
"we are given the description of a polynomial-time Turing machine").

The numbers `g`, `q`, `q₀`, `qa`, `qr`, `i0`, `i1` in self-delimiting binary (`encBin`), followed
by the transition table: for every state `s` (in increasing order) and every scanned symbol
(blank first, then `0, …, g − 1`), the new state, the written symbol (`0` for blank, `i + 1` for
symbol `i`) and one bit for the move (`true` = right). -/
def encMCode (M : MCode) : List Bool :=
  encBin M.g ++ encBin M.q ++ encBin M.q₀.val ++ encBin M.qa.val ++ encBin M.qr.val ++
    encBin M.i0.val ++ encBin M.i1.val ++
    (List.finRange M.q).flatMap (fun s =>
      (none :: (List.finRange M.g).map some).flatMap (fun c =>
        encBin (M.δ s c).1.val ++
          encBin (match (M.δ s c).2.1 with
            | none => 0
            | some i => i.val + 1) ++
          [decide ((M.δ s c).2.2 = CookPvsNP.Move.right)]))

end ConstrSOSP



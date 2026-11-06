-- Prove2me | Definitions.Def_ConstrSOSP_MCode_toTM
-- name    : ConstrSOSP_MCode_toTM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:59.562202+00:00
-- url     : https://prove2.me/theorems/3de47b18-52ff-4b51-b750-5a52d10e41bc
-- title:
--   The Turing machine of a description
-- statement:
--   The one-tape Cook machine described by a machine description: its states, start, accepting and rejecting states, and transition function are read off the description.
-- source:
--   Kontogiannis, Panageas & Pollatos, The Computational Complexity of Avoiding Strict Saddle Points in Constrained Optimization, arXiv:2604.02285 (2 Nov 2026), §4.1, p.17

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ConstrSOSP_MCode

namespace ConstrSOSP

/-- **The Turing machine described by an `MCode`**: the public Cook machine
`CookPvsNP.TM (Fin g)` with states `Fin q`, start state `q₀`, accepting state `qa`, rejecting
state `qr` and transition function `δ` (arXiv:2604.02285, 2 Nov 2026, §4.1, p.17). -/
def MCode.toTM (M : MCode) : CookPvsNP.TM (Fin M.g) where
  Q := Fin M.q
  q₀ := M.q₀
  qaccept := M.qa
  qreject := M.qr
  accept_ne_reject := M.hne
  δ := M.δ

end ConstrSOSP



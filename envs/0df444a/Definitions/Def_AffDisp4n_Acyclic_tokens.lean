-- Prove2me | Definitions.Def_AffDisp4n_Acyclic_tokens
-- name    : AffDisp4n_Acyclic_tokens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:57:23.166524+00:00
-- url     : https://prove2.me/theorems/0c511d63-99fe-4da8-ae5e-b0345cf48ff4
-- title:
--   The words of a straight-line circuit
-- statement:
--   A straight-line circuit is written as a list of words: the number of gates; for each gate in topological order its truth table of four bits and its two inputs; the output and its negation bit. Each input is a tag followed by the constant, the input or the gate index.
-- source:
--   Mishra, Santhanam, An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits, STOC 2027 submission (manuscript sha256 6bc3ff9d…fd96), §2.3 (ii)–(iii), pp.13–14

import Mathlib
import Definitions.Def_AffDisp4n_Src
import Definitions.Def_AffDisp4n_Acyclic
import Definitions.Def_AffDisp4n_vecWord

namespace AffDisp4n

/-- The words of a source: a tag, then the constant, the input (written by `idx`) or the gate index. -/
def Src.tokens {V : Type} {k : ℕ} (idx : V → List Bool) : Src V k → List (List Bool)
  | .const c => [[false, false], [bitOf c]]
  | .input v => [[false, true], idx v]
  | .gate j => [[true, false], natWord j.val]

/-- An operation `𝔽₂ × 𝔽₂ → 𝔽₂` as its truth table of four bits. -/
def opWord (h : ZMod 2 → ZMod 2 → ZMod 2) : List Bool :=
  [bitOf (h 0 0), bitOf (h 0 1), bitOf (h 1 0), bitOf (h 1 1)]

/-- The **words of a straight-line circuit**, for the machine statements (Mishra–Santhanam, *An Explicit 4n−O(log(n)) Size Lower Bound against General Boolean Circuits*, STOC 2027 submission (manuscript sha256 6bc3ff9d…), §2.3 (ii)–(iii), pp.13–14): the number of gates in unary; for each gate in topological order its
truth table and its two inputs; the output and its negation bit. Inputs are written by `idx`. -/
def Acyclic.tokens {V : Type} (idx : V → List Bool) (C : Acyclic V) : List (List Bool) :=
  [natWord C.size] ++
    (List.ofFn fun g : Fin C.size =>
      [opWord (C.op g)] ++ (C.in₁ g).tokens idx ++ (C.in₂ g).tokens idx).flatten ++
    C.out.tokens idx ++ [[bitOf C.outNeg]]

end AffDisp4n



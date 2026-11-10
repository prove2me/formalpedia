-- Prove2me | Definitions.Def_AvgWorstGap_code
-- name    : AvgWorstGap_code
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:02.603069+00:00
-- url     : https://prove2.me/theorems/ad58fb53-e781-44ea-83b7-7af56f700dbe
-- title:
--   The fixed standard encoding of machines
-- statement:
--   The paper assumes "a fixed standard encoding for Turing machines" $\langle M\rangle$. This module fixes one concretely. $\langle M\rangle$ lists the number of states, the number of work tapes, and the start, halting, query and two answer states, each as a self-delimiting binary number $\mathrm{dbl}(\mathrm{bin}(n))\,01$. It then lists the whole transition table, entry by entry, in a fixed order: by state, then by the scanned read-only symbols, then by the scanned read/write symbols. Each entry gives the target state, the four read-only head moves, and the written symbol and move for each read/write tape, with two bits per symbol and per move.
--
--   The encoding is injective. It is decoded and checked for validity in a single left-to-right pass, in time polynomial in its length.
--
--   **Formalization Note** The mission uses this one encoding everywhere. It does not quantify over encodings.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, The Gap Between Average-Case and Worst-Case Complexity, arXiv:2610.19162 (Oct. 30, 2026), §2.1, p.12, footnote 7

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_AvgWorstGap_pairStr

namespace AvgWorstGap

open NKtLB

/-- A self-delimiting binary code of a natural number: its binary representation bit-doubled,
then `01`. -/
def natEnc (n : ℕ) : List Bool := dbl (bin n) ++ [false, true]

/-- Two bits per tape symbol. -/
def symEnc : Sym → List Bool
  | Sym.zero => [false, false]
  | Sym.one => [false, true]
  | Sym.bot => [true, false]
  | Sym.blank => [true, true]

/-- Two bits per head move. -/
def moveEnc : Move → List Bool
  | Move.left => [false, false]
  | Move.stay => [false, true]
  | Move.right => [true, false]

/-- The tape symbols in a fixed order. -/
def symList : List Sym := [Sym.zero, Sym.one, Sym.bot, Sym.blank]

/-- All functions `Fin k → Sym` in a fixed (lexicographic) order. -/
def funList : (k : ℕ) → List (Fin k → Sym)
  | 0 => [fun i => i.elim0]
  | k + 1 => (funList k).flatMap (fun f => symList.map (fun a => (Fin.cons a f : Fin (k + 1) → Sym)))

/-- The code of one transition-table entry: target state, the four read-only moves, and the
written symbol and move of each read/write tape. -/
def entryEnc (M : Machine)
    (e : Fin M.nStates × (Fin 4 → Move) × (Fin (M.works + 2) → Sym × Move)) : List Bool :=
  natEnc e.1 ++ (List.finRange 4).flatMap (fun i => moveEnc (e.2.1 i)) ++
    (List.finRange (M.works + 2)).flatMap (fun j => symEnc (e.2.2 j).1 ++ moveEnc (e.2.2 j).2)

/-- **The fixed standard encoding `⟨M⟩` of machines** (arXiv:2610.19162, version of October 30,
2026, §2.1, p.12 and footnote 7: "we assume a fixed standard encoding for Turing machines").

`code M` lists, each as `natEnc`, the number of states, the number of work tapes, and the start,
halting, query, `qyes` and `qno` states; then the whole transition table, entry by entry, with the
states in increasing order, then the scanned read-only symbols, then the scanned read/write symbols,
each in the order of `funList`.

**Formalization Note.** One concrete encoding is fixed for the whole mission (the paper's "fixed
standard encoding"); the mission does not quantify over encodings. The code is injective and is
decoded (and checked for validity) by a single left-to-right pass, in time polynomial in its
length. -/
def code (M : Machine) : List Bool :=
  natEnc M.nStates ++ natEnc M.works ++ natEnc M.start ++ natEnc M.halt ++ natEnc M.query ++
    natEnc M.qyes ++ natEnc M.qno ++
    (List.finRange M.nStates).flatMap (fun q => (funList 4).flatMap (fun a =>
      (funList (M.works + 2)).flatMap (fun b => entryEnc M (M.δ q a b))))

end AvgWorstGap



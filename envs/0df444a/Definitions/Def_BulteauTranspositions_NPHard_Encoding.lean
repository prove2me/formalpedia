-- Prove2me | Definitions.Def_BulteauTranspositions_NPHard_Encoding
-- name    : BulteauTranspositions_NPHard_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T21:54:05.256988+00:00
-- url     : https://prove2.me/theorems/5150bc74-7ba5-453f-bb82-4de6fda7f6da
-- title:
--   Explicit binary encoding and the full sorting decision language
-- statement:
--   The published general binary-number code writes a unary bit-length header and a binary magnitude, using logarithmic space per number. A natural-number list is its encoded length followed by its encoded entries. A sorting code writes a sign bit, n, the magnitude of its integer budget, and every value π(0),…,π(n), with unambiguous lengths. The sorting language consists exactly of codes of positive-span sentinel permutations having an actual sorting sequence within the signed budget. Invalid codes, invalid permutations, noncanonical negative zero, and negative budgets are outside the language. In particular the entire permutation is explicit and a large budget is never expanded in unary.
--
--   A 3DT code records span and each oriented triple by its occupied positions, thereby preserving dots and removing dependence on alphabet names. An assembling code records each gate kind and its three port numbers after compact renaming in first input-occurrence order. These are syntactic encodings only; polynomial running time remains a theorem obligation.
-- source:
--   Bulteau, Fertin and Rusu, Sorting by Transpositions is Difficult, supplied PDF arXiv:1011.1157v1, definitions and constructions, printed/PDF pp. 3, 26–34; https://arxiv.org/abs/1011.1157v1

import Definitions.Def_BulteauTranspositions_NPHard_Blocks
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ClickomaniaNPC_ThreeColor_Code

namespace BulteauTranspositions.NPHard

def encodeNats (xs : List ℕ) : List Bool :=
  ClickomaniaNPC.ThreeColor.encodeNat xs.length ++
    xs.flatMap ClickomaniaNPC.ThreeColor.encodeNat

/-- The sign bit precedes the binary magnitude. Both sentinels and every entry are written. -/
def encodeSorting (n : ℕ) (p : ℕ → ℕ) (k : ℤ) : List Bool :=
  (decide (k < 0)) :: encodeNats (n :: k.natAbs :: (List.range (n+1)).map p)

/-- Malformed codes and negative budgets cannot satisfy this membership predicate. -/
def sortingLanguage : CookPvsNP.Lang Bool :=
  {s | ∃ n p k, IsPermutation n p ∧ s = encodeSorting n p k ∧ SortsWithin n p k}

/-- Triple positions encode the alphabet up to renaming, retaining the fixed span and dots. -/
def encodeInstance (I : Instance) : List Bool :=
  encodeNats (I.span :: I.triples.flatMap (fun t => t.symbols.map I.pos))

def gateTag (g : Gate) : ℕ :=
  match g.kind with
  | .copy => 0 | .and => 1 | .or => 2 | .var => 3

/-- Compact wire renaming makes input length polynomial in span, even for sparse wire names. -/
def encodeAssembly (gs : List Gate) : List Bool :=
  let ws := (gs.flatMap Gate.inputs).eraseDups
  encodeNats (gs.flatMap fun g => [gateTag g, ws.idxOf g.w0, ws.idxOf g.w1, ws.idxOf g.w2])

end BulteauTranspositions.NPHard



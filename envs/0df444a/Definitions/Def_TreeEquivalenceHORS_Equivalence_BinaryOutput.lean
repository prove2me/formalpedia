-- Prove2me | Definitions.Def_TreeEquivalenceHORS_Equivalence_BinaryOutput
-- name    : TreeEquivalenceHORS_Equivalence_BinaryOutput
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T18:27:41.221676+00:00
-- url     : https://prove2.me/theorems/8ee1d0aa-6c39-451c-bdbd-f051db3003db
-- title:
--   Translation of recursion schemes to the fixed binary alphabet
-- statement:
--   Replace the three source constructors by fresh first-order rules generating their binary contexts. The new rules occupy the first three positions, so each original nonterminal index is shifted by three.
-- source:
--   Xiao and Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, Section 5.6, equation (26) and Lemma 5.9, printed p. 21. https://arxiv.org/html/2610.39678v1#S5.SS6

import Definitions.Def_TreeEquivalenceHORS_Equivalence_Syntax

namespace TreeEquivalenceHORS.Equivalence

def binaryTerm : Tm → Tm
  | .var i => .var i
  | .nt i => .nt (3 + i)
  | .tm i => if i < 3 then .nt i else .tm 2
  | .app t u => .app (binaryTerm t) (binaryTerm u)

def binaryFork (t u : Tm) := ((Tm.tm 1).app t).app u
def binaryLeaf := Tm.tm 0

def binaryRules : List Tm :=
  [binaryLeaf, binaryFork binaryLeaf (.var 0), binaryFork (binaryFork binaryLeaf binaryLeaf) (binaryFork (.var 0) (binaryFork (.var 1) (.var 2)))]

def binaryScheme (G : HORS) : HORS :=
  ⟨sigma2, sigma0.map termTy ++ G.nts, binaryRules ++ G.rules.map binaryTerm, 3 + G.start⟩

end TreeEquivalenceHORS.Equivalence



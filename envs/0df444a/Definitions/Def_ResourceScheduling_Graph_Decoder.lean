-- Prove2me | Definitions.Def_ResourceScheduling_Graph_Decoder
-- name    : ResourceScheduling_Graph_Decoder
-- status  : Definition
-- author  : @arexychen
-- created : 2026-10-02T05:47:49.686862+00:00
-- url     : https://prove2.me/theorems/073880c2-6d48-4351-81da-cf3cf4f4b3fa
-- title:
--   A total parser for the scheduling mission graph encoding
-- statement:
--   For a word over the scheduling alphabet, parse a separator-terminated unary natural $t$ and a remaining candidate adjacency matrix. Accept precisely when the matrix has $(3t)^2$ entries and its row-major relation is symmetric and irreflexive; return the resulting graph on $3t$ vertices. All other words return a failure value. The empty graph ($t=0$) is included. These are executable finite definitions; correctness and polynomial running time are separate obligations.
-- source:
--   New elementary encoding lemma for the exact Prove2Me ResourceScheduling.Graph encodings (ResourceScheduling_Graph_Complexity, ResourceScheduling_Graph_GraphPartition, ResourceScheduling_Graph_ResDot11, ResourceScheduling_Graph_Construction). Construction: Blazewicz, Lenstra and Rinnooy Kan, Discrete Applied Mathematics 5 (1983), p. 15, Theorems 2-3, https://doi.org/10.1016/0166-218X(83)90012-4; author preprint https://ir.cwi.nl/pub/9642/9642D.pdf, printed pp. 5-6. The numerical encoding bound and parser lemmas are auxiliary results for the platform encoding, not numbered claims of the paper.

import Definitions.Def_ResourceScheduling_Graph_Codec
import Definitions.Def_ResourceScheduling_Graph_GraphPartition

set_option autoImplicit false

namespace ResourceScheduling.Graph

/-- Row-major access to a candidate adjacency matrix. Bounds are checked by `ValidGraphBody`. -/
def rawAdj (n : ℕ) (bits : List Letter) (i j : Fin n) : Prop :=
  bits.getD (i.val * n + j.val) Letter.sep = Letter.one

instance (n : ℕ) (bits : List Letter) : DecidableRel (rawAdj n bits) :=
  fun _ _ => inferInstanceAs (Decidable (_ = _))

/-- A graph body has exactly the declared size and describes a simple undirected graph. -/
def ValidGraphBody (n : ℕ) (bits : List Letter) : Prop :=
  bits.length = n * n ∧ (∀ i j, rawAdj n bits i j → rawAdj n bits j i) ∧
    (∀ i, ¬ rawAdj n bits i i)

instance (n : ℕ) (bits : List Letter) : Decidable (ValidGraphBody n bits) := by
  unfold ValidGraphBody
  infer_instance

/-- Parse the original graph encoding, rejecting missing separators, wrong sizes,
loops, and asymmetric adjacency matrices. -/
def decodeGraph (w : List Letter) : Option GraphData :=
  match readUnary w with
  | none => none
  | some (t, bits) =>
    if h : ValidGraphBody (3 * t) bits then
      some {
        t := t
        G := {
          Adj := rawAdj (3 * t) bits
          symm := ⟨fun {i j} => h.2.1 i j⟩
          loopless := ⟨h.2.2⟩ } }
    else
      none

end ResourceScheduling.Graph



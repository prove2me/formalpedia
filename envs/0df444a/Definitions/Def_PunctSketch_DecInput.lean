-- Prove2me | Definitions.Def_PunctSketch_DecInput
-- name    : PunctSketch_DecInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:33.500251+00:00
-- url     : https://prove2.me/theorems/304bb6af-201b-473f-96c4-ace35eb686e5
-- title:
--   Input of the coordinator
-- statement:
--   The coordinator knows $n$, $k$, the public coins and the messages of the $n$ node players, and nothing else about $G$. The public coins are part of the input because the verification step of Lemma 5.1 computes a fingerprint from the shared vector $\boldsymbol r$. The encoding writes $n$ in unary.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §2, p.5 (PDF p.6); proof of Lemma 5.1, p.16 (PDF p.17)

import Mathlib
import Definitions.Def_PunctSketch_encBits
open OnlineCRS.Combine

namespace PunctSketch

/-- **Input of the coordinator.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §2, p.5: "The coordinator starts out with no input but
learns some information about G from these messages." The coordinator knows `n`, `k`, the public
coins (the verification of Lemma 5.1, p.16, computes the fingerprint from `𝒓`) and the messages.

**Formalization Note.** The graph is not a field: the coordinator sees it only through the
messages. -/
structure DecInput where
  n : ℕ
  k : ℕ
  coins : List ℕ
  messages : List (List Bool)

/-- The tape encoding of the coordinator's input (`n` in unary). -/
def DecInput.code (x : DecInput) : List Sym :=
  encUnary x.n ++ [3] ++ encNat x.k ++ [3] ++ encNatList x.coins ++ [3] ++
    encBitsList x.messages

end PunctSketch



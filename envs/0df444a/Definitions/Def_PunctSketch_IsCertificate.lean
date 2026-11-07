-- Prove2me | Definitions.Def_PunctSketch_IsCertificate
-- name    : PunctSketch_IsCertificate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:42:34.88829+00:00
-- url     : https://prove2.me/theorems/27d06051-bfe5-4bdb-96a2-e481398a57df
-- title:
--   A correct certified answer of the coordinator
-- statement:
--   An output string certifies the $k$-connectivity answer for $G$ when it has exactly the form (flag, $\binom n2$ bits for a graph $H$, $n$ bits for a set $Z$), so that a malformed output is never a certificate, and:
--
--   1. $H$ is a subgraph of $G$ with at most $kn-\binom{k+1}{2}$ edges;
--   2. for every $F$ with $|F|<k$, two vertices are connected in $H\setminus F$ exactly when they are connected in $G\setminus F$;
--   3. if the flag is true, both $G$ and $H$ are $k$-connected;
--   4. if the flag is false, $|Z|<k$ and $G\setminus Z$ is disconnected.
--
--   Clause 3 is the "small $k$-connected spanning subgraph that witness a yes answer", clause 4 the "subset of fewer than $k$ vertices that witnesses a no answer".
--
--   **Formalization Note** The edge bound is written additively, $|E(H)|+\binom{k+1}{2}\le kn$, so no natural-number subtraction occurs. $k$-connectivity is the published `IsNTuplyConnected`, which for $k\ge1$ is the paper's definition.
-- source:
--   Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity, STOC 2027 submission (manuscript sha256 a630f88815653b5f1b35579cbfa2100b617a4d540f009489027b8c55f65e1a2c), §1, p.1 (PDF p.2); §5.4, pp.21–22 (PDF pp.22–23); Result 1, p.2 (PDF p.3)

import Mathlib
import Definitions.Def_Balinski61_Connectivity_TuplyConnected
import Definitions.Def_PunctSketch_ConnAvoid
import Definitions.Def_PunctSketch_graphOfBits

namespace PunctSketch

/-- **A correct certified answer of the coordinator.** Çekirge, Chakrabarti, Dutta, McGregor, Vinayak, *Puncturable Graph Sketches and the Complexity of Distributed Vertex Connectivity*, STOC 2027 submission (manuscript sha256 a630f888…), §1, p.1: "A stronger goal is to certify
the answer, providing either a subset of fewer than k vertices that witnesses a "no" answer, or a
small k-connected spanning subgraph that witness a "yes" answer", with the size and the agreement
from §5.4, pp.21–22: "a k-vertex-connectivity certificate of size kn − (k+1 choose 2) edges".

`out` must parse as a flag, `n.choose 2` bits for a graph `H` and `n` bits for a set `Z`, with exact
lengths, so that a malformed output is not a certificate. Then: `H ≤ G`;
`|E(H)| + (k+1 choose 2) ≤ k n`; `H ∖ F` and `G ∖ F` have the same connectivity relation for every
`|F| < k`; flag `true` means `G` and `H` are both `k`-connected; flag `false` means `|Z| < k` and
`G ∖ Z` is disconnected.

**Formalization Note.** The edge bound is additive, so no natural-number subtraction occurs.
`IsNTuplyConnected G k` asks for at least `k + 1` vertices and `G.induce Xᶜ` connected for all
`|X| < k`, the paper's "deleting fewer than k of its vertices leaves a connected graph with at least
two vertices" when `k ≥ 1`. -/
def IsCertificate {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (out : List Bool) : Prop :=
  ∃ (flag : Bool) (hBits zBits : List Bool),
    out = flag :: (hBits ++ zBits) ∧ hBits.length = n.choose 2 ∧ zBits.length = n ∧
    (graphOfBits hBits : SimpleGraph (Fin n)) ≤ G ∧
    (graphOfBits hBits : SimpleGraph (Fin n)).edgeSet.ncard + (k + 1).choose 2 ≤ k * n ∧
    (∀ F : Finset (Fin n), F.card < k → ∀ x y,
      ConnAvoid (graphOfBits hBits : SimpleGraph (Fin n)) F x y ↔ ConnAvoid G F x y) ∧
    (flag = true →
      Balinski61.Connectivity.IsNTuplyConnected G k ∧
        Balinski61.Connectivity.IsNTuplyConnected (graphOfBits hBits : SimpleGraph (Fin n)) k) ∧
    (flag = false →
      (setOfBits zBits : Finset (Fin n)).card < k ∧
        ¬ (G.induce ((setOfBits zBits : Finset (Fin n)) : Set (Fin n))ᶜ).Connected)

end PunctSketch



-- Prove2me | Definitions.Def_DirTeleMC_Inst
-- name    : DirTeleMC_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:29:17.270289+00:00
-- url     : https://prove2.me/theorems/49057096-2ccd-41e9-9039-9e2201a5e737
-- title:
--   An instance of directed telephone multicast and $k$-multicast
-- statement:
--   An **instance** consists of a digraph $G = (V, E)$ with $n = |V|$ vertices, a source $s \in V$, a set $K$ of terminals and the number $k$ of terminals to inform. Directed telephone multicast (DTM) is the case $k = |K|$; directed $k$-multicast lets $K$ contain $t \ge k$ terminals of which any $k$ must be informed.
--
--   The instance is **well-formed** when the standing assumptions of the paper hold:
--   1. $s \notin K$, that is $K \subseteq V \setminus \{s\}$;
--   2. $2 \le k \le |K|$;
--   3. every terminal is reachable from $s$.
--
--   **Formalization Note** Vertices are `Fin n` and the digraph is an adjacency matrix; loops are allowed and play no role.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), §1, p.1 (PDF p.2); §3, p.8 (PDF p.9); Algorithm 2, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_DirTeleMC_IsJump

namespace DirTeleMC

/-- **An instance of directed telephone multicast and of directed k-multicast.**
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), §1, p.1: "The input is a directed graph G = (V, E) with n = |V| vertices, a
source s ∈ V, and a set K ⊆ V \ {s} of k terminals, all reachable from s"; §3, p.8: "For k-multicast, K
instead contains t ≥ k terminals, of which any k must be informed"; Algorithm 2, p.24: "k: the number of
terminals to inform; k = |K| for DTM, and k ≤ |K| for k-multicast".

`n` is the number of vertices (`V = Fin n`), `adj` the adjacency matrix, `s` the source, `K` the terminal set
and `k` the number of terminals to inform.

**Formalization Note.** One structure covers both problems: DTM is the case `k = K.card`. The standing
assumptions of the paper are not part of the type; they are `Inst.WF`. -/
structure Inst where
  n : ℕ
  adj : Fin n → Fin n → Bool
  s : Fin n
  K : Finset (Fin n)
  k : ℕ

/-- **The standing assumptions on an instance** (§1, p.1; §3, p.8; Theorem 1.1, p.1: "k ≥ 2"):
the source is not a terminal (`K ⊆ V \ {s}`), at least two terminals are to be informed, at most `|K|`
of them (`k = |K|` for DTM), and every terminal is reachable from `s`. -/
def Inst.WF (I : Inst) : Prop :=
  I.s ∉ I.K ∧ 2 ≤ I.k ∧ I.k ≤ I.K.card ∧ ∀ t ∈ I.K, Reach I.adj I.s t

end DirTeleMC



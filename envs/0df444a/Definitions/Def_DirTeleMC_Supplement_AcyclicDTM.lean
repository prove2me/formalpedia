-- Prove2me | Definitions.Def_DirTeleMC_Supplement_AcyclicDTM
-- name    : DirTeleMC_Supplement_AcyclicDTM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:39:07.249379+00:00
-- url     : https://prove2.me/theorems/6926f2c2-bbb4-47ef-9f94-4c1502c9d2c7
-- title:
--   Acyclic DTM instances
-- statement:
--   A digraph is **acyclic** if it has no directed closed walk with at least one arc, that is, no directed cycle (a loop counts as a cycle).
--
--   An **acyclic DTM instance** is an instance $(G,s,K)$ of directed telephone multicast — all $k=|K|$ terminals must be informed — that is well formed ($s\notin K$, every terminal reachable from $s$, $k\ge2$) and whose digraph $G$ is acyclic.
--
--   These are the instances of the hardness result, Theorem 1.4.
--
--   **Formalization Note** Walks are vertex lists, as in the published `DirTeleMC.IsJump`; well-formedness is the published `Inst.WF`.
-- source:
--   S. Kamali, S.-M. Seyed-Javadi, Approximation Algorithms for Directed Telephone Multicast, arXiv:2610.27422 (manuscript sha256 e56edddf…), Theorem 1.4, p.4 (PDF p.5); §D.1, p.51 (PDF p.52)

import Mathlib
import Definitions.Def_DirTeleMC_Inst

namespace DirTeleMC.Supplement

open DirTeleMC

/-- **An acyclic digraph**: no directed closed walk with at least one arc, i.e. no directed cycle (loops included).
Kamali, Seyed-Javadi, *Approximation Algorithms for Directed Telephone Multicast*, arXiv:2610.27422
(manuscript sha256 e56edddf…), Theorem 1.4, p.4 ("acyclic DTM instances"); §D.1, p.51 (the hub gadget "is
acyclic").

**Formalization Note.** Walks are vertex lists, as in the published `DirTeleMC.IsJump`; a closed walk with at least
one arc is a list with at least two entries whose first and last entries agree. A digraph has such a walk iff it has
a directed cycle. -/
def IsAcyclic {n : ℕ} (adj : Fin n → Fin n → Bool) : Prop :=
  ∀ P : List (Fin n), 2 ≤ P.length → P.head? = P.getLast? → ¬ P.IsChain fun a b => adj a b = true

/-- **An acyclic DTM instance** (Theorem 1.4, p.4): a well-formed instance (`s ∉ K`, every terminal reachable from
`s`, at least two terminals; the published `Inst.WF`) of directed telephone multicast (`k = |K|`, all terminals must
be informed) whose digraph is acyclic. -/
def AcyclicDTM (I : Inst) : Prop :=
  I.WF ∧ I.k = I.K.card ∧ IsAcyclic I.adj

end DirTeleMC.Supplement



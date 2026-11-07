-- Prove2me | Definitions.Def_DynOracleConn_ProbeTree
-- name    : DynOracleConn_ProbeTree
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:46:40.221972+00:00
-- url     : https://prove2.me/theorems/1299394f-f392-41c4-bec8-7151fb446e9b
-- title:
--   Adaptive probe trees: run, transcript and probe count
-- statement:
--   An **adaptive probe tree** with questions in $Q$, replies in $A$ and results in $R$ is a finite-depth decision procedure: an inner node asks one question $q\in Q$ and branches on the reply, and a leaf carries a result $r\in R$. Given an oracle $O:Q\to A$, the tree selects one path, and that path determines the **result**, the **transcript** (the list of question and reply pairs in order) and the **cost** (the number of probes along the path).
--
--   This is the form in which one update of a dynamic algorithm, or one block of queries, is processed: the number of oracle calls the procedure makes while processing it is the paper's query measure.
--
--   **Formalization Note** The type is inductive, so every path is finite and the procedure always halts. Nothing limits the memory used while walking the tree; only what the leaf returns can be carried on.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and §2, p.15

import Mathlib

namespace DynOracleConn

/-!
# Adaptive probe trees

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §1.1, p.4 and §2, p.15
("its queries, the number of oracle calls it makes while processing an update").

An algorithm that processes one update (or one block of queries) by asking an oracle questions is
an adaptive tree: each inner node asks one question `q : Q`, and the next step depends on the reply
`a : Ans`; each leaf carries the result. The number of probes along the path taken is the cost.

**Formalization Note.** The tree is an inductive type, so every path is finite: the procedure
always halts. Temporary memory used while walking the tree is not restricted; only what is
returned at the leaf can be carried on (see `DetAlg`).
-/

/-- An adaptive probe tree with questions in `Q`, replies in `Ans` and results in `R`:
`done r` returns `r`; `probe q k` asks `q` and continues with `k a` on reply `a`. -/
inductive ProbeTree (Q Ans R : Type) : Type where
  | done (r : R) : ProbeTree Q Ans R
  | probe (q : Q) (k : Ans → ProbeTree Q Ans R) : ProbeTree Q Ans R

namespace ProbeTree

variable {Q Ans R : Type}

/-- The result of the tree when the oracle answers question `q` by `O q`. -/
def run : ProbeTree Q Ans R → (Q → Ans) → R
  | done r, _ => r
  | probe q k, O => run (k (O q)) O

/-- The list of (question, reply) pairs along the path the oracle `O` selects, in order. -/
def transcript : ProbeTree Q Ans R → (Q → Ans) → List (Q × Ans)
  | done _, _ => []
  | probe q k, O => (q, O q) :: transcript (k (O q)) O

/-- The number of oracle probes along the path the oracle `O` selects. -/
def cost (t : ProbeTree Q Ans R) (O : Q → Ans) : ℕ := (t.transcript O).length

end ProbeTree

end DynOracleConn



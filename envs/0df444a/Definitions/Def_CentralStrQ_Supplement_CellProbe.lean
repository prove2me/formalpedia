-- Prove2me | Definitions.Def_CentralStrQ_Supplement_CellProbe
-- name    : CentralStrQ_Supplement_CellProbe
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:22:42.011017+00:00
-- url     : https://prove2.me/theorems/a797610f-66fd-4cc6-98c0-7e36ebda621c
-- title:
--   Deterministic static cell-probe data structures
-- statement:
--   In the **static cell-probe model** with cells of $b$ bits, a deterministic data structure for a family of inputs consists of a number $M$ of cells, a memory content for every input (cell $a$ holds a value in $[0\,.\,.\,2^b)$, computed by unrestricted preprocessing, and cells $a\ge M$ hold $0$), and for every query an adaptive probing strategy: a decision tree whose inner nodes probe a cell, the next node depending on the content read, and whose leaves output the answer. The data structure uses $Mb$ bits of space; its query time is the largest number of probes made, over all inputs and queries.
--
--   This is the model of Theorems 7.47–7.49, in which preprocessing is free and only probes are counted.
--
--   **Formalization Note** A probing strategy is the published adaptive probe tree `DynOracleConn.ProbeTree` with cell addresses as questions and cell contents as replies; its cost on a memory is the number of probes on the path actually followed (`ProbeTree.cost`). The cell size $b$ is a parameter, constrained by each statement.
-- source:
--   Kempa–Kociumaka, A Complete Characterization of Central String Queries in Compact Space, STOC 2027 submission (manuscript sha256 dea2f74f66f1bd686c8e3c6d4e11f36643253c3c86a04fc5faa1c3ac1c96f346), Theorems 7.47–7.49 and the proof of Theorem 7.47, pp.143–144 (pdf pp.144–145)

import Mathlib
import Definitions.Def_DynOracleConn_ProbeTree

set_option autoImplicit false

namespace CentralStrQ.Supplement

/-!
# The static cell-probe model

Kempa–Kociumaka, *A Complete Characterization of Central String Queries in Compact Space*,
STOC 2027 submission (manuscript sha256 dea2f74f…c96f346), Theorems 7.47–7.49, pp.143–144
(PDF pp.144–145): "In the static cell-probe model with Θ(log N)-bit cells, a deterministic data
structure … using S(σ, N) bits of space and Q(σ, N) probes per query"; proof of Theorem 7.47:
"Preprocessing computation is unrestricted in the static cell-probe model."

**Formalization Note.** A deterministic static cell-probe data structure with cells of `b` bits for
a family of inputs: a number `M` of cells; for every input `x` a memory `store x` (cell `a` holds a
value in `[0..2^b)`, and every cell `a ≥ M` holds `0`), computed by unrestricted preprocessing;
and for every query `q` an adaptive probing strategy `alg q`, a decision tree whose inner nodes
probe a cell (the child is chosen by the content read) and whose leaves give the answer: the
published `DynOracleConn.ProbeTree ℕ ℕ A` (questions = cell addresses, replies = cell contents),
run against the memory with `ProbeTree.run`, its probe count being `ProbeTree.cost`. The
space usage is `M · b` bits. The query cost on an input is the number of probes on the path that
the strategy actually follows; the query time is the worst case over inputs and queries. The
cell size `b` is a parameter; "Θ(log N)-bit cells" is imposed by each statement.
-/

/-- A deterministic static cell-probe data structure with `b`-bit cells for the inputs `inputs`,
the queries `queries x` on input `x`, and answers `ans`, using at most `S` bits of space and at
most `t` probes per query. -/
def CellProbeDS {I Q A : Type} (inputs : Set I) (queries : I → Set Q) (ans : I → Q → A)
    (b : ℕ) (S t : ℝ) : Prop :=
  ∃ (M : ℕ) (store : I → ℕ → ℕ) (alg : Q → DynOracleConn.ProbeTree ℕ ℕ A),
    ((M : ℝ) * b ≤ S) ∧
    (∀ x ∈ inputs, ∀ a : ℕ, store x a < 2 ^ b ∧ (M ≤ a → store x a = 0)) ∧
    ∀ x ∈ inputs, ∀ q ∈ queries x,
      (alg q).run (store x) = ans x q ∧ (((alg q).cost (store x) : ℕ) : ℝ) ≤ t

end CentralStrQ.Supplement



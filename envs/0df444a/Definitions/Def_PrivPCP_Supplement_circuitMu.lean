-- Prove2me | Definitions.Def_PrivPCP_Supplement_circuitMu
-- name    : PrivPCP_Supplement_circuitMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:54:37.419217+00:00
-- url     : https://prove2.me/theorems/84dbc1a3-b62d-4b84-80ea-f200e2a06c5b
-- title:
--   The measure $\mu$ on transcript coordinates induced by the query procedure $V_C$ (§6.3)
-- statement:
--   For a circuit $C$ with $L$ layers and a tester $T$, the **query procedure** $V_C$ does one of three things, each with probability $1/3$:
--   1. it queries the final output;
--   2. it chooses one of the $L$ layers uniformly, then a computation gate of that layer uniformly, and queries the gate's inputs and output;
--   3. it runs the tester $T$.
--
--   For a random choice $r$ of $V_C$ with probability $p(r)$ and nonempty queried set $Q(r)$ of transcript coordinates, $\mu$ is the law of a uniformly random coordinate of $Q(r)$:
--   $$
--   \mu(U)=\sum_r p(r)\,\frac{|U\cap Q(r)|}{|Q(r)|}.
--   $$
--   Joint privacy under $\mu$ (Definition 5.3(2b)) asks that every set $U$ of transcript coordinates of small $\mu$-measure has a law independent of the input.
--
--   **Formalization Note** Defined for every circuit–tester pair. A layer without gates, or a tester entry that queries nothing, contributes $0$; for the circuit of §5.3 every queried set is nonempty.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), §6.3, p.39 (PDF p.41)

import Mathlib
import Definitions.Def_PrivPCP_Supplement_LTester

set_option autoImplicit false

namespace PrivPCP.Supplement

open Classical

/-- The set of transcript coordinates read when gate `o` is queried: its input wires and its output. -/
noncomputable def gateQuery (C : LCircuit) (o : C.OutIdx) : Finset C.Coord :=
  insert (C.outC o) ((C.gate o).ins.filterMap (C.blockCoord o.1)).toFinset

/-- The set of transcript coordinates an entry of the tester queries. -/
noncomputable def testQuery (C : LCircuit) (e : TestEntry) : Finset C.Coord :=
  (e.queries.filterMap (LTester.queryCoord C)).toFinset

/-- The **measure `µ` on transcript coordinates induced by the query procedure `V_C`** (Bafna, Vyas,
*Private PCPs from Product Expansion*, STOC 2027 submission manuscript (sha256 c2cac1e0…), §6.3,
p.39): with probability `1/3`, `V_C` queries the final output; with probability `1/3`, it chooses one
of the `L` layers uniformly, then a computation gate of that layer uniformly, and queries its inputs
and output; with probability `1/3`, it runs the tester `T`. For a random choice `r` of `V_C` with
queried set `Q(r)` and probability `p(r)`, `µ` is the law of a uniformly random coordinate of `Q(r)`:
`µ(U) = ∑_r p(r) |U ∩ Q(r)| / |Q(r)|`.

**Formalization Note** Defined for every circuit–tester pair. A layer without gates, or a tester entry
that queries nothing, contributes `0` (Lean's `x / 0 = 0`); for the circuits of §5.3 every queried set
is nonempty. -/
noncomputable def circuitMu (C : LCircuit) (T : LTester) (U : Set C.Coord) : ℝ :=
  (1 / 3 : ℝ) * (match C.finalCoord with
    | some c => if c ∈ U then 1 else 0
    | none => 0) +
  (1 / 3 : ℝ) * ((1 : ℝ) / C.L) * ∑ ℓ : Fin C.L, ((1 : ℝ) / (C.layer ℓ).gates.length) *
    ∑ j : Fin (C.layer ℓ).gates.length,
      (((gateQuery C ⟨ℓ, j⟩).filter (· ∈ U)).card : ℝ) / (gateQuery C ⟨ℓ, j⟩).card +
  (1 / 3 : ℝ) * (T.tests.map fun e =>
    ((e.weight : ℝ) / T.totalWeight) *
      ((((testQuery C e).filter (· ∈ U)).card : ℝ) / (testQuery C e).card)).sum

end PrivPCP.Supplement



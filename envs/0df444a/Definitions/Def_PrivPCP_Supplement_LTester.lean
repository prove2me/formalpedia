-- Prove2me | Definitions.Def_PrivPCP_Supplement_LTester
-- name    : PrivPCP_Supplement_LTester
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:53:15.613221+00:00
-- url     : https://prove2.me/theorems/30ee3766-c0d5-4b81-affb-94a51021d877
-- title:
--   Randomized local testers of a circuit and their rejection probability (Definition 5.3)
-- statement:
--   A **randomized local tester** $T$ of a circuit has oracle access to the input wires and to the computation-output wires of all layers. It is a finite list of entries, one for each fixing of its randomness; an entry has a nonnegative integer **weight**, a list of queried wires and a decision program. The tester picks an entry with probability proportional to its weight, independently of the circuit's words and of the faulty gates, queries its wires, and accepts or rejects as its decision program says.
--
--   For a fixed execution (transcript) $t$,
--   $$
--   \Pr[T\text{ rejects}]=\frac{\sum_{\text{rejecting entries } e} \mathrm{weight}(e)}{\sum_e \mathrm{weight}(e)}.
--   $$
--   A tester is well formed when its total weight is positive and every queried wire exists. Its description lists every entry.
--
--   **Formalization Note** The tester is nonadaptive: each fixing of the randomness fixes the queried wires. The tester of §5.3 (p.33) is of this form, its rational probabilities written as integer weights.
-- source:
--   Bafna, Vyas, Private PCPs from Product Expansion, STOC 2027 submission manuscript (sha256 c2cac1e07fc4af8721f673867373fc5bd417aa65f45cf170c543568abcf1e47e), Definition 5.3, p.27 (PDF p.29)

import Mathlib
import Definitions.Def_PrivPCP_Supplement_LCircuit

set_option autoImplicit false

open QAlgorithms.Complexity QAdvFew.PoQOracle ZKSheafPCP

namespace PrivPCP.Supplement

/-- One fixing of the tester's randomness: its weight (the probability of this fixing is its weight
divided by the total weight), the wires it queries, and the local program deciding acceptance from
the queried values. A queried wire `(0, j)` is input position `j`; `(1, ℓ, j)`, written `(1, (ℓ, j))`,
is the output of gate `j` of layer `ℓ`. -/
structure TestEntry where
  /-- the weight of this fixing of the randomness -/
  weight : ℕ
  /-- the queried wires, in order -/
  queries : List (Fin 2 × ℕ × ℕ)
  /-- the decision -/
  check : LocalProg

/-- A **randomized local tester** (Bafna, Vyas, *Private PCPs from Product Expansion*, STOC 2027
submission manuscript (sha256 c2cac1e0…), Definition 5.3, p.27): it has oracle access to the input
and computation-output wires of all layers, picks one of its entries with probability proportional to
its weight (fresh randomness, independent of the circuit's words and of the faulty gates), queries
that entry's wires, and accepts or rejects.

**Formalization Note** The tester is nonadaptive: for each fixing of its randomness, the queried
wires are fixed in advance. The tester of §5.3 (p.33) is of this form, with rational probabilities
written as integer weights. -/
structure LTester where
  /-- the fixings of the randomness -/
  tests : List TestEntry

namespace LTester

variable (C : LCircuit) (T : LTester)

/-- The transcript coordinate of a queried wire, if it exists: an input wire or a
computation-output wire. -/
def queryCoord (w : Fin 2 × ℕ × ℕ) : Option C.Coord :=
  if w.1 = 0 then
    (if h : w.2.2 < C.N0 then some (Sum.inl ⟨w.2.2, h⟩) else none)
  else if hℓ : w.2.1 < C.L then
    (if h : w.2.2 < (C.layer ⟨w.2.1, hℓ⟩).gates.length then
      some (C.outC ⟨⟨w.2.1, hℓ⟩, ⟨w.2.2, h⟩⟩) else none)
  else none

/-- The total weight. -/
def totalWeight : ℕ := (T.tests.map TestEntry.weight).sum

/-- Entry `e` accepts the transcript `t`. -/
def EntryAccepts {q : ℕ} (e : TestEntry) (t : C.Coord → ZMod q) : Prop :=
  e.check.Accepts (e.queries.map fun w =>
    match queryCoord C w with
    | some c => t c
    | none => 0)

open Classical in
/-- The **rejection probability** `Pr[T rejects]` on a fixed execution `t`: the total weight of the
rejecting entries divided by the total weight. -/
noncomputable def rejProb {q : ℕ} (t : C.Coord → ZMod q) : ℝ :=
  ((T.tests.map fun e => if EntryAccepts C e t then 0 else e.weight).sum : ℝ) / T.totalWeight

/-- **Well-formedness**: the total weight is positive and every queried wire exists. -/
def WF : Prop :=
  0 < T.totalWeight ∧ ∀ e ∈ T.tests, ∀ w ∈ e.queries, (queryCoord C w).isSome

/-- The **description** of a tester: every entry with its weight, its queried wires and its
decision program. -/
def code : Str :=
  tup (T.tests.map fun e =>
    tup [binN e.weight, tup (e.queries.map fun w => tup [binN w.1.val, binN w.2.1, binN w.2.2]),
      e.check.code])

end LTester

end PrivPCP.Supplement



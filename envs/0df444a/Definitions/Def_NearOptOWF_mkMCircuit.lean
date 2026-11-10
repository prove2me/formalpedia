-- Prove2me | Definitions.Def_NearOptOWF_mkMCircuit
-- name    : NearOptOWF_mkMCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:23.96465+00:00
-- url     : https://prove2.me/theorems/32e57989-cb04-4781-a6af-82cf8b77aaa6
-- title:
--   Building a multi-output circuit from a gate list
-- statement:
--   A helper that turns a list of gates and a list of output wires into a multi-output circuit with $n$ inputs. A gate that reads a wire not yet defined is replaced by the constant $0$, and output wires that do not exist are dropped. On a well-formed gate list nothing is changed. It is used only to write circuit composition without proof obligations.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16) (construction helper for $G \circ H$)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- The multi-output circuit with `n` inputs built from a gate list `gs` and output wires `outs`
(a construction helper for circuit composition, Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4.2, p.14 (PDF p.16): the circuit `G ∘ H`):
a gate that reads a wire not yet defined is replaced by the constant `0`, and output wires that do not
exist are dropped.

**Formalization Note** On a well-formed gate list (gate `g` reads only wires `< n + g`) and existing
output wires, nothing is replaced, and the circuit is exactly `(gs, outs)`. The repair only makes
the construction total. -/
def mkMCircuit (n : ℕ) (gs : List KarpLiptonOM.Gate) (outs : List ℕ) : MCircuit n where
  base :=
    { gates := gs.mapIdx fun g gt =>
        if ∀ i ∈ gt.refs, i < n + g then gt else KarpLiptonOM.Gate.const false
      wf := by
        intro g hg i hi
        simp only [List.getElem_mapIdx] at hi
        split_ifs at hi with h
        · exact h i hi
        · simp [KarpLiptonOM.Gate.refs] at hi }
  outs := outs.filter fun i => decide (i < n + gs.length)
  outs_wf := by
    intro i hi
    simp only [List.mem_filter, decide_eq_true_eq] at hi
    simpa [List.length_mapIdx] using hi.2

end NearOptOWF



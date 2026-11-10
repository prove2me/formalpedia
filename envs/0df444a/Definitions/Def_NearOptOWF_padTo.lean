-- Prove2me | Definitions.Def_NearOptOWF_padTo
-- name    : NearOptOWF_padTo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:26.181053+00:00
-- url     : https://prove2.me/theorems/6aefce5b-986b-4e45-95bc-e655226729d8
-- title:
--   Padding a circuit with dummy gates to size $S$
-- statement:
--   For a circuit $C$ and a size $S$, $\mathrm{pad}_S(C)$ is $C$ with $S - |C|$ constant gates appended that no wire reads (none when $|C| \ge S$). It computes the same function as $C$ and has size $\max(S, |C|)$.
--
--   The paper pads every obfuscated circuit of its construction "with sufficiently many dummy gates so that the size of this obfuscated circuit matches other obfuscated circuits later in our proof" (pp.11–12). Indistinguishability obfuscation only hides circuits of equal size, so this padding is what makes the obfuscations comparable.
--
--   **Formalization Note** The size of a multi-output circuit is its number of gates plus its number of output wires.
-- source:
--   Ilango–Lombardi–Tu, Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4, pp.11–12 (PDF pp.13–14)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit

namespace NearOptOWF

open LaconicBarrier

/-- `C` **padded with dummy gates** to size `max S |C|` (Ilango–Lombardi–Tu, *Near-Optimal One-Way Functions, Direct Product Hardness and Hash Functions from iO and NP versus coNP*, STOC 2027 submission (manuscript of 2026-11-03, sha256 91ede246…), §4, pp.11–12 (PDF pp.13–14): "We
will also pad F with sufficiently many dummy gates so that the size of this obfuscated circuit
matches other obfuscated circuits later in our proof"): `S − |C|` constant gates that no wire reads
are appended; the output wires are unchanged, so the padded circuit computes the same function.

**Formalization Note** The size is `MCircuit.size` (gates plus output wires). The paper fixes no
padding procedure; any one that keeps the function and reaches a common size serves. -/
def padTo {n : ℕ} (S : ℕ) (C : MCircuit n) : MCircuit n where
  base :=
    { gates := C.base.gates ++ List.replicate (S - C.size) (KarpLiptonOM.Gate.const false)
      wf := by
        intro g hg i hi
        by_cases h : g < C.base.gates.length
        · rw [List.getElem_append_left h] at hi
          exact C.base.wf g h i hi
        · rw [List.getElem_append_right (by omega)] at hi
          simp [KarpLiptonOM.Gate.refs] at hi }
  outs := C.outs
  outs_wf := by
    intro i hi
    have := C.outs_wf i hi
    simp only [List.length_append]
    omega

end NearOptOWF



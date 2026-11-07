-- Prove2me | Definitions.Def_ReplicableOL_modeDefect
-- name    : ReplicableOL_modeDefect
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:43:37.201236+00:00
-- url     : https://prove2.me/theorems/690692ea-55ce-4f3a-a100-fd7817d9cf00
-- title:
--   Mode deviation $\varepsilon_F(Q,r)$
-- statement:
--   For a finite set $Z$, a map $F(S,r)\in Z$ and a law $Q$ of $S$, the **mode deviation** is $\varepsilon_F(Q,r)=1-\max_z\mathbb P_{S\sim Q}[F(S,r)=z]$: the probability that $F$ misses its most likely output at seed $r$.
--
--   **Formalization Note** `X` is the data space and `Z` is a finite nonempty output set; probabilities are read in `ℝ` through `toReal`.
-- source:
--   Lu, Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability, STOC 2027 submission (held version, sha256 71ae0088…bbc2aa), Sec. 2.3, p.8

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ReplicableOL

/-- **Mode deviation $\varepsilon_F(Q,r)$.** Lu, *Replicable Online Learners Must Gamble: The Typical-Case Price of Replicability*, STOC 2027 submission (held version), Sec. 2.3, p.8. `ε_F(Q, r) := 1 − max_z P_{S∼Q}[F(S, r) = z]`.

**Formalization Note.** `X` is the data space and `Z` is a finite nonempty output set; probabilities are read in `ℝ` through `toReal`. -/
noncomputable def modeDefect {X Z R : Type*} [MeasurableSpace X] [Fintype Z] [Nonempty Z]
    (F : X → R → Z) (Q : Measure X) (r : R) : ℝ :=
  1 - Finset.univ.sup' Finset.univ_nonempty (fun z => (Q {S | F S r = z}).toReal)

end ReplicableOL



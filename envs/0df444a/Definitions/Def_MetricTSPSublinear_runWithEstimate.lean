-- Prove2me | Definitions.Def_MetricTSPSublinear_runWithEstimate
-- name    : MetricTSPSublinear_runWithEstimate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:24:35.757575+00:00
-- url     : https://prove2.me/theorems/44bacd39-84d9-481b-af38-3b65f778bfa4
-- title:
--   Runs of the distance-oracle machine given an MST estimate $\widehat M$
-- statement:
--   The paper's algorithm of Section 9 receives an estimate $\widehat M$ of the MST weight with $M\le\widehat M\le(1+O(\varepsilon))M$. A run of a program $P$ given $\widehat M$ is the run of the published distance-oracle real RAM with fair coins (`SublinearSteiner`): the start state holds $n$ in integer memory, as the published input layout with every point a terminal, and in addition $\widehat M$ in real memory cell $0$. Every other aspect of the machine (instructions, query and work counters, coin tape) is the published one.
--
--   **Formalization Note.** The published `SublinearSteiner.run` starts with real memory $0$; `runWithEstimate` iterates the published step function from the modified start state `initWithEstimate`.
-- source:
--   A. Azarmehr, S. Behnezhad, Metric TSP in Sublinear Time: Breaking Two Approximation, arXiv:2611.04283 (held version, sha256 a86ea2397da2e82c8f8baada200e333f32a133395de02943b1fce22946e4a745), https://arxiv.org/abs/2611.04283, §3, p.9 (PDF p.11); Lemma 9.1, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_SublinearSteiner_Machine

namespace MetricTSPSublinear

/-- The start state on the instance `Fin n` with the real `Mhat` in real memory cell `0`: the published
`SublinearSteiner.initState` with terminal set `Finset.univ` (integer memory `I 0 = n`, `I (1 + v) = 1` for every
point `v`), otherwise unchanged. -/
noncomputable def initWithEstimate (n : ℕ) (Mhat : ℝ) : SublinearSteiner.State :=
  let s := SublinearSteiner.initState (Finset.univ : Finset (Fin n))
  { s with cfg := { s.cfg with mem := Function.update s.cfg.mem 0 Mhat } }

/-- **A run of the distance-oracle machine that is given the MST estimate `M̂`.**
Azarmehr, Behnezhad, *Metric TSP in Sublinear Time: Breaking Two Approximation*, arXiv:2611.04283 (held version,
sha256 a86ea239…), §3, p.9 (PDF p.11): "Throughout the paper, we assume access to an estimation M̂ satisfying:
M ≤ M̂ ≤ (1 + O(ε))M"; Lemma 9.1, p.33 (PDF p.35).

`runWithEstimate P w Mhat tape t` is the state after `t` steps of the published machine
(`SublinearSteiner.step`, the distance-oracle real RAM with fair coins) on the metric `w` and the tape, started from
`initWithEstimate n Mhat`.

**Formalization Note.** The published `SublinearSteiner.run` starts with real memory `0`; this run differs only in
the start state, which also holds `M̂`. The step function, the cost counters and the tape convention (a `B`-bit tape
extended by `false`) are the published ones. -/
noncomputable def runWithEstimate (P : SublinearSteiner.Program) {n : ℕ} (w : Fin n → Fin n → ℝ) (Mhat : ℝ)
    {B : ℕ} (tape : Fin B → Bool) (t : ℕ) : SublinearSteiner.State :=
  (SublinearSteiner.step P w (SublinearSteiner.extendTape tape))^[t] (initWithEstimate n Mhat)

end MetricTSPSublinear



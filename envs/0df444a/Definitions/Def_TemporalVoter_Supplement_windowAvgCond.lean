-- Prove2me | Definitions.Def_TemporalVoter_Supplement_windowAvgCond
-- name    : TemporalVoter_Supplement_windowAvgCond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:32:08.433544+00:00
-- url     : https://prove2.me/theorems/49a9de15-689a-44f4-8693-ce076a656566
-- title:
--   Window-averaged conductance condition $\frac1{|I|}\sum_{t\in I}\phi^t(S)\ge\phi$ over all windows of length $L$
-- statement:
--   Let $\mathcal G=(G_t)_{t\ge0}$ be a temporal graph with fixed degrees on a finite vertex set $V$, with volume $\mathrm{Vol}$, $m$ edges, and set conductances $\phi^t(S)=e_t(S,\overline S)/\mathrm{Vol}(S)$. For a window length $L\in\mathbb N$ and a threshold $\phi\in\mathbb R$, $\mathcal G$ satisfies the **window-averaged conductance condition** with parameters $(L,\phi)$ if, for every time interval $I=\{a,a+1,\dots,a+L-1\}$ with $a\in\mathbb N$ and every set $S\subseteq V$ with $0<\mathrm{Vol}(S)\le m$,
--   $$
--   \frac{1}{|I|}\sum_{t\in I}\phi^t(S)\;\ge\;\phi .
--   $$
--
--   The interval conductance $\phi^{I}(S)$ of the mission takes the *maximum* of $\phi^t(S)$ over $I$; this condition asks for a large *average*, which is a stronger requirement on the graph. It is the hypothesis of the paper's lower bounds (Theorem 1.4(i) and Theorem 4.7(ii)), which show that even this stronger notion does not remove the dependence of the consensus time on the window length.
--
--   **Formalization Note** The interval is `Finset.Ico a (a + L)` and $|I|=L$; $\phi^t(S)$ is the published `condAt`. Theorem 4.7(ii) writes the volume bound as $\mathrm{Vol}(S)\le\mathrm{Vol}(V)/2$, which is $m$ by definition. With $L=0$ the average is $0$; every theorem using the condition has $L\ge1$ at all large indices.
-- source:
--   Rocha Avila, Dell, Lapinskas, Temporal Conductance and Bounds on the Voter Model for Dynamic Networks, arXiv:2606.13374 (2 Nov 2026), Theorem 1.4(i), p.7; Theorem 4.7(ii), p.32

import Mathlib
import Definitions.Def_TemporalVoter_temporalConductance

open scoped Classical

namespace TemporalVoter

namespace Supplement

variable {V : Type} [Fintype V]

/-- **Window-averaged conductance condition** (Rocha Avila, Dell, Lapinskas, *Temporal Conductance
and Bounds on the Voter Model for Dynamic Networks*, arXiv:2606.13374, version of 2 Nov 2026,
Theorem 1.4(i), p.7, and Theorem 4.7(ii), p.32): for every time interval `I = {a, …, a + L − 1}`
of length `L` and every vertex set `S` with `0 < Vol(S) ≤ m`,
`(1/|I|) ∑_{t ∈ I} φ^t(S) ≥ φ`.

**Formalization Note** Intervals of `ℕ` of length `L` are `Finset.Ico a (a + L)`, `a : ℕ`, and
`|I| = L`. `φ^t(S)` is the published `condAt`. Theorem 4.7(ii) writes the volume bound as
`Vol(S) ≤ Vol(V)/2`, which equals `m` by definition. Every theorem using this condition has
`L ≥ 1` for all large indices. -/
def windowAvgCond (T : TemporalGraph V) (L : ℕ) (φ : ℝ) : Prop :=
  ∀ a : ℕ, ∀ S : Finset V, 0 < T.vol S → T.vol S ≤ T.m →
    φ ≤ (1 / (L : ℝ)) * ∑ t ∈ Finset.Ico a (a + L), condAt T t S

end Supplement

end TemporalVoter



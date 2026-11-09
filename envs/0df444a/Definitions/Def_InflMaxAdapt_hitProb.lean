-- Prove2me | Definitions.Def_InflMaxAdapt_hitProb
-- name    : InflMaxAdapt_hitProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:30.510202+00:00
-- url     : https://prove2.me/theorems/154e8ad4-94b7-439a-8a24-b5ed4b6b56fd
-- title:
--   Activation probability $\mathbb P(u \leftrightarrow S(\pi))$
-- statement:
--   For an adaptive policy $\pi$ and a vertex $u$, $\mathbb P(u \leftrightarrow S(\pi))$ is the probability that $u$ is connected to some seed probed by $\pi$, that is, that $\pi$ activates $u$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_ConnSet
import Definitions.Def_InflMaxAdapt_edgeCascade
import Definitions.Def_InflMaxAdapt_Policy_seeds

open MeasureTheory

namespace InflMaxAdapt

/-- `P(u ↔ S(π))`, the probability that a policy activates the vertex `u` (Lemma 4, printed
p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), in the undirected-edge representation. -/
noncomputable def hitProb {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (q : Sym2 V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) (u : V) : ℝ :=
  ∫ ω, edgeProb q (fun E => ConnSet E u (π.seeds ω (fun w => edgeCascade E {w}))) ∂μ

end InflMaxAdapt



-- Prove2me | Definitions.Def_InflMaxAdapt_seedProb
-- name    : InflMaxAdapt_seedProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:35:04.602271+00:00
-- url     : https://prove2.me/theorems/f688b386-bdff-4950-bf23-837ed56a2799
-- title:
--   Seed probability $x_v = \mathbb P(v \in S(\pi))$
-- statement:
--   Given an adaptive policy $\pi$, the **seed probability** of a vertex $v$ is
--   $$
--   x_v \;=\; \mathbb P\big(v \in S(\pi)\big),
--   $$
--   the probability over the live edges and the external randomness that $\pi$ probes $v$. The vector $\mathbf x = (x_v)_{v \in V}$ satisfies $\sum_v x_v \le k$ for a policy with budget $k$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), Section 2, printed p.5 (PDF p.6)

import Mathlib
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_edgeCascade
import Definitions.Def_InflMaxAdapt_Policy_seeds

open MeasureTheory

namespace InflMaxAdapt

/-- The seed probability `x_v = P(v ∈ S(π))` of a vertex under an adaptive policy
(Section 2, printed p.5 = PDF p.6, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), in the undirected-edge representation: the probability
over the live edges and over `ω ∼ μ`. -/
noncomputable def seedProb {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (q : Sym2 V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) (v : V) : ℝ :=
  ∫ ω, edgeProb q (fun E => v ∈ π.seeds ω (fun w => edgeCascade E {w})) ∂μ

end InflMaxAdapt



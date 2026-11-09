-- Prove2me | Definitions.Def_InflMaxAdapt_activProb
-- name    : InflMaxAdapt_activProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:09.648215+00:00
-- url     : https://prove2.me/theorems/7836fa6c-5a24-4a49-bef8-4a1367a696a0
-- title:
--   Contribution $\mathbb P(v \text{ activates } u)$
-- statement:
--   The **contribution** of a seed $v$ to the activation of a vertex $u$ under an adaptive policy $\pi$ is the probability $\mathbb P(v \text{ activates } u)$ that $v$ is probed by $\pi$ and activates $u$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_Activates
import Definitions.Def_InflMaxAdapt_edgeProb

open MeasureTheory

namespace InflMaxAdapt

/-- `P(v activates u)`, the contribution of the seed `v` to the activation of `u` (proof of
Lemma 4, printed p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)). -/
noncomputable def activProb {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (q : Sym2 V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) (v u : V) : ℝ :=
  ∫ ω, edgeProb q (fun E => Activates E ω π v u) ∂μ

end InflMaxAdapt



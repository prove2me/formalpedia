-- Prove2me | Definitions.Def_InflMaxAdapt_excess
-- name    : InflMaxAdapt_excess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:03.005725+00:00
-- url     : https://prove2.me/theorems/9fa8c1c7-bf67-45b8-81a6-70f3a451f9de
-- title:
--   Excess $e(v)$ of a seed
-- statement:
--   Fix a vertex $u$ and a set $S \subseteq V$. For an adaptive policy $\pi$ with seed probabilities $\mathbf x$, the **excess** of a seed $v$ is
--   $$
--   e(v) \;:=\; \big(\mathbb P(v \text{ activates } u) - 2 x_v\, \mathbb P(u \leftrightarrow v,\ u \not\leftrightarrow S)\big)_+ ,
--   $$
--   where $y_+ = \max(y, 0)$. It measures how much the contribution of $v$ exceeds twice the marginal increase $\mathbb P(u \leftrightarrow v,\ u \not\leftrightarrow S)$ of the activation probability of $u$ when $v$ is added to $S$, weighted by $x_v$.
-- source:
--   de Azevedo–Hennebelle, Adaptivity Gaps for Influence Maximization: Percolation and Depletion, STOC 2027 submission (manuscript sha256 67dfe75c…abe5d5), proof of Lemma 4, printed p.6 (PDF p.7)

import Mathlib
import Definitions.Def_InflMaxAdapt_activProb
import Definitions.Def_InflMaxAdapt_seedProb
import Definitions.Def_InflMaxAdapt_edgeProb
import Definitions.Def_InflMaxAdapt_Conn
import Definitions.Def_InflMaxAdapt_ConnSet

open MeasureTheory

namespace InflMaxAdapt

/-- The excess of a seed (proof of Lemma 4, printed p.6 = PDF p.7, of de Azevedo–Hennebelle, *Adaptivity Gaps for Influence Maximization: Percolation and Depletion*, STOC 2027 submission manuscript (sha256 67dfe75c…abe5d5)), for a fixed
vertex `u` and set `S`: `e(v) := (P(v activates u) − 2 x_v P(u ↔ v, u ↮ S))_+`, with `y_+ = max(y, 0)`. -/
noncomputable def excess {V : Type} [Fintype V] [DecidableEq V] {k : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (q : Sym2 V → ℝ) (μ : Measure Ω) (π : Policy V k Ω) (u : V) (S : Finset V) (v : V) : ℝ :=
  max (activProb q μ π v u - 2 * seedProb q μ π v *
    edgeProb q (fun E => Conn E u v ∧ ¬ ConnSet E u S)) 0

end InflMaxAdapt



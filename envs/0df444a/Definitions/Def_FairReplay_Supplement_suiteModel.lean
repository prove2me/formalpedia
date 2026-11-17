-- Prove2me | Definitions.Def_FairReplay_Supplement_suiteModel
-- name    : FairReplay_Supplement_suiteModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:46:28.549777+00:00
-- url     : https://prove2.me/theorems/422e9286-316b-48e1-b4ec-548cded1ce84
-- title:
--   Synchronized suite-replay model
-- statement:
--   Let $H$ be a residual graph. In the **suite family**, every active vertex has old threshold $p$ and, under the null, new threshold $p+s$; under the alternative for $x\in V_+(H)$, the vertex $x$ instead has new threshold $p+s+d$. A **raw suite round** draws one tape $U\sim\mathrm{Unif}[0,1]$ and reveals $(P_0(v;U),P_1(v;U))$ for every active vertex $v$; rounds use independent tapes. One round costs $2n_+$ concrete executions.
--
--   **Formalization Note** One action; the observation is the coded vector indexed by (vertex, version), with constant entries at inactive vertices.
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.6, pp.16–17 (PDF pp.18–19)

import Mathlib
import Definitions.Def_BanditTrajectory
import Definitions.Def_FairReplay_thresholdOut
import Definitions.Def_FairReplay_uniformTape
import Definitions.Def_FairReplay_obsCode
import Definitions.Def_FairReplay_Supplement_activeVertices

open MeasureTheory

namespace FairReplay.Supplement

/-- The ordered raw outputs of one synchronized suite-replay round on the tape value `U`: for each
vertex `v` and version `j ∈ {0, 1}` (coordinate `finProdFinEquiv (v, j)`), the output `Pj(v;U)` if
`v` is active, and the constant `false` if `v` is inactive (inactive vertices are not executed).
Old thresholds are `p`; the new threshold is `p + s`, plus `d` at the vertex `x` when `alt = some x`. -/
noncomputable def suiteObs {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p s d : ℝ)
    (alt : Option (Fin n)) (U : ℝ) : Fin (n * 2) → Bool := fun j =>
  if (finProdFinEquiv.symm j).1 ∈ activeVertices H then
    (if (finProdFinEquiv.symm j).2 = 0 then thresholdOut p U
      else thresholdOut (p + s + (if alt = some (finProdFinEquiv.symm j).1 then d else 0)) U)
  else false

lemma measurable_suiteObs {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p s d : ℝ)
    (alt : Option (Fin n)) : Measurable (fun U : ℝ => suiteObs H p s d alt U) := by
  rw [measurable_pi_iff]
  intro j
  simp only [suiteObs]
  split_ifs <;> first | exact measurable_thresholdOut _ | exact measurable_const

/-- The law of the coded observation of one suite round: the image of the uniform tape under
`U ↦ obsCode (suiteObs H p s d alt U)`. -/
noncomputable def suiteLaw {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p s d : ℝ)
    (alt : Option (Fin n)) : Measure ℝ :=
  uniformTape.map (fun U => obsCode (suiteObs H p s d alt U))

instance suiteLaw.instIsProbabilityMeasure {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (p s d : ℝ) (alt : Option (Fin n)) : IsProbabilityMeasure (suiteLaw H p s d alt) :=
  Measure.isProbabilityMeasure_map
    (measurable_obsCode.comp (measurable_suiteObs H p s d alt)).aemeasurable

/-- **Synchronized suite-replay model** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software
under Uncertainty*, STOC 2027 submission, manuscript of 2026-11-03, sha256 e23940a0…, Theorem 10.6,
p.16 (PDF p.18)): "Under the null, every active vertex has old threshold p and new threshold p + s;
under an alternative, exactly one endpoint of an active edge has new threshold p + s + d. A raw
suite round reveals both version outputs at every active vertex under one common tape."

`suiteModel H p s d alt` is the sequential-sampling environment with one action, the suite round,
observing the coded vector of all old and new outputs at the active vertices `V+(H)` on one uniform
tape. `alt = none` is the null; `alt = some x` is the alternative in which `x` has new threshold
`p + s + d`.

**Formalization Note** Alternatives are meaningful for `x ∈ V+(H)`; the theorems quantify over
those. Inactive coordinates of the observation vector are constant, so they carry no information.
One round executes both versions at the `|V+(H)|` active vertices (concrete cost `2 n+`). -/
noncomputable def suiteModel {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (p s d : ℝ)
    (alt : Option (Fin n)) : BanditAlgorithm.StochasticBandit 1 where
  P _ := suiteLaw H p s d alt
  prob _ := inferInstance

end FairReplay.Supplement



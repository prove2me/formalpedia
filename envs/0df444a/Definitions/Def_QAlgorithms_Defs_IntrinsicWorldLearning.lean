-- Prove2me | Definitions.Def_QAlgorithms_Defs_IntrinsicWorldLearning
-- name    : QAlgorithms_Defs_IntrinsicWorldLearning
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:15.210057+00:00
-- url     : https://prove2.me/theorems/4d376ff3-534e-49b5-a27e-3d2a0e0046ba
-- title:
--   IntrinsicWorldLearning
-- statement:
--   IntrinsicWorldLearning
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\IntrinsicWorldLearning.lean

import Definitions.Def_QAlgorithms_Defs_ChannelDiamondNorm
import Definitions.Def_QAlgorithms_Defs_WorldModelExperiments
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.IntrinsicLearning

/-- Raw state/effect matrices and complex-linear channel reports, without positivity,
trace, channel or accuracy constraints (2204.13691 p.20, C.5 and pp.31-33, D.6-D.7). -/
structure Description (d : ℕ) (X Y Z B : Type) where
  states : X → Matrix (Fin d) (Fin d) ℂ
  channels : Y → Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ
  effects : Z → B → Matrix (Fin d) (Fin d) ℂ

/-- Stabilized unhalved error between a true CPTP channel and a common-gauge linear report.
Both maps are linear, hence the unit trace-norm ball has bounded image
(2204.13691 p.20, C.5). -/
def channelError {d : ℕ} {X Y Z B : Type} [Fintype B]
    (W : WorldModel d X Y Z B) (D : Description d X Y Z B) (G : Gauge d) (y : Y) : ℝ :=
  sSup {v | ∃ X : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ, traceNorm X ≤ 1 ∧
    v = traceNorm (idTensorSuperop (R := Fin d)
      (fun M => W.channel y M-G.apply (D.channels y (gaugeInverse G M))) X)}

/-- A single public staged learner, eventual marginal accuracy for every candidate world,
and one common gauge outside all probability clauses. The stage threshold may depend on the
world; there is no uniform finite sample bound (2204.13691 pp.20-21, C.5, D.1; p.23, D.2). -/
def IsIntrinsicallyLearnable {d : ℕ} {X Y Z B : Type}
    [Fintype X] [Fintype Y] [Fintype Z] [Fintype B]
    (Q : Set (WorldModel d X Y Z B)) : Prop :=
  ∃ learner : ℕ → ExperimentProgram X Y Z B (Description d X Y Z B),
    ∀ W ∈ Q, ∀ eps delta : ℝ, 0 < eps → 0 < delta → delta < 1 →
    ∃ k0 : ℕ, ∀ k ≥ k0, ∃ G : Gauge d,
      (∀ x, programEventLaw W
        (fun D => traceNorm (W.rho x-G.apply (D.states x)) ≤ eps) (learner k) ≥ 1-delta) ∧
      (∀ y, programEventLaw W
        (fun D => channelError W D G y ≤ eps) (learner k) ≥ 1-delta) ∧
      ∀ z b, programEventLaw W
        (fun D => traceNorm (W.measurement z b-G.apply (D.effects z b)) ≤ eps) (learner k) ≥ 1-delta

example {d : ℕ} {X Y Z B : Type} [Fintype B] (W : WorldModel d X Y Z B) (a : Description d X Y Z B) :
    programEventLaw W (fun _ => True)
      (.output a : ExperimentProgram X Y Z B (Description d X Y Z B)) = 1 := by
  simp [programEventLaw]

end QAlgorithms.IntrinsicLearning



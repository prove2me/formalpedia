-- Prove2me | Definitions.Def_QMCLeafB_gate_m1
-- name    : QMCLeafB_gate_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:44:42.770049+00:00
-- url     : https://prove2.me/theorems/1cfd012e-744e-4d75-88d2-6acf4f323db2
-- title:
--   QMCLeafB gate_m1
-- statement:
--   # `gate_m1` — phase 29, member m1: the spec's family is EMPTY
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_m2
import Definitions.Def_QMCLeafB_falsify26
/-
# `gate_m1` — phase 29, member m1: the spec's family is EMPTY

The phase-29 spec's TARGET is

  `Fal28M5.target_of_runPartsFamily (B : ∀ (G,t), RunParts campaignBit G t paramsKbc2) hQn hsound`

with `hsound` the `∃`-soundness of `B`'s `ok` stream.  This file machine-checks that the first
hypothesis has no input at all, so the stroke is vacuous whatever `hsound` says.

The argument is the campaign's own ball obstruction, at the sliver `(G₁, t₁)`:

* the sliver's relaxation carries the campaign ball (`BallM2.sliver_ball_campaign`), so **every**
  `RunParts` at `(G₁, t₁)` forces its bit `true` (`BallM2.no_runParts_of_ball`);
* the frozen program reads `false` there (`Falsify26M8.campaignBit_sliver_false`).

Hence no `RunParts` family exists at `Audit2M5.campaignBit`, and the leaf must be re-keyed at a
repaired program's own loop bit.  The re-keyed submission file is `solution_m1.lean`: it states the
verbatim `d9f601e5` sentence and takes the family at the program's own bit, importing only the
published bundles `Definitions.Def_QMCLeafB_unionShallow` and `Definitions.Def_QMCLeafB_audit25`.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

set_option autoImplicit false

noncomputable section

namespace SubM1

open QuantumMaxCutEnergy

/-- **The phase-29 `RunParts` family is uninhabited at the frozen campaign bit.** -/
theorem no_runPartsFamily_campaignBit :
    ¬ Nonempty (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.FinalStroke.RunParts QMCLeafB.Audit2M5.campaignBit G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) := by
  rintro ⟨B⟩
  have h := QMCLeafB.BallM2.no_runParts_of_ball
    (G := QMCLeafB.AnchorFactsM2.G₁) (t := QMCLeafB.AnchorFactsM2.t₁)
    (P := QMCLeafB.AnchorFactsM2.P₁) QMCLeafB.AnchorFactsM2.hn₁
    QMCLeafB.BallM2.sliver_ball_campaign (B _ _)
  rw [QMCLeafB.Falsify26M8.campaignBit_sliver_false] at h
  exact Bool.noConfusion h

#print axioms SubM1.no_runPartsFamily_campaignBit

end SubM1



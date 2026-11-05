-- Prove2me | Definitions.Def_QMCLeafB_audit_m3
-- name    : QMCLeafB_audit_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:18:51.226111+00:00
-- url     : https://prove2.me/theorems/b325deaa-8167-46a0-b375-b4e0a78d333b
-- title:
--   QMCLeafB audit_m3
-- statement:
--   `Check_audit_m3` — phase 21, member m3, direction `d6` (`anchors-and-audit`).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_flags_m5
import Definitions.Def_QMCLeafB_records_m2
import Definitions.Def_QMCLeafB_record_m2
import Definitions.Def_QMCLeafB_stateDiag
import Definitions.Def_QMCLeafB_bundleFull
import Definitions.Def_QMCLeafB_pinchrec
import Definitions.Def_QMCLeafB_hmemStateB
import Definitions.Def_QMCLeafB_lamstream_m8
import Definitions.Def_QMCLeafB_traceBudget2_m8
import Definitions.Def_QMCLeafB_traceBudget_m8
import Definitions.Def_QMCLeafB_contract_m7
import Definitions.Def_QMCLeafB_unitdiag_m7
import Definitions.Def_QMCLeafB_ldltcert2_m5
import Definitions.Def_QMCLeafB_centreCore
import Definitions.Def_QMCLeafB_brick_verdict_sound
import Definitions.Def_QMCLeafB_final_stroke_m7
import Definitions.Def_QMCLeafB_brick_finish_line
import Definitions.Def_QMCLeafB_sim_loop_m6
import Definitions.Def_QMCLeafB_closingAssembly_m3
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_emptybody2
import Definitions.Def_QMCLeafB_residb_m7
import Definitions.Def_QMCLeafB_residbundle_m7
import Definitions.Def_QMCLeafB_cutbudget
import Definitions.Def_QMCLeafB_okprod_m6
import Definitions.Def_QMCLeafB_okprodB
import Definitions.Def_QMCLeafB_verdbridge
import Definitions.Def_QMCLeafB_emptybottom
import Definitions.Def_QMCLeafB_cutrec
import Definitions.Def_QMCLeafB_refuted_m3
/-
  `Check_audit_m3` — phase 21, member m3, direction `d6` (`anchors-and-audit`).

  The verification backbone of the endgame, not a producer and not a shape:

  * §1 **statement locks.**  The verbatim `d9f601e5` sentence is *definitionally* the shelf's name
    `QMCLeafB.FinishLine.SolutionStatement` (`Iff.rfl`), and the closing theorems
    `RecordsM2.solution_of_finite` / `solution_statement_of_finite` have exactly that conclusion
    from exactly the named residual.  The residual's own expansion (including the interior bracket)
    is locked the same way, so any drift in the closing modules fails to compile here.
  * §2 **what the residual demands of the body.**  `CoreDataF.hcutfin` contraposes to: every round
    at or beyond the horizon is an `ok` round, i.e. the pinched centre of the state at round `K·m`
    is a member of the relaxation.  This is a *positive* consequence, and its contrapositive is the
    phase-21 refutation skeleton: no member anywhere $\Rightarrow$ no record.  It is stated for an
    arbitrary runner `P`, so a producer or a refuter may use it without touching the shapes.
  * §3 **non-vacuity anchors.**  The ok point `(G₀, −1/2)` carries the record through the whole
    ladder `CoreDataF → CoreData → StreamCore → BundleH` in one term, and the §2 extraction is
    non-vacuous there (it exhibits an actual member certificate at the horizon round).
  * §4 **the axiom cone.**  `#print axioms` over 400 declarations of the twenty closing modules;
    every cone is a subset of `[propext, Classical.choice, Quot.sound]` (no `sorryAx` anywhere).

  Nothing here is new mathematics; every statement is either the shelf's own or an immediate
  unfolding.  What it buys is that the endgame's *interface* is now pinned at the sentence, at the
  residual, and at the axes of the record ladder.
-/

set_option autoImplicit false

namespace QMCLeafB.AuditM3

/-! ## 1.  Statement locks

The sentence of `d9f601e5-8c68-4369-a27d-701e73e686b8`, copied by hand from the leaf's statement
(not from any library declaration).  §1.1 proves it is *the same proposition* as the shelf's
`FinishLine.SolutionStatement`, and §1.2–§1.4 lock the two closing theorems' conclusion types. -/

/-- The leaf's sentence, verbatim. -/
abbrev TargetSentence : Prop :=
  ∃ L : QuantumMaxCutEnergy.Input → ℚ≥0,
    Nonempty (Turing.TM2ComputableInPolyTime QuantumMaxCutEnergy.encodeRequest
      QuantumMaxCutEnergy.encodeValue
      (fun request : QuantumMaxCutEnergy.Input × List Bool => L request.1)) ∧
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue
        (Matrix.of fun i j : Fin G.n =>
          if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
          else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) S ∧
      (L G : ℝ) ≤ S ∧
      S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000

/-- **Lock 1.**  The verbatim sentence and the shelf's `SolutionStatement` are definitionally equal
(no `Iff` glue, no `simp`). -/
theorem lock_finishLine : TargetSentence ↔ QMCLeafB.FinishLine.SolutionStatement :=
  Iff.rfl

#print axioms QMCLeafB.AuditM3.lock_finishLine

/-- The leaf's verdict bit: the program's answer at `(G, t)`. -/
noncomputable abbrev leafBit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
    QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2

/-- **The named residual**: the phase-20 finite-cut residual at the leaf's own program and
parameter family. -/
abbrev ResidEndgame : Type :=
  QMCLeafB.RecordsM2.ResidFinite leafBit QMCLeafB.UnionShallow.paramsKbc2

/-- **Lock 2.**  The residual's exact expansion: uniformly over the interior bracket
`−Rq G ≤ t < −(Rq G / 40000)`, one `CoreDataF`.  (This is the quantifier the phase-21 refutation
candidate attacks; the lock records it without interpretation.) -/
theorem lock_residExpansion : ResidEndgame =
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.RecordsM2.CoreDataF leafBit G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn) :=
  rfl

#print axioms QMCLeafB.AuditM3.lock_residExpansion

/-- **Lock 3.**  The closing theorem's conclusion, at the verbatim sentence. -/
theorem lock_solution_of_finite (H : ResidEndgame) : TargetSentence :=
  QMCLeafB.RecordsM2.solution_of_finite H

#print axioms QMCLeafB.AuditM3.lock_solution_of_finite

/-- **Lock 4.**  The same through the shelf's own name for the sentence. -/
theorem lock_solution_statement_of_finite (H : ResidEndgame) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.RecordsM2.solution_statement_of_finite H

#print axioms QMCLeafB.AuditM3.lock_solution_statement_of_finite

/-- **Lock 5.**  The second closing route, at the reduced residual `ResidData` (canonical centres,
one `CoreData` per interior point). -/
theorem lock_solution_of_coreData (H : QMCLeafB.RecordsM2.ResidData leafBit
    QMCLeafB.UnionShallow.paramsKbc2) : TargetSentence :=
  QMCLeafB.RecordsM2.solution_of_coreData H

#print axioms QMCLeafB.AuditM3.lock_solution_of_coreData

/-- **Lock 6.**  The third closing route, at the `FlagsM5` residual `ResidCore` (`StreamCore` per
interior point) — the shape in which the phase-19/20 bricks are stated. -/
theorem lock_solution_of_residCore (H : QMCLeafB.FlagsM5.ResidCore leafBit
    QMCLeafB.UnionShallow.paramsKbc2) : TargetSentence :=
  QMCLeafB.FlagsM5.solution_of_residCore H

#print axioms QMCLeafB.AuditM3.lock_solution_of_residCore

/-! ## 2.  What the residual demands of the body

`CoreDataF.hcutfin` (`flagOf … k = false → k < K·m`) has a contrapositive that no producer escapes:
past the horizon the canonical flag must be `true`, and a `true` flag *carries its member
certificate* (`FlagsM5.relaxMem_of_flagOf_true`).  So the phase-20 residual demands, at every
interior `(G,t)`, a member of the relaxed body among the run's pinched centres — in fact at the
horizon round itself.  Read backwards: if no pinched centre is ever a member, there is no record.

Both statements are shape-level identities, uniform in the runner `P`; the phase-21 refutation
needs only the second with the body-emptiness of the specific `(G₀, t)` supplied as a hypothesis. -/

/-- **Every round at or beyond the horizon is an `ok` round.** -/
theorem flag_true_of_horizon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) {k : ℕ} (hk : P.K * P.m ≤ k) :
    QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k = true := by
  cases hb : QMCLeafB.FlagsM5.flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k with
  | false => exact absurd (D.hcutfin k hb) (Nat.not_lt.mpr hk)
  | true => rfl

#print axioms QMCLeafB.AuditM3.flag_true_of_horizon

/-- **The member obligation at the horizon.**  The pinched centre of the record's own state at round
`K·m` lies in the relaxation. -/
theorem member_at_horizon {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq (P.K * P.m))
      (t - QMCLeafB.RundataCert.eps G) P.dq :=
  QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P _ _ (flag_true_of_horizon D (le_refl _))

#print axioms QMCLeafB.AuditM3.member_at_horizon

/-- **The refutation skeleton** (the step the phase-21 candidate needs at its last line): if no
pinched centre is a member, there is no record — for *any* verdict bit `o`. -/
theorem not_coreDataF_of_notMem {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (h : ∀ (X : ℕ → List ℚ) (k : ℕ),
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
          (QMCLeafB.RecordsM2.cXst G.n X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq) :
    QMCLeafB.RecordsM2.CoreDataF o G t P hn → False :=
  fun D => h D.X (P.K * P.m) (member_at_horizon D)

#print axioms QMCLeafB.AuditM3.not_coreDataF_of_notMem

/-- **The same at the level of the leaf's residual, at one interior point.**  A point whose
pinched centres are never members refutes the whole `ResidFinite` of phase 20 — so a single such
point empties `solution_of_finite`'s hypothesis. -/
theorem not_residEndgame_of_point {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (hn : 2 ≤ G.n)
    (h : ∀ (X : ℕ → List ℚ) (k : ℕ),
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
          (QMCLeafB.RecordsM2.cXst G.n X (QMCLeafB.UnionShallow.paramsKbc2 G).dq k)
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ResidEndgame → False :=
  fun H => not_coreDataF_of_notMem h (H G t hn hlo hhi)

#print axioms QMCLeafB.AuditM3.not_residEndgame_of_point

/-! ## 3.  Non-vacuity anchors at the ok point `(G₀, −1/2)`

`G₀` is the one-edge instance (`Rq = 1`, `2 ≤ G₀.n`) and `−1/2` is the threshold at which the
phase-19/20 bricks are anchored: the pinched centre there *is* a member, every canonical flag is
`true`, and the record exists.  The anchors below re-elaborate the banked ones and, in
`anchor_ladder`, drive the *whole* closing ladder in one term (`CoreDataF → CoreData → StreamCore →
BundleH`), which is the check that the ladder is coherent at a point where the residual is
satisfiable. -/

/-- The ok point's record, at the banked anchor. -/
theorem anchor_coreDataF :
    Nonempty (QMCLeafB.RecordsM2.CoreDataF (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.RecordsM2.coreDataF_G₀_inhabited

#print axioms QMCLeafB.AuditM3.anchor_coreDataF

/-- The same point at `StreamCore`. -/
theorem anchor_streamCore :
    Nonempty (QMCLeafB.FlagsM5.StreamCore (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.RecordsM2.streamCore_G₀_inhabited

#print axioms QMCLeafB.AuditM3.anchor_streamCore

/-- **The ladder anchor**: the phase-20 finite-cut record *derives* the phase-19 `BundleH` at the ok
point, through `coreData_of_finite` and `streamCore_of_core` — the two conversions the closing chain
depends on, exercised at an inhabited point rather than only stated. -/
theorem anchor_ladder :
    Nonempty (QMCLeafB.FlagsM5.BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.RecordsM2.coreDataF_G₀_inhabited.elim fun D =>
    ⟨QMCLeafB.FlagsM5.bundleH_of_core
      (QMCLeafB.RecordsM2.streamCore_of_core
        (QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀ QMCLeafB.ResidKill.hnG₀)
        (QMCLeafB.RecordsM2.coreData_of_finite D))⟩

#print axioms QMCLeafB.AuditM3.anchor_ladder

/-- **The §2 extraction is non-vacuous**: at the ok point it hands over an actual member certificate
at the horizon round.  (Its negation at a body-empty point is what refutes the residual.) -/
theorem anchor_ok_member :
    ∃ X : ℕ → List ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
        (QMCLeafB.RecordsM2.cXst QMCLeafB.ResidRefute.G₀.n X
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq
          ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K *
            (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m))
        (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq := by
  obtain ⟨D⟩ := anchor_coreDataF
  exact ⟨D.X, member_at_horizon D⟩

#print axioms QMCLeafB.AuditM3.anchor_ok_member

/-! ## 5.  Locks on the closing strokes, and the anchors of the assembled shapes

`Check_endgame_m2` (d7) closes the leaf from three residuals — `ResidB` (horizon-bounded canonical),
`ResidScalarB` (its collapsed one-scalar form) and `ResidG` (supplier-friendly: own flag stream and
own cut records).  The locks below type-check each stroke's conclusion against **§1's hand-copied
sentence**, not against the library's own spelling, so a drift in any of the four modules involved
fails here.  §5.5–§5.8 re-elaborate the non-vacuity anchors of all three shapes at `(G₀, −1/2)` and
run the `CoreDataB → BundleH` conversion once, in a term. -/

/-- **Lock 7.**  `solution_of_bounded` at the verbatim sentence. -/
theorem lock_solution_of_bounded
    (H : QMCLeafB.EndgameM2.ResidB leafBit QMCLeafB.UnionShallow.paramsKbc2) :
    TargetSentence :=
  QMCLeafB.EndgameM2.solution_of_bounded H

#print axioms QMCLeafB.AuditM3.lock_solution_of_bounded

/-- **Lock 8.**  The same at the shelf's name. -/
theorem lock_solution_statement_of_bounded
    (H : QMCLeafB.EndgameM2.ResidB leafBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.EndgameM2.solution_statement_of_bounded H

#print axioms QMCLeafB.AuditM3.lock_solution_statement_of_bounded

/-- **Lock 9.**  The one-scalar stroke. -/
theorem lock_solution_of_scalar_bounded
    (H : QMCLeafB.EndgameM2.ResidScalarB leafBit QMCLeafB.UnionShallow.paramsKbc2) :
    TargetSentence :=
  QMCLeafB.EndgameM2.solution_of_scalar_bounded H

#print axioms QMCLeafB.AuditM3.lock_solution_of_scalar_bounded

/-- **Lock 10.**  The supplier-friendly stroke — the one the leaf currently rests on. -/
theorem lock_solution_of_supplied
    (H : QMCLeafB.EndgameM2.ResidG leafBit QMCLeafB.UnionShallow.paramsKbc2) :
    TargetSentence :=
  QMCLeafB.EndgameM2.solution_of_supplied H

#print axioms QMCLeafB.AuditM3.lock_solution_of_supplied

/-- **Lock 11.**  The same at the shelf's name. -/
theorem lock_solution_statement_of_supplied
    (H : QMCLeafB.EndgameM2.ResidG leafBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.EndgameM2.solution_statement_of_supplied H

#print axioms QMCLeafB.AuditM3.lock_solution_statement_of_supplied

/-- **Lock 12.**  The conservativity stroke: phase 20's residual still gives the sentence, through the
bounded successor (so nothing banked in phase 20 is lost by the restatement). -/
theorem lock_solution_of_finite_via_bounded (H : ResidEndgame) : TargetSentence :=
  QMCLeafB.EndgameM2.solution_of_finite_via_bounded H

#print axioms QMCLeafB.AuditM3.lock_solution_of_finite_via_bounded

/-- **Anchor (bounded)**: `CoreDataB` at `(G₀, −1/2)`. -/
theorem anchor_coreDataB :
    Nonempty (QMCLeafB.EndgameM2.CoreDataB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataB_G₀_inhabited

#print axioms QMCLeafB.AuditM3.anchor_coreDataB

/-- **Anchor (one-scalar)**: the collapsed form at the same point. -/
theorem anchor_coreDataScalarB :
    Nonempty (QMCLeafB.EndgameM2.CoreDataScalarB (fun _ _ => true) QMCLeafB.ResidRefute.G₀
      (-(1 / 2)) (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataScalarB_G₀_inhabited

#print axioms QMCLeafB.AuditM3.anchor_coreDataScalarB

/-- **Anchor (supplier-friendly)**: the shape the leaf rests on, at the ok point. -/
theorem anchor_coreDataG :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataG_G₀_inhabited

#print axioms QMCLeafB.AuditM3.anchor_coreDataG

/-- **The assembled ladder anchor**: the supplier-friendly record *derives* the closing stroke's
`BundleH` at the ok point, in one term (`bundleH_of_dataG`), so the conversion the leaf's closure
depends on is exercised at an inhabited point rather than only stated. -/
theorem anchor_bundleH_of_dataG :
    Nonempty (QMCLeafB.FlagsM5.BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataG_G₀_inhabited.elim fun D =>
    ⟨QMCLeafB.EndgameM2.bundleH_of_dataG
      (QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀ QMCLeafB.ResidKill.hnG₀) D⟩

#print axioms QMCLeafB.AuditM3.anchor_bundleH_of_dataG

/-- **The residual's exact remaining obligation at an empty body** (d7's `coreDataB_at_empty`, read as
an elimination principle): any bounded record at a body-empty point *supplies* the two drift slots
below the horizon and the `false` bit.  This is the slot d3/d8 must fill; it is the only content the
leaf still owes. -/
theorem emptyBody_obligation {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.EndgameM2.CoreDataB o G t P hn) :
    o G t = false :=
  (QMCLeafB.EndgameM2.coreDataB_at_empty hempty D).2.2

#print axioms QMCLeafB.AuditM3.emptyBody_obligation
/-! ## 4.  The axiom cone

`#print axioms` for **every** theorem and lemma of the 33 closing modules of the phase-21 library —
the twenty of the phase-20 chain plus the members' phase-21 bricks (empty-body refutation, bounded
restate, cut budget, ok-production, verdict bridges, integration, campaign) and my own two modules
(generated; the generation is comment-stripped, so doc-comment prose cannot leak in).  Each line must
read `[propext, Classical.choice, Quot.sound]` or a subset of it; anything else — in particular
`sorryAx` — fails the audit at sight.  Checking them in one file also checks that the whole set
*co-loads* (the library's standing hazard is duplicate declaration names from `MergeAll3_m8`'s
copies). -/

#print axioms QMCLeafB.FlagsM5.solution_statement_of_residH
#print axioms QMCLeafB.FlagsM5.solution_of_residH
#print axioms QMCLeafB.FlagsM5.relaxMem_of_flagOf_true
#print axioms QMCLeafB.FlagsM5.flagOf_false_of_not_mem
#print axioms QMCLeafB.FlagsM5.cutOf_spec
#print axioms QMCLeafB.FlagsM5.flagOf_all_false
#print axioms QMCLeafB.FlagsM5.solution_of_residCore
#print axioms QMCLeafB.FlagsM5.Q₀_diag
#print axioms QMCLeafB.FlagsM5.Q₀_symm
#print axioms QMCLeafB.FlagsM5.Q₀_transpose
#print axioms QMCLeafB.FlagsM5.Q₀_qf
#print axioms QMCLeafB.FlagsM5.frob_Q₀
#print axioms QMCLeafB.FlagsM5.eps_G₀
#print axioms QMCLeafB.FlagsM5.relaxMem_G₀
#print axioms QMCLeafB.FlagsM5.flatQ_one_ne_zero'
#print axioms QMCLeafB.FlagsM5.bundleH_G₀_inhabited
#print axioms QMCLeafB.RecordsM2.cXst_diag
#print axioms QMCLeafB.RecordsM2.cXst_trace
#print axioms QMCLeafB.RecordsM2.hTrc_cXst
#print axioms QMCLeafB.RecordsM2.cXst_symm
#print axioms QMCLeafB.RecordsM2.frob_cXst
#print axioms QMCLeafB.RecordsM2.dOne_flat_diagPinch
#print axioms QMCLeafB.RecordsM2.hdriftd_diagPinch_iff
#print axioms QMCLeafB.RecordsM2.hdriftc_diagPinch_iff
#print axioms QMCLeafB.RecordsM2.drift_pair_of_collapse
#print axioms QMCLeafB.RecordsM2.cnOf_ne
#print axioms QMCLeafB.RecordsM2.lamOf_spec
#print axioms QMCLeafB.RecordsM2.rmax_pos_paramsKbc2
#print axioms QMCLeafB.RecordsM2.solution_of_coreData
#print axioms QMCLeafB.RecordsM2.solution_statement_of_coreData
#print axioms QMCLeafB.RecordsM2.solution_of_scalar
#print axioms QMCLeafB.RecordsM2.solution_statement_of_scalar
#print axioms QMCLeafB.RecordsM2.flagOf_eq_true_of_mem
#print axioms QMCLeafB.RecordsM2.flatQ_normal_cutOf_of_mem
#print axioms QMCLeafB.RecordsM2.flag_pinchG₀
#print axioms QMCLeafB.RecordsM2.flatQ_normal_cutOf_pinchG₀
#print axioms QMCLeafB.RecordsM2.streamCore_G₀_inhabited
#print axioms QMCLeafB.RecordsM2.hTrc_state_fails
#print axioms QMCLeafB.RecordsM2.scalar_budget_not_free
#print axioms QMCLeafB.RecordsM2.wMatrixQ_diag
#print axioms QMCLeafB.RecordsM2.flag_cXst_of_ok
#print axioms QMCLeafB.RecordsM2.anyOk_congr
#print axioms QMCLeafB.RecordsM2.hverdict_of_agreement
#print axioms QMCLeafB.RecordsM2.anyOk_true_of_imp
#print axioms QMCLeafB.RecordsM2.hverdict_sound_half
#print axioms QMCLeafB.RecordsM2.hverdict_cut_half
#print axioms QMCLeafB.RecordsM2.hverdict_of_halves
#print axioms QMCLeafB.RecordsM2.notMem_of_psdMargin
#print axioms QMCLeafB.RecordsM2.notMem_of_diag
#print axioms QMCLeafB.RecordsM2.notMem_of_trace
#print axioms QMCLeafB.RecordsM2.flag_false_of_psdMargin
#print axioms QMCLeafB.RecordsM2.solution_of_finite
#print axioms QMCLeafB.RecordsM2.solution_statement_of_finite
#print axioms QMCLeafB.RecordsM2.stMat_Q₀code
#print axioms QMCLeafB.RecordsM2.relaxMem_pinch_Q₀
#print axioms QMCLeafB.RecordsM2.flag_cXst_Q₀
#print axioms QMCLeafB.RecordsM2.coreDataF_G₀_inhabited
#print axioms QMCLeafB.RecordM2.anyOk_false_stream
#print axioms QMCLeafB.RecordM2.cutRecOfEmpty_normal
#print axioms QMCLeafB.RecordM2.cutRecOfEmpty_margin
#print axioms QMCLeafB.RecordM2.cXof_symm
#print axioms QMCLeafB.RecordM2.hTrc_cXof
#print axioms QMCLeafB.RecordM2.dq_pos_paramsKbc2
#print axioms QMCLeafB.RecordM2.dq_lt_four_paramsKbc2
#print axioms QMCLeafB.RecordM2.dq_pos_paramsShallow
#print axioms QMCLeafB.RecordM2.dq_lt_four_paramsShallow
#print axioms QMCLeafB.RecordM2.solution_guardT_of_streamData
#print axioms QMCLeafB.RecordM2.solution_of_streamData
#print axioms QMCLeafB.RecordM2.solution_statement_of_streamData
#print axioms QMCLeafB.RecordM2.witRel_of_posQ
#print axioms QMCLeafB.RecordM2.witOf_irrel
#print axioms QMCLeafB.RecordM2.witOf_eq_of_eq
#print axioms QMCLeafB.RecordM2.shapeChain_step
#print axioms QMCLeafB.RecordM2.runChain_val_eq
#print axioms QMCLeafB.RecordM2.runShape_eq_shapeVal
#print axioms QMCLeafB.RecordM2.shapeVal_ext
#print axioms QMCLeafB.RecordM2.witAt_eq_witRel
#print axioms QMCLeafB.RecordM2.lamInd_eq
#print axioms QMCLeafB.RecordM2.lamInd_ge_one
#print axioms QMCLeafB.RecordM2.lamInd_nonneg
#print axioms QMCLeafB.RecordM2.lamInd_gt
#print axioms QMCLeafB.RecordM2.cnInd_ne
#print axioms QMCLeafB.RecordM2.max_mul_ge
#print axioms QMCLeafB.RecordM2.pairing_pos_of_posQ
#print axioms QMCLeafB.RecordM2.lamInd_spec
#print axioms QMCLeafB.RecordM2.u0_d0idx
#print axioms QMCLeafB.RecordM2.rmax_pos_paramsKbc2
#print axioms QMCLeafB.RecordM2.rmax_pos_paramsShallow
#print axioms QMCLeafB.RecordM2.solution_of_records
#print axioms QMCLeafB.RecordM2.solution_guardT_of_records
#print axioms QMCLeafB.RecordM2.solution_statement_of_records
#print axioms QMCLeafB.RecordM2.exists_multiplier
#print axioms QMCLeafB.RecordM2.threshold_needs_positivity
#print axioms QMCLeafB.RecordM2.bundleForcesFalse
#print axioms QMCLeafB.RecordM2.hdriftd_of_scalar_budget
#print axioms QMCLeafB.RecordM2.residStream_kbc2_impossible
#print axioms QMCLeafB.StateDiag.stMat_apply
#print axioms QMCLeafB.StateDiag.idxs_of_le
#print axioms QMCLeafB.StateDiag.list_sum_eq_zero_of_forall
#print axioms QMCLeafB.StateDiag.diagSumV_eq_zero_iff
#print axioms QMCLeafB.StateDiag.stMat_diag_eq_one
#print axioms QMCLeafB.StateDiag.stMat_diag_abs_le
#print axioms QMCLeafB.StateDiag.stMat_trace_le
#print axioms QMCLeafB.StateDiag.relaxMem_of_oracleV_ok_state
#print axioms QMCLeafB.StateDiag.list_sum_map_range_eq
#print axioms QMCLeafB.StateDiag.frobV_eq_frob
#print axioms QMCLeafB.StateDiag.fvR_eq_frob
#print axioms QMCLeafB.ResidKill.G₀_bracket
#print axioms QMCLeafB.ResidKill.hnG₀
#print axioms QMCLeafB.ResidKill.bundle_false_kbc2
#print axioms QMCLeafB.ResidKill.bundle_false_shallow
#print axioms QMCLeafB.ResidKill.resid_false_kbc2
#print axioms QMCLeafB.ResidKill.resid_false_shallow
#print axioms QMCLeafB.ResidKill.no_closure_via_resid
#print axioms QMCLeafB.ResidKill.exists_ok_round
#print axioms QMCLeafB.ResidKill.exists_ok_round_of_bundle
#print axioms QMCLeafB.ResidKill.bundleFull_not_allFalse
#print axioms QMCLeafB.ResidKill.solution_statement_of_residFull
#print axioms QMCLeafB.ResidKill.solution_of_residFull
#print axioms QMCLeafB.PinchRec.frob_deltaDelta
#print axioms QMCLeafB.PinchRec.nonempty_relaxCut_pinch
#print axioms QMCLeafB.PinchRec.hdriftd_pinch_iff
#print axioms QMCLeafB.PinchRec.pinch_centre_slots
#print axioms QMCLeafB.HmemState.matOf_eq_stMat
#print axioms QMCLeafB.HmemState.hmem_at_state
#print axioms QMCLeafB.HmemState.hmem_slot
#print axioms QMCLeafB.LamStreamM8.flatQ_one_apply
#print axioms QMCLeafB.LamStreamM8.flatQ_one_ne_zero
#print axioms QMCLeafB.LamStreamM8.witAt_pairing_pos
#print axioms QMCLeafB.LamStreamM8.exists_lam_of_hl
#print axioms QMCLeafB.TraceBudgetM8.sum_diag_cast_of_unitDiag
#print axioms QMCLeafB.TraceBudgetM8.drift_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.hdriftd_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.hdriftc_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.happr_of_drifts
#print axioms QMCLeafB.TraceBudgetM8.happr_linear_iff
#print axioms QMCLeafB.TraceBudgetM8.exists_lam_of_trace_lt
#print axioms QMCLeafB.TraceBudgetM8.exists_lam_happr
#print axioms QMCLeafB.TraceBudgetM8.hstrict_iff_trace
#print axioms QMCLeafB.TraceBudgetM8.hstrict_iff_trace_unitDiag
#print axioms QMCLeafB.ContractM7.Gtwo_n
#print axioms QMCLeafB.ContractM7.Gtwo_hn
#print axioms QMCLeafB.ContractM7.univ_edge_two
#print axioms QMCLeafB.ContractM7.Rq_Gtwo
#print axioms QMCLeafB.ContractM7.Ztwo_unitDiagPSD
#print axioms QMCLeafB.ContractM7.trace_Gtwo_Ztwo
#print axioms QMCLeafB.ContractM7.anyOk_all_false
#print axioms QMCLeafB.ContractM7.no_runParts_allFalse_of_body
#print axioms QMCLeafB.ContractM7.no_bundle_at
#print axioms QMCLeafB.ContractM7.Rq_Gtwo_pos
#print axioms QMCLeafB.ContractM7.Gtwo_bracket_lo
#print axioms QMCLeafB.ContractM7.Gtwo_bracket_hi
#print axioms QMCLeafB.ContractM7.resid_kbc2_empty
#print axioms QMCLeafB.ContractM7.resid_shallow_empty
#print axioms QMCLeafB.ContractM7.tolerance_floor
#print axioms QMCLeafB.ContractM7.sum_sq_witness
#print axioms QMCLeafB.ContractM7.qf_Xgrid_nat
#print axioms QMCLeafB.ContractM7.not_pivPsdMargin_sGrid
#print axioms QMCLeafB.ContractM7.pivFSpec_false
#print axioms QMCLeafB.ContractM7.dqShallow_lt_floor
#print axioms QMCLeafB.ContractM7.pivFSpec_false_campaign
#print axioms QMCLeafB.ContractM7.interior_point_is_above_a_body_point
#print axioms QMCLeafB.ContractM7.hcert_slot_inhabited
#print axioms QMCLeafB.ContractM7.sGrid_is_campaign_grid_state
#print axioms QMCLeafB.UnitDiagPivotM7.toRows_ud
#print axioms QMCLeafB.UnitDiagPivotM7.Xud_toMatrix
#print axioms QMCLeafB.UnitDiagPivotM7.qf_Xud
#print axioms QMCLeafB.UnitDiagPivotM7.sum_sq_ud
#print axioms QMCLeafB.UnitDiagPivotM7.not_psd_Xud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStep_ud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStep_ud2
#print axioms QMCLeafB.UnitDiagPivotM7.runPiv_ud
#print axioms QMCLeafB.UnitDiagPivotM7.pivStepL_ud1
#print axioms QMCLeafB.UnitDiagPivotM7.pivStepL_ud2
#print axioms QMCLeafB.UnitDiagPivotM7.runPivL_ud
#print axioms QMCLeafB.UnitDiagPivotM7.descents_disagree_ud
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_pivAns
#print axioms QMCLeafB.UnitDiagPivotM7.idxs_ud
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_unitDiag
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_matrix
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_diag_one
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_trace
#print axioms QMCLeafB.UnitDiagPivotM7.qf_Xud_nat
#print axioms QMCLeafB.UnitDiagPivotM7.not_pivPsdMargin_sUd
#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false
#print axioms QMCLeafB.UnitDiagPivotM7.dqShallow_lt_unitDiag_floor
#print axioms QMCLeafB.UnitDiagPivotM7.unitDiag_pivFSpec_false_campaign
#print axioms QMCLeafB.UnitDiagPivotM7.sUd_side_conditions
#print axioms QMCLeafB.LdltCertM5.sum_sq_tail_le
#print axioms QMCLeafB.LdltCertM5.schur_split_qf
#print axioms QMCLeafB.LdltCertM5.schur_step_radius
#print axioms QMCLeafB.LdltCertM5.drop_step_radius
#print axioms QMCLeafB.LdltCertM5.nrmQ_zero
#print axioms QMCLeafB.LdltCertM5.nrmRows_eq_map
#print axioms QMCLeafB.LdltCertM5.nrmQ_error_of_box
#print axioms QMCLeafB.LdltCertM5.evRun_of_box
#print axioms QMCLeafB.LdltCertM5.getD_le_of_all
#print axioms QMCLeafB.LdltCertM5.box_le_of_all
#print axioms QMCLeafB.LdltCertM5.nrmBox_of_nrmBoxB
#print axioms QMCLeafB.LdltCertM5.boxRun_of_boxRunB
#print axioms QMCLeafB.LdltCertM5.getD_err_of_all
#print axioms QMCLeafB.LdltCertM5.errRows_of_all
#print axioms QMCLeafB.LdltCertM5.evRun_of_evRunB
#print axioms QMCLeafB.LdltCertM5.pivStepL_empty
#print axioms QMCLeafB.LdltCertM5.pivStepL_neg
#print axioms QMCLeafB.LdltCertM5.pivStepL_zeroCut
#print axioms QMCLeafB.LdltCertM5.pivStepL_drop
#print axioms QMCLeafB.LdltCertM5.pivStepL_schur
#print axioms QMCLeafB.LdltCertM5.runPivLFuel_inl
#print axioms QMCLeafB.LdltCertM5.runPivLFuel_inr
#print axioms QMCLeafB.LdltCertM5.nextL_inl
#print axioms QMCLeafB.LdltCertM5.nextL_inr
#print axioms QMCLeafB.LdltCertM5.specR_runPivLFuel
#print axioms QMCLeafB.LdltCertM5.qf_margin_of_false
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_boxRun
#print axioms QMCLeafB.LdltCertM5.qf_margin_of_false_eps
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_measured
#print axioms QMCLeafB.LdltCertM5.psd_of_exactRun
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_exactRun
#print axioms QMCLeafB.LdltCertM5.sharp_needs_grid
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_tolerance
#print axioms QMCLeafB.LdltCertM5.no_unconditional_campaign_margin
#print axioms QMCLeafB.LdltCertM5.pivPsdMargin_of_entryBound
#print axioms QMCLeafB.LdltCertM5.toRows_one
#print axioms QMCLeafB.LdltCertM5.boxRun_one
#print axioms QMCLeafB.LdltCertM5.runPivL_one
#print axioms QMCLeafB.LdltCertM5.simpleState_margin
#print axioms QMCLeafB.LdltCertM5.simpleState_margin_campaign
#print axioms QMCLeafB.CentreClosure.trace_cast_le
#print axioms QMCLeafB.CentreClosure.hbody_of_trace
#print axioms QMCLeafB.CentreClosure.hbody_of_trace_body
#print axioms QMCLeafB.CentreClosure.trace_le_of_diag
#print axioms QMCLeafB.CentreClosure.flatQ_smul
#print axioms QMCLeafB.CentreClosure.castMat_smul
#print axioms QMCLeafB.CentreClosure.flat_smul
#print axioms QMCLeafB.CentreClosure.flat_castMat_smul
#print axioms QMCLeafB.CentreClosure.centre_shift
#print axioms QMCLeafB.CentreClosure.centre_shift_dot_le
#print axioms QMCLeafB.CentreClosure.diag_scaled_le
#print axioms QMCLeafB.CentreClosure.dOne_eq_flat_one
#print axioms QMCLeafB.CentreClosure.dOne_dot_flat_eq_trace
#print axioms QMCLeafB.CentreClosure.hstated_iff_trace
#print axioms QMCLeafB.CentreClosure.relaxMem_scaled_false
#print axioms QMCLeafB.CentreClosure.relaxBodyLE_scaled_false
#print axioms QMCLeafB.CentreClosure.flatQ_unflatQ
#print axioms QMCLeafB.CentreClosure.flat_castMat_eq_flatQ
#print axioms QMCLeafB.CentreClosure.muUp_eq_muQUp
#print axioms QMCLeafB.CentreClosure.qVec_cast
#print axioms QMCLeafB.CentreClosure.flat_qMat
#print axioms QMCLeafB.CentreClosure.hstated_at_surrogate
#print axioms QMCLeafB.CentreClosure.hstatec_at_surrogate
#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_iff
#print axioms QMCLeafB.VerdictSound.eps_nonneg
#print axioms QMCLeafB.VerdictSound.exists_trace_le_of_neg_eps_le
#print axioms QMCLeafB.VerdictSound.soundAt_true_of_neg_eps_le
#print axioms QMCLeafB.VerdictSound.soundAt_false_of_le_floor
#print axioms QMCLeafB.VerdictSound.soundAt_false_at_floor
#print axioms QMCLeafB.VerdictSound.exists_trace_le_zero
#print axioms QMCLeafB.VerdictSound.edge_isEmpty_of_le_one
#print axioms QMCLeafB.VerdictSound.Rq_eq_zero_of_le_one
#print axioms QMCLeafB.VerdictSound.wMatrix_eq_zero_of_le_one
#print axioms QMCLeafB.VerdictSound.trace_eq_zero_of_le_one
#print axioms QMCLeafB.VerdictSound.soundAt_of_le_one
#print axioms QMCLeafB.VerdictSound.soundAt_of_runData
#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData
#print axioms QMCLeafB.VerdictSound.soundEpsOnBracket_of_runData_interior
#print axioms QMCLeafB.VerdictSound.solution_of_loop_via_runData
#print axioms QMCLeafB.FinalStroke.noTape_fst
#print axioms QMCLeafB.FinalStroke.noTape_snd
#print axioms QMCLeafB.FinalStroke.loopBit_apply
#print axioms QMCLeafB.FinalStroke.hspec_of_tape_free
#print axioms QMCLeafB.FinalStroke.endgame_of_tape_free_loop
#print axioms QMCLeafB.FinalStroke.encodeList_drop_length_le
#print axioms QMCLeafB.FinalStroke.boundedRun_loopBody_orbit
#print axioms QMCLeafB.FinalStroke.poly_loop_state_orbit
#print axioms QMCLeafB.FinalStroke.poly_simulate_count_orbit
#print axioms QMCLeafB.FinalStroke.ho_of_loop_orbit
#print axioms QMCLeafB.FinalStroke.solution_of_loop_orbit
#print axioms QMCLeafB.FinalStroke.orbit_of_hsize
#print axioms QMCLeafB.FinalStroke.sizesOrbitPow_eval
#print axioms QMCLeafB.FinalStroke.orbit_of_monomial_pow
#print axioms QMCLeafB.FinalStroke.list_drop_succ_eq_tail
#print axioms QMCLeafB.FinalStroke.sizesAdd_eval
#print axioms QMCLeafB.FinalStroke.horbit_of_additive_step
#print axioms QMCLeafB.FinalStroke.endgame_orbit_of_parts
#print axioms QMCLeafB.FinalStroke.endgame_of_parts
#print axioms QMCLeafB.FinalStroke.endgame_of_concrete_params
#print axioms QMCLeafB.FinalStroke.endgame_of_concrete
#print axioms QMCLeafB.FinalStroke.hbudget_of_le_budgetRounds
#print axioms QMCLeafB.FinalStroke.endgame_of_dominated_rounds
#print axioms QMCLeafB.FinalStroke.endgame_of_dominated_rounds_interior
#print axioms QMCLeafB.FinalStroke.solution
#print axioms QMCLeafB.FinishLine.solutionStatement_iff_wMatrix
#print axioms QMCLeafB.FinishLine.solution_of_eng
#print axioms QMCLeafB.FinishLine.bool_eq_false_of_ne_true
#print axioms QMCLeafB.FinishLine.sbit_engineOfε
#print axioms QMCLeafB.FinishLine.solution_of_ho
#print axioms QMCLeafB.FinishLine.poly_of_pointwise
#print axioms QMCLeafB.FinishLine.solution_of_program
#print axioms QMCLeafB.FinishLine.slack_sum
#print axioms QMCLeafB.FinishLine.Rq_eq_two_sum
#print axioms QMCLeafB.FinishLine.slack_budget
#print axioms QMCLeafB.FinishLine.soundεOnBracket_of_soundε
#print axioms QMCLeafB.FinishLine.neg_Rq_le_trace
#print axioms QMCLeafB.FinishLine.one_trace_eq_zero
#print axioms QMCLeafB.FinishLine.soundε_clampBit
#print axioms QMCLeafB.FinishLine.poly_clampBit
#print axioms QMCLeafB.FinishLine.solution_of_bracket_verdict
#print axioms QMCLeafB.FinishLine.solution_of_bracket_program
#print axioms QMCLeafB.FinishLine.soundε_truthBit
#print axioms QMCLeafB.FinishLine.exists_soundε
#print axioms QMCLeafB.FinishLine.exists_soundε_bracket
#print axioms QMCLeafB.FinishLine.solution_of_exists_sound
#print axioms QMCLeafB.FinishLine.solution_of_exists_sound_bracket
#print axioms QMCLeafB.SimLoop.sbit_eq_sbitAns
#print axioms QMCLeafB.SimLoop.cast_witness_prefix
#print axioms QMCLeafB.SimLoop.Aat_cast_posDef_prefix
#print axioms QMCLeafB.SimLoop.Aat_det_prefix
#print axioms QMCLeafB.SimLoop.Aat_det_ge_prefix
#print axioms QMCLeafB.SimLoop.Aat_vol_le_prefix
#print axioms QMCLeafB.SimLoop.Aat_vol_below_of_halving_prefix
#print axioms QMCLeafB.SimLoop.Prefix.body_containment_prefix
#print axioms QMCLeafB.SimLoop.Prefix.body_containment_at_halving_margin_prefix
#print axioms QMCLeafB.SimLoop.Prefix.strictBody_refuted_prefix
#print axioms QMCLeafB.SimLoop.Prefix.strictBody_refuted_prefix_concrete
#print axioms QMCLeafB.SimLoop.anyOk_succ
#print axioms QMCLeafB.SimLoop.anyOk_eq_true_iff
#print axioms QMCLeafB.SimLoop.anyOk_eq_false_iff
#print axioms QMCLeafB.SimLoop.simulate_feasible_sound
#print axioms QMCLeafB.SimLoop.simulate_refuted_sound
#print axioms QMCLeafB.SimLoop.simulate_agrees_engine
#print axioms QMCLeafB.SimLoop.simulate_sound
#print axioms QMCLeafB.SimLoop.vol_halving_K_explicit
#print axioms QMCLeafB.SimLoop.vol_below_K_explicit
#print axioms QMCLeafB.SimLoop.simRounds_budget
#print axioms QMCLeafB.SimLoop.rho0R_zero_ge_one_add
#print axioms QMCLeafB.SimLoop.sq_four
#print axioms QMCLeafB.SimLoop.halving_time_explicit
#print axioms QMCLeafB.SimLoop.central_run_budget
#print axioms QMCLeafB.ClosingAssembly.noMem_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_pos
#print axioms QMCLeafB.ClosingAssembly.rmaxOf_le_one
#print axioms QMCLeafB.ClosingAssembly.budget_dqShallow
#print axioms QMCLeafB.ClosingAssembly.solution_statement
#print axioms QMCLeafB.ClosingAssembly.solution
#print axioms QMCLeafB.ClosingAssembly.solution_guardT
#print axioms QMCLeafB.ClosingAssembly.verdict_eq_false_of_allFalse
#print axioms QMCLeafB.ClosingAssembly.resid_range_nonempty_iff
#print axioms QMCLeafB.UnionShallow.solution_of_runParts_interior_of_params_hn
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_K
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_m
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_dq
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_rmax
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_K_mul_m
#print axioms QMCLeafB.UnionShallow.solution_union_shallow_gen
#print axioms QMCLeafB.UnionShallow.solution_union_shallow
#print axioms QMCLeafB.UnionShallow.dqShallow_eq_core
#print axioms QMCLeafB.UnionShallow.shallowKbound_of_dq_one
#print axioms QMCLeafB.UnionShallow.budgetRounds_eq
#print axioms QMCLeafB.UnionShallow.roundArg_eq_pow
#print axioms QMCLeafB.UnionShallow.roundArg_le
#print axioms QMCLeafB.UnionShallow.budgetRounds_le_one_add
#print axioms QMCLeafB.UnionShallow.inv_Rq_le_two_pow_bitCost
#print axioms QMCLeafB.UnionShallow.dqShallow_le_one
#print axioms QMCLeafB.UnionShallow.inv_dqShallow_le
#print axioms QMCLeafB.UnionShallow.Kbc_le_Kbc2
#print axioms QMCLeafB.UnionShallow.budgetRounds_dqShallow_le_Kbc2
#print axioms QMCLeafB.UnionShallow.poly_Kbc2_mHalve_mul
#print axioms QMCLeafB.UnionShallow.pow22_le
#print axioms QMCLeafB.UnionShallow.Kbc2_mHalve_le_seed
#print axioms QMCLeafB.UnionShallow.shallowKbound_Kbc2
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_rmax_pos
#print axioms QMCLeafB.UnionShallow.paramsShallowKf_budget
#print axioms QMCLeafB.UnionShallow.interior_bracket_empty_of_Rq_zero
#print axioms QMCLeafB.UnionShallow.solution_union_shallow_final
#print axioms QMCLeafB.UnionShallow.paramsKbc2_K
#print axioms QMCLeafB.UnionShallow.paramsKbc2_m
#print axioms QMCLeafB.UnionShallow.paramsKbc2_dq
#print axioms QMCLeafB.UnionShallow.paramsKbc2_K_mul_m
#print axioms QMCLeafB.UnionShallow.one_le_Kbc2_mul
#print axioms QMCLeafB.UnionShallow.paramsKbc2_rmax_pos
#print axioms QMCLeafB.UnionShallow.paramsKbc2_budget
#print axioms QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ
#print axioms QMCLeafB.RunPartsDilate.dotProduct_mulVec_symm
#print axioms QMCLeafB.RunPartsDilate.depth_of_dilation
#print axioms QMCLeafB.RunPartsDilate.A0P_posDef
#print axioms QMCLeafB.RunPartsDilate.runShape_posQ
#print axioms QMCLeafB.RunPartsDilate.runCut_wit
#print axioms QMCLeafB.RunPartsDilate.runCut_c
#print axioms QMCLeafB.RunPartsDilate.runCut_rho
#print axioms QMCLeafB.RunPartsDilate.runShape_mulVec_wit
#print axioms QMCLeafB.RunPartsDilate.runShape_mulVec_dirWit
#print axioms QMCLeafB.RunPartsDilate.flatQ_add
#print axioms QMCLeafB.RunPartsDilate.flatQ_smul
#print axioms QMCLeafB.RunPartsDilate.dilCut_margin
#print axioms QMCLeafB.RunPartsDilate.dilCut_normal
#print axioms QMCLeafB.RunPartsDilate.witAt_spec
#print axioms QMCLeafB.RunPartsDilate.runCut_eq_witAt
#print axioms QMCLeafB.RunPartsDilate.flatQ_eq_zero
#print axioms QMCLeafB.RunPartsDilate.runParamsShallow_rmax_pos
#print axioms QMCLeafB.EndgameM2.anyOk_congr
#print axioms QMCLeafB.EndgameM2.okHor_of_lt
#print axioms QMCLeafB.EndgameM2.okHor_of_not_lt
#print axioms QMCLeafB.EndgameM2.okHor_lt
#print axioms QMCLeafB.EndgameM2.okHor_flag
#print axioms QMCLeafB.EndgameM2.anyOk_okHor
#print axioms QMCLeafB.EndgameM2.solution_of_bounded
#print axioms QMCLeafB.EndgameM2.solution_statement_of_bounded
#print axioms QMCLeafB.EndgameM2.solution_of_finite_via_bounded
#print axioms QMCLeafB.EndgameM2.coreDataB_G₀_inhabited
#print axioms QMCLeafB.EndgameM2.bundleH_G₀_inhabited
#print axioms QMCLeafB.EndgameM2.solution_of_scalar_bounded
#print axioms QMCLeafB.EndgameM2.solution_statement_of_scalar_bounded
#print axioms QMCLeafB.EndgameM2.hverdict_false_of_empty
#print axioms QMCLeafB.EndgameM2.coreDataB_at_empty
#print axioms QMCLeafB.EndgameM2.solution_lock
#print axioms QMCLeafB.EndgameM2.flag_eq_false_of_empty
#print axioms QMCLeafB.EndgameM2.not_hcutfin_of_empty
#print axioms QMCLeafB.EndgameM2.not_coreDataF_of_empty
#print axioms QMCLeafB.EndgameM2.not_residFinite_of_empty_point
#print axioms QMCLeafB.EndgameM2.nonempty_coreDataB_iff
#print axioms QMCLeafB.EndgameM2.coreDataScalarB_G₀_inhabited
#print axioms QMCLeafB.EndgameM2.gCn_ne
#print axioms QMCLeafB.EndgameM2.solution_of_supplied
#print axioms QMCLeafB.EndgameM2.solution_statement_of_supplied
#print axioms QMCLeafB.EndgameM2.coreDataG_G₀_inhabited
#print axioms QMCLeafB.EndgameM2.verdict_false_of_empty
#print axioms QMCLeafB.EndgameM2.hdriftc_trivial
#print axioms QMCLeafB.EndgameM2.hdriftd_is_the_content
#print axioms QMCLeafB.EndgameM2.hdriftd_of_nonpos_increments
#print axioms QMCLeafB.EndgameM2.hdriftd_of_increment_bound
#print axioms QMCLeafB.EmptyBodyM5.eps_G₀
#print axioms QMCLeafB.EmptyBodyM5.dq₀_eq
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_00
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_01
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_10
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₀_11
#print axioms QMCLeafB.EmptyBodyM5.frob_ge_of_relaxMem
#print axioms QMCLeafB.EmptyBodyM5.frob_ge_G₀
#print axioms QMCLeafB.EmptyBodyM5.not_relaxMem_G₀_of_lt
#print axioms QMCLeafB.EmptyBodyM5.not_relaxMem_G₀
#print axioms QMCLeafB.EmptyBodyM5.the_gap
#print axioms QMCLeafB.EmptyBodyM5.flagOf_false_of_emptyBody
#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_of_emptyBody
#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_G₀
#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₀_empty
#print axioms QMCLeafB.EmptyBodyM5.t₀_mem_bracket
#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₀_empty_of_dq
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty_of_dq
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty'
#print axioms QMCLeafB.EmptyBodyM5.solution_of_finite_hypothesis_empty
#print axioms QMCLeafB.EmptyBodyM5.hverdict_eq_false_G₀
#print axioms QMCLeafB.EmptyBodyM5.relaxMem_diagPinch_of_psd
#print axioms QMCLeafB.EmptyBodyM5.member_counterexample
#print axioms QMCLeafB.EmptyBodyM5.pinch_of_member_false
#print axioms QMCLeafB.EmptyBodyM5.Rq_G₁
#print axioms QMCLeafB.EmptyBodyM5.eps_G₁
#print axioms QMCLeafB.EmptyBodyM5.dq₁_eq
#print axioms QMCLeafB.EmptyBodyM5.dqShallow_G₁
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01
#print axioms QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10
#print axioms QMCLeafB.EmptyBodyM5.frob_ge_of_pinched
#print axioms QMCLeafB.EmptyBodyM5.no_pinched_member_G₁_lit
#print axioms QMCLeafB.EmptyBodyM5.no_pinched_member_G₁
#print axioms QMCLeafB.EmptyBodyM5.body_nonempty_G₁_lit
#print axioms QMCLeafB.EmptyBodyM5.body_nonempty_G₁
#print axioms QMCLeafB.EmptyBodyM5.not_coreDataF_of_pinchedEmpty
#print axioms QMCLeafB.EmptyBodyM5.t₁_mem_bracket
#print axioms QMCLeafB.EmptyBodyM5.coreDataF_G₁_empty
#print axioms QMCLeafB.EmptyBodyM5.residFinite_empty_of_body_nonempty
#print axioms QMCLeafB.EmptyBodyM5.not_residFinite_of_no_pinched_member
#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_residB
#print axioms QMCLeafB.EmptyBody2M5.not_nonempty_residFinite
#print axioms QMCLeafB.EmptyBody2M5.solution_of_finite_hypothesis_empty'
#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_sliver
#print axioms QMCLeafB.EmptyBody2M5.lock_verbatim
#print axioms QMCLeafB.EmptyBody2M5.lock_statement
#print axioms QMCLeafB.EmptyBody2M5.solution_of_finiteB_via_m2
#print axioms QMCLeafB.EmptyBody2M5.lock_statement_m2
#print axioms QMCLeafB.ResidB_M7.okClip_apply_lt
#print axioms QMCLeafB.ResidB_M7.okClip_apply_ge
#print axioms QMCLeafB.ResidB_M7.okClip_eq_false_iff
#print axioms QMCLeafB.ResidB_M7.anyOk_okClip
#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB
#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB_of_finite
#print axioms QMCLeafB.ResidB_M7.solution_statement_of_finiteB
#print axioms QMCLeafB.ResidB_M7.lock_solution_of_finiteB
#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB_eq_solution_of_finite
#print axioms QMCLeafB.ResidB_M7.member_beyond_horizon_of_hcutfin
#print axioms QMCLeafB.ResidB_M7.not_nonempty_coreDataF_of_emptyBody
#print axioms QMCLeafB.ResidB_M7.not_residFinite_of_emptyBody
#print axioms QMCLeafB.ResidB_M7.bundleH_of_coreB_ok_ge
#print axioms QMCLeafB.ResidB_M7.coreDataB_G₀_inhabited
#print axioms QMCLeafB.ResidB_M7.streamCoreB_G₀_inhabited
#print axioms QMCLeafB.ResidB_M7.bundleH_G₀_of_bounded
#print axioms QMCLeafB.ResidB_M7.solution_of_scalarB
#print axioms QMCLeafB.ResidB_M7.anyOk_false_fun
#print axioms QMCLeafB.ResidB_M7.bundleH_of_coreB_at_allFalse
#print axioms QMCLeafB.ResidB_M7.solution_statement_of_residCoreB
#print axioms QMCLeafB.ResidB_M7.solution_of_residCoreB
#print axioms QMCLeafB.ResidB_M7.hdriftd_centre_free
#print axioms QMCLeafB.ResidB_M7.coreDataB_hdriftd_centre_free
#print axioms QMCLeafB.ResidB_M7.hdriftd_of_centre_free
#print axioms QMCLeafB.ResidB_M7.bundleH_forces_engine_trace
#print axioms QMCLeafB.ResidB_M7.streamCoreB_forces_engine_trace
#print axioms QMCLeafB.ResidBundle_M7.solution_statement_of_window
#print axioms QMCLeafB.ResidBundle_M7.solution_of_window
#print axioms QMCLeafB.ResidBundle_M7.lock_solution_of_window
#print axioms QMCLeafB.ResidBundle_M7.window_G₀_inhabited
#print axioms QMCLeafB.ResidBundle_M7.window_forces_engine_trace
#print axioms QMCLeafB.CutBudgetM8.vecMulVec_mulVec'
#print axioms QMCLeafB.CutBudgetM8.iso_mulVec
#print axioms QMCLeafB.CutBudgetM8.iso_mulVec_smul
#print axioms QMCLeafB.CutBudgetM8.iso_transpose
#print axioms QMCLeafB.CutBudgetM8.iso_qf
#print axioms QMCLeafB.CutBudgetM8.iso_posQ
#print axioms QMCLeafB.CutBudgetM8.fr_apply
#print axioms QMCLeafB.CutBudgetM8.fr_dot
#print axioms QMCLeafB.CutBudgetM8.fr_ne_zero
#print axioms QMCLeafB.CutBudgetM8.Mpar_pos
#print axioms QMCLeafB.CutBudgetM8.alphaQ_val
#print axioms QMCLeafB.CutBudgetM8.betaQ_val
#print axioms QMCLeafB.CutBudgetM8.gammaR_val
#print axioms QMCLeafB.CutBudgetM8.gamQ_pos
#print axioms QMCLeafB.CutBudgetM8.alpQ_pos
#print axioms QMCLeafB.CutBudgetM8.geoQ_pos
#print axioms QMCLeafB.CutBudgetM8.geoQ_eq
#print axioms QMCLeafB.CutBudgetM8.alpQ_le_geoQ
#print axioms QMCLeafB.CutBudgetM8.cd_c
#print axioms QMCLeafB.CutBudgetM8.cd_p
#print axioms QMCLeafB.CutBudgetM8.cd_rho
#print axioms QMCLeafB.CutBudgetM8.cd_cne
#print axioms QMCLeafB.CutBudgetM8.Mpar_inv_pos
#print axioms QMCLeafB.CutBudgetM8.tsc_pos
#print axioms QMCLeafB.CutBudgetM8.tsc_ne
#print axioms QMCLeafB.CutBudgetM8.asc_pos
#print axioms QMCLeafB.CutBudgetM8.asc_le_tsc
#print axioms QMCLeafB.CutBudgetM8.bsc_nonneg
#print axioms QMCLeafB.CutBudgetM8.tsc_succ
#print axioms QMCLeafB.CutBudgetM8.asc_succ
#print axioms QMCLeafB.CutBudgetM8.bsc_succ
#print axioms QMCLeafB.CutBudgetM8.sigmaQ_fr_pvec
#print axioms QMCLeafB.CutBudgetM8.initShapeOf_eq
#print axioms QMCLeafB.CutBudgetM8.iso_step
#print axioms QMCLeafB.CutBudgetM8.tsc_zero
#print axioms QMCLeafB.CutBudgetM8.asc_zero
#print axioms QMCLeafB.CutBudgetM8.Aex_succ
#print axioms QMCLeafB.CutBudgetM8.Aat_eq_Aex
#print axioms QMCLeafB.CutBudgetM8.Aex_wit
#print axioms QMCLeafB.CutBudgetM8.Aex_posQ
#print axioms QMCLeafB.CutBudgetM8.sqQ_pos
#print axioms QMCLeafB.CutBudgetM8.inv_geoQ_pow
#print axioms QMCLeafB.CutBudgetM8.sQ_eq
#print axioms QMCLeafB.CutBudgetM8.cast_dotQ
#print axioms QMCLeafB.CutBudgetM8.cutCR_cd
#print axioms QMCLeafB.CutBudgetM8.cutPR_cd
#print axioms QMCLeafB.CutBudgetM8.sigmaR_cd
#print axioms QMCLeafB.CutBudgetM8.sqrtSigmaR_cd
#print axioms QMCLeafB.CutBudgetM8.engLam_val
#print axioms QMCLeafB.CutBudgetM8.diagSum_cutPR
#print axioms QMCLeafB.CutBudgetM8.sqrt_s_val
#print axioms QMCLeafB.CutBudgetM8.div_sqrt_mul_self
#print axioms QMCLeafB.CutBudgetM8.incr_val
#print axioms QMCLeafB.CutBudgetM8.incr_nonneg
#print axioms QMCLeafB.CutBudgetM8.sqrt_two_M_ge
#print axioms QMCLeafB.CutBudgetM8.sqQ_sum_four
#print axioms QMCLeafB.CutBudgetM8.drift_overflow
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_ge
#print axioms QMCLeafB.CutBudgetM8.hdriftd_false_pinch
#print axioms QMCLeafB.CutBudgetM8.nonempty_relaxCut_of_emptyBody
#print axioms QMCLeafB.CutBudgetM8.capOf_n_two
#print axioms QMCLeafB.CutBudgetM8.rmaxOf_four_eq
#print axioms QMCLeafB.CutBudgetM8.A0_eq_campaign
#print axioms QMCLeafB.CutBudgetM8.normal_budget_eq_trace
#print axioms QMCLeafB.CutBudgetM8.vecMulVec_smul_self
#print axioms QMCLeafB.CutBudgetM8.sigmaQ_smul
#print axioms QMCLeafB.CutBudgetM8.rStep_smul
#print axioms QMCLeafB.CutBudgetM8.Aat_smul
#print axioms QMCLeafB.CutBudgetM8.cutCR_smul
#print axioms QMCLeafB.CutBudgetM8.cutPR_smul
#print axioms QMCLeafB.CutBudgetM8.sigmaR_smul
#print axioms QMCLeafB.CutBudgetM8.lam_smul
#print axioms QMCLeafB.CutBudgetM8.incr_smul
#print axioms QMCLeafB.CutBudgetM8.drift_smul
#print axioms QMCLeafB.CutBudgetM8.drift_smul_cd
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_scaled
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_scaled_ge
#print axioms QMCLeafB.CutBudgetM8.hdriftd_false_pinch_scaled
#print axioms QMCLeafB.OkProdM6.flag_horizon_of_coreDataF
#print axioms QMCLeafB.OkProdM6.exists_mem_of_coreDataF
#print axioms QMCLeafB.OkProdM6.not_coreDataF_of_emptyBody
#print axioms QMCLeafB.OkProdM6.exists_mem_of_residFinite
#print axioms QMCLeafB.OkProdM6.not_residFinite_of_emptyBody
#print axioms QMCLeafB.OkProdM6.anyOk_const_true
#print axioms QMCLeafB.OkProdM6.coreDataF_of_allOk
#print axioms QMCLeafB.OkProdM6.coreDataF_of_okRound
#print axioms QMCLeafB.OkProdM6.coreDataF_drifts_vacuous_of_ok
#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_interval
#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_at_neg_half
#print axioms QMCLeafB.OkProdM6.coreDataF_G₀_at_neg_thousandth
#print axioms QMCLeafB.OkProdM6.neg_thousandth_mem_bracket
#print axioms QMCLeafB.OkProdM6.loopBit_Tbc2_eq_anyOk
#print axioms QMCLeafB.OkProdM6.verdict_true_of_okRound
#print axioms QMCLeafB.OkProdM6.flags_false_below_of_verdict_false
#print axioms QMCLeafB.OkProdM6.cut_rounds_exactly_below_horizon
#print axioms QMCLeafB.OkProdM6.relaxCut_trivial
#print axioms QMCLeafB.OkProdM6.relaxMem_or_cut_vacuous
#print axioms QMCLeafB.OkProdM6.defaultCut_spec
#print axioms QMCLeafB.OkProdM6.defaultCut_satisfies_cutOf_spec
#print axioms QMCLeafB.OkProdM6.margOf_of_mem
#print axioms QMCLeafB.OkProdM6.nrmOf_of_mem
#print axioms QMCLeafB.OkProdM6.flag_cXst_false_iff
#print axioms QMCLeafB.OkProdM6.trace_test_cXst
#print axioms QMCLeafB.OkProdM6.cutOfC_of_mem
#print axioms QMCLeafB.OkProdM6.cutOfC_spec
#print axioms QMCLeafB.OkProdM6.cutOfC_trace
#print axioms QMCLeafB.OkProdM6.qf_transpose
#print axioms QMCLeafB.OkProdM6.qf_transpose_avg
#print axioms QMCLeafB.OkProdM6.symm_avg_shift
#print axioms QMCLeafB.OkProdM6.cutOfC₀_of_mem
#print axioms QMCLeafB.OkProdM6.cutOfC₀_spec
#print axioms QMCLeafB.OkProdM6.cutOfC₀_trace
#print axioms QMCLeafB.OkProdM6.nrmOfC_of_mem
#print axioms QMCLeafB.OkProdM6.margOfC_of_mem
#print axioms QMCLeafB.OkProdM6.nrmOfC_trace
#print axioms QMCLeafB.OkProdM6.margOfC_trace
#print axioms QMCLeafB.OkProdB_M6.coreDataB_of_allOk
#print axioms QMCLeafB.OkProdB_M6.flags_all_false_of_emptyBody
#print axioms QMCLeafB.OkProdB_M6.anyOk_const_false
#print axioms QMCLeafB.OkProdB_M6.hverdict_iff_of_emptyBody
#print axioms QMCLeafB.OkProdB_M6.residFiniteB_okBranch
#print axioms QMCLeafB.VerdictBridge.oracleR_ok_le_fvR
#print axioms QMCLeafB.VerdictBridge.oracleR_ok_dvR
#print axioms QMCLeafB.VerdictBridge.not_relaxMem_diagPinch_of_oracleR_ok
#print axioms QMCLeafB.VerdictBridge.flagOf_false_of_oracleR_ok
#print axioms QMCLeafB.VerdictBridge.paramsKbc2_dq_half_lt_eps
#print axioms QMCLeafB.VerdictBridge.flagOf_false_of_oracleR_ok_kbc2
#print axioms QMCLeafB.VerdictBridge.relaxMem_diagPinch_of_okV
#print axioms QMCLeafB.VerdictBridge.flag_true_of_okV
#print axioms QMCLeafB.VerdictBridge.fvR_le_levelOf_of_mem
#print axioms QMCLeafB.VerdictBridge.pivCut_fst_of_pivAns
#print axioms QMCLeafB.VerdictBridge.oracleV_ok_of_mem
#print axioms QMCLeafB.VerdictBridge.oracleV_ok_of_mem_pivAns
#print axioms QMCLeafB.VerdictBridge.hon_slot
#print axioms QMCLeafB.VerdictBridge.hoff_slot
#print axioms QMCLeafB.VerdictBridge.dqK_def
#print axioms QMCLeafB.VerdictBridge.dqK_pos
#print axioms QMCLeafB.VerdictBridge.dqK_le_four
#print axioms QMCLeafB.VerdictBridge.eps_G₀_eq
#print axioms QMCLeafB.VerdictBridge.wMatrixQ_G₀_zero_zero
#print axioms QMCLeafB.VerdictBridge.wMatrixQ_G₀_one_one
#print axioms QMCLeafB.VerdictBridge.wMatrixQ_G₀_zero_one
#print axioms QMCLeafB.VerdictBridge.wMatrixQ_G₀_one_zero
#print axioms QMCLeafB.VerdictBridge.stMat_wCode
#print axioms QMCLeafB.VerdictBridge.flag_false_at_sId
#print axioms QMCLeafB.VerdictBridge.diagSumV_four'
#print axioms QMCLeafB.VerdictBridge.dvR_sCut
#print axioms QMCLeafB.VerdictBridge.oracleR_sCut
#print axioms QMCLeafB.VerdictBridge.pinchedCut_00
#print axioms QMCLeafB.VerdictBridge.pinchedCut_11
#print axioms QMCLeafB.VerdictBridge.pinchedCut_01
#print axioms QMCLeafB.VerdictBridge.pinchedCut_10
#print axioms QMCLeafB.VerdictBridge.relaxMem_pinchedCut
#print axioms QMCLeafB.VerdictBridge.flag_true_at_sCut
#print axioms QMCLeafB.VerdictBridge.hverdict_of_state_plugs
#print axioms QMCLeafB.VerdictBridge.hverdict_at_roundW
#print axioms QMCLeafB.EmptyBottomM1.flagOf_false_of_emptyBody
#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_of_emptyBody
#print axioms QMCLeafB.EmptyBottomM1.no_horizon_of_emptyBody
#print axioms QMCLeafB.EmptyBottomM1.flagOf_false_at_bottom
#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_at_bottom
#print axioms QMCLeafB.EmptyBottomM1.bottom_mem_bracket
#print axioms QMCLeafB.EmptyBottomM1.not_residFinite_of_dqShallow
#print axioms QMCLeafB.EmptyBottomM1.residFinite_empty_kbc2
#print axioms QMCLeafB.EmptyBottomM1.slice_width_pos
#print axioms QMCLeafB.EmptyBottomM1.no_relaxMem_of_lt
#print axioms QMCLeafB.EmptyBottomM1.not_coreDataF_of_lt
#print axioms QMCLeafB.EmptyBottomM1.bit_false_of_allFalse
#print axioms QMCLeafB.EmptyBottomM1.bit_false_at_bottom
#print axioms QMCLeafB.EmptyBottomM1.solution_of_finite_hypothesis_empty
#print axioms QMCLeafB.RecordsM2.coreDataHb_bit_false_at_bottom
#print axioms QMCLeafB.RecordsM2.bit_false_at_all_bottoms
#print axioms QMCLeafB.CutRecM5.cutC_trace
#print axioms QMCLeafB.CutRecM5.cnC_ne
#print axioms QMCLeafB.CutRecM5.lamC_spec
#print axioms QMCLeafB.CutRecM5.solution_of_dataC
#print axioms QMCLeafB.CutRecM5.solution_statement_of_dataC
#print axioms QMCLeafB.RefutedM3.not_relaxBall_of_emptyBody
#print axioms QMCLeafB.RefutedM3.e₀_ne
#print axioms QMCLeafB.RefutedM3.wMatrix_G₀_00
#print axioms QMCLeafB.RefutedM3.wMatrix_G₀_11
#print axioms QMCLeafB.RefutedM3.wMatrix_G₀_01
#print axioms QMCLeafB.RefutedM3.wMatrix_G₀_10
#print axioms QMCLeafB.RefutedM3.body_empty_G₀
#print axioms QMCLeafB.RefutedM3.bit_false_of_emptyBody


/-! ## 7.  The sign obstruction at a cut round (a falsification receipt)

d7's `hdriftd_of_nonpos_increments` offers a criterion for the accumulated trace budget: **all
weighted diagonal increments nonpositive**.  That criterion is *uninhabitable*, and the reason is
`hlam2`'s `+1`:

At a cut round let `c` be the recorded normal, `λ` the multiplier, `cn = c + λ•u₀` the dilated
normal (so `cn` is the stream the engine actually steps along), `A` the shape, and
`q = ⟪u₀, A⁻¹u₀⟫ > 0`, `a = ⟪c, A⁻¹u₀⟫ = ⟪u₀, A⁻¹c⟫` (the pairing is symmetric).  Then

* `hlam2` reads `2|a| + ⟪c, A⁻¹c⟫ + 9·marg²/(4·rmax²) + 1 ≤ λ·q`, and `⟪c, A⁻¹c⟫ ≥ 0`;
* the round's diagonal increment is `⟪u₀, A⁻¹cn⟫ = a + λ·q` (it is `diagSum` of the recorded
  witness, and `u₀` is the flattened identity).

So the increment is nonpositive exactly when `a ≤ −λq`, i.e. `|a| ≥ λq`; but then `hlam2` gives
`λq ≥ 2λq + 1`, absurd.  **Hence every cut round's increment is strictly positive** — by at least
`λq/2 ≥ 1/2` — and no choice of normal, margin or multiplier can buy a nonpositive increment.

The arithmetic core is proved below in the form the identification produces.  (The transport
`diagSum (cutPR cd j) = a + λq` is the engine's own witness relation plus `u₀`'s definition; the
strict positivity of `q` is `σ > 0`, `RunPartsShallow.sigmaQ_pos_of_wit`.) -/

/-- **No cut round can have a nonpositive diagonal increment.**  `a` is the normal's pairing with
`A⁻¹u₀`, `q` the identity direction's; `hlam2`'s left side is bounded below by `2|a| + 1`. -/
theorem increment_pos_of_depth {a q lam marg rmax : ℝ} (hrmax : 0 < rmax)
    (hlam2 : 2 * |a| + 9 * marg ^ 2 / (4 * rmax ^ 2) + 1 ≤ lam * q) :
    0 < a + lam * q := by
  have hd : (0 : ℝ) ≤ 9 * marg ^ 2 / (4 * rmax ^ 2) :=
    div_nonneg (by positivity) (by positivity)
  have hq : 0 < lam * q := by nlinarith [abs_nonneg a]
  by_contra hneg
  rw [not_lt] at hneg
  have ha : a ≤ 0 := by linarith
  rw [abs_of_nonpos ha] at hlam2
  linarith

#print axioms QMCLeafB.AuditM3.increment_pos_of_depth

/-- The same with the `⟪c, A⁻¹c⟫` term retained: any nonnegative quadratic term keeps the
conclusion, so exact PSD-ness of the shape at the round is not even needed. -/
theorem increment_pos_of_depth' {a q lam marg rmax cc : ℝ} (hrmax : 0 < rmax) (hcc : 0 ≤ cc)
    (hlam2 : 2 * |a| + cc + 9 * marg ^ 2 / (4 * rmax ^ 2) + 1 ≤ lam * q) :
    0 < a + lam * q := by
  have h : 2 * |a| + 9 * marg ^ 2 / (4 * rmax ^ 2) + 1 ≤ lam * q := by linarith
  exact increment_pos_of_depth hrmax h

#print axioms QMCLeafB.AuditM3.increment_pos_of_depth'

end QMCLeafB.AuditM3



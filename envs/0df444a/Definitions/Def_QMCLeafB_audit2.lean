-- Prove2me | Definitions.Def_QMCLeafB_audit2
-- name    : QMCLeafB_audit2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T06:21:07.808676+00:00
-- url     : https://prove2.me/theorems/890aaec4-13f4-43c2-a395-642edc00dc95
-- title:
--   QMCLeafB audit2
-- statement:
--   # `Check_audit2_m5` — phase 22, member m5, direction d6 (`audit2`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_audit_m3
import Definitions.Def_QMCLeafB_refuted_m3
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_crater
/-
# `Check_audit2_m5` — phase 22, member m5, direction d6 (`audit2`)

Audit of the **final** phase-21/22 shapes, with the two non-vacuity anchors the problem names
(`(G₀, −1/2)` and `(G₀, −99999/100000)`), statement locks, an axiom-cone receipt, and — the
decisive audit output — the **split closure** that removes the crater from the empty-body stratum.

What the audit finds, in order:

* §1 **Statement locks.** `LockCoreDataB`/`LockCoreDataG` are hand-written field lists with a
  two-way isomorphism to `EndgameM2.CoreDataB`/`CoreDataG`.  Any drift in a field *type* of the
  final shapes breaks this file's elaboration rather than the packaging step.
* §2 **Anchor 1, `(G₀, −1/2)`** (the ok point): both final shapes are inhabited.
* §3 **Anchor 2, `(G₀, −99999/100000)`** (where phase 20's shape died): interior, and the relaxed
  body is empty in **both** readings — real (`RefutedM3.body_empty_G₀`) and rational
  (`EmptyBodyM5.not_relaxMem_G₀`).  At the leaf's own analytic shape `RunParts`/`RunData` the point
  **is inhabited with no drift at all** for any bit that reads `false` there
  (`RefutedM3.runParts_G₀_of_bitFalse`).  At the *conduit* shape `CoreDataG` the point owes exactly
  `{ok ≡ false below the horizon, the two drift budgets, the bit}` — and the bit is **forced**
  (§3.3), so the crater is the whole content there.
* §4 **The audit's repair, machine-checked.**  `CoreDataG` on the **nonempty** stratum plus the
  program's own read-out/`ok ⇒ member` premises give the leaf's whole `RunParts` obligation over the
  interior bracket (`runParts_of_split`), hence `HdProp`, hence the verbatim `d9f601e5` sentence
  (`solution_of_split`, `solution_statement_of_split`).  The empty stratum needs **no** drift pair,
  so the crater is confined to the stratum where the trace budget is genuinely forced by the
  geometry.  `residSplit_of_bounded` shows nothing is lost: every `ResidB` producer is a
  `ResidSplit` producer.
* §5 **Axiom receipt**: `#print axioms` on every declaration here.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Audit2M5

open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (BundleH ResidH cutOf flagOf)
open QMCLeafB.RecordsM2

/-! ## 1.  Statement locks on the final shapes

The two structures below are the phase-21 residuals **written out by hand** — every field name,
every field type, no `abbrev` anywhere.  `LockCoreDataB.to`/`.of` (and `LockCoreDataG.to`/`.of`)
are the two halves of an isomorphism, so the lock fails unless `EndgameM2.CoreDataB`/`CoreDataG`
have *exactly* these fields at exactly these types.  In particular the horizon bound
`k < P.K * P.m` on every drift slot, the *supplied* cut record `C`, the supplied margin and normal,
and the verdict equation at `K * P.m` are all pinned here. -/

/-- **The hand-written field list of the phase-21 bounded residual.** -/
structure LockCoreDataB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  X : ℕ → List ℚ
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

/-- **`LockCoreDataB → CoreDataB`**: the hand-written fields *are* the residual's fields. -/
def LockCoreDataB.to {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : LockCoreDataB o G t P hn) : QMCLeafB.EndgameM2.CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

/-- **`CoreDataB → LockCoreDataB`**: the reverse half of the lock. -/
def LockCoreDataB.of {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataB o G t P hn) : LockCoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.Audit2M5.LockCoreDataB.to
#print axioms QMCLeafB.Audit2M5.LockCoreDataB.of

/-- **The hand-written field list of the supplier-friendly residual.** -/
structure LockCoreDataG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  X : ℕ → List ℚ
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  ok : ℕ → Bool
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X P.dq k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X P.dq k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  marg : ℕ → ℚ
  hmarg : ∀ k (h : ok k = false), marg k = (C k h).margin
  c : ℕ → Fin (G.n * G.n) → ℚ
  hcEq : ∀ k (h : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k h).normal
  hdriftc : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  hdriftd : ∀ k, ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **`LockCoreDataG → CoreDataG`**. -/
def LockCoreDataG.to {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : LockCoreDataG o G t P hn) : QMCLeafB.EndgameM2.CoreDataG o G t P hn where
  X := D.X
  hsym := D.hsym
  ok := D.ok
  hmem := D.hmem
  C := D.C
  marg := D.marg
  hmarg := D.hmarg
  c := D.c
  hcEq := D.hcEq
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

/-- **`CoreDataG → LockCoreDataG`**. -/
def LockCoreDataG.of {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) : LockCoreDataG o G t P hn where
  X := D.X
  hsym := D.hsym
  ok := D.ok
  hmem := D.hmem
  C := D.C
  marg := D.marg
  hmarg := D.hmarg
  c := D.c
  hcEq := D.hcEq
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.Audit2M5.LockCoreDataG.to
#print axioms QMCLeafB.Audit2M5.LockCoreDataG.of

/-- **The residual *types* themselves, locked by ascription.**  `ResidG` is the supplier-friendly
residual the closing stroke names; the statement below is its hand-written unfolding, so a change of
bracket, or of `CoreDataG`, breaks this declaration. -/
theorem lock_residG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) :
    QMCLeafB.EndgameM2.ResidG o Pfam
      = (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
          -QMCLeafB.EngineRuntime.Rq G ≤ t →
          (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
          QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn) := rfl

#print axioms QMCLeafB.Audit2M5.lock_residG

/-- **The closing stroke's conclusion, locked by ascription**: the verbatim `d9f601e5` sentence. -/
theorem lock_solution_of_supplied
    (H : QMCLeafB.EndgameM2.ResidG
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.EndgameM2.solution_of_supplied H

#print axioms QMCLeafB.Audit2M5.lock_solution_of_supplied

/-! ## 2.  Anchor 1 — the ok point `(G₀, −1/2)`

Both final shapes are inhabited at the ok point (the pinched `Q₀` stream is `ok` at every round below
the horizon, so the drift slots are never read).  Restated here as this file's own receipts. -/

/-- **Anchor 1 at `CoreDataB`.** -/
theorem anchor_ok_coreDataB :
    Nonempty (QMCLeafB.EndgameM2.CoreDataB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataB_G₀_inhabited

/-- **Anchor 1 at `CoreDataG`** (the supplier-friendly residual). -/
theorem anchor_ok_coreDataG :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) :=
  QMCLeafB.EndgameM2.coreDataG_G₀_inhabited

/-- **Anchor 1 through the locked shape**: the inhabitant really is a `LockCoreDataG`. -/
theorem anchor_ok_lockCoreDataG :
    Nonempty (LockCoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) :=
  anchor_ok_coreDataG.elim fun D => ⟨LockCoreDataG.of D⟩

#print axioms QMCLeafB.Audit2M5.anchor_ok_coreDataB
#print axioms QMCLeafB.Audit2M5.anchor_ok_coreDataG
#print axioms QMCLeafB.Audit2M5.anchor_ok_lockCoreDataG

/-! ## 3.  Anchor 2 — the refuted point `(G₀, −99999/100000)`

This is where phase 20's shape died.  The audit records four machine-checked facts about it and then
the gate that localises the crater exactly.

* the point is in the interior bracket (`t₀_mem_bracket`);
* the relaxed body is empty in the **real** reading (`RefutedM3.body_empty_G₀` — the ball lives in
  real matrices) and in the **rational** reading (`EmptyBodyM5.not_relaxMem_G₀`);
* at the leaf's own analytic shape `RunParts`/`RunData` the point is **inhabited with no drift at
  all** (`RefutedM3.runParts_G₀_of_bitFalse`) — for any bit that reads `false` there;
* at the conduit shape `CoreDataG` the point owes `ok ≡ false` below the horizon, both drift budgets
  at every round below the horizon, and the bit — and the bit is **forced**. -/

/-- **`t₀` is inside the interior bracket at `G₀`.** -/
theorem anchor2_interior :
    -QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ ≤ QMCLeafB.EmptyBodyM5.t₀
      ∧ (QMCLeafB.EmptyBodyM5.t₀ : ℝ)
          < -(((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₀_mem_bracket

/-- **The real relaxed body at `(G₀, t₀)` is empty.** -/
theorem anchor2_body_empty (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀)
      ((QMCLeafB.EmptyBodyM5.t₀ : ℝ)
        - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ))
      (((QMCLeafB.EmptyBodyM5.dq₀ : ℚ)) : ℝ) X :=
  QMCLeafB.RefutedM3.body_empty_G₀ X

/-- **No rational centre is a member at `(G₀, t₀)`.** -/
theorem anchor2_no_member (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem
        (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) Q
        (QMCLeafB.EmptyBodyM5.t₀ - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
        QMCLeafB.EmptyBodyM5.dq₀ :=
  QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ Q

/-- **Anchor 2 is inhabited at the leaf's own analytic shape.**  At the empty body `RunParts` holds
with the all-`cut` stream and zero recorded margins: no cut budget, no dilation multiplier, no
pinch, no drift (d6's phase-21 construction). -/
noncomputable def anchor2_runParts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    QMCLeafB.FinalStroke.RunParts o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.RefutedM3.runParts_G₀_of_bitFalse o hbit

/-- **Anchor 2 at the `hd` shape** (`RunData`, what the closing stroke consumes). -/
noncomputable def anchor2_runData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hbit : o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false) :
    QMCLeafB.VerdictSound.RunData o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ :=
  QMCLeafB.RefutedM3.runData_G₀_of_bitFalse o hbit

#print axioms QMCLeafB.Audit2M5.anchor2_interior
#print axioms QMCLeafB.Audit2M5.anchor2_body_empty
#print axioms QMCLeafB.Audit2M5.anchor2_no_member
#print axioms QMCLeafB.Audit2M5.anchor2_runParts
#print axioms QMCLeafB.Audit2M5.anchor2_runData

/-! ### 3.3  The vacuity gate: what the conduit shape owes on an empty body

At an empty relaxed body the member certificate can never hold, so **every** inhabitant of the
conduit shape has `ok ≡ false` below the horizon.  Consequently every round below the horizon
carries a supplied cut record and both drift budgets, and the verdict bit is forced.  Nothing else
is owed by the shape — and nothing less.  That is the exact localisation of the crater. -/

section Gate

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- **`ok` is `false` below the horizon at an empty body.** -/
theorem ok_false_below_of_empty
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) :
    ∀ k, k < P.K * P.m → D.ok k = false := by
  intro k hk
  cases h : D.ok k with
  | false => rfl
  | true => exact absurd (D.hmem k hk h) (hempty (cXst G.n D.X P.dq k))

/-- **The verdict bit is forced at an empty body.** -/
theorem bit_forced_of_empty
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) :
    o G t = false := by
  rw [D.hverdict, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  intro k hk
  exact ok_false_below_of_empty hempty D k hk

/-- **The whole obligation list of the conduit shape at an empty body**: both drift budgets at every
round below the horizon, at no round above it, and the forced bit.  (`hdriftc` is *not* free at a
supplied record — the normal is the record's normal and it is the trace direction the engine reads;
see `EndgameM2.hdriftc_trivial` for the trivial-record case.) -/
theorem drift_pair_of_empty
    (hempty : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) :
    (∀ k, k < P.K * P.m →
      (fun i => ((D.c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.EndgameM2.gStream G P hn D.c D.marg) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n D.X P.dq k)))
        ≤ ((D.marg k : ℚ) : ℝ) / 2)
    ∧ (∀ k, k < P.K * P.m →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.EndgameM2.gStream G P hn D.c D.marg) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n D.X P.dq k)))
        ≤ 0)
    ∧ o G t = false := by
  refine ⟨fun k hk => D.hdriftc k (ok_false_below_of_empty hempty D k hk),
    fun k hk => D.hdriftd k (ok_false_below_of_empty hempty D k hk),
    bit_forced_of_empty hempty D⟩

#print axioms QMCLeafB.Audit2M5.ok_false_below_of_empty
#print axioms QMCLeafB.Audit2M5.bit_forced_of_empty
#print axioms QMCLeafB.Audit2M5.drift_pair_of_empty

end Gate

/-- **The gate, at anchor 2.**  Every inhabitant of the conduit shape at `(G₀, −99999/100000)` has
`ok ≡ false` on the window, both drift budgets on the window, and the bit `false`.  So the *only*
open content of the anchor is the drift pair — the crater. -/
theorem anchor2_gate (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (D : QMCLeafB.EndgameM2.CoreDataG o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) :
    (∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m → D.ok k = false)
    ∧ o QMCLeafB.ResidRefute.G₀ QMCLeafB.EmptyBodyM5.t₀ = false :=
  ⟨ok_false_below_of_empty (fun Q => anchor2_no_member Q) D,
    bit_forced_of_empty (fun Q => anchor2_no_member Q) D⟩

#print axioms QMCLeafB.Audit2M5.anchor2_gate

/-! ## 4.  The audit's repair: the split closure

The phase-21/22 conduit demands the two drift budgets at *every* refuted interior point, and §3.3
shows that on the empty-body stratum that is the whole obligation.  But the leaf does not need it
there: `RefutedM3.runParts_of_emptyBody` produces the **analytic** run record at an empty body with
the all-`cut` stream, zero margins and *no* drift — the ball the cut rounds separate is empty, and
the `ok` branch is vacuous.  So the honest residual is the split one below: `CoreDataG` is demanded
**only off the empty stratum**, and the empty stratum is discharged outright.

`residSplit_of_bounded`/`residSplit_of_supplied` show the split residual is strictly *weaker* than
the phase-21 shapes: every `ResidB`/`ResidG` producer is a split producer.  So nothing banked is
lost, and the crater is confined to the stratum where the trace budget is genuinely forced by the
geometry (`RecordsM2.hdriftd_diagPinch_iff`, m7's `window_forces_engine_trace`). -/

/-- **The split residual**: `CoreDataG` only where the relaxed body is nonempty. -/
abbrev ResidSplit (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((Pfam G).dq : ℚ) : ℝ) X) →
    QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **Conservativity, canonical producer**: every `ResidB` producer is a split producer. -/
def residSplit_of_bounded {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.EndgameM2.ResidB o QMCLeafB.UnionShallow.paramsKbc2) :
    ResidSplit o QMCLeafB.UnionShallow.paramsKbc2 :=
  fun G t hn hlo hhi _ => QMCLeafB.EndgameM2.coreDataG_of_data (H G t hn hlo hhi)

/-- **Conservativity, supplier-friendly producer**: every `ResidG` producer is a split producer. -/
def residSplit_of_supplied {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.EndgameM2.ResidG o QMCLeafB.UnionShallow.paramsKbc2) :
    ResidSplit o QMCLeafB.UnionShallow.paramsKbc2 :=
  fun G t hn hlo hhi _ => H G t hn hlo hhi

#print axioms QMCLeafB.Audit2M5.residSplit_of_bounded
#print axioms QMCLeafB.Audit2M5.residSplit_of_supplied

/-- **The split assembly.**  From the program's own `ok` read-out and its `ok ⇒ member` implication
(both m4's verdict-bridge lane), the real-empty ⇒ no-rational-member bridge, and `CoreDataG` off the
empty stratum, the leaf's whole `RunParts` obligation over the interior bracket follows. -/
def runParts_of_split {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidSplit o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  by_cases hbody : ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      (QMCLeafB.RefutedM3.bit_false_of_emptyBody (hbit G t) (hok G t) (hemptyR G t hbody)) hbody
  · exact QMCLeafB.FlagsM5.runParts_of_bundleH o G t
      (QMCLeafB.UnionShallow.paramsKbc2 G) hn
      (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
      (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
      (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
        (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
      (QMCLeafB.EndgameM2.bundleH_of_dataG
        (QMCLeafB.RecordM2.rmax_pos_paramsKbc2 G hn) (H G t hn hlo hhi hbody))

#print axioms QMCLeafB.Audit2M5.runParts_of_split

/-- The campaign's program bit, exactly as `AssemblyM5.HdProp` writes it. -/
abbrev campaignBit : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
    QMCLeafB.RoundProgram.verdict
    (fun G' _ => QMCLeafB.UnionShallow.Kbc2
      (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
      * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))

/-- **The campaign's whole residual from the split one.**  At the campaign bit, the split residual
plus the verdict-bridge premises give `AssemblyM5.HdProp` — the type the accepted ending
`AssemblyM5.endgame_of_hd` consumes. -/
def hdProp_of_split
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidSplit campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  fun G t hn hlo hhi =>
    runParts_of_split rb cXp hbit hok hemptyR H G t hn hlo hhi

#print axioms QMCLeafB.Audit2M5.hdProp_of_split

/-- **`SolutionStatement` from the split residual** (the shelf's own name for the sentence). -/
theorem solution_statement_of_split
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidSplit campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hdProp_of_split rb cXp hbit hok hemptyR H)

#print axioms QMCLeafB.Audit2M5.solution_statement_of_split

/-- **The verbatim `d9f601e5` sentence from the split residual** (statement locked by ascription). -/
theorem solution_of_split
    (rb : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Bool)
    (cXp : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      campaignBit G t = QMCLeafB.SimLoop.anyOk (rb G t)
        ((QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), rb G t k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXp G t k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hemptyR : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X) →
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (H : ResidSplit campaignBit QMCLeafB.UnionShallow.paramsKbc2) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 :=
  QMCLeafB.AssemblyM5.endgame_of_hd (hdProp_of_split rb cXp hbit hok hemptyR H)

#print axioms QMCLeafB.Audit2M5.solution_of_split

/-- **Anchor 2 through the split closure.**  At `(G₀, −99999/100000)` the split residual's
`CoreDataG` stratum is never reached — the real body is empty — so the split closure owes *nothing*
at the anchor beyond the program's own read-out.  This is the audit's answer to the phase-21 crater
at the refuted point: on the split shape there is no drift obligation there at all. -/
theorem anchor2_split_stratum_vacuous :
    ¬ (∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix QMCLeafB.ResidRefute.G₀)
          ((QMCLeafB.EmptyBodyM5.t₀ : ℝ)
            - (((QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq : ℚ) : ℝ) X) :=
  fun ⟨X, hX⟩ => QMCLeafB.RefutedM3.body_empty_G₀ X hX

#print axioms QMCLeafB.Audit2M5.anchor2_split_stratum_vacuous


/-! ## 5.  The honest limit of the split: the refuted anchor `(G₁, t₁)`

The split of §4 removes the drift obligation only where the relaxed body is **empty**.  It does not
remove it at a refuted point whose body is *nonempty*: `EmptyBodyM5.G₁`'s sliver point
`t₁ = −2 + 71/1520000` carries a rational member (`EmptyBodyM5.body_nonempty_G₁`), yet **no pinched
matrix** is a member there (`EmptyBodyM5.no_pinched_member_G₁`), and every centre the run can query
is pinched (`RecordsM2.cXst_diag`).  So `hmem` is impossible, `ok ≡ false` below the horizon, and the
whole drift pair is owed.  That is the stratum where route (a) (a free stream) or route (b) (a wider
ceiling) must still be settled — the audit's repair confines the crater, it does not remove it. -/

/-- The sliver instance. -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The sliver threshold. -/
abbrev t₁ : ℚ := -(2 : ℚ) + 71 / 1520000

/-- **`(G₁, t₁)` is in the interior bracket.** -/
theorem anchor3_interior :
    -QMCLeafB.EngineRuntime.Rq G₁ ≤ t₁
      ∧ (t₁ : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) :=
  QMCLeafB.EmptyBodyM5.t₁_mem_bracket

/-- **A rational member exists at `(G₁, t₁)`** — the body is *nonempty*. -/
theorem anchor3_body_nonempty :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁)
      QMCLeafB.EmptyBodyM5.Q₁ (t₁ - QMCLeafB.RundataCert.eps G₁)
      (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq :=
  QMCLeafB.EmptyBodyM5.body_nonempty_G₁

/-- **No pinched matrix is a member at `(G₁, t₁)`**, so no centre family the run can query is one. -/
theorem anchor3_no_pinched_member (Q : Matrix (Fin 2) (Fin 2) ℚ)
    (hdiag : ∀ i, Q i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq / 4) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (t₁ - QMCLeafB.RundataCert.eps G₁) (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq :=
  QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hdiag

/-- **The gate at the refuted-nonempty anchor**: any inhabitant of the conduit shape at `(G₁, t₁)`
has `ok ≡ false` on the window and the bit `false`.  So the split residual of §4 demands `CoreDataG`
there and receives the full drift obligation — this is the point where the crater survives. -/
theorem anchor3_gate (o : QuantumMaxCutEnergy.Input → ℚ → Bool) (hn : 2 ≤ G₁.n)
    (D : QMCLeafB.EndgameM2.CoreDataG o G₁ t₁
      (QMCLeafB.UnionShallow.paramsKbc2 G₁) hn) :
    (∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G₁).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G₁).m → D.ok k = false)
    ∧ o G₁ t₁ = false := by
  have hok : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G₁).K
      * (QMCLeafB.UnionShallow.paramsKbc2 G₁).m → D.ok k = false := by
    intro k hk
    cases h : D.ok k with
    | false => rfl
    | true =>
      exact absurd (D.hmem k hk h)
        (anchor3_no_pinched_member (cXst 2 D.X (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq k)
          (fun i => cXst_diag 2 D.X (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq k i))
  refine ⟨hok, ?_⟩
  rw [D.hverdict, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  exact hok

#print axioms QMCLeafB.Audit2M5.anchor3_interior
#print axioms QMCLeafB.Audit2M5.anchor3_body_nonempty
#print axioms QMCLeafB.Audit2M5.anchor3_no_pinched_member
#print axioms QMCLeafB.Audit2M5.anchor3_gate

/-! ## 6.  The audit's verdict: the conduit shapes are vacuous, the interface is not

`CraterM2.not_coreDataG` (direction d1, accepted) refutes the conduit shape at anchor 2 for **every**
verdict bit.  The audit has to draw the consequence the problem's own vacuity bar demands:

* `ResidG` and `ResidB` are **uninhabited** at the campaign family, so `solution_of_supplied`,
  `solution_statement_of_supplied`, `solution_of_bounded`, `solution_of_finite_via_bounded` and the
  locks of §1 are *vacuous*: true, and closing nothing.  (This is the phase-20 defect
  `solution_of_finite_hypothesis_empty` recurring one level up.)
* The leaf's **own** interface `RunParts` is inhabited at *both* anchors — at anchor 1 by the
  ok-anchor conduit (`bundleH_of_dataG` → `runParts_of_bundleH`), at anchor 2 by the empty-body
  construction (`RefutedM3.runParts_of_emptyBody`, no drift).

So the endgame residual must be stated at `RunParts`/`RunData`, not at `CoreDataG`/`CoreDataB`.  My
§4 split is the minimal repair that keeps `CoreDataG` usable where it is *alive* (the nonempty
stratum, ok rounds included) and discharges the empty stratum outright; it is still not enough at the
refuted-**nonempty** sliver `(G₁, t₁)` of §5, where §5 shows the conduit dies by the same argument —
so the refuted production there must also run at `RunParts` level. -/

/-- **The supplier-friendly residual is uninhabited** at the campaign family, for every program bit. -/
theorem supplier_hypothesis_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.EndgameM2.ResidG o QMCLeafB.UnionShallow.paramsKbc2) :=
  fun ⟨H⟩ => QMCLeafB.CraterM2.not_residG o H

/-- **The canonical bounded residual is uninhabited** as well (`ResidB → ResidG`). -/
theorem bounded_hypothesis_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.EndgameM2.ResidB o QMCLeafB.UnionShallow.paramsKbc2) :=
  fun ⟨H⟩ => QMCLeafB.CraterM2.not_residG o (QMCLeafB.EndgameM2.residG_of_bounded H)

/-- **`solution_of_supplied` closes nothing**: its hypothesis type is empty, so the leaf is *not*
closed by it.  (Recorded as the audit's vacuity bar on the phase-22 closing strokes.) -/
theorem solution_of_supplied_is_vacuous :
    ¬ Nonempty (QMCLeafB.EndgameM2.ResidG campaignBit QMCLeafB.UnionShallow.paramsKbc2) :=
  supplier_hypothesis_empty _

#print axioms QMCLeafB.Audit2M5.supplier_hypothesis_empty
#print axioms QMCLeafB.Audit2M5.bounded_hypothesis_empty
#print axioms QMCLeafB.Audit2M5.solution_of_supplied_is_vacuous

/-- **Anchor 1 at the leaf's own interface**: `RunParts` at the ok point (via the ok-anchor conduit,
whose drift slots are vacuous because every round below the horizon is an `ok` round). -/
noncomputable def anchor_ok_runParts :
    QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) :=
  QMCLeafB.FlagsM5.runParts_of_bundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀
    (QMCLeafB.RecordM2.rmax_pos_paramsKbc2 _ QMCLeafB.ResidKill.hnG₀)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one _ QMCLeafB.ResidKill.hnG₀)
    (QMCLeafB.ClosingAssembly.budget_dqShallow _ QMCLeafB.ResidKill.hnG₀
      (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num))
    (QMCLeafB.EndgameM2.bundleH_of_dataG
      (QMCLeafB.RecordM2.rmax_pos_paramsKbc2 _ QMCLeafB.ResidKill.hnG₀)
      (Classical.choice anchor_ok_coreDataG))

#print axioms QMCLeafB.Audit2M5.anchor_ok_runParts

/-- **THE AUDIT'S VERDICT, in one statement.**  The conduit shape `CoreDataG` is inhabited at
anchor 1 and **refuted** at anchor 2 (for every bit); the leaf's own interface `RunParts` is inhabited
at **both** anchors.  Hence the endgame's residual must be repointed to `RunParts`/`RunData`; the
phase-22 shapes cannot carry the leaf. -/
theorem audit_verdict :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀)
    ∧ ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG (fun _ _ => false) QMCLeafB.ResidRefute.G₀
        QMCLeafB.EmptyBodyM5.t₀
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀)
    ∧ Nonempty (QMCLeafB.FinalStroke.RunParts (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀))
    ∧ Nonempty (QMCLeafB.FinalStroke.RunParts (fun _ _ => false) QMCLeafB.ResidRefute.G₀
        QMCLeafB.EmptyBodyM5.t₀
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)) :=
  ⟨anchor_ok_coreDataG, QMCLeafB.CraterM2.not_coreDataG _,
    ⟨anchor_ok_runParts⟩, ⟨anchor2_runParts (fun _ _ => false) rfl⟩⟩

#print axioms QMCLeafB.Audit2M5.audit_verdict

end QMCLeafB.Audit2M5



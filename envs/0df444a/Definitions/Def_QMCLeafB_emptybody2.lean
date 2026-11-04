-- Prove2me | Definitions.Def_QMCLeafB_emptybody2
-- name    : QMCLeafB_emptybody2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:35:10.844578+00:00
-- url     : https://prove2.me/theorems/888a84fc-afec-47c3-b413-c29260e27f14
-- title:
--   QMCLeafB emptybody2
-- statement:
--   # leaf B phase 21 — d1/m5 cross-check of the phase-21 endpoints
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_residb_m7
import Definitions.Def_QMCLeafB_endgame_m2
/-
# leaf B phase 21 — d1/m5 cross-check of the phase-21 endpoints
  (swarm `smw1m5nkm`, member m5, direction d1 `falsify-hcutfin`)

Three independent checks on the two modules that decide the phase:

1. **`d5`'s general refutation instantiated with my numbers.**  `ResidB_M7.not_residFinite_of_emptyBody`
   (m7's "an empty body kills the ∀k shape", proved abstractly: `hcutfin` forces a member at *every*
   `k ≥ K·m`) is applied to `EmptyBodyM5.not_relaxMem_G₀` (my arithmetic: the body of `G₀` is empty
   at `t₀ = -99999/100000`).  Two independent derivations of the same refutation — one from the
   Bool/horizon side, one from the objective floor — agree, so `ResidFinite` is dead at
   `paramsKbc2` for **every** verdict bit.

2. **The weaker "no pinched member" hypothesis is enough** (`EmptyBodyM5.not_residFinite_of_no_pinched_member`
   at `(G₁, t₁)`), i.e. the old shape dies at a point whose relaxed body is nonempty.

3. **Statement lock on the successor** (`ResidB_M7.ResidFiniteB → …`): the verbatim `d9f601e5`
   sentence, and the same conclusion as `QMCLeafB.FinishLine.SolutionStatement`, are checked against
   `solution_of_finiteB`'s actual type by ascription — if the successor's statement had drifted, this
   file would not elaborate.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.EmptyBody2M5

open QuantumMaxCutEnergy

/-! ## 1.  The refutation through m7's general lemma -/

/-- **`ResidFinite` is empty at `paramsKbc2`** — my arithmetic fed into `ResidB_M7`'s general
horizon lemma (an independent route to the same conclusion as `EmptyBodyM5.residFinite_empty`). -/
theorem residFinite_via_residB (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) → False :=
  QMCLeafB.ResidB_M7.not_residFinite_of_emptyBody
    (o := o) (Pfam := QMCLeafB.UnionShallow.paramsKbc2)
    (G := QMCLeafB.EmptyBodyM5.G₀) (t := QMCLeafB.EmptyBodyM5.t₀) (hn := le_refl 2)
    QMCLeafB.EmptyBodyM5.t₀_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₀_mem_bracket.2
    (fun Q => QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ Q)

#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_residB

/-- The same in `Nonempty` form (the shape of the hypothesis of `solution_of_finite`). -/
theorem not_nonempty_residFinite (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite o QMCLeafB.UnionShallow.paramsKbc2) :=
  fun ⟨H⟩ => residFinite_via_residB o H

#print axioms QMCLeafB.EmptyBody2M5.not_nonempty_residFinite

/-- The hypothesis of phase-20's `solution_of_finite` is empty (the same statement from the other
direction, so the two files agree on the exact term). -/
theorem solution_of_finite_hypothesis_empty' :
    ¬ Nonempty (QMCLeafB.RecordsM2.ResidFinite
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :=
  not_nonempty_residFinite _

#print axioms QMCLeafB.EmptyBody2M5.solution_of_finite_hypothesis_empty'

/-! ## 2.  The sliver: the old shape dies at a nonempty body, through the shape of §7.5

`EmptyBodyM5.not_residFinite_of_no_pinched_member` consumes only "no matrix with the campaign's
pinched diagonal `1 - dq/4` is a member", which `(G₁, t₁)` satisfies although its body is nonempty
(`EmptyBodyM5.body_nonempty_G₁`).  Restated here as the `Nonempty ResidFinite → False` implication at
`paramsKbc2`, so the two hypotheses are visible side by side. -/

/-- **The sliver kills `ResidFinite` too** (at `G₁`, `t₁`; body nonempty, no pinched member). -/
theorem residFinite_via_sliver :
    QMCLeafB.RecordsM2.ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
        QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
      QMCLeafB.UnionShallow.paramsKbc2 → False :=
  QMCLeafB.EmptyBodyM5.not_residFinite_of_no_pinched_member
    (Pfam := QMCLeafB.UnionShallow.paramsKbc2)
    (G := QMCLeafB.EmptyBodyM5.G₁) (t := -(2 : ℚ) + 71 / 1520000) (hn := le_refl 2)
    QMCLeafB.EmptyBodyM5.t₁_mem_bracket.1 QMCLeafB.EmptyBodyM5.t₁_mem_bracket.2
    (fun Q hdiag => QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hdiag)

#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_sliver

/-! ## 3.  Statement lock on the successor residual (`ResidB_M7`)

The two ascriptions below are the whole lock: `solution_of_finiteB` must have (i) the verbatim
`d9f601e5` implication type and (ii) the `FinishLine.SolutionStatement` conclusion at the same
hypothesis.  Both are checked by elaboration against the successor's actual type, so a drifted
statement in `Check_residb_m7` would fail here rather than at the coordinator's final assembly. -/

/-- **(i) the verbatim `d9f601e5` shape.** -/
theorem lock_verbatim :
    (QMCLeafB.ResidB_M7.ResidFiniteB
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) →
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
  QMCLeafB.ResidB_M7.solution_of_finiteB

#print axioms QMCLeafB.EmptyBody2M5.lock_verbatim

/-- **(ii) the shelf's own name for the sentence.** -/
theorem lock_statement :
    (QMCLeafB.ResidB_M7.ResidFiniteB
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) →
      QMCLeafB.FinishLine.SolutionStatement :=
  fun H => QMCLeafB.ResidB_M7.solution_of_finiteB H

#print axioms QMCLeafB.EmptyBody2M5.lock_statement

/-! ## 5.  The two successor residuals built in this swarm are the *same* record

`ResidB_M7.CoreDataB` (d5, `Check_residb_m7`) and `EndgameM2.CoreDataB` (d7,
`Check_endgame_m2`) were built independently from the same analysis and have the same five fields
(`X`, `hsym`, `hdriftc`, `hdriftd`, `hverdict`) with the same types.  The conversions below are
field-for-field, so the two assemblies are interchangeable: a producer may target either residual and
the coordinator may close with either stroke.  This removes the only real risk of the duplication
(the two halves diverging). -/

/-- `d5`'s bounded record is `d7`'s. -/
def coreDataB_m7_to_m2 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.ResidB_M7.CoreDataB o G t P hn) :
    QMCLeafB.EndgameM2.CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m7_to_m2

/-- `d7`'s bounded record is `d5`'s. -/
def coreDataB_m2_to_m7 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.EndgameM2.CoreDataB o G t P hn) :
    QMCLeafB.ResidB_M7.CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m2_to_m7

/-- **`d5`'s residual is `d7`'s.** -/
def residB_m7_to_m2 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.ResidB_M7.ResidFiniteB o Pfam) : QMCLeafB.EndgameM2.ResidB o Pfam :=
  fun G t hn hlo hhi => coreDataB_m7_to_m2 (H G t hn hlo hhi)

#print axioms QMCLeafB.EmptyBody2M5.residB_m7_to_m2

/-- **`d7`'s residual is `d5`'s.** -/
def residB_m2_to_m7 {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.EndgameM2.ResidB o Pfam) : QMCLeafB.ResidB_M7.ResidFiniteB o Pfam :=
  fun G t hn hlo hhi => coreDataB_m2_to_m7 (H G t hn hlo hhi)

#print axioms QMCLeafB.EmptyBody2M5.residB_m2_to_m7

/-- **The verbatim sentence from `d5`'s residual via `d7`'s stroke** (cross-firing check). -/
theorem solution_of_finiteB_via_m2
    (H : QMCLeafB.ResidB_M7.ResidFiniteB
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
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
  QMCLeafB.EndgameM2.solution_of_bounded (residB_m7_to_m2 H)

#print axioms QMCLeafB.EmptyBody2M5.solution_of_finiteB_via_m2

/-- **(iii) statement lock on `d7`'s stroke as well.** -/
theorem lock_statement_m2 :
    (QMCLeafB.EndgameM2.ResidB
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.RoundProgram.round
          QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) →
      QMCLeafB.FinishLine.SolutionStatement :=
  fun H => QMCLeafB.EndgameM2.solution_statement_of_bounded H

#print axioms QMCLeafB.EmptyBody2M5.lock_statement
#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m7_to_m2
#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m2_to_m7
#print axioms QMCLeafB.EmptyBody2M5.residB_m7_to_m2
#print axioms QMCLeafB.EmptyBody2M5.residB_m2_to_m7
#print axioms QMCLeafB.EmptyBody2M5.solution_of_finiteB_via_m2
#print axioms QMCLeafB.EmptyBody2M5.lock_statement_m2

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_residB
#print axioms QMCLeafB.EmptyBody2M5.not_nonempty_residFinite
#print axioms QMCLeafB.EmptyBody2M5.solution_of_finite_hypothesis_empty'
#print axioms QMCLeafB.EmptyBody2M5.residFinite_via_sliver
#print axioms QMCLeafB.EmptyBody2M5.lock_verbatim
#print axioms QMCLeafB.EmptyBody2M5.lock_statement
#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m7_to_m2
#print axioms QMCLeafB.EmptyBody2M5.coreDataB_m2_to_m7
#print axioms QMCLeafB.EmptyBody2M5.residB_m7_to_m2
#print axioms QMCLeafB.EmptyBody2M5.residB_m2_to_m7
#print axioms QMCLeafB.EmptyBody2M5.solution_of_finiteB_via_m2
#print axioms QMCLeafB.EmptyBody2M5.lock_statement_m2

end QMCLeafB.EmptyBody2M5



-- Prove2me | Definitions.Def_QMCLeafB_asm35
-- name    : QMCLeafB_asm35
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:52:47.559666+00:00
-- url     : https://prove2.me/theorems/42766abe-4cc3-424d-887a-5b6d6621be2c
-- title:
--   QMCLeafB asm35
-- statement:
--   # `Check_asm35_m4` — phase 35, member m4, direction `assembly35`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sound31
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_hokupper34
import Definitions.Def_QMCLeafB_pbit33
/-
# `Check_asm35_m4` — phase 35, member m4, direction `assembly35`

**The two-horn assembly of leaf B (`d9f601e5`) at the ball-free thin stratum.**

Phase 34 ended with `hfalse` reduced (`QMCLeafB.ThinRec34M4`, `Check_thinrec34_m4`) to ONE
program-free satisfaction problem at bit-`false` points, `ShallowCut`, and with the upper side
reduced (`HokUpper34M8`, `Check_hokupper34_m8`) to the released gate's stream data.  This file wires
both into the verbatim sentence, so that whichever horn is filled the leaf closes by one application.

## The interface

At the campaign program (`o33`, `P33`, `T33` — `Check_pbit33_m6`), phase 33's two slots are

* `hok`    — `o33 G t = true` at an interior bracket point ⟹ a symmetric rational `RelaxMem`
             of the ball relaxation at `(t − eps, dqShallow)`;
* `hfalse` — `o33 G t = false` there ⟹ `RunParts o33 G t (P33 G)`.

`Pbit33.Hd33_of_relaxMem` turns the pair into `Hd33`, and `Pbit33.solution33_statement` turns `Hd33`
into the platform sentence.  So the whole content is the pair.  Here:

* §1 names the pair's sharpest forms: `HokSlot` (`hok` itself, verbatim), `ShallowSlot` (the
  bit-`false` points carry `ThinRec34M4.ShallowCut`) and `CompleteSlot` (the bit reads `true` at
  every NON-EMPTY body — phase 31's `hcomplete`, the alternative horn);
* §2 `hfalseSlot_of_shallow`, `hfalseSlot_of_complete` — the bit-`false` record slot from either
  horn.  The empty stratum is inside both (banked `runParts_of_emptyBody`), so neither horn owes
  anything there;
* §3 the assemblies: `solution_via_shallowCut` (HORN 1, build the record),
  `solution_via_bitComplete` (HORN 2, make the bit true), `solution_of_horns` (either suffices),
  and the released-gate feed `solution_via_releasedGate_shallowCut` /
  `solution_via_releasedGate_bitComplete`, where the upper slot is produced from the gate data by
  `HokUpper34M8.hok_of_releasedGate` and the ONLY analytic hypothesis left is the horn;
* §4 the load-bearing receipts: `not_shallowCut_of_ball` (`ShallowCut` is FALSE at every
  ball-bearing body — so ball-freeness is not decoration, it is necessary, and any proof of
  `ShallowCut` must consume the thin geometry); `not_shallowCut_of_strictBelow` /
  `noStrictBelow_of_shallowCut` (`ShallowCut` is FALSE wherever a real unit-diagonal PSD matrix sits
  strictly below `t − Rq/40000`, so it FORCES `NoStrictBelow`); `shallowCut_of_emptyBody`
  (`ShallowCut` is inhabited at every EMPTY body: identity normal, `del ≡ 0`), hence
  `shallowSlot_iff_nonempty`; `shallowSlot_bit_true_at_ball` /
  `shallowSlot_bit_true_at_strictBelow` / `shallowSlot_bit_false_thin` (a filled HORN 1 forces the
  bit `true` at ball bodies and at strict-below points — the bit-false points of a filled HORN 1 are
  exactly nonempty ∧ ball-free ∧ `NoStrictBelow`, agreeing with m3's `bit_true_of_ball`);
  `bodyEmpty_eq_published` (`Iff.rfl`);
* §4b `ShallowSlotThin` (the stratum-scoped slot: nonempty AND non-ball-bearing) and
  `shallowSlot_iff_thin` — the two forms of the residual agree, given the program-level fact that the
  bit reads `true` at ball-bearing interior points (which `shallowSlot_bit_true_at_ball` derives from
  the slot itself); `solution_via_thinSlot` is the assembly in the scoped form;
* §4d `member_of_horns` — HORN 2 + the upper slot force a relaxed member at every nonempty interior
  point, i.e. HORN 2 is a completeness demand on the gate at every visited centre (contrast:
  `HokUpper34M8.campaign_witness_rejected`, the sum gate's rejection of the canonical member);
* §4e `sigmaQ_NormalCut_pos` (σ > 0 at every round of a `NormalCut`, so the ledger is exactly
  `del ≤ rmax·√σ`), `shallowCut_of_support` (SUPPORTING cuts give `ShallowCut` with `del ≡ 0` — the
  ledger never binds), `SupportSlot` + `shallowSlot_of_support` + `solution_via_support`: the
  sharpest assembly, whose whole analytic content is "the accumulated centre never enters the
  relaxation below the horizon" (m3's F4 form, re-derived independently here);
* §5 `solutionLock_via_shallowCut` / `solutionLock_via_bitComplete` / `solutionLock_direct` at the
  fuel exponent `k = 5`, in `FinishLine.SolutionStatement` form.

**The exact residual** (nothing else is owed): `ShallowSlot` at `o33`/`P33` — at a bit-`false`
interior point with a NON-EMPTY (hence, by §4, ball-free) relaxed body, a nonzero rational normal
stream whose accumulated centres stay within `rmax·√σ` of a supporting hyperplane of the relaxation
at every round below the horizon — or else `CompleteSlot`, the bit reading `true` at every
nonempty body.  §3 shows either closes the leaf; §4 shows neither can be weakened.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
every `#print axioms` below is exactly `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace Asm35M4

open Matrix
open QuantumMaxCutEnergy

/-! ## 1.  The three slots, in their sharpest forms -/

/-- The campaign program's bit (`Check_pbit33_m6`). -/
abbrev o33 : QuantumMaxCutEnergy.Input → ℚ → Bool := QMCLeafB.Pbit33.o33

/-- The campaign parameter family (`dq = dqShallow`, `rmax = rmaxOf (n·n)`, `m = mHalve (n·n)`,
`K = 4·Kbc`, `K·m = T33`). -/
abbrev P33 : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.Pbit33.P33

/-- **The upper slot (`hok`), verbatim**: at a bit-`true` interior bracket point, a symmetric
rational member of the ball relaxation at `(t − eps, dqShallow)`.  This is exactly
`Pbit33.Hd33_of_relaxMem`'s first argument, i.e. `HokUpper34M8.HokShape` along the bracket. -/
def HokSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o33 G t = true →
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

/-- **HORN 1 — the analytic obligation, at its exact domain**: the shallow-cut datum at every
bit-`false` interior bracket point.  `ShallowCut` (`Check_thinrec34_m4` §5) is the program-free
statement that a nonzero rational normal stream keeps the accumulated centre `Cat k` within
`rmax·√σ_k` of a supporting hyperplane of the whole relaxation, with the rational depth check
`del k² ≤ rmax²·σ_k`.  No emptiness hypothesis: at an empty body the slot is free (§4,
`shallowCut_of_emptyBody`), so nothing is lost by demanding it everywhere. -/
def ShallowSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o33 G t = false →
    QMCLeafB.ThinRec34M4.ShallowCut G t (P33 G) hn

/-- **HORN 2 — the programme-side alternative**: the bit reads `true` at every interior bracket
point whose relaxed body is NON-EMPTY.  This is phase 31's `hcomplete` (completeness of the ok
test), localized to the interior by the bracket's own top slice.  At an empty body nothing is
asked. -/
def CompleteSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G) → o33 G t = true

/-- The body-emptiness predicate of `ThinRec34M4` IS the published `AsmM8.EmptyBody` (both are
`∀ X, ¬ relaxBodyLE (wMatrix G) (t − Rq/40000) dq X`), so slots stated against either agree. -/
theorem bodyEmpty_eq_published {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} :
    QMCLeafB.ThinRec34M4.BodyEmpty G t P ↔ AsmM8.EmptyBody G t P :=
  Iff.rfl

#print axioms Asm35M4.bodyEmpty_eq_published

/-! ## 2.  The bit-`false` record slot from either horn

`ThinRec34M4.runParts_false_iff_bodyRec` says a record at a bit-`false` point is exactly the
program-free class `BodyRec`, and `bodyRec_of_shallowCut` says `ShallowCut` inhabits it.  So HORN 1
supplies the record slot outright; HORN 2 kills the slot's domain instead, leaving only the empty
stratum, which the banked `runParts_of_emptyBody` covers. -/

/-- **HORN 1 gives the record slot.** -/
noncomputable def hfalseSlot_of_shallow (H : ShallowSlot) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → QMCLeafB.FinalStroke.RunParts o33 G t (P33 G) := by
  intro G t hn hlo hlt hb
  exact Classical.choice
    ((QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec (P := P33 G) hb).2
      (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (H G t hn hlo hlt hb)))

#print axioms Asm35M4.hfalseSlot_of_shallow

/-- **HORN 2 gives the record slot** (empty bodies are the banked free case). -/
noncomputable def hfalseSlot_of_complete (H : CompleteSlot) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o33 G t = false → QMCLeafB.FinalStroke.RunParts o33 G t (P33 G) := by
  intro G t hn hlo hlt hb
  by_cases he : QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G)
  · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P33 G) hn hb he
  · exact absurd (H G t hn hlo hlt he) (by rw [hb]; simp)

#print axioms Asm35M4.hfalseSlot_of_complete


/-! ## 3.  The assemblies -/

/-- **HORN 1 ASSEMBLY — the leaf from {upper slot} + {shallow-cut slot}.**
The verbatim `d9f601e5` sentence, at the campaign program `o33`/`P33`.  The two hypotheses are
exactly `Pbit33.Hd33_of_relaxMem`'s two slots; the first is produced from the released gate's stream
data by `HokUpper34M8.hok_of_releasedGate` (see `solution_via_releasedGate_shallowCut` below), so
`ShallowSlot` is the whole analytic content. -/
theorem solution_via_shallowCut (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlot) (Hsc : ShallowSlot) :
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
  QMCLeafB.Pbit33.solution33_statement k hk
    (QMCLeafB.Pbit33.Hd33_of_relaxMem hok (hfalseSlot_of_shallow Hsc))

#print axioms Asm35M4.solution_via_shallowCut

/-- **HORN 2 ASSEMBLY — the leaf from {upper slot} + {bit completeness}.**
The same sentence with the programme-side hypothesis: the bit reads `true` wherever the body is
nonempty, so the record slot's domain is only the empty stratum (banked free). -/
theorem solution_via_bitComplete (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlot) (Hc : CompleteSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution33 k hk
    (QMCLeafB.Pbit33.Hd33_of_relaxMem hok (hfalseSlot_of_complete Hc))

#print axioms Asm35M4.solution_via_bitComplete

/-- **EITHER HORN CLOSES THE LEAF.**  The second component of the residual is a disjunction: a
shallow-cut stream at the bit-`false` points, or a bit that reads `true` at every nonempty body.
Whichever the swarm fills, the leaf is one application away. -/
theorem solution_of_horns (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlot) (H : ShallowSlot ∨ CompleteSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  H.elim (fun hsc => QMCLeafB.FinishLine.solutionStatement_iff_wMatrix.2
      (solution_via_shallowCut k hk hok hsc))
    (fun hc => solution_via_bitComplete k hk hok hc)

#print axioms Asm35M4.solution_of_horns

/-! ### 3b.  Feeding the upper slot from the released gate

`HokUpper34M8.hok_of_releasedGate` produces `HokShape` from the released gate's stream data at any
programme: `dvR s ≤ dq/4` (a sum gate, sound per coordinate by
`HokUpper34M8.abs_stMat_diag_le_dvR`), the pivot's PSD answer, the objective clause
`fvR ≤ stT − epsOf + dq/2`, and the level/tolerance coherence.  Substituting it here leaves the
horn as the only analytic hypothesis — every remaining hypothesis of the theorem below is a fact
about the PROGRAMME (which accumulator/pivot/test the round runs), not about the leaf's geometry. -/

/-- The released gate's stream data feeds the upper slot. -/
theorem hokSlot_of_releasedGate
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o33 G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stN (σ G t k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) j i))
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ G t k)), acc)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.dvR (σ G t k) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.fvR (σ G t k)
        ≤ QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
          + QMCLeafB.OkLower.dqOf (σ G t k) / 2)
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.OkLower.dqOf (σ G t k) = QMCLeafB.RundataParams.dqShallow G) :
    HokSlot :=
  HokUpper34M8.hok_of_releasedGate o33 okT σ T hRq hbit hdat hpiv hdv hfv hlev hdqv

#print axioms Asm35M4.hokSlot_of_releasedGate

/-- **THE RESIDUAL, AS ONE THEOREM**: the verbatim sentence from the released gate's stream data
(the programme's own facts) and HORN 1.  `ShallowSlot` is the only hypothesis that is not a fact
about which program is running. -/
theorem solution_via_releasedGate_shallowCut (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o33 G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stN (σ G t k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) j i))
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ G t k)), acc)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.dvR (σ G t k) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.fvR (σ G t k)
        ≤ QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
          + QMCLeafB.OkLower.dqOf (σ G t k) / 2)
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.OkLower.dqOf (σ G t k) = QMCLeafB.RundataParams.dqShallow G)
    (Hsc : ShallowSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_horns k hk
    (hokSlot_of_releasedGate okT σ T hRq hbit hdat hpiv hdv hfv hlev hdqv) (Or.inl Hsc)

#print axioms Asm35M4.solution_via_releasedGate_shallowCut


/-! ### 3c.  The programme-agnostic forms

The two assemblies above are stated at m6's campaign program `o33`/`P33`, because that is the program
whose bit is `Automatic.Poly`-proved (`Pbit33.ho33`) and whose count side is a theorem.  When the bit
is re-pointed (a released-gate `oRel`, or any repaired program), only `Automatic.Poly` of the new bit
is owed — the analysis does not change.  These two forms are the same assemblies at an ARBITRARY bit
`o` and parameter family `P`, so a re-pointed program plugs in by supplying `ho`/`htop` and the horn.
They are built on the published stroke `Pbit33.solution_of_runPartsFamily_bracket`, not on any
`Solutions.*` module. -/

/-- The shallow-cut family at an arbitrary bit and parameter family. -/
def ShallowSlotG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false →
    QMCLeafB.ThinRec34M4.ShallowCut G t (P G) hn

/-- The completeness family at an arbitrary bit and parameter family. -/
def CompleteSlotG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P G) → o G t = true

/-- **HORN 1 at an ARBITRARY programme**: the verbatim leaf's `SolutionStatement` from the bit's
`Poly` proof, its top slice, the upper slot and the shallow-cut family.  Nothing about the round, the
count, the size ledger or the test coherence appears. -/
theorem solution_of_two_slots_shallowCut
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (Hsc : ShallowSlotG o P) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution_of_runPartsFamily_bracket o P ho htop
    (fun G t hn hlo hlt => by
      by_cases hb : o G t = true
      · exact AsmM8.runParts_of_member (P G) hn (hKm G) hb
          (Asm2M8.memberAt_of_relaxMem (G := G) (t := t) hn ⟨hlo, hlt⟩ (hok G t hn hlo hlt hb))
      · have hf : o G t = false := by
          cases h : o G t with
          | false => rfl
          | true => exact absurd h hb
        exact Classical.choice
          ((QMCLeafB.ThinRec34M4.runParts_false_iff_bodyRec (P := P G) (o := o) hf).2
            (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn (Hsc G t hn hlo hlt hf))))

#print axioms Asm35M4.solution_of_two_slots_shallowCut

/-- **HORN 2 at an ARBITRARY programme.** -/
theorem solution_of_two_slots_complete
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : OAI.MetricKMedian.Binary.Automatic.Poly
      (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2))
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (Hc : CompleteSlotG o P) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution_of_runPartsFamily_bracket o P ho htop
    (fun G t hn hlo hlt => by
      by_cases hb : o G t = true
      · exact AsmM8.runParts_of_member (P G) hn (hKm G) hb
          (Asm2M8.memberAt_of_relaxMem (G := G) (t := t) hn ⟨hlo, hlt⟩ (hok G t hn hlo hlt hb))
      · have hf : o G t = false := by
          cases h : o G t with
          | false => rfl
          | true => exact absurd h hb
        by_cases he : QMCLeafB.ThinRec34M4.BodyEmpty G t (P G)
        · exact QMCLeafB.RefutedM3.runParts_of_emptyBody G t (P G) hn hf he
        · exact absurd (Hc G t hn hlo hlt he) (by rw [hf]; simp))

#print axioms Asm35M4.solution_of_two_slots_complete

/-! ## 4.  The load-bearing receipts

`ShallowCut` is not vacuous and not a formality: it is FALSE at every ball-bearing body (so
ball-freeness is a NECESSARY hypothesis of any proof of it, and the thin geometry must be
consumed), it is INHABITED at every empty body (so the residual slot cannot be dismissed on the
empty stratum), and a filled HORN 1 forces the bit `true` at ball bodies — the same consequence m3's
`bit_true_of_ball` draws from the record family, which is the consistency check between the two
lanes. -/

/-- **`ShallowCut` FAILS at ball-bearing bodies.**  Composing the sufficient half
(`bodyRec_of_shallowCut`) with the banked volume obstruction (`not_bodyRec_of_ball`) — the record a
shallow-cut stream would produce cannot exist once the body carries the campaign ball.  So every
proof of `ShallowCut` must use the ball-free thin geometry; conversely the residual is confined to
the ball-free stratum exactly as phase 24's dreg analysis says. -/
theorem not_shallowCut_of_ball {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1))) ⊆ QMCLeafB.BallM2.runBall G t P) :
    ¬ QMCLeafB.ThinRec34M4.ShallowCut G t P hn :=
  fun H => QMCLeafB.ThinRec34M4.not_bodyRec_of_ball hn hball
    (QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn H)

#print axioms Asm35M4.not_shallowCut_of_ball

/-- **A filled HORN 1 forces the bit `true` at ball bodies.**  Any point where the body carries the
campaign ball cannot be a bit-`false` point of a successful shallow-cut family, so the family
localizes itself to the ball-free stratum.  This is the HORN 1 counterpart of
`Sub34M3.bit_true_of_ball` (which says the same for the record family): the two lanes agree about
which stratum is left. -/
theorem shallowSlot_bit_true_at_ball (H : ShallowSlot)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ}
    (hball : QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((((P33 G).dq : ℚ) : ℝ) / (8 * ((((P33 G).cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P33 G)) :
    o33 G t = true := by
  by_contra hb
  have hbf : o33 G t = false := by
    cases h : o33 G t with
    | false => rfl
    | true => exact absurd h hb
  exact not_shallowCut_of_ball hn hball (H G t hn hlo hlt hbf)

#print axioms Asm35M4.shallowSlot_bit_true_at_ball

/-- **`ShallowCut` is INHABITED at every EMPTY body** (the identity direction, zero margins: the
separation is vacuous).  So the residual slot cannot be dismissed as unsatisfiable on the empty
stratum, and by `shallowSlot_bit_true_at_ball` its only live stratum is the ball-free nonempty one —
the phase-24 dreg band and nothing else. -/
theorem shallowCut_of_emptyBody {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hempty : QMCLeafB.ThinRec34M4.BodyEmpty G t P) :
    QMCLeafB.ThinRec34M4.ShallowCut G t P hn := by
  have hN2 : 2 ≤ G.n * G.n := by
    have := Nat.mul_le_mul hn hn
    omega
  have hnpos : 0 < G.n := by omega
  have hNpos : 0 < G.n * G.n := Nat.mul_pos hnpos hnpos
  -- the constant all-ones normal stream
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ _ => 1 with hcdef
  have hc : ∀ k, c k ≠ 0 := by
    intro k h
    have := congrFun h ⟨0, hNpos⟩
    simp [hcdef] at this
  have hwit := QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc
  have hρ0 : ∀ k, 0 ≤ (QMCLeafB.RunPartsDilate.runCut G P hn c hc k).rho := by
    intro k
    rw [QMCLeafB.RunPartsDilate.runCut_rho]
    exact P.hrmax
  have hσpos : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (c k)
      ((QMCLeafB.ThinRec34M4.NormalCut G P hn c hc k).p) :=
    QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit (N := G.n * G.n) hN2
      (A0 := QMCLeafB.RunPartsDilate.A0P G P)
      (cd := QMCLeafB.ThinRec34M4.NormalCut G P hn c hc)
      (QMCLeafB.RunPartsDilate.A0P_posDef G P) hwit hρ0 hc
  refine ⟨c, hc, fun _ => 0, ?_, ?_, ?_⟩
  · intro k _; exact le_refl (0 : ℚ)
  · intro k
    have h := hσpos k
    nlinarith [P.hrmax, sq_nonneg P.rmax]
  · intro k _ z hz
    have hz' : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((P.dq : ℚ) : ℝ)) (QMCLeafB.Boundary.unflat z) := by
      have h := hz
      rw [QMCLeafB.ThinRec34M4.relaxBallP, QMCLeafB.Boundary.relaxBall,
        Set.mem_ofPred_eq] at h
      exact h.1
    exact absurd hz' (hempty (QMCLeafB.Boundary.unflat z))

#print axioms Asm35M4.shallowCut_of_emptyBody

/-- **The residual is owed only at NON-EMPTY bodies.**  `ShallowSlot` is equivalent to its
nonempty-localized form: the empty stratum is free (`shallowCut_of_emptyBody`), so the two statements
about the residual — "at every bit-`false` interior point" and "at every bit-`false` interior point
with a nonempty body" — are the same obligation. -/
theorem shallowSlot_iff_nonempty :
    ShallowSlot ↔
      (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
        -QMCLeafB.EngineRuntime.Rq G ≤ t →
        (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
        o33 G t = false →
        ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G) →
        QMCLeafB.ThinRec34M4.ShallowCut G t (P33 G) hn) := by
  constructor
  · intro H G t hn hlo hlt hb _
    exact H G t hn hlo hlt hb
  · intro H G t hn hlo hlt hb
    by_cases he : QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G)
    · exact shallowCut_of_emptyBody hn he
    · exact H G t hn hlo hlt hb he

#print axioms Asm35M4.shallowSlot_iff_nonempty

/-- **HORN 2 ASSEMBLY at the released gate**: the verbatim leaf from the gate's stream data and the
bit reading `true` at every nonempty body.  This is the alternative the phase-24/32 lanes favour
(the search-side repair, `hcomplete`); compare its cost with `solution_via_releasedGate_shallowCut`,
whose analytic hypothesis is a trajectory (a stream of normals) rather than a decision procedure for
body emptiness. -/
theorem solution_via_releasedGate_bitComplete (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      o33 G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
    (hdat : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stN (σ G t k) = G.n ∧
      G.n ≤ (QMCLeafB.RoundProgram.stA (σ G t k)).length ∧
      G.n ≤ (QMCLeafB.RoundProgram.stX (σ G t k)).length ∧
      QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stA (σ G t k))
        = QMCLeafB.Finalization.wMatrixQ G ∧
      (∀ i j, QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) i j
        = QMCLeafB.StateDiag.stMat G.n (QMCLeafB.RoundProgram.stX (σ G t k)) j i))
    (hpiv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true → ∃ acc : QMCLeafB.PivotProgram.Acc,
      (QMCLeafB.PivotProgram.runPiv
        (QMCLeafB.RoundProgram.toRows (G.n, QMCLeafB.RoundProgram.stX (σ G t k)), acc)).1 = false)
    (hdv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.dvR (σ G t k) ≤ QMCLeafB.RundataParams.dqShallow G / 4)
    (hfv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.fvR (σ G t k)
        ≤ QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
          + QMCLeafB.OkLower.dqOf (σ G t k) / 2)
    (hlev : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.RoundProgram.stT (σ G t k) - QMCLeafB.RoundT.epsOf (σ G t k)
        = t - QMCLeafB.RundataCert.eps G)
    (hdqv : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), k < T G →
      okT (σ G t k) = true →
      QMCLeafB.OkLower.dqOf (σ G t k) = QMCLeafB.RundataParams.dqShallow G)
    (Hc : CompleteSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_horns k hk
    (hokSlot_of_releasedGate okT σ T hRq hbit hdat hpiv hdv hfv hlev hdqv) (Or.inr Hc)

#print axioms Asm35M4.solution_via_releasedGate_bitComplete



/-- **The STRICT-BELOW localization.**  If a real unit-diagonal PSD matrix sits strictly below the
programme's level `t − Rq/40000`, the campaign ball is inside the run's relaxation
(`Sound31.ball_of_strict_below`), so by `not_shallowCut_of_ball` no shallow-cut stream can exist at
that point.  Equivalently: `ShallowCut` FORCES `NoStrictBelow G t` — every real unit-diagonal PSD
matrix at or above the level.  So a proof of HORN 1 may not start from a strict-below witness: the
residual's donor set is exactly

    nonempty  ∧  NoStrictBelow  ∧  ball-free

The same statement from the record side is `Check_fal34_m6`'s
`noStrictBelow_of_bit_false_record`; this is its HORN 1 counterpart. -/
theorem not_shallowCut_of_strictBelow {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ¬ QMCLeafB.ThinRec34M4.ShallowCut G t P hn := by
  obtain ⟨Z, hZ, hlt⟩ := hstrict
  exact not_shallowCut_of_ball hn (QMCLeafB.Sound31.ball_of_strict_below P hZ hlt)

#print axioms Asm35M4.not_shallowCut_of_strictBelow

/-- **`ShallowCut` implies `NoStrictBelow`** — the strict-below localization in the form a producer
consumes. -/
theorem noStrictBelow_of_shallowCut {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (H : QMCLeafB.ThinRec34M4.ShallowCut G t P hn) :
    ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ, QMCLeafB.AnswerProducer.IsUnitDiagPSD Z →
      (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
        ≤ (QMCLeafB.wMatrix G * Z).trace := by
  intro Z hZ
  by_contra hcon
  rw [not_le] at hcon
  exact not_shallowCut_of_strictBelow hn ⟨Z, hZ, hcon⟩ H

#print axioms Asm35M4.noStrictBelow_of_shallowCut


/-- **A filled HORN 1 forces the bit `true` at every strict-below point** (contrapositive of
`not_shallowCut_of_strictBelow`).  So the shallow-cut lane does NOT need the programme to be
repaired on the strict stratum: it supplies that half of completeness itself. -/
theorem shallowSlot_bit_true_at_strictBelow (H : ShallowSlot)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hstrict : ∃ Z : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD Z ∧
        (QMCLeafB.wMatrix G * Z).trace
          < (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    o33 G t = true := by
  by_contra hb
  have hbf : o33 G t = false := by
    cases h : o33 G t with
    | false => rfl
    | true => exact absurd h hb
  exact not_shallowCut_of_strictBelow hn hstrict (H G t hn hlo hlt hbf)

#print axioms Asm35M4.shallowSlot_bit_true_at_strictBelow

/-- **WHERE A FILLED HORN 1 LEAVES THE BIT `false`** — nowhere except the thin stratum: at every
interior point where the bit reads `false`, the body is nonempty (else the slot is free anyway), it
carries no campaign ball, and no real unit-diagonal PSD matrix sits strictly below the level.  So
HORN 1's own domain is the phase-24 dreg band and its non-strict neighbourhoods, and the lane demands
nothing of the programme outside that band. -/
theorem shallowSlot_bit_false_thin (H : ShallowSlot)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbf : o33 G t = false)
    {X₀ : Matrix (Fin G.n) (Fin G.n) ℝ} :
    ¬ (QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((((P33 G).dq : ℚ) : ℝ) / (8 * ((((P33 G).cAq : ℚ) : ℝ) + 1)))
        ⊆ QMCLeafB.BallM2.runBall G t (P33 G)) ∧
      ∀ Z : Matrix (Fin G.n) (Fin G.n) ℝ, QMCLeafB.AnswerProducer.IsUnitDiagPSD Z →
        (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)
          ≤ (QMCLeafB.wMatrix G * Z).trace :=
  ⟨fun hball => Bool.false_ne_true (hbf.symm.trans (shallowSlot_bit_true_at_ball H hn hlo hlt hball)),
   noStrictBelow_of_shallowCut (P := P33 G) hn (H G t hn hlo hlt hbf)⟩

#print axioms Asm35M4.shallowSlot_bit_false_thin

/-! ## 4b.  The stratum-scoped slot, and why it is the same obligation

m3's phase-35 audit (f2, `Check_fa35_m3`) observes that a family demanding `ShallowCut` at *every*
bit-`false` point is unsatisfiable unless the program reads `true` at ball-bearing points — where by
§4 no record (hence no shallow-cut datum) can exist.  That is a fact about the PROGRAM, not about the
analysis, and here it is made explicit: the stratum-scoped slot (`ShallowSlotThin`) plus the bit's
behaviour on ball-bearing points is EQUIVALENT to `ShallowSlot`.  So a producer may work with the
scoped form and the assembly loses nothing. -/

/-- The body carries the campaign ball at `(G,t)` (the "fat" stratum, where no record exists). -/
def BallBearing (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
      ((((P33 G).dq : ℚ) : ℝ) / (8 * ((((P33 G).cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t (P33 G)

/-- **The stratum-scoped slot**: `ShallowCut` at bit-`false` interior points with a NON-EMPTY,
NON-ball-bearing body — exactly the phase-24/25 dreg stratum. -/
def ShallowSlotThin : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o33 G t = false →
    ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G) →
    ¬ BallBearing G t →
    QMCLeafB.ThinRec34M4.ShallowCut G t (P33 G) hn

/-- **The two forms of the residual agree.**  `ShallowSlot` is equivalent to its stratum-scoped form
plus the program-level fact that the bit reads `true` at ball-bearing interior points — the fact any
correct fill must have (`shallowSlot_bit_true_at_ball` derives it from `ShallowSlot` itself, and
`Sub34M3.bit_true_of_ball` from a record family). -/
theorem shallowSlot_iff_thin :
    ShallowSlot ↔
      (ShallowSlotThin ∧
        ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
          -QMCLeafB.EngineRuntime.Rq G ≤ t →
          (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
          BallBearing G t → o33 G t = true) := by
  constructor
  · intro H
    refine ⟨fun G t hn hlo hlt hb _ _ => H G t hn hlo hlt hb, fun G t hn hlo hlt hball => ?_⟩
    obtain ⟨X₀, hball'⟩ := hball
    exact shallowSlot_bit_true_at_ball H hn hlo hlt hball'
  · rintro ⟨Hthin, Hball⟩ G t hn hlo hlt hb
    by_cases he : QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G)
    · exact shallowCut_of_emptyBody hn he
    · by_cases hball : BallBearing G t
      · exact absurd (Hball G t hn hlo hlt hball) (by rw [hb]; simp)
      · exact Hthin G t hn hlo hlt hb he hball

#print axioms Asm35M4.shallowSlot_iff_thin

/-- **HORN 1 from the stratum-scoped slot.**  The assembly with `ShallowSlotThin` (plus the program's
own ball-stratum bit behaviour) in place of the family slot. -/
theorem solution_via_thinSlot (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlot) (Hthin : ShallowSlotThin)
    (Hball : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      BallBearing G t → o33 G t = true) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_via_shallowCut k hk hok ((shallowSlot_iff_thin).2 ⟨Hthin, Hball⟩)

#print axioms Asm35M4.solution_via_thinSlot


/-! ## 4e.  The sharpest form of the residual: supporting cuts, `del ≡ 0`

m3's phase-35 audit (f2, §F4) observes that a SUPPORTING cut — one whose hyperplane passes through the
accumulated centre with the whole relaxation on the far side — satisfies the shallow-cut inequality
with margin `del ≡ 0`, so the ledger `del² ≤ rmax²σ` does not bind and `ShallowCut` reduces to
keeping the accumulated centre OUT of the relaxation at every round below the horizon.  That form is
re-derived here (independently of m3's module, whose mirror would collide with
`Solutions.Check_thinrec34_m4`) and wired to the leaf, so the residual can be stated as a purely
geometric trajectory condition. -/

/-- **`σ_k > 0` at every round of a `NormalCut` transcript** — so the `σ ≤ 0` branch of the ledger is
vacuous for the canonical transcript (independently of m3's `sigmaQ_NormalCut_pos`). -/
theorem sigmaQ_NormalCut_pos {G : QuantumMaxCutEnergy.Input}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0) (k : ℕ) :
    0 < QMCLeafB.EngineIterates.sigmaQ (c k)
      ((QMCLeafB.ThinRec34M4.NormalCut G P hn c hc k).p) := by
  have hN2 : 2 ≤ G.n * G.n := by
    have := Nat.mul_le_mul hn hn; omega
  refine QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit (N := G.n * G.n) hN2
    (A0 := QMCLeafB.RunPartsDilate.A0P G P)
    (cd := QMCLeafB.ThinRec34M4.NormalCut G P hn c hc)
    (QMCLeafB.RunPartsDilate.A0P_posDef G P)
    (QMCLeafB.RunPartsDilate.runCut_wit G P hn c hc) ?_ hc k
  intro j
  simpa [QMCLeafB.ThinRec34M4.NormalCut, QMCLeafB.RunPartsDilate.runCut_rho] using P.hrmax

#print axioms Asm35M4.sigmaQ_NormalCut_pos

/-- **SUPPORTING CUTS GIVE `ShallowCut` WITH `del ≡ 0`.**  If a nonzero normal stream's cuts all
support the relaxation at their own accumulated centre, the shallow-cut datum exists with the margin
identically zero — the ledger never binds, and `rmax` enters nowhere. -/
theorem shallowCut_of_support {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0)
    (hsupp : ∀ k, k < P.K * P.m → ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P,
      0 ≤ QMCLeafB.EngineIterates.cutCR (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k
        ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
            (0 : Fin (G.n * G.n) → ℝ) (QMCLeafB.ThinRec34M4.NormalCut G P hn c hc) k)) :
    QMCLeafB.ThinRec34M4.ShallowCut G t P hn := by
  refine ⟨c, hc, fun _ => 0, (fun k _ => le_refl (0 : ℚ)), (fun k => ?_), (fun k hk z hz => ?_)⟩
  · have h := sigmaQ_NormalCut_pos (P := P) hn c hc k
    nlinarith [P.hrmax, sq_nonneg P.rmax]
  · have h := hsupp k hk z hz
    rw [dotProduct_sub] at h
    have h0 : (((fun _ => (0 : ℚ)) k : ℚ) : ℝ) = 0 := by norm_num
    rw [h0]
    linarith

#print axioms Asm35M4.shallowCut_of_support

/-- **The residual in supporting-cut form**: at every bit-`false` interior point, a nonzero normal
stream whose cuts support the relaxation at the accumulated centre.  By `shallowCut_of_support` this
implies `ShallowSlot`, so it is a sufficient form of the same obligation — the one m3's numerics test
(greedy max-margin normalised depth `L_k ≈ −0.1…−0.25` against the requirement `L_k ≤ rmax = 1/16` at
the exemplar). -/
def SupportSlot : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o33 G t = false →
    ∃ (c : ℕ → Fin (G.n * G.n) → ℚ) (hc : ∀ k, c k ≠ 0),
      ∀ k, k < (P33 G).K * (P33 G).m →
        ∀ z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t (P33 G),
          0 ≤ QMCLeafB.EngineIterates.cutCR
              (QMCLeafB.ThinRec34M4.NormalCut G (P33 G) hn c hc) k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ)
                (QMCLeafB.ThinRec34M4.NormalCut G (P33 G) hn c hc) k)

/-- `SupportSlot` implies `ShallowSlot`. -/
theorem shallowSlot_of_support (H : SupportSlot) : ShallowSlot := by
  intro G t hn hlo hlt hb
  obtain ⟨c, hc, hsupp⟩ := H G t hn hlo hlt hb
  exact shallowCut_of_support hn c hc hsupp

#print axioms Asm35M4.shallowSlot_of_support

/-- **THE LEAF FROM SUPPORTING CUTS ALONE** — the sharpest assembly: the upper slot plus a trajectory
of supporting cuts at the bit-`false` points.  No margin, no `rmax`, no depth: the whole analytic
content is "the accumulated centre never enters the relaxation below the horizon". -/
theorem solution_via_support (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlot) (H : SupportSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_via_shallowCut k hk hok (shallowSlot_of_support H)

#print axioms Asm35M4.solution_via_support

/-! ## 4d.  The cost of HORN 2, named

HORN 2 is not free at a FIXED bit: it must be consistent with the upper slot, and together they force
the relaxed-membership certificate to exist at every NON-EMPTY interior point — the bit cannot read
`true` where the ok test has no witness.  So filling HORN 2 at `o33` demands that the released gate
accept at some visited centre at every nonempty bracket point, which is exactly the point where
phase 34's `campaign_witness_rejected` (m6's correction: the sum gate `dvR ≤ dq/4` rejects the
canonical member, whose sum deviation is `n·dq/4`) puts pressure.  HORN 1 carries no such joint
constraint: `ShallowCut` lives entirely on the bit-`false` side. -/

/-- **HORN 2 + the upper slot force a relaxed member everywhere the body is nonempty.**  The joint
consistency condition of the programme-side horn, in the leaf's own terms. -/
theorem member_of_horns (hok : HokSlot) (Hc : CompleteSlot)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hlt : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hne : ¬ QMCLeafB.ThinRec34M4.BodyEmpty G t (P33 G)) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) :=
  hok G t hn hlo hlt (Hc G t hn hlo hlt hne)

#print axioms Asm35M4.member_of_horns

/-! ## 5.  The locked strokes -/

/-- **The lock at the smallest admissible fuel exponent.**  `k = 5` is the phase-33 choice
(`21 ≤ 2^5`); the verbatim sentence in `FinishLine.SolutionStatement` form. -/
theorem solutionLock_via_shallowCut (hok : HokSlot) (Hsc : ShallowSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FinishLine.solutionStatement_iff_wMatrix.2
    (solution_via_shallowCut 5 (by norm_num) hok Hsc)

#print axioms Asm35M4.solutionLock_via_shallowCut

/-- The same lock on the other horn. -/
theorem solutionLock_via_bitComplete (hok : HokSlot) (Hc : CompleteSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_via_bitComplete 5 (by norm_num) hok Hc

#print axioms Asm35M4.solutionLock_via_bitComplete

/-- The same lock via `Pbit33.solution33_five`'s own route (cross-check that the assembly's two
slots are exactly m6's two slots, with no drift between the frames). -/
theorem solutionLock_direct (hok : HokSlot) (Hsc : ShallowSlot) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Pbit33.solution33_five
    (QMCLeafB.Pbit33.Hd33_of_relaxMem hok (hfalseSlot_of_shallow Hsc))

#print axioms Asm35M4.solutionLock_direct

end Asm35M4



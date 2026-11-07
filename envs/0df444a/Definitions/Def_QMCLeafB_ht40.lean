-- Prove2me | Definitions.Def_QMCLeafB_ht40
-- name    : QMCLeafB_ht40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:44:05.230886+00:00
-- url     : https://prove2.me/theorems/9be6f7cf-44cb-4c0a-a8ac-d2ea8d9f0316
-- title:
--   QMCLeafB ht40
-- statement:
--   # `Check_ht40_m2` — phase 40, member m2, direction `hok-and-top`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_pbit33
import Definitions.Def_QMCLeafB_by35
import Definitions.Def_QMCLeafB_asm36_m8
import Definitions.Def_QMCLeafB_asm35
import Definitions.Def_QMCLeafB_asm_m8
import Definitions.Def_QMCLeafB_conformance_m8
/-
# `Check_ht40_m2` — phase 40, member m2, direction `hok-and-top`

**The two PROGRAMME slots of the closing move, at the enlarged ceiling, plus the Poly bit.**

Phase 38 left the leaf as `Check_rf38_m1.solution_of_separating`: the verbatim `d9f601e5`
sentence from

    {Automatic.Poly (the bit)}  +  {1 ≤ K·m}  +  {top slice}  +  {hok}  +  {SepStream}.

Phase 39/40's closing move enlarges the depth ceiling from `rmaxOf (n·n) = 1/(4n²)` to `1/n²`,
which makes the standard ellipsoid step's ATTAINED supporting ratio `(1−ρ)/(N+ρ)·√σ'` fit the
leaf's `(1/N)·√σ'` allowance exactly (`Check_eq38_m2.supporting_ratio_attained`,
`reuse_short_of_leaf`).  This file settles the part of that move that is *programme bookkeeping*:

* **§1 — the three slots do not mention the parameter family.**  `PolySlot o`, `TopSlot o` and
  `HokSlotOf o` are the exact binder *types* of `solution_of_separating`'s `ho`, `htop`, `hok`,
  written with the family `P` abstracted away.  The consequence is the whole point of this file:
  **`rmax` does not occur in any of them**, so the ceiling change cannot break them and there is
  nothing to re-discharge.  `hokSlotOf_iff_banked` identifies `HokSlotOf o33` with the campaign's
  banked `Asm35M4.HokSlot` definitionally, so the phase-34 released-gate discharge
  (`hokSlot_of_releasedGate`) plugs into the *phase-38* binder with no adaptation.
* **§2 — the top slice, discharged unconditionally at `o33`** (`topSlot33`), from the banked
  `ConformanceM8.htop_roundGT`; and the resulting free record at the top slice
  (`runParts_at_top`) is stated at an **arbitrary** family `P` with only `1 ≤ P.K·P.m` — i.e. it
  survives the ceiling change verbatim.
* **§3 — the Poly bit, discharged** (`polySlot33`, from the banked `Pbit33.ho33` — the one place
  where the `21 ≤ 2^k` fuel exponent is consumed).
* **§4 — the assembly at an ARBITRARY family.**  `solution_of_sep_family`: `d9f601e5` from
  `{SepStream P}` + `{1 ≤ P.K·P.m}` + `{hok}`, with `ho` and `htop` supplied here.  Since `P` is a
  variable, this is the closing move's "re-discharge at the new constant": the theorem holds at
  `rmax := 1/(n·n)` with *no* change to the three programme slots, and the only `P`-dependent
  hypotheses are the horizon arithmetic and separation itself.
* **§5 — the exact one-hypothesis remainder**: `solution_of_sep_one`, where `hok` is additionally
  discharged from the released-gate stream data (`Asm35M4.hokSlot_of_releasedGate`), leaving
  `{SepStream P}` as the single analytic hypothesis, and its statement-lock twin.

What is *not* claimed: that `SepStream` is inhabited at `rmax = 1/n²` (that is the construction
half, phases 39–40's other lanes), nor the halving/budget re-discharge of `RunParams` at the new
constant (the parameter family is a variable here, deliberately).

Discipline: `set_option autoImplicit false`; every declaration's closure is printed below and is
exactly `[propext, Classical.choice, Quot.sound]`; nothing is left unfinished.  Imports are
published `Definitions.*` only (no `Solutions.*`), so the file sits on the submission cone.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open Matrix

namespace QMCLeafB.Ht40M2

open QuantumMaxCutEnergy
open QMCLeafB.EngineIterates
open QMCLeafB.ThinRec34M4 (ShallowCut NormalCut relaxBallP BodyRec)

/-! ## 0.  The supporting stream (the phase-38 residual, restated locally)

`SepStream` is phase-38's `QMCLeafB.Rf38M1.SepStream` verbatim: at every round below the horizon a
nonzero rational normal puts the engine's accumulated centre on the far side of the WHOLE
relaxation.  It is the leaf's single analytic hypothesis; everything in this file is about the
*other* slots. -/

/-- A nonzero rational stream which, at every round below the horizon, places the accumulated centre
on the far side of the relaxation: a supporting-hyperplane certificate. -/
def SepStream (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    ∀ k, k < (P G).K * (P G).m → ∀ z ∈ relaxBallP G t (P G),
      (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
          Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (NormalCut G (P G) hn (c G t) (hc G t)) k
        ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

#print axioms QMCLeafB.Ht40M2.SepStream

/-- **THE RECORD FROM SEPARATION** (reuse: phase 35's `shallowCut_of_separating` with `del ≡ 0`,
transported through phase-34's `bodyRec_of_shallowCut`).  The all-cut identity at an ARBITRARY
programme and an ARBITRARY parameter family — no `rmax`, no `sigma` estimate, no ellipsoid, so no
ceiling to re-discharge. -/
theorem selfRecG_of_separating
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  exact QMCLeafB.ThinRec34M4.bodyRec_of_shallowCut hn
    (QMCLeafB.Bypass35M6.shallowCut_of_separating (P := P G) hn (c G t) (hc G t)
      (hsep G t hn))

#print axioms QMCLeafB.Ht40M2.selfRecG_of_separating

/-! ## 1.  The three programme slots, with the parameter family abstracted away

`solution_of_separating`'s binders `ho`, `htop`, `hok` are *types about the bit* (and the runtime's
own constants `Rq`, `eps`, `dqShallow`) and mention the family `P` **nowhere**.  Written as `def`s
here, they make the ceiling change's bookkeeping auditable: `rmax` is not a parameter of any of
them. -/

/-- The `Poly` slot of the assembly: the bit is polynomial-time in the request. -/
def PolySlot (o : QuantumMaxCutEnergy.Input → ℚ → Bool) : Prop :=
  OAI.MetricKMedian.Binary.Automatic.Poly
    (fun p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) => o p.1.1 p.2)

#print axioms QMCLeafB.Ht40M2.PolySlot

/-- The top-slice slot: the bit reads `true` on `[-Rq/40000, 0]`. -/
def TopSlot (o : QuantumMaxCutEnergy.Input → ℚ → Bool) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 → o G t = true

#print axioms QMCLeafB.Ht40M2.TopSlot

/-- The upper slot `hok`: a bit-`true` interior bracket point carries a symmetric rational
`RelaxMem` at `(t − eps, dqShallow)`.  Note: **no `rmax`**. -/
def HokSlotOf (o : QuantumMaxCutEnergy.Input → ℚ → Bool) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true →
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

#print axioms QMCLeafB.Ht40M2.HokSlotOf

/-- **The banked campaign slot IS the phase-38 binder.**  `Asm35M4.HokSlot` (phase 35's `hok`,
discharged mechanically by `Asm35M4.hokSlot_of_releasedGate` from the released gate's stream data)
is `HokSlotOf o33` *definitionally* — so the phase-34/35 upper-side discharge plugs into the
phase-38 separation stroke with no adaptation, and the ceiling change cannot reach it. -/
theorem hokSlotOf_iff_banked : HokSlotOf QMCLeafB.Pbit33.o33 ↔ Asm35M4.HokSlot :=
  Iff.rfl

#print axioms QMCLeafB.Ht40M2.hokSlotOf_iff_banked

/-- **THE CEILING DOES NOT REACH THE SLOTS.**  The three programme slots are `P`-free: the same
three terms serve the assembly at *any* parameter family.  Stated as the transport that the closing
move needs — from a family `P₁` to any other family `P₂`, the slots pass across unchanged, so only
the horizon arithmetic `1 ≤ K·m` and the geometric hypothesis change when `rmax` moves. -/
theorem slots_ceiling_invariant
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P₁ P₂ : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (ho : PolySlot o) (htop : TopSlot o) (hok : HokSlotOf o) :
    PolySlot o ∧ TopSlot o ∧ HokSlotOf o ∧
      (PolySlot o ∧ TopSlot o ∧ HokSlotOf o) :=
  ⟨ho, htop, hok, ho, htop, hok⟩

#print axioms QMCLeafB.Ht40M2.slots_ceiling_invariant

/-! ## 2.  The top slice, discharged at the campaign bit, at ANY family

The banked `ConformanceM8.htop_roundGT` decides the top slice from the first round alone, and the
record there is the identity (`Pbit33.memberAt_top`) — both are statements about the *bit*, so the
resulting record is available at an arbitrary parameter family as soon as the horizon is positive. -/

/-- **THE TOP SLICE, UNCONDITIONALLY.**  The campaign bit `o33` reads `true` on `[-Rq/40000, 0]`.
No family, no ceiling, no side condition. -/
theorem topSlot33 : TopSlot QMCLeafB.Pbit33.o33 :=
  fun G t hn hlo hhi =>
    QMCLeafB.ConformanceM8.htop_roundGT (fun G' => QMCLeafB.Pbit33.T33 G')
      QMCLeafB.Pbit33.one_le_T33 G t hlo hhi

#print axioms QMCLeafB.Ht40M2.topSlot33

/-- **THE TOP-SLICE RECORD, AT AN ARBITRARY FAMILY.**  At any family with a positive horizon, the
all-`ok` record of `AsmM8.runParts_of_member` exists on the top slice.  `rmax` is not consulted, so
this is the record the enlarged ceiling inherits verbatim. -/
noncomputable def runParts_at_top (P : (G : QuantumMaxCutEnergy.Input) →
      QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.RunParts QMCLeafB.Pbit33.o33 G t (P G) :=
  AsmM8.runParts_of_member (P G) hn (hKm G)
    (topSlot33 G t hn hlo hhi) (QMCLeafB.Pbit33.memberAt_top hlo)

#print axioms QMCLeafB.Ht40M2.runParts_at_top

/-! ## 3.  The Poly bit, discharged

`Pbit33.ho33` is the campaign's `Automatic.Poly` proof for the concrete bit `o33`.  The single
non-structural input is the fuel exponent `21 ≤ 2^k`; everything else is the banked size ledger. -/

/-- **THE POLY SLOT.**  `Automatic.Poly` of the campaign bit, in the assembly's own binder shape. -/
theorem polySlot33 (k : ℕ) (hk : 21 ≤ 2 ^ k) : PolySlot QMCLeafB.Pbit33.o33 :=
  QMCLeafB.Pbit33.ho33 k hk

#print axioms QMCLeafB.Ht40M2.polySlot33

/-! ## 4.  The assembly at an ARBITRARY family — the closing move's shape

`Asm36M8.solution_of_two_slots_selfRec` takes the `Poly` bit, the count, the top slice, `hok` and
the all-cut identity.  Firing it with §1–§3 leaves exactly `{1 ≤ P.K·P.m}` and `{SepStream P}`.  The
family is a VARIABLE: this is what "re-discharge at the new constant `rmax = 1/n²`" amounts to on
the programme side — nothing in `ho`/`htop`/`hok` moves. -/

/-- **THE LEAF AT ANY PARAMETER FAMILY.**  `d9f601e5` from the horizon arithmetic, the upper slot
and a supporting rational stream.  No `rmax` hypothesis, no test coherence, no ledger. -/
theorem solution_of_sep_family (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (hok : HokSlotOf QMCLeafB.Pbit33.o33)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.Asm36M8.solution_of_two_slots_selfRec QMCLeafB.Pbit33.o33 P
    (polySlot33 k hk) hKm (topSlot33) hok
    (selfRecG_of_separating QMCLeafB.Pbit33.o33 P c hc hsep)

#print axioms QMCLeafB.Ht40M2.solution_of_sep_family

/-- The same, with the upper slot taken in the campaign's banked `HokSlot` shape (so
`Asm35M4.hokSlot_of_releasedGate` — and hence the released-gate stream data — plugs straight in). -/
theorem solution_of_sep_family_banked (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (hok : Asm35M4.HokSlot)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sep_family k hk P hKm (hokSlotOf_iff_banked.2 hok) c hc hsep

#print axioms QMCLeafB.Ht40M2.solution_of_sep_family_banked

/-- **THE STATEMENT LOCK TWIN** — the same theorem in the platform's own `d9f601e5` type, written
out, so the frame is auditable against the live statement. -/
theorem solution_of_sep_family_statement (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (hok : HokSlotOf QMCLeafB.Pbit33.o33)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
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
  solution_of_sep_family k hk P hKm hok c hc hsep

#print axioms QMCLeafB.Ht40M2.solution_of_sep_family_statement

/-! ## 5.  The exact one-hypothesis remainder

`hok` is mechanical: `Asm35M4.hokSlot_of_releasedGate` turns the released gate's stream data into
`HokSlot`, and *every one of its hypotheses is about the run's registers* (`dvR`, `fvR`, `dqOf`,
`levelOf`, the pivot answer) — **not about `rmax`**.  So the ceiling enlargement leaves them all
standing, and `SepStream` is the only hypothesis that is not a fact about which programme runs. -/

/-- **`hok` FROM THE RELEASED GATE, at the phase-38 binder.**  Re-export of phase-34/35's discharge
with the conclusion in `HokSlotOf o33` form.  Every hypothesis is register data; `rmax` occurs in
none of them, so the enlarged ceiling re-discharges them verbatim. -/
theorem hokSlotOf_of_releasedGate
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Pbit33.o33 G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
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
    HokSlotOf QMCLeafB.Pbit33.o33 :=
  hokSlotOf_iff_banked.2
    (Asm35M4.hokSlot_of_releasedGate okT σ T hRq hbit hdat hpiv hdv hfv hlev hdqv)

#print axioms QMCLeafB.Ht40M2.hokSlotOf_of_releasedGate

/-- **THE LEAF FROM SEPARATION ALONE** (with the released gate's stream data on the programme
side).  Exactly one analytic hypothesis: a supporting rational stream at the family `P` — which may
be the enlarged-ceiling family, since no step of the argument consults `rmax`. -/
theorem solution_of_sep_one (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (hKm : ∀ G : QuantumMaxCutEnergy.Input, 1 ≤ (P G).K * (P G).m)
    (okT : QMCLeafB.RoundProgram.RSt → Bool)
    (σ : QuantumMaxCutEnergy.Input → ℚ → ℕ → QMCLeafB.RoundProgram.RSt)
    (T : QuantumMaxCutEnergy.Input → ℕ)
    (hRq : ∀ G : QuantumMaxCutEnergy.Input, 0 < QMCLeafB.EngineRuntime.Rq G)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      QMCLeafB.Pbit33.o33 G t = QMCLeafB.SimLoop.anyOk (fun k => okT (σ G t k)) (T G))
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
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream P c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sep_family k hk P hKm
    (hokSlotOf_of_releasedGate okT σ T hRq hbit hdat hpiv hdv hfv hlev hdqv) c hc hsep

#print axioms QMCLeafB.Ht40M2.solution_of_sep_one



/-! ## 6.  The ceiling arithmetic: the new constant is exactly `4 ×` the old one

The closing move replaces `rmaxOf (n·n) = 1/(4n²)` by `1/n²`.  The *slots* do not see either
number (§1), so the only thing to record here is the arithmetic relation between them — a receipt
for "the acknowledgement `4N(1−ρ)/(N+ρ) → 4` is exactly a factor-4 change of ceiling", nothing more.
The `RunParams` fields themselves (`hhalve`, `hbudget`, the horizon) are the parameter lane's
business and are deliberately NOT touched: the family is a variable in every theorem above. -/

/-- The closing move's ceiling: `1/(n·n)`. -/
def newCeil (G : QuantumMaxCutEnergy.Input) : ℚ := ((G.n * G.n : ℕ) : ℚ)⁻¹

/-- **The new ceiling is exactly four times the campaign's.**  So the phase-38 allowance
`rmax·√σ'` is multiplied by `4`, uniformly in `n` — the quantity `Check_eq38_m2`'s
`supporting_ratio_attained` / `reuse_short_of_leaf` show to be exactly the miss. -/
theorem newCeil_eq_four_mul_rmaxOf (G : QuantumMaxCutEnergy.Input) :
    newCeil G = 4 * QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := by
  rcases Nat.eq_zero_or_pos (G.n * G.n) with h | h
  · simp [newCeil, QMCLeafB.RundataHalving.rmaxOf, h]
  · have hq : ((G.n * G.n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast h.ne'
    simp only [newCeil, QMCLeafB.RundataHalving.rmaxOf]
    field_simp

#print axioms QMCLeafB.Ht40M2.newCeil_eq_four_mul_rmaxOf

/-- The ceiling is enlarged, not shrunk: `rmaxOf (n·n) ≤ 1/(n·n)`. -/
theorem rmaxOf_le_newCeil (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) ≤ newCeil G := by
  rw [newCeil_eq_four_mul_rmaxOf]
  rcases Nat.eq_zero_or_pos (G.n * G.n) with h | h
  · simp [QMCLeafB.RundataHalving.rmaxOf, h]
  · have hq : (0 : ℚ) < ((G.n * G.n : ℕ) : ℚ) := by exact_mod_cast h
    have hr : 0 < QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) := by
      simp only [QMCLeafB.RundataHalving.rmaxOf]
      positivity
    linarith

#print axioms QMCLeafB.Ht40M2.rmaxOf_le_newCeil

/-! ## 7.  Non-vacuity at a concrete family

The family is a variable above; to show the horizon slot is not vacuous, instantiate at the
campaign's own family `P33` (where `1 ≤ K·m` is `Pbit33.one_le_T33`).  This also cross-checks that
the variable-`P` stroke specialises to the banked programme. -/

/-- **`1 ≤ K·m` at the campaign family.** -/
theorem hKm_P33 (G : QuantumMaxCutEnergy.Input) : 1 ≤ (QMCLeafB.Pbit33.P33 G).K *
    (QMCLeafB.Pbit33.P33 G).m := by
  rw [QMCLeafB.Pbit33.P33_K_mul_m]
  exact QMCLeafB.Pbit33.one_le_T33 G

#print axioms QMCLeafB.Ht40M2.hKm_P33

/-- **THE LEAF AT THE CAMPAIGN FAMILY** — the `P`-variable stroke specialised, confirming the two
`P`-dependent slots (`hKm`, `SepStream`) are the only ones and that `ho`/`htop`/`hok` are untouched. -/
theorem solution_of_sep_P33 (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hok : HokSlotOf QMCLeafB.Pbit33.o33)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsep : SepStream QMCLeafB.Pbit33.P33 c hc) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_of_sep_family k hk QMCLeafB.Pbit33.P33 hKm_P33 hok c hc hsep

#print axioms QMCLeafB.Ht40M2.solution_of_sep_P33

end QMCLeafB.Ht40M2



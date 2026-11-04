-- Prove2me | Definitions.Def_QMCLeafB_integration2
-- name    : QMCLeafB_integration2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:41:38.502749+00:00
-- url     : https://prove2.me/theorems/3bdf2f76-4932-4167-9bb2-61d816d38ba7
-- title:
--   QMCLeafB integration2
-- statement:
--   # leaf B phase 22 — the integration spine (swarm `smw1ntur6`, member m7, direction 7 `integration2`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_verdbridge
import Definitions.Def_QMCLeafB_emptybottom
import Definitions.Def_QMCLeafB_cutbudget
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_htop_ledgerW_m7
/-
# leaf B phase 22 — the integration spine (swarm `smw1ntur6`, member m7, direction 7 `integration2`)

Direction 7 asks that directions 1–6 be zipped into the full residual family and the locked stroke
fired **at the repointed program bit** (`loopBit InitDq.init0 OkLower.roundW RoundProgram.verdict`),
delivering a *local* `FinishLine.SolutionStatement` and the verbatim `d9f601e5` sentence.

This file is the zipper.  It does not build a stream (d1), analyse the ceiling (d2), cut the bounded
twins (d3), repoint the outer endgame (d4), produce the ok branch (d5) or audit (d6).  It fixes the
**interfaces**, proves every composition that is provable now, and reduces the whole closing
obligation to named fields that a later file discharges one at a time.  Everything below is
sorry-free and axiom-audited.

* §1 the reported bit `oW` and its count (`Tbc2 = K·m`, definitional).
* §2 **bit-generic descent**: `ResidG o → RunParts o` at *any* program bit `o` — so the repoint of
  the residual is a substitution, not a re-derivation (`EndgameM2.hd_of_residH` was at `round`).
* §3 the point predicate `EmptyBodyAt` and the split `ResidG = ResidRefuted ⊓ ResidOk` — the
  interface between d1/d2 (refuted interiors) and d5 (ok interiors).
* §4 **the refuted-point normal form**: at an empty body a `CoreDataG` is exactly a crater record
  `CoreCrater` — records/margins/normals and the two drift budgets at `k < K·m` with the flag stream
  `okBot` (`false` below the horizon, `true` above) — plus the bit equation `o G t = false`.  Both
  directions are proved, so the interface is an `↔`, not a guess.
* §5 the verdict-lane checksum at *any* bit: an inhabited residual forces `o G t = false` at every
  refuted interior point (the generic form of m1's `bit_false_at_all_bottoms`).
* §6 the `Spine` bundle, `ResidG` from it, and the two degenerate cases (all-refuted, all-ok).
* §7 **the ending**: `Ending o` is the outer stroke at bit `o`; `ending_GU` proves the interface is
  inhabited at the banked round (so it is not an idle hypothesis), and the missing instance is
  exactly `Ending oW` — d4's deliverable.
* §8 `endgame_final` and `solution` (verbatim `d9f601e5`) at `oW`, plus the statement lock.
* §9 non-vacuity of the ok branch of the spine **at the final bit**: `(G₀, −1/2)` is a member point,
  and its `CoreDataG` at `oW` follows from the reported round's verdict value there.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Integration2M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (BundleH ResidH)

/-! ## 1.  The reported bit and its count -/

/-- **The campaign program bit at the lower-body round** `roundW` (m4's orientation result: the
verdict slot is refuted at `RoundProgram.round` and true here). -/
def oW : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.OkLower.roundW
    QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2

/-- The round count the verdict slot reads is the campaign count `K·m` of `paramsKbc2`. -/
theorem Tbc2_eq_Kmul (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    QMCLeafB.ClosingAssembly.Tbc2 G t
      = (QMCLeafB.UnionShallow.paramsKbc2 G).K * (QMCLeafB.UnionShallow.paramsKbc2 G).m := rfl

#print axioms QMCLeafB.Integration2M7.Tbc2_eq_Kmul

/-! ## 2.  Bit-generic descent: the residual at ANY program bit gives the run bundles

`EndgameM2.hd_of_residH` is stated at `RoundProgram.round`.  The descent itself never looks at the
bit — `FlagsM5.runParts_of_bundleH` takes `o` explicitly and `BundleH`'s only bit-dependent field is
`hverdict`, which `bundleH_of_dataG` copies from the residual.  So the whole repoint is a
substitution, and this section makes that machine-checked. -/

/-- **`ResidG` at an arbitrary program bit gives one `RunParts` bundle per interior point.** -/
def runParts_of_residG {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (H : QMCLeafB.EndgameM2.ResidG o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact QMCLeafB.FlagsM5.runParts_of_bundleH o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.AssemblyM5.rmax_pos_at_interior G hn)
    (QMCLeafB.AssemblyM5.rmax_le_one G hn)
    (QMCLeafB.AssemblyM5.budget_at_interior G t hn hlo hhi)
    (QMCLeafB.EndgameM2.bundleH_of_dataG (QMCLeafB.AssemblyM5.rmax_pos_at_interior G hn)
      (H G t hn hlo hhi))

#print axioms QMCLeafB.Integration2M7.runParts_of_residG

/-- The same at the repointed bit. -/
def runParts_of_residG_W
    (H : QMCLeafB.EndgameM2.ResidG oW QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts oW G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  runParts_of_residG H

#print axioms QMCLeafB.Integration2M7.runParts_of_residG_W

/-! ## 3.  The point predicate and the branch split -/

/-- **No centre is a member at `(G, t)`**: the relaxation body is empty.  This is the predicate that
separates the two producing directions. -/
def EmptyBodyAt (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Prop :=
  ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) P.dq

/-- **The refuted branch** (d1/d2's deliverable): the residual at interior points whose body is empty.
`EndgameM2.coreDataB_at_empty` is the canonical-residual statement of exactly this obligation. -/
abbrev ResidRefuted (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    EmptyBodyAt G t (Pfam G) hn → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The ok branch** (d5's deliverable): the residual at interior points with a non-empty body. -/
abbrev ResidOk (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ EmptyBodyAt G t (Pfam G) hn → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The two branches zip into the residual.**  `by_cases` on the body: nothing is lost and nothing
is assumed. -/
def residG_of_branches {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (R : ResidRefuted o Pfam) (K : ResidOk o Pfam) :
    QMCLeafB.EndgameM2.ResidG o Pfam :=
  fun G t hn hlo hhi => by
    by_cases h : EmptyBodyAt G t (Pfam G) hn
    · exact R G t hn hlo hhi h
    · exact K G t hn hlo hhi h

#print axioms QMCLeafB.Integration2M7.residG_of_branches

/-! ## 4.  The refuted-point normal form

At an empty body the flag stream is *not* free in a useful way: `hmem` is unsatisfiable below the
horizon, so every round below `K·m` is a cut round; and above the horizon the budgets are not asked,
so the canonical stream is `okBot` (`false` below, `true` above).  The three consequences:

* the records, margins, normals and both budgets are needed **only at `k < K·m`**;
* the verdict bit is forced `false`;
* hence a `CoreDataG` at an empty body is *exactly* a `CoreCrater` — which is what makes the crater
  a satisfiability problem over `k < K·m` slots rather than an infinite stream.
-/

/-- The refuted flag stream: `false` below the horizon, `true` above it. -/
def okBot (T : ℕ) : ℕ → Bool := fun k => if k < T then false else true

theorem okBot_false_iff (T k : ℕ) : okBot T k = false ↔ k < T := by
  unfold okBot
  by_cases h : k < T <;> simp [h]

theorem okBot_true_iff (T k : ℕ) : okBot T k = true ↔ ¬ k < T := by
  unfold okBot
  by_cases h : k < T <;> simp [h]

/-- `anyOk` sees only the window, so the above-horizon `true` is invisible. -/
theorem anyOk_okBot (T : ℕ) : QMCLeafB.SimLoop.anyOk (okBot T) T = false := by
  rw [QMCLeafB.SimLoop.anyOk_eq_false_iff]
  intro k hk
  exact (okBot_false_iff T k).2 hk

#print axioms QMCLeafB.Integration2M7.anyOk_okBot

section Refuted

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- At an empty body every round below the horizon of a `CoreDataG` stream is a cut round. -/
theorem ok_eq_false_of_empty (hempty : EmptyBodyAt G t P hn)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) :
    ∀ k, k < P.K * P.m → D.ok k = false := by
  intro k hk
  cases h : D.ok k with
  | false => rfl
  | true => exact absurd (D.hmem k hk h) (hempty _)

#print axioms QMCLeafB.Integration2M7.ok_eq_false_of_empty

/-- **The verdict-lane checksum at an arbitrary bit**: at an empty body the program's bit is `false`. -/
theorem verdict_false_of_empty (hempty : EmptyBodyAt G t P hn)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) : o G t = false := by
  rw [D.hverdict, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  exact ok_eq_false_of_empty hempty D

#print axioms QMCLeafB.Integration2M7.verdict_false_of_empty

/-- **The crater interface** — every `CoreDataG` field of a refuted interior point, with the flag
stream erased.  This is the exact list d1/d2 owe: the coded states with their symmetry, a legal
separating record with its margin and flat normal at every round below the horizon, the centre
mismatch budget, the trace budget, and the bit equation. -/
structure CoreCrater (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **the supplied separating record** at every round below the horizon -/
  C : ∀ k, k < P.K * P.m →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.RecordsM2.cXst G.n X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the supplied margins -/
  marg : ℕ → ℚ
  hmarg : ∀ k (hk : k < P.K * P.m), marg k = (C k hk).margin
  /-- the supplied flat normals -/
  c : ℕ → Fin (G.n * G.n) → ℚ
  hcEq : ∀ k (hk : k < P.K * P.m), c k = QMCLeafB.RelaxOracle.flatQ (C k hk).normal
  /-- **the cut normal's centre mismatch** at the supplied records -/
  hdriftc : ∀ k (hk : k < P.K * P.m),
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget** at the supplied records -/
  hdriftd : ∀ k (hk : k < P.K * P.m),
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
      ≤ 0
  /-- the leaf's verdict bit at a refuted point -/
  hbit : o G t = false

/-- **A crater record is a residual bundle at an empty body.** -/
def coreDataG_of_crater (D : CoreCrater o G t P hn) :
    QMCLeafB.EndgameM2.CoreDataG o G t P hn where
  X := D.X
  hsym := D.hsym
  ok := okBot (P.K * P.m)
  hmem := fun k hk htrue => by
    rw [okBot_true_iff] at htrue
    exact absurd hk htrue
  C := fun k hfalse => D.C k ((okBot_false_iff (P.K * P.m) k).1 hfalse)
  marg := D.marg
  hmarg := fun k hfalse => D.hmarg k ((okBot_false_iff (P.K * P.m) k).1 hfalse)
  c := D.c
  hcEq := fun k hfalse => D.hcEq k ((okBot_false_iff (P.K * P.m) k).1 hfalse)
  hdriftc := fun k hfalse => D.hdriftc k ((okBot_false_iff (P.K * P.m) k).1 hfalse)
  hdriftd := fun k hfalse => D.hdriftd k ((okBot_false_iff (P.K * P.m) k).1 hfalse)
  hverdict := by rw [D.hbit, anyOk_okBot]

#print axioms QMCLeafB.Integration2M7.coreDataG_of_crater

/-- **Every residual bundle at an empty body is a crater record** (the other direction). -/
def crater_of_coreDataG (hempty : EmptyBodyAt G t P hn)
    (D : QMCLeafB.EndgameM2.CoreDataG o G t P hn) : CoreCrater o G t P hn where
  X := D.X
  hsym := D.hsym
  C := fun k hk => D.C k (ok_eq_false_of_empty hempty D k hk)
  marg := D.marg
  hmarg := fun k hk => D.hmarg k (ok_eq_false_of_empty hempty D k hk)
  c := D.c
  hcEq := fun k hk => D.hcEq k (ok_eq_false_of_empty hempty D k hk)
  hdriftc := fun k hk => D.hdriftc k (ok_eq_false_of_empty hempty D k hk)
  hdriftd := fun k hk => D.hdriftd k (ok_eq_false_of_empty hempty D k hk)
  hbit := verdict_false_of_empty hempty D

#print axioms QMCLeafB.Integration2M7.crater_of_coreDataG

/-- **The refuted-point interface is an `↔`**: at an empty body, a residual bundle and a crater
record are inter-derivable.  The crater's `k < K·m` slot list is therefore *exact* — no round above
the horizon is ever owed, and no slot below it is dispensable. -/
theorem nonempty_coreDataG_iff_crater (hempty : EmptyBodyAt G t P hn) :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG o G t P hn) ↔ Nonempty (CoreCrater o G t P hn) :=
  ⟨fun ⟨D⟩ => ⟨crater_of_coreDataG hempty D⟩, fun ⟨D⟩ => ⟨coreDataG_of_crater D⟩⟩

#print axioms QMCLeafB.Integration2M7.nonempty_coreDataG_iff_crater

end Refuted

/-! ## 5.  The residual forces the bit `false` at every refuted point -/

/-- **Verdict-lane checksum, generic form.**  An inhabited residual at program bit `o` forces
`o G t = false` at every refuted interior point — so a candidate program bit is admissible only if it
is `false` there.  (At `oW` this is d4's obligation; at the bottom point it is m1's
`bit_false_at_all_bottoms`.) -/
theorem bit_false_at_refuted {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.EndgameM2.ResidG o Pfam)
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hempty : EmptyBodyAt G t (Pfam G) hn) : o G t = false :=
  verdict_false_of_empty hempty (H G t hn hlo hhi)

#print axioms QMCLeafB.Integration2M7.bit_false_at_refuted

/-- The checksum as a refutation: a residual at a bit that is `true` at a refuted point is
uninhabited. -/
theorem not_residG_of_refuted_bit_true {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hempty : EmptyBodyAt G t (Pfam G) hn) (hbit : o G t = true) :
    QMCLeafB.EndgameM2.ResidG o Pfam → False := by
  intro H
  have h := bit_false_at_refuted H hn hlo hhi hempty
  rw [h] at hbit
  exact Bool.noConfusion hbit

#print axioms QMCLeafB.Integration2M7.not_residG_of_refuted_bit_true

/-! ## 6.  The spine -/

/-- **The integration spine at a program bit**: one residual bundle per interior point, produced by
whichever branch applies.  The two fields are the whole of directions 1/2 and 5–6; nothing else is
owed anywhere in the closing cone. -/
structure Spine (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the refuted branch: interiors with empty body -/
  refuted : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    EmptyBodyAt G t (Pfam G) hn → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn
  /-- the ok branch: interiors with non-empty body -/
  okpt : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ EmptyBodyAt G t (Pfam G) hn → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The spine in crater form** — the recommended interface.  The refuted field asks for the
`CoreCrater` slot list only, so a refuted-point producer never has to invent a flag stream, an `ok`
bit, or the verdict equation: §4 supplies them from the crater record and the bit equation. -/
structure SpineC (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the refuted branch, in crater form -/
  refuted : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    EmptyBodyAt G t (Pfam G) hn → CoreCrater o G t (Pfam G) hn
  /-- the ok branch -/
  okpt : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    ¬ EmptyBodyAt G t (Pfam G) hn → QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn

/-- **The crater spine is exactly the residual.** -/
def residG_of_spineC {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (S : SpineC o Pfam) : QMCLeafB.EndgameM2.ResidG o Pfam :=
  residG_of_branches
    (fun G t hn hlo hhi h => coreDataG_of_crater (S.refuted G t hn hlo hhi h))
    S.okpt

#print axioms QMCLeafB.Integration2M7.residG_of_spineC

/-- **The spine is exactly the residual.** -/
def residG_of_spine {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (S : Spine o Pfam) : QMCLeafB.EndgameM2.ResidG o Pfam :=
  residG_of_branches S.refuted S.okpt

#print axioms QMCLeafB.Integration2M7.residG_of_spine

/-- The crater form implies the flag-stream form (one way). -/
def spine_of_spineC {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (S : SpineC o Pfam) : Spine o Pfam :=
  ⟨fun G t hn hlo hhi h => coreDataG_of_crater (S.refuted G t hn hlo hhi h), S.okpt⟩

#print axioms QMCLeafB.Integration2M7.spine_of_spineC

/-- The flag-stream form implies the crater form (the other way). -/
def spineC_of_spine {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (S : Spine o Pfam) : SpineC o Pfam :=
  ⟨fun G t hn hlo hhi h => crater_of_coreDataG h (S.refuted G t hn hlo hhi h), S.okpt⟩

#print axioms QMCLeafB.Integration2M7.spineC_of_spine

/-- The residual gives the spine back (so the decomposition is conservative). -/
def spine_of_residG {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.EndgameM2.ResidG o Pfam) : Spine o Pfam :=
  ⟨fun G t hn hlo hhi _ => H G t hn hlo hhi, fun G t hn hlo hhi _ => H G t hn hlo hhi⟩

#print axioms QMCLeafB.Integration2M7.spine_of_residG

/-- **An all-ok campaign needs no refuted branch at all** — the degenerate case that shows the split
is not a way of assuming the hard half. -/
def spine_of_okOnly {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (K : ResidOk o Pfam)
    (hNo : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      ¬ EmptyBodyAt G t (Pfam G) hn) : Spine o Pfam :=
  ⟨fun G t hn _ _ h => absurd h (hNo G t hn), K⟩

#print axioms QMCLeafB.Integration2M7.spine_of_okOnly

/-! ## 7.  The outer endgame as an interface

`ResidG → SolutionStatement` is *not* bit-generic: the banked ending
(`RoundGUEndgame.solution_roundGU_of_init`) is stated for the reported round `roundGU`, and the loop
bit of `roundW` differs from `roundGU`'s bit at exactly the refuted interior points (that is the
whole finding).  So the outer stroke at `oW` is a real obligation — d4's — and this section records
it as a named interface while proving that the interface is inhabited at the banked bit (so it is a
generalisation of the shelf's theorem, not a weakening of the target). -/

/-- **The outer endgame at a program bit.** -/
structure Ending (o : QuantumMaxCutEnergy.Input → ℚ → Bool) : Type where
  run : (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G)) →
    QMCLeafB.FinishLine.SolutionStatement

/-- The same bit at the banked `roundGU` program. -/
def oGU : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 QMCLeafB.HtopFinish.roundGU
    QMCLeafB.RoundProgram.verdict QMCLeafB.ClosingAssembly.Tbc2

/-- **The interface at the banked round** (`roundGU`): the shelf's own ending, reused verbatim. -/
def ending_GU : Ending oGU :=
  ⟨fun hd =>
    QMCLeafB.RoundGUEndgame.solution_roundGU_of_init QMCLeafB.InitDq.init0 20
      QMCLeafB.AssemblyM5.hk_twenty QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
      QMCLeafB.AssemblyM5.fvR_init0_any QMCLeafB.InitDq.stT_init0
      QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.init0_tape hd⟩

#print axioms QMCLeafB.Integration2M7.ending_GU

/-- **`Ending` is a generalisation, not a weakening**: any program bit that agrees with `roundGU`'s
on the interior gets the shelf's ending for free (`runParts_congr` moves the bundle across, then
§the banked ending applies).  So a repoint that keeps the interior bit can skip the size ledger
entirely; a repoint that moves it (as `roundW` does) owes the ledger. -/
def ending_of_bit_eq {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      o G t = oGU G t) : Ending o :=
  ⟨fun hd => ending_GU.run (fun G t hn hlo hhi =>
    QMCLeafB.RoundGUEndgame.runParts_congr (hd G t hn hlo hhi) (h G t hn hlo hhi).symm)⟩

#print axioms QMCLeafB.Integration2M7.ending_of_bit_eq

/-- **`Ending oW` is not an obligation: the banked `roundWG` ledger gives it.**  Phase 16's
`LedgerW.solution_roundWG_of_init_hd_round` takes the run bundle at exactly this bit (`roundW`'s loop
bit at the campaign count) and produces `SolutionStatement`; the only work here is instantiating the
`init0` slots and the count (`Tbc2` is that count by definition).  So the repoint of the *outer*
stroke costs the `phase-16` ledger and nothing else. -/
def ending_W : Ending oW :=
  ⟨fun hd =>
    QMCLeafB.LedgerW.solution_roundWG_of_init_hd_round QMCLeafB.InitDq.init0 20
      QMCLeafB.AssemblyM5.hk_twenty QMCLeafB.InitDq.poly_init0 QMCLeafB.InitDq.init_normalised
      QMCLeafB.InitDq.stT_init0 QMCLeafB.AssemblyM5.epsOf_init0_any QMCLeafB.InitDq.stOks_init0
      QMCLeafB.InitDq.init0_tape hd⟩

#print axioms QMCLeafB.Integration2M7.ending_W

/-! ## 8.  The endgame at the reported bit -/

/-- **`FinishLine.SolutionStatement` at `oW` from the spine and the repointed outer stroke.** -/
theorem endgame_final_of_ending (S : SpineC oW QMCLeafB.UnionShallow.paramsKbc2) (E : Ending oW) :
    QMCLeafB.FinishLine.SolutionStatement :=
  E.run (runParts_of_residG (residG_of_spineC S))

#print axioms QMCLeafB.Integration2M7.endgame_final_of_ending

/-- **`FinishLine.SolutionStatement` from the spine alone** — the outer stroke is discharged
(`ending_W`), so the crater and ok branches are the entire remaining content. -/
theorem endgame_final (S : SpineC oW QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_final_of_ending S ending_W

#print axioms QMCLeafB.Integration2M7.endgame_final

/-- **The verbatim `d9f601e5` sentence at `oW`, from the spine alone.** -/
theorem solution (S : SpineC oW QMCLeafB.UnionShallow.paramsKbc2) :
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
  endgame_final S

#print axioms QMCLeafB.Integration2M7.solution

/-- **Statement lock**: the conclusion written out again, so any drift in the sentence breaks this
file rather than the packaging step. -/
theorem solution_lock_W (S : SpineC oW QMCLeafB.UnionShallow.paramsKbc2) :
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
  solution S

#print axioms QMCLeafB.Integration2M7.solution_lock_W

/-- The two spellings are definitionally the same sentence (`FinishLine.SolutionStatement` at
`Iff.rfl`), recorded as a defeq probe. -/
theorem solution_statement_eq (S : SpineC oW QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution S

#print axioms QMCLeafB.Integration2M7.solution_statement_eq

/-! ## 9.  Non-vacuity of the ok branch at the final bit

The spine's ok field is not idle: `(G₀, −1/2)` has a member centre, and the banked
`CoreDataG` there carries a stream whose every round below the horizon is `ok`.  Transporting it to
`oW` costs exactly the reported round's verdict value at that point — which is d4's bridge, not a new
stream construction.  So: **the ok half of the spine is inhabited at the ok anchor as soon as the
bit is `true` there**. -/

/-- `(G₀, −1/2)` has a member centre, so its body is **not** empty. -/
theorem not_emptyBody_G₀ :
    ¬ EmptyBodyAt QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀ := by
  intro h
  refine h (QMCLeafB.CentreAdm.diagPinch QMCLeafB.FlagsM5.Q₀
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq) ?_
  exact QMCLeafB.RecordsM2.relaxMem_pinch_Q₀

#print axioms QMCLeafB.Integration2M7.not_emptyBody_G₀

/-- **The ok branch is inhabited at the final bit at `(G₀, −1/2)`**, given the reported round's
verdict value there. -/
theorem coreDataG_G₀_at_oW
    (hbit : oW QMCLeafB.ResidRefute.G₀ (-(1 / 2)) = true) :
    Nonempty (QMCLeafB.EndgameM2.CoreDataG oW QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨D⟩ := QMCLeafB.EndgameM2.coreDataG_G₀_inhabited
  exact ⟨{ D with hverdict := by rw [hbit]; exact D.hverdict }⟩

#print axioms QMCLeafB.Integration2M7.coreDataG_G₀_at_oW

end QMCLeafB.Integration2M7

namespace QMCLeafB.Integration2M7

/-! ## 10.  The ok branch is non-vacuous at every member point -/

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (BundleH ResidH)

/-- **An all-member stream at a `true` bit is a residual bundle.**  `anyOk` of the constant-`true`
stream is `true` below a positive horizon, so the verdict slot closes; every cut slot is vacuous.
This is the whole of the ok branch's *shape* — the content of d5 is the per-round member certificate,
not the bundle. -/
def coreDataG_of_memberStream {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hKm : 0 < P.K * P.m)
    (hmem : ∀ k, k < P.K * P.m →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
        (QMCLeafB.RecordsM2.cXst G.n X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hbit : o G t = true) : QMCLeafB.EndgameM2.CoreDataG o G t P hn where
  X := X
  hsym := hsym
  ok := fun _ => true
  hmem := fun k hk _ => hmem k hk
  C := fun k h => absurd h (by simp)
  marg := fun _ => 1
  hmarg := fun k h => absurd h (by simp)
  c := fun _ _ => 0
  hcEq := fun k h => absurd h (by simp)
  hdriftc := fun k h => absurd h (by simp)
  hdriftd := fun k h => absurd h (by simp)
  hverdict := by
    rw [hbit]
    exact ((QMCLeafB.SimLoop.anyOk_eq_true_iff (fun _ => true) (P.K * P.m)).2
      ⟨0, hKm, rfl⟩).symm

#print axioms QMCLeafB.Integration2M7.coreDataG_of_memberStream

/-- A member centre refutes emptiness of the body. -/
theorem not_emptyBody_of_mem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    ¬ EmptyBodyAt G t P hn :=
  fun hE => hE cX h

#print axioms QMCLeafB.Integration2M7.not_emptyBody_of_mem

end QMCLeafB.Integration2M7

namespace QMCLeafB.Integration2M7

/-! ## 11.  The two non-vacuity anchors, classified by branch

The campaign's audit demands that the final family be inhabited at **both** `(G₀, −1/2)` and
`(G₀, −99999/100000)`; the second is where phase 20's shape died.  The spine makes the reason
structural: at `−1/2` the body is non-empty, so the ok branch serves the point; at `−99999/100000`
the body is **empty** (m5's two-test-vector estimate), so *only* the crater branch can serve it and
the reported bit must be `false` there.  Hence the crater is not an optional refinement of the
residual: it is the only shape that reaches the second anchor at all. -/

/-- `EmptyBodyAt` is exactly the hypothesis the shelf's refutation toolkit consumes
(`EmptyBodyM5.flagOf_false_of_emptyBody`, `EndgameM2.coreDataB_at_empty`). -/
theorem emptyBodyAt_iff {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) :
    EmptyBodyAt G t P hn ↔
      ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
            (t - QMCLeafB.RundataCert.eps G) P.dq :=
  Iff.rfl

#print axioms QMCLeafB.Integration2M7.emptyBodyAt_iff

/-- **The body is empty at `(G₀, −99999/100000)`** (m5's estimate, restated in the spine's
predicate). -/
theorem emptyBody_G₀_alt :
    EmptyBodyAt QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀ :=
  fun Q => QMCLeafB.EmptyBodyM5.not_relaxMem_G₀ Q

#print axioms QMCLeafB.Integration2M7.emptyBody_G₀_alt

/-- **At the alt anchor the ok-branch shape is impossible**: `hmem` is unsatisfiable at every round
below a positive horizon. -/
theorem not_memberStream_at_G₀_alt
    (hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) :
    ¬ ∃ X : ℕ → List ℚ,
        ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
            * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m →
          QMCLeafB.RelaxOracle.RelaxMem
            (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
            (QMCLeafB.RecordsM2.cXst QMCLeafB.ResidRefute.G₀.n X
              (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq k)
            (-(99999 / 100000) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
            (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq := by
  rintro ⟨X, hX⟩
  exact emptyBody_G₀_alt (QMCLeafB.RecordsM2.cXst QMCLeafB.ResidRefute.G₀.n X
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq 0) (hX 0 hKm)

#print axioms QMCLeafB.Integration2M7.not_memberStream_at_G₀_alt

/-- **At the alt anchor a `true` reported bit admits no residual bundle** — so the repointed program
bit must be `false` there (the second half of the verdict-lane checksum). -/
theorem coreDataG_G₀_alt_uninhabited_of_bit_true
    (hbit : oW QMCLeafB.ResidRefute.G₀ (-(99999 / 100000)) = true) :
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG oW QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  rintro ⟨D⟩
  have h := verdict_false_of_empty emptyBody_G₀_alt D
  rw [h] at hbit
  exact Bool.noConfusion hbit

#print axioms QMCLeafB.Integration2M7.coreDataG_G₀_alt_uninhabited_of_bit_true

/-- **The anchor pair, as the audit will want it**: the ok anchor's body is non-empty, the alt
anchor's is empty, and a residual at a `true` bit cannot live at the second. -/
theorem anchors_classified :
    (¬ EmptyBodyAt QMCLeafB.ResidRefute.G₀ (-(1 / 2))
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀)
    ∧ EmptyBodyAt QMCLeafB.ResidRefute.G₀ (-(99999 / 100000))
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀ :=
  ⟨not_emptyBody_G₀, emptyBody_G₀_alt⟩

#print axioms QMCLeafB.Integration2M7.anchors_classified



/-! ## 13.  The producer-keyed interface: split on the **bit**, not on the body

§3 splits the interior points by `EmptyBodyAt`.  That is sound but *coarser than the producers*:
`Check_okprod2_m8` §10 machine-checks a point `(G₁, t₁)` whose body is **non-empty** yet no
*pinched* matrix is a member, so no round of the run can carry a member certificate there and every
`CoreDataG` at that point has the bit `false` (and therefore owes the crater).  A producer keyed on
"body non-empty ⇒ ok branch" would be asked for the wrong thing at such a point.

The aligned split is on the verdict bit — which is also what the two producers actually key on: one
frozen member certificate when the bit is `true` (`OkProd_M8.coreDataG_of_okPoint`, reproduced here as
`coreDataG_of_okCert`), the crater record when the bit is `false`.  Since `o G t` is a `Bool`, this
split is exhaustive by `cases`, with no analysis. -/

/-- **The ok point**: one frozen code whose pinched matrix is a member, plus a positive horizon.
(This is `OkProd_M8.OkPoint`; the two structures are inter-derivable field for field.) -/
structure OkCert (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Type where
  /-- the frozen row-major code -/
  x : List ℚ
  /-- its matrix is symmetric -/
  hsym : (QMCLeafB.StateDiag.stMat G.n x)ᵀ = QMCLeafB.StateDiag.stMat G.n x
  /-- **the one member certificate**: the pinched frozen centre is a member -/
  hmem : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
    (QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G.n x) P.dq)
    (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the horizon carries at least one round -/
  hKm : 0 < P.K * P.m

/-- **The ok-branch reduction**: at a `true` bit one member certificate closes the bundle. -/
def coreDataG_of_okCert {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : OkCert G t P) (hT : o G t = true) : QMCLeafB.EndgameM2.CoreDataG o G t P hn :=
  coreDataG_of_memberStream (fun _ => D.x) (fun _ => D.hsym)
    D.hKm (fun _ _ => D.hmem) hT

#print axioms QMCLeafB.Integration2M7.coreDataG_of_okCert

/-- **The crater producer's obligation at `false` bits**: a crater record wherever the bit is
`false`. -/
abbrev CraterSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = false → CoreCrater o G t (Pfam G) hn

/-- **The ok producer's obligation at `true` bits**. -/
abbrev OkSupply (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    o G t = true → OkCert G t (Pfam G)

/-- The residual bundle from the two producers, at the branch the bit selects. -/
def coreDataG_of_supplies {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (K : OkSupply o Pfam) (R : CraterSupply o Pfam)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    QMCLeafB.EndgameM2.CoreDataG o G t (Pfam G) hn :=
  match h : o G t with
  | true => coreDataG_of_okCert (K G t hn hlo hhi h) h
  | false => coreDataG_of_crater (R G t hn hlo hhi h)

#print axioms QMCLeafB.Integration2M7.coreDataG_of_supplies

/-- **The two producers fill the spine**: at each interior point, whichever branch the bit selects. -/
def spineC_of_supplies {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (K : OkSupply o Pfam) (R : CraterSupply o Pfam) : SpineC o Pfam where
  refuted := fun G t hn hlo hhi hem =>
    crater_of_coreDataG hem (coreDataG_of_supplies K R G t hn hlo hhi)
  okpt := fun G t hn hlo hhi _ => coreDataG_of_supplies K R G t hn hlo hhi

#print axioms QMCLeafB.Integration2M7.spineC_of_supplies

/-- **The closing statement at the producer interface**: two supplies keyed on the bit give the
verbatim `d9f601e5` sentence at the reported round. -/
theorem solution_of_supplies (K : OkSupply oW QMCLeafB.UnionShallow.paramsKbc2)
    (R : CraterSupply oW QMCLeafB.UnionShallow.paramsKbc2) :
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
  solution (spineC_of_supplies K R)

#print axioms QMCLeafB.Integration2M7.solution_of_supplies

/-- The same in the shelf's own name for the sentence. -/
theorem solution_statement_of_supplies (K : OkSupply oW QMCLeafB.UnionShallow.paramsKbc2)
    (R : CraterSupply oW QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  endgame_final (spineC_of_supplies K R)

#print axioms QMCLeafB.Integration2M7.solution_statement_of_supplies

/-! ## 14.  A sufficient criterion for the crater's trace slot at a frozen code

The crater's `hdriftd` is stated at the *per-round* centre `cXst G.n X P.dq k`.  With a frozen code
(`X ≡ x`) that centre is the single `diagPinch (stMat G.n x) P.dq`, and `EndgameM2`'s per-round
criteria apply verbatim.  So a refuted-point producer can discharge the trace slot by choosing the
recorded normals so that every weighted diagonal increment of the engine's stream is nonpositive —
exactly the choice m8's `hdriftd_false_pinch` shows is *necessary* (the trace-direction drill
overflows the ceiling, so a normal on the trace direction cannot work). -/

/-- **Crater trace budget from nonpositive weighted increments** (frozen code). -/
theorem crater_hdriftd_of_frozen_nonpos {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {x : List ℚ} {c : ℕ → Fin (G.n * G.n) → ℚ} {marg : ℕ → ℚ}
    (hdq : P.dq ≤ 4)
    (h : ∀ k, k < P.K * P.m → ∀ j, j < k →
      QMCLeafB.DriftExact.engLam (G.n * G.n) (QMCLeafB.EndgameM2.gStream G P hn c marg) j
        * QMCLeafB.DriftExact.diagSum
            (QMCLeafB.EngineIterates.cutPR (QMCLeafB.EndgameM2.gStream G P hn c marg) j) ≤ 0) :
    ∀ k, k < P.K * P.m →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.EndgameM2.gStream G P hn c marg) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat
                  (QMCLeafB.RecordsM2.cXst G.n (fun _ => x) P.dq k)))
        ≤ 0 := by
  intro k hk
  exact QMCLeafB.EndgameM2.hdriftd_of_nonpos_increments hdq
    (QMCLeafB.EndgameM2.gStream G P hn c marg)
    (QMCLeafB.StateDiag.stMat G.n x) k (h k hk)

#print axioms QMCLeafB.Integration2M7.crater_hdriftd_of_frozen_nonpos

/-- **Crater trace budget from a per-round increment bound** (frozen code). -/
theorem crater_hdriftd_of_frozen_bound {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {x : List ℚ} {c : ℕ → Fin (G.n * G.n) → ℚ} {marg : ℕ → ℚ}
    (cst : ℝ) (k : ℕ)
    (h : ∀ j, j < k →
      QMCLeafB.DriftExact.engLam (G.n * G.n) (QMCLeafB.EndgameM2.gStream G P hn c marg) j
        * QMCLeafB.DriftExact.diagSum
            (QMCLeafB.EngineIterates.cutPR (QMCLeafB.EndgameM2.gStream G P hn c marg) j) ≤ cst)
    (hk : (k : ℝ) * cst ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)) :
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.EndgameM2.gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat
                (QMCLeafB.RecordsM2.cXst G.n (fun _ => x) P.dq k)))
      ≤ 0 :=
  QMCLeafB.EndgameM2.hdriftd_of_increment_bound
    (QMCLeafB.EndgameM2.gStream G P hn c marg)
    (QMCLeafB.StateDiag.stMat G.n x) k cst h hk

#print axioms QMCLeafB.Integration2M7.crater_hdriftd_of_frozen_bound

end QMCLeafB.Integration2M7



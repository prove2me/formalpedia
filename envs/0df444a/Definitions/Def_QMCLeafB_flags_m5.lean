-- Prove2me | Definitions.Def_QMCLeafB_flags_m5
-- name    : QMCLeafB_flags_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T04:01:06.369207+00:00
-- url     : https://prove2.me/theorems/55d07150-7104-4919-a989-cddd196376fb
-- title:
--   QMCLeafB flags_m5
-- statement:
--   # leaf B phase 19 — brick `flag-stream` + repair audit (swarm `smw1k12jb`, member m5, direction d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_bundleFull
import Definitions.Def_QMCLeafB_inhabit_m5
import Definitions.Def_QMCLeafB_centre_adm_m1
/-
# leaf B phase 19 — brick `flag-stream` + repair audit (swarm `smw1k12jb`, member m5, direction d7)

Two things, in the order they matter now.

### 1.  Status of the phase-19 refutation (phase-20 audit repair, m6)

m8 (`Check_residrefute_m8`) shows the phase-19 flag stream `hokAll` cannot hold: at the two-vertex
input `G₀` (one edge of weight `1/2`, `Rq G₀ = 1`) and `t = -1/2` — inside the interior bracket —
an all-`false` stream makes the refuted branch's own soundness theorem
(`SimLoop.simulate_refuted_sound`) conclude `∀ Z, IsUnitDiagPSD Z → -1/2 - 1/40000 ≤ frob A Z`,
which is false at `Z₀ = !![1,-1;-1,1]` (`frob A Z₀ = -1`).

When this file was compiled (03:41) `ResidKill.BundleFull` still carried a
`toBundle : ClosingAssembly.Bundle` field, i.e. the refuted `hokAll` stream, and §1 then proved
`ResidFull` unsatisfiable.  **`Check_residkill_m8` was rewritten at 03:43**: `BundleFull` is now a
field-inlined record with no `toBundle`, and its field list is *identical* to `BundleH` below.  The
all-`false` refutation therefore no longer applies to it, and the six theorems that carried it
(`bundle_of_bundleFull`, `hmem_vacuous`, `bundleFull_false_{kbc2,shallow}`,
`residFull_false_{kbc2,shallow}`) are removed in this revision: they were about a record that no
longer exists, and they also made the whole file fail to recompile against the new `ResidKill`.  What
replaces them is the crosswalk of §2b — the two residual shapes are the same obligation, so
`ResidKill.solution_of_residFull` and `solution_of_residH` are interchangeable.
### 2.  The corrected shape, and the flag stream is *free* data

§2 defines `BundleH` — `Bundle` with `hokAll` **replaced** by the `ok`-round `RelaxMem` slot, i.e.
exactly phase-17 `DriftExact.runParts_of_exact_trace`'s hypothesis list — with
`runParts_of_bundleH`, `ResidH` and the two closing strokes re-aimed at it (`hd_of_residH`,
`solution_of_residH`, verbatim `d9f601e5`).  `bundleH_of_bundle` shows nothing is lost: a phase-19
`Bundle` is a `BundleH`.

§3 is the flag-stream content: the *per-round dichotomy* `RelaxMem ∨ Nonempty RelaxCut`
(`RelaxOracle.relaxMem_or_cut`) is total, so on a fixed family of centres the entire stream —
the `ok` bit, the margin `marg`, the normal id `c`, the cut record `C` — is **canonical**, not an
obligation: `flagOf` decides each round, `cutOf` supplies the record on the cut side (with the
zero-normal unit-margin cut as the canonical record when the centre is a member).  Hence the
repaired residual carries *no* free stream data: what a supplier owes is the centres, the scalars
`lam/cn/hlam*`, the trace budget `hTrc`, the drift pair `hdriftc/hdriftd`, and the verdict bit.
`no_mem_then_all_cut` records the exact scope of the all-`false` stream: it is available precisely
at thresholds where no centre at all is a member — which the interior bracket, by m8's kill, is not.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.FlagsM5

open QuantumMaxCutEnergy
open QMCLeafB.RelaxOracle
open QMCLeafB.SepOracle
open Classical

/-! ## 1.  (retired)  the `toBundle`-carrying `BundleFull` refutation

Removed in the phase-20 audit repair (m6, direction `falsify`); see the header and §2b.  The record
that this section refuted — `BundleFull` with a `toBundle : ClosingAssembly.Bundle` field — no longer
exists in `Check_residkill_m8`, and the six theorems that refuted it kept this file from recompiling.
-/

/-! ## 2.  The corrected shape: `hokAll` **replaced** by the `ok`-round `RelaxMem` slot

The structure below is `QMCLeafB.ClosingAssembly.Bundle` with the single line
`hokAll : ∀ k, k < P.K * P.m → ok k = false` **deleted** and the `ok`-round `RelaxMem` slot
(phase 17's `hmem`) inserted in its place.  Every other field is verbatim, so
`DriftExact.runParts_of_exact_trace` consumes it directly — no `noMem_of_allFalse` splice. -/

structure BundleH (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- did round `k` report `ok`? -/
  ok : ℕ → Bool
  /-- the per-round oracle margins -/
  marg : ℕ → ℚ
  /-- the per-round queried centres -/
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the dilation parameters -/
  lam : ℕ → ℚ
  /-- the oracle's flat cut normals -/
  c : ℕ → Fin (G.n * G.n) → ℚ
  /-- the dilated (recorded) flat normals -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- **the cut records** -/
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  /-- **the `ok`-round `RelaxMem` slot** (phase 17's `hmem`): the member certificate, at every round
  that reported `ok` — the slot the all-`false` stream tried to eliminate and cannot -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- **the queried centre is symmetric** -/
  hCsym : ∀ k, (cX k)ᵀ = cX k
  /-- the recorded normal is the oracle's -/
  hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal
  /-- the recorded normal is the dilated one -/
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, ok k = false →
    |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (c k) k|
      + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
          (P) hn cn hcne (c k) k|
      + 9 * marg k ^ 2
          / (4 * ((P).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- **the trace budget at the queried centres** (`hdiagc`, in the trace form) -/
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  /-- the oracle normal's centre mismatch -/
  hdriftc : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- the identity direction's cumulative trace budget -/
  hdriftd : ∀ k, ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **A phase-19 `Bundle` is a `BundleH`** — deleting `hokAll` and adding `hmem` loses nothing: the
added slot is vacuous under the deleted one, so every phase-19 bundle is a bundle in the corrected
sense.  (The converse fails at `(G₀, -1/2)`: §1.) -/
def bundleH_of_bundle {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : QMCLeafB.ClosingAssembly.Bundle o G t P hn) : BundleH o G t P hn :=
  { ok := B.ok
    marg := B.marg
    cX := B.cX
    lam := B.lam
    c := B.c
    cn := B.cn
    C := B.C
    hmarg := B.hmarg
    hmem := fun k hk htrue => absurd htrue (by rw [B.hokAll k hk]; simp)
    hCsym := B.hCsym
    hcEq := B.hcEq
    hcn := B.hcn
    hcne := B.hcne
    hlam0 := B.hlam0
    hlam1 := B.hlam1
    hlam2 := B.hlam2
    hTrc := B.hTrc
    hdriftc := B.hdriftc
    hdriftd := B.hdriftd
    hverdict := B.hverdict }

/-! ### 2b.  Crosswalk to `ResidKill.BundleFull` (phase-20 audit repair)

`Check_residkill_m8` now defines `BundleFull` as a field-inlined record — the very field list of
`BundleH` above (`ok`, `marg`, `cX`, `lam`, `c`, `cn`, `C`, `hmarg`, `hmem`, `hCsym`, `hcEq`, `hcn`,
`hcne`, `hlam0`, `hlam1`, `hlam2`, `hTrc`, `hdriftc`, `hdriftd`, `hverdict`) — with no
`ClosingAssembly.Bundle` inside it.  So the two residual interfaces are the same obligation, and the
two closing strokes (`ResidKill.solution_of_residFull`, `solution_of_residH`) are interchangeable:
nothing is lost by working at either. -/

/-- **`BundleH` is a `ResidKill.BundleFull`** (field for field; the two records are the same list). -/
def bundleFull_of_bundleH {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : BundleH o G t P hn) : QMCLeafB.ResidKill.BundleFull o G t P hn where
  ok := B.ok
  marg := B.marg
  cX := B.cX
  lam := B.lam
  c := B.c
  cn := B.cn
  C := B.C
  hmarg := B.hmarg
  hmem := B.hmem
  hCsym := B.hCsym
  hcEq := B.hcEq
  hcn := B.hcn
  hcne := B.hcne
  hlam0 := B.hlam0
  hlam1 := B.hlam1
  hlam2 := B.hlam2
  hTrc := B.hTrc
  hdriftc := B.hdriftc
  hdriftd := B.hdriftd
  hverdict := B.hverdict

#print axioms QMCLeafB.FlagsM5.bundleFull_of_bundleH

/-- **A `ResidKill.BundleFull` is a `BundleH`** (field for field, the converse direction). -/
def bundleH_of_bundleFull {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : QMCLeafB.ResidKill.BundleFull o G t P hn) : BundleH o G t P hn where
  ok := B.ok
  marg := B.marg
  cX := B.cX
  lam := B.lam
  c := B.c
  cn := B.cn
  C := B.C
  hmarg := B.hmarg
  hmem := B.hmem
  hCsym := B.hCsym
  hcEq := B.hcEq
  hcn := B.hcn
  hcne := B.hcne
  hlam0 := B.hlam0
  hlam1 := B.hlam1
  hlam2 := B.hlam2
  hTrc := B.hTrc
  hdriftc := B.hdriftc
  hdriftd := B.hdriftd
  hverdict := B.hverdict

#print axioms QMCLeafB.FlagsM5.bundleH_of_bundleFull

/-- **The corrected bundle is a `RunParts`** — the phase-17 drift brick applied to the corrected
slot list, with no flag-stream hypothesis anywhere. -/
def runParts_of_bundleH (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (B : BundleH o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.DriftExact.runParts_of_exact_trace o G t P hn hrmaxPos hrmax1 hbudP
    B.ok B.marg B.cX B.lam B.c B.cn B.C B.hmarg B.hmem
    B.hCsym B.hcEq B.hcn B.hcne B.hlam0 B.hlam1 B.hlam2 B.hTrc
    B.hdriftc B.hdriftd B.hverdict

#print axioms QMCLeafB.FlagsM5.runParts_of_bundleH

/-- **The corrected residual**: one `BundleH` per interior `(G, t)`. -/
abbrev ResidH (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    BundleH o G t (Pfam G) hn

/-- **`ResidH` gives `ResidKill.ResidFull`**: the two residual interfaces are the same bracket
obligation, so either closing stroke closes the leaf. -/
def residH_to_residFull {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidH o Pfam) : QMCLeafB.ResidKill.ResidFull o Pfam :=
  fun G t hn hlo hhi => bundleFull_of_bundleH (h G t hn hlo hhi)

#print axioms QMCLeafB.FlagsM5.residH_to_residFull

/-- **`ResidKill.ResidFull` gives `ResidH`** (the converse). -/
def residFull_to_residH {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : QMCLeafB.ResidKill.ResidFull o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_bundleFull (h G t hn hlo hhi)

#print axioms QMCLeafB.FlagsM5.residFull_to_residH

/-- **`hd` at `RoundProgram.round` from the corrected residual.** -/
def hd_of_residH
    (h : ResidH (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp := by
  intro G t hn hlo hhi
  exact runParts_of_bundleH _ G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (h G t hn hlo hhi)

#print axioms QMCLeafB.FlagsM5.hd_of_residH

/-- **`d9f601e5` from the corrected residual, in the shelf's own name for the sentence.** -/
theorem solution_statement_of_residH
    (h : ResidH (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.AssemblyM5.endgame_of_hd_statement (hd_of_residH h)

#print axioms QMCLeafB.FlagsM5.solution_statement_of_residH

/-- **The verbatim `d9f601e5` sentence from the corrected residual.** -/
theorem solution_of_residH
    (h : ResidH (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hd_of_residH h)

#print axioms QMCLeafB.FlagsM5.solution_of_residH

/-! ## 3.  The flag stream is *canonical*: the per-round dichotomy supplies it

`RelaxOracle.relaxMem_or_cut` is total — every rational centre is either a member of the relaxation
or is separated from it by an explicit rational cut.  Hence, once the centres are fixed, the flag
bit, the cut record, the margin and the normal id of every round are *canonical*:
`flagOf` decides, `cutOf` supplies the record.  So the repaired residual owes no stream data at
all: `StreamCore` below carries only the centres, the scalars, the trace budget, the drift pair and
the verdict bit, and `bundleH_of_core` turns it into a `BundleH`. -/

/-- The canonical trivial cut record: zero normal, margin `1`.  (Used as the record on the member
side of the dichotomy, where no genuine cut is needed.) -/
def defaultCut {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) : RelaxCut A cX u δ where
  normal := 0
  margin := 1
  margin_pos := by norm_num
  separates := by
    intro X hX
    simp [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.castMat]

/-- **The canonical flag bit of round `k`**: `true` iff the queried centre is a member of the
relaxation at the round's threshold. -/
noncomputable def flagOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : Bool :=
  if RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq then true else false

/-- **The member side of the dichotomy**: a `true` flag carries its `RelaxMem` certificate. -/
theorem relaxMem_of_flagOf_true (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ)
    (h : flagOf G t P cX k = true) :
    RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq := by
  by_contra hc
  simp [flagOf, hc] at h

#print axioms QMCLeafB.FlagsM5.relaxMem_of_flagOf_true

/-- The flag is `false` at a centre that is not a member. -/
theorem flagOf_false_of_not_mem (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ)
    (h : ¬ RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    flagOf G t P cX k = false := by
  simp [flagOf, h]

#print axioms QMCLeafB.FlagsM5.flagOf_false_of_not_mem

/-- **The canonical cut record of round `k`**: the separating record chosen from the dichotomy when
the centre is not a member, the trivial record otherwise. -/
noncomputable def cutOf (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq :=
  if h : RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq then
    defaultCut _ _ _ _
  else
    Classical.choice ((relaxMem_or_cut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq P.hdq).resolve_left h)

/-- **The cut side of the dichotomy**: the canonical record separates, with a positive margin. -/
theorem cutOf_spec (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    0 < (cutOf G t P cX k).margin ∧
      ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
            (QMCLeafB.Finalization.wMatrixQ G))
          (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ) (((P.dq : ℚ)) : ℝ) X →
        -(((((cutOf G t P cX k).margin : ℚ)) : ℝ)) ≤
          frob (QMCLeafB.SepOracle.castMat (cutOf G t P cX k).normal)
            (X - QMCLeafB.SepOracle.castMat (cX k)) :=
  ⟨(cutOf G t P cX k).margin_pos, fun X hX => (cutOf G t P cX k).separates X hX⟩

#print axioms QMCLeafB.FlagsM5.cutOf_spec

/-- **The exact scope of the all-`false` stream**: at a threshold where no centre at all is a
member, every round's flag is `false` — for *any* family of centres.  (m8's kill shows the interior
bracket is not such a threshold, which is why `hokAll` cannot be imposed there.) -/
theorem flagOf_all_false (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (h : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    flagOf G t P cX k = false :=
  flagOf_false_of_not_mem G t P cX k (h (cX k))

#print axioms QMCLeafB.FlagsM5.flagOf_all_false

/-- **The stream core**: the corrected residual minus the flag stream — centres, scalars, trace
budget, drift pair, verdict bit.  The stream itself is produced by §3's canonical construction. -/
structure StreamCore (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the per-round queried centres -/
  cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  /-- the dilation parameters -/
  lam : ℕ → ℚ
  /-- the dilated (recorded) flat normals -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- the queried centre is symmetric -/
  hCsym : ∀ k, (cX k)ᵀ = cX k
  /-- the recorded normal is the canonical cut's, dilated -/
  hcn : ∀ k, cn k = QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal
    + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, flagOf G t P cX k = false → 1 ≤ lam k
  hlam2 : ∀ k, flagOf G t P cX k = false →
    |QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal) k|
      + |QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal) k|
      + 9 * ((cutOf G t P cX k).margin) ^ 2 / (4 * ((P).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- the trace budget at the queried centres -/
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  /-- the canonical normal's centre mismatch -/
  hdriftc : ∀ k, flagOf G t P cX k = false →
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((((cutOf G t P cX k).margin : ℚ)) : ℝ) / 2
  /-- the identity direction's cumulative trace budget -/
  hdriftd : ∀ k, flagOf G t P cX k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m)

/-- **The corrected residual with the flag stream restored canonically.**  Nothing about the stream
is assumed: `ok`, `marg`, `c`, `C` and the member certificates are the canonical ones. -/
def bundleH_of_core {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (S : StreamCore o G t P hn) : BundleH o G t P hn where
  ok := flagOf G t P S.cX
  marg := fun k => (cutOf G t P S.cX k).margin
  cX := S.cX
  lam := S.lam
  c := fun k => QMCLeafB.RelaxOracle.flatQ (cutOf G t P S.cX k).normal
  cn := S.cn
  C := fun k _ => cutOf G t P S.cX k
  hmarg := fun k _ => rfl
  hmem := fun k _ htrue => relaxMem_of_flagOf_true G t P S.cX k htrue
  hCsym := S.hCsym
  hcEq := fun k _ => rfl
  hcn := S.hcn
  hcne := S.hcne
  hlam0 := S.hlam0
  hlam1 := S.hlam1
  hlam2 := S.hlam2
  hTrc := S.hTrc
  hdriftc := S.hdriftc
  hdriftd := S.hdriftd
  hverdict := S.hverdict

#print axioms QMCLeafB.FlagsM5.bundleH_of_core

/-- **The corrected residual, at the stream-core shape.** -/
abbrev ResidCore (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    StreamCore o G t (Pfam G) hn

/-- **`ResidH` from `ResidCore`**: the canonical stream is built, not owed. -/
def residH_of_core {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidCore o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_core (h G t hn hlo hhi)

#print axioms QMCLeafB.FlagsM5.residH_of_core

/-- **`d9f601e5` from the stream core** — the end of the chain: the verbatim sentence from the
centres, the scalars, the trace budget, the drift pair and the verdict bit. -/
theorem solution_of_residCore
    (h : ResidCore (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_residH (residH_of_core h)

#print axioms QMCLeafB.FlagsM5.solution_of_residCore

/-! ## 4.  The corrected shape is *inhabited* where the phase-19 shape is refuted

m8's kill is at `(G₀, -1/2)` (`G₀` the two-vertex input with one edge of weight `1/2`).  The
corrected shape is not vacuous there: an all-`ok` stream with the centres at the pinch boundary
`(1 - dq/4) • Q₀`, `Q₀ = !![1, -3/4; -3/4, 1]`, satisfies every slot of `BundleH`.  So the repair
replaces a false obligation by a satisfiable one — it is not a vacuous dodge. -/

/-- The pinch-boundary shape at the two-vertex input: unit diagonal, positive semidefinite, and its
objective is `-3/4` — deep enough below `t - ε = -1/2 - 1/40000` to be a member. -/
noncomputable def Q₀ : Matrix (Fin 2) (Fin 2) ℚ := !![1, -(3 / 4); -(3 / 4), 1]

theorem Q₀_diag (i : Fin 2) : Q₀ i i = 1 := by
  fin_cases i <;> simp [Q₀]

theorem Q₀_symm (i j : Fin 2) : Q₀ j i = Q₀ i j := by
  fin_cases i <;> fin_cases j <;> simp [Q₀]

theorem Q₀_transpose : Q₀ᵀ = Q₀ := by
  ext i j
  rw [Matrix.transpose_apply]
  exact Q₀_symm i j

/-- `Q₀` is positive semidefinite over `ℚ`. -/
theorem Q₀_qf (x : Fin 2 → ℚ) : 0 ≤ QMCLeafB.SepOracle.qf Q₀ x := by
  rw [QMCLeafB.SepOracle.qf_eq_sum]
  simp only [Fin.sum_univ_two, Q₀, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.of_apply]
  nlinarith [sq_nonneg (x 0 - (3 / 4) * x 1), sq_nonneg (x 1)]

/-- **The objective at `Q₀`**: `frob (wMatrixQ G₀) Q₀ = -3/4`. -/
theorem frob_Q₀ :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) Q₀
      = -(3 / 4) := by
  have e00 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  have e11 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 0 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  have e01 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (0 : Fin QMCLeafB.ResidRefute.G₀.n) (1 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  have e10 : QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀
      (1 : Fin QMCLeafB.ResidRefute.G₀.n) (0 : Fin QMCLeafB.ResidRefute.G₀.n) = 1 / 2 := by
    unfold QMCLeafB.Finalization.wMatrixQ
    norm_num [QMCLeafB.ResidRefute.G₀]
  simp only [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, e00, e01, e10, e11, Q₀,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply]
  norm_num

/-- **The campaign tolerance at `G₀`**: `ε = Rq/40000 = 1/40000`. -/
theorem eps_G₀ : QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀ = 1 / 40000 := by
  unfold QMCLeafB.RundataCert.eps
  rw [QMCLeafB.ResidRefute.Rq_G₀]

/-- **The `ok`-round certificate at `(G₀, -1/2)`**: the pinch boundary is a member of the relaxation
at the round threshold `-1/2 - ε`.  This is the slot the all-`false` stream tried to delete. -/
theorem relaxMem_G₀ :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
      ((1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀)
      (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq QMCLeafB.ResidRefute.G₀ := by
    rw [QMCLeafB.ResidRefute.Rq_G₀]
    norm_num
  have hδ : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq :=
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).hdq
  have hδ4 : (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq ≤ 4 := by
    rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
    exact QMCLeafB.CentreAdm.dqShallow_le_four QMCLeafB.ResidRefute.G₀ hRq
  exact QMCLeafB.InhabitM5.relaxMem_pinch
    (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀) Q₀ hδ hδ4 Q₀_diag Q₀_qf
    (by rw [frob_Q₀, eps_G₀]; nlinarith [hδ])

/-- The dilation direction `flatQ 1` is nonzero. -/
theorem flatQ_one_ne_zero' {n : ℕ} (hn : 0 < n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  intro h
  have h1 : QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ)
      (finProdFinEquiv ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n))) = 0 := by
    rw [h]
    rfl
  have hs : finProdFinEquiv.symm (finProdFinEquiv ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n)))
      = ((⟨0, hn⟩ : Fin n), (⟨0, hn⟩ : Fin n)) := Equiv.symm_apply_apply _ _
  rw [QMCLeafB.RelaxOracle.flatQ, hs] at h1
  rw [Matrix.one_apply_eq] at h1
  exact one_ne_zero h1

/-- **The corrected residual is inhabited at `(G₀, -1/2)`** — the exact point at which §1 refutes the
phase-19 shape.  The all-`ok` stream makes the cut-side slots (`C`, `hlam1`, `hlam2`, `hdriftc`,
`hdriftd`) vacuous, and `hmem` is the certificate of `relaxMem_G₀`. -/
theorem bundleH_G₀_inhabited :
    Nonempty (BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
      * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
  have hany : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true)
      ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
    conv_lhs => rw [show (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m
          = ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
              * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m - 1) + 1 from by omega]
    exact QMCLeafB.InhabitM5.anyOk_true_succ _
  have hfalse : ∀ k : ℕ, (fun _ : ℕ => true) k = false → False :=
    fun k hk => absurd hk (QMCLeafB.InhabitM5.okTrue_ne_false k)
  refine ⟨{ ok := fun _ => true
            marg := fun _ => 1
            cX := fun _ => (1 - (QMCLeafB.UnionShallow.paramsKbc2
              QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀
            lam := fun _ => 1
            c := fun _ => 0
            cn := fun _ => QMCLeafB.RelaxOracle.flatQ
              (1 : Matrix (Fin QMCLeafB.ResidRefute.G₀.n) (Fin QMCLeafB.ResidRefute.G₀.n) ℚ)
            C := fun k hok => (hfalse k hok).elim
            hmarg := fun k hok => (hfalse k hok).elim
            hmem := fun k _ _ => relaxMem_G₀
            hCsym := fun _ => by
              show ((1 - (QMCLeafB.UnionShallow.paramsKbc2
                QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀)ᵀ
                = (1 - (QMCLeafB.UnionShallow.paramsKbc2
                  QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀
              rw [Matrix.transpose_smul, Q₀_transpose]
            hcEq := fun k hok => (hfalse k hok).elim
            hcn := fun _ => by
              show QMCLeafB.RelaxOracle.flatQ
                  (1 : Matrix (Fin QMCLeafB.ResidRefute.G₀.n) (Fin QMCLeafB.ResidRefute.G₀.n) ℚ)
                = 0 + (1 : ℚ) • QMCLeafB.RelaxOracle.flatQ 1
              simp
            hcne := fun _ => flatQ_one_ne_zero' (by norm_num)
            hlam0 := fun _ => by norm_num
            hlam1 := fun k hok => (hfalse k hok).elim
            hlam2 := fun k hok => (hfalse k hok).elim
            hTrc := fun _ => by
              have htr : ∑ i, ((1 - (QMCLeafB.UnionShallow.paramsKbc2
                    QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀) i i
                  = 2 * (1 - (QMCLeafB.UnionShallow.paramsKbc2
                      QMCLeafB.ResidRefute.G₀).dq / 4) := by
                rw [Fin.sum_univ_two]
                simp only [Matrix.smul_apply, smul_eq_mul, Q₀_diag, mul_one]
                ring
              have hn2 : ((QMCLeafB.ResidRefute.G₀.n : ℕ) : ℚ) = 2 := by
                norm_num [QMCLeafB.ResidRefute.G₀]
              show ∑ i, ((1 - (QMCLeafB.UnionShallow.paramsKbc2
                    QMCLeafB.ResidRefute.G₀).dq / 4) • Q₀) i i
                ≤ (QMCLeafB.ResidRefute.G₀.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2
                    QMCLeafB.ResidRefute.G₀).dq / 4)
              rw [htr, hn2]
            hdriftc := fun k hok => (hfalse k hok).elim
            hdriftd := fun k hok => (hfalse k hok).elim
            hverdict := hany.symm }⟩

#print axioms QMCLeafB.FlagsM5.frob_Q₀
#print axioms QMCLeafB.FlagsM5.eps_G₀
#print axioms QMCLeafB.FlagsM5.relaxMem_G₀
#print axioms QMCLeafB.FlagsM5.bundleH_G₀_inhabited

end QMCLeafB.FlagsM5

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.FlagsM5.bundleH_of_bundle
#print axioms QMCLeafB.FlagsM5.bundleFull_of_bundleH
#print axioms QMCLeafB.FlagsM5.bundleH_of_bundleFull
#print axioms QMCLeafB.FlagsM5.residH_to_residFull
#print axioms QMCLeafB.FlagsM5.residFull_to_residH
#print axioms QMCLeafB.FlagsM5.runParts_of_bundleH
#print axioms QMCLeafB.FlagsM5.hd_of_residH
#print axioms QMCLeafB.FlagsM5.solution_statement_of_residH
#print axioms QMCLeafB.FlagsM5.solution_of_residH
#print axioms QMCLeafB.FlagsM5.relaxMem_of_flagOf_true
#print axioms QMCLeafB.FlagsM5.flagOf_false_of_not_mem
#print axioms QMCLeafB.FlagsM5.cutOf_spec
#print axioms QMCLeafB.FlagsM5.flagOf_all_false
#print axioms QMCLeafB.FlagsM5.bundleH_of_core
#print axioms QMCLeafB.FlagsM5.residH_of_core
#print axioms QMCLeafB.FlagsM5.solution_of_residCore



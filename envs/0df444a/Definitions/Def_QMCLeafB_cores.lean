-- Prove2me | Definitions.Def_QMCLeafB_cores
-- name    : QMCLeafB_cores
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:33:57.585188+00:00
-- url     : https://prove2.me/theorems/8dbb1c53-d594-4cfb-a198-496b7017a91f
-- title:
--   QMCLeafB cores
-- statement:
--   # leaf B phase 20 — degenerate-centre cores (swarm `smw1kspvn`, member m1, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_flags_m5
import Definitions.Def_QMCLeafB_inhabit_m5
import Definitions.Def_QMCLeafB_centre_adm_m1
/-
# leaf B phase 20 — degenerate-centre cores (swarm `smw1kspvn`, member m1, direction d5)

The phase-20 residual is `QMCLeafB.FlagsM5.ResidCore`: one `StreamCore o G t P hn` per interior
`(G, t)`.  `BundleH` is already `hmem`-free on the member side (`FlagsM5.relaxMem_of_flagOf_true`
extracts the certificate from the canonical flag) and `C`/`marg`/`c`-free on the cut side
(`FlagsM5.cutOf` supplies the record), so the *only* freedom in a `StreamCore` is

    the centre family `cX`, the dilation scalars `lam`, the dilated normals `cn`,
    the trace budget `hTrc`, the drift pair `hdriftc`/`hdriftd`, and the verdict bit `hverdict`.

This file takes the centre family away too, and closes the two *degenerate* patches of it where the
drift content is empty.  It is disjoint from the interior brick (d3): nothing here touches the
carrier `∑_j λ_j diagSum p_j` or the `witAt` pairing used at a genuine cut round.

## §1  The canonical centre family is `diagPinch` of the run's states, and two slots are free

`QMCLeafB.CentreAdm.diagPinch` overwrites the diagonal with `1 − dq/4` and nothing else.  For that
family — at *every* base matrix, no hypothesis on the base at all —

* the trace budget holds **with equality** (`sum_diagPinch`), and
* symmetry is inherited (`diagPinch_symm`).

So `hCsym` and `hTrc` are not obligations of the residual: `centreOf` below discharges both, for an
arbitrary state sequence `Q`.

## §2  The reduced residual

`CoreData` is `StreamCore` with `cX` replaced by `centreOf P Q` and with `hCsym`/`hTrc`/`hcn`
supplied by §1.  `streamCoreOfCore` turns it back into `StreamCore`, so a supplier of the interior
brick owes only the scalars, the dilated normals, the two drift inequalities and the verdict bit —
at centres that are already fixed.

## §3  The closing applications, at the verbatim `d9f601e5` type

`residCore_of_coreData` and `solution_of_coreData` are the two `FlagsM5` strokes pre-composed with
`streamCoreOfCore`, so brick-2 output at the `CoreData` shape closes the leaf with no further glue.

## §4–§5  The degenerate patches

`flagOf` decides membership; where the canonical centre is *provably* a member the whole cut side of
the round is vacuous and the record costs nothing.  Two machine-checked sources of that:

* **pinch centres** — a base already sitting on the boundary `diag = 1 − dq/4` is its own
  `diagPinch`, and carries `RelaxMem` from its own PSD margin and trace test alone
  (`relaxMem_of_pinched`: the diagonal shift costs nothing, which is the `ok`-branch pinch of
  phase 17 in the conduit's own `δ/2` currency);
* **unit-diagonal states** — `dvR = 0` states: `dvR = 0` forces the diagonal to `1`
  (`QMCLeafB.CentreAdm.unit_diag_of_dvR_zero`), and `CentreAdm.relaxMem_diagPinch` then gives
  `RelaxMem` at `diagPinch` from the state's exact PSD and the programme's own `ok` test.

§9–§10 are the missing dictionary in the other direction: `dOne` *is* the identity's flattening and
`flatQ normal` is the cut's own functional, so the two drift slots — stated in the engine's flat
coordinates — are exactly
    hdriftd : tr(state_k) ≤ n(1 − dq/4)          (the phase-18 trace budget),
    hdriftc : frob (castMat normal_k) (state_k − centre_k) ≤ margin_k / 2   (centre tracking).
No ellipsoid survives either, and at a steady round (state = centre) both are free.

`CoreData` reaches `BundleH`, `RunParts` and `hd` by `bundleH_of_coreData` /
`runParts_of_coreData` / `hd_of_coreData`.

Hence: if every round of the patch is degenerate, the *whole* `StreamCore` exists, with `lam ≡ 1`,
`cn ≡ flatQ 1` and the four cut-side slots vacuous (`coreData_allTrue`, `streamCore_allTrue`).  That
is the degenerate-core closure of my registered direction; the interior is exactly the complement.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end.  `Solutions/Check_flags_m5.lean` is imported read-only (m6 owns its §1
patch); nothing here depends on the patched `ResidKill` section.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CoresM1

open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5
open QMCLeafB.RelaxOracle
open QMCLeafB.SepOracle
open QMCLeafB.CentreAdm
open Classical

/-! ## 1.  The canonical centre family `diagPinch` of the run's states -/

/-- **The canonical centre family**: the run's state sequence with every diagonal overwritten by
`1 − P.dq/4`.  This is the family phase 18's centre ledger forces (`CentreAdm.diagPinch`) — no
rescaling of the state can serve (`CentreAdm.smul_centre_admissible_iff`). -/
def centreOf {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ :=
  fun k => diagPinch (Q k) P.dq

theorem centreOf_apply {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    centreOf P Q k = diagPinch (Q k) P.dq := rfl

/-- **`hCsym` is free**: `diagPinch` preserves symmetry, at every base. -/
theorem centreOf_symm {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} (hQ : ∀ k i j, Q k i j = Q k j i) (k : ℕ) :
    (centreOf P Q k)ᵀ = centreOf P Q k := by
  ext i j
  rw [Matrix.transpose_apply]
  simp only [centreOf]
  exact diagPinch_symm (fun i j => hQ k i j) P.dq j i

/-- **`hTrc` is free, with equality**: the pinched centre's trace is exactly `n(1 − dq/4)`,
whatever the base. -/
theorem centreOf_trace {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    ∑ i, centreOf P Q k i i = (G.n : ℚ) * (1 - P.dq / 4) :=
  sum_diagPinch (Q k) P.dq

/-- The trace budget, in the inequality form the conduit asks. -/
theorem centreOf_trace_le {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    ∑ i, centreOf P Q k i i ≤ (G.n : ℚ) * (1 - P.dq / 4) :=
  le_of_eq (centreOf_trace P Q k)

/-- The pinch is invisible to the weight matrix: `wMatrixQ` has zero diagonal, so the overwrite does
not move `frob` (hence not `RelaxMem.trace_le` either).  This is `CentreAdm.frob_diagPinch` at the
campaign's weight matrix. -/
theorem frob_centreOf {G : QuantumMaxCutEnergy.Input} (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    frob (QMCLeafB.Finalization.wMatrixQ G) (centreOf P Q k)
      = frob (QMCLeafB.Finalization.wMatrixQ G) (Q k) :=
  frob_diagPinch (fun _ => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) 

/-- `flatQ` of the zero matrix is zero. -/
theorem flatQ_zero {n : ℕ} : QMCLeafB.RelaxOracle.flatQ (0 : Matrix (Fin n) (Fin n) ℚ) = 0 := by
  funext k
  simp [QMCLeafB.RelaxOracle.flatQ]

/-! ## 2.  The reduced residual: `StreamCore` with the centre family fixed

`StreamCore` has thirteen fields.  With `cX := centreOf P Q` three of them are decided by §1
(`hCsym`, `hTrc`, and `hcn` which becomes a definition of `cn` in terms of `lam`), so what a
supplier of the interior brick actually owes is the *drift* content and the verdict bit.

Nothing about the base sequence `Q` is assumed beyond symmetry: in particular the states need not be
PSD, unit-diagonal, or pinched.  Both degenerate patches of §4–§5 are special cases.
-/

/-- **The reduced residual at a fixed centre family.**  `ok`, `marg`, `c`, `C` and the member
certificates are already canonical (`FlagsM5.flagOf`/`cutOf`); the centres are `centreOf P Q`; the
trace budget and symmetry are §1.  What remains is exactly the dilation data and the two drift
inequalities — the content of the interior brick. -/
structure CoreData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) : Type where
  /-- the base state sequence is symmetric -/
  hQsym : ∀ k i j, Q k i j = Q k j i
  /-- the dilation parameters -/
  lam : ℕ → ℚ
  /-- the dilated (recorded) flat normals -/
  cn : ℕ → Fin (G.n * G.n) → ℚ
  /-- the recorded normal is the canonical cut's, dilated -/
  hcn : ∀ k, cn k = QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal
    + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, flagOf G t P (centreOf P Q) k = false → 1 ≤ lam k
  hlam2 : ∀ k, flagOf G t P (centreOf P Q) k = false →
    |QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
        + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal) k|
      + |QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal) k|
      + 9 * ((cutOf G t P (centreOf P Q) k).margin) ^ 2 / (4 * ((P).rmax) ^ 2) + 1
    ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
        QMCLeafB.RunPartsDilate.witAt G (P) hn
          cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k)
  /-- the canonical normal's centre mismatch -/
  hdriftc : ∀ k, flagOf G t P (centreOf P Q) k = false →
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (centreOf P Q k)))
      ≤ ((((cutOf G t P (centreOf P Q) k).margin : ℚ)) : ℝ) / 2
  /-- the identity direction's cumulative trace budget -/
  hdriftd : ∀ k, flagOf G t P (centreOf P Q) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (centreOf P Q k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (centreOf P Q)) (P.K * P.m)

/-- **`CoreData` is a `StreamCore`.**  §1 supplies the three centre slots; nothing else is touched. -/
def streamCoreOfCore {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} (D : CoreData o G t P hn Q) :
    StreamCore o G t P hn where
  cX := centreOf P Q
  lam := D.lam
  cn := D.cn
  hCsym := fun k => centreOf_symm P D.hQsym k
  hcn := D.hcn
  hcne := D.hcne
  hlam0 := D.hlam0
  hlam1 := D.hlam1
  hlam2 := D.hlam2
  hTrc := fun k => centreOf_trace_le P Q k
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.CoresM1.streamCoreOfCore

/-- **A reduced core at a chosen base**: the base sequence, its symmetry, and the `CoreData` at the
`diagPinch` centre family it induces.  The base is the supplier's to choose — the run's own states
are one choice, not the only one (§7 uses the pinch base). -/
structure CoreAt (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ
  hQsym : ∀ k i j, Q k i j = Q k j i
  core : CoreData o G t P hn Q

/-- **The residual, at the reduced shape**: one `CoreAt` per interior `(G, t)`. -/
abbrev ResidCoreData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreAt o G t (Pfam G) hn

/-- **`FlagsM5.ResidH` from the reduced residual** — the whole centre bookkeeping (choice of base,
`hCsym`, `hTrc`) is gone. -/
def residH_of_coreData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidCoreData o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => FlagsM5.bundleH_of_core (streamCoreOfCore (h G t hn hlo hhi).core)

#print axioms QMCLeafB.CoresM1.residH_of_coreData

/-- **`FlagsM5.ResidCore` from the reduced residual.** -/
def residCore_of_coreData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidCoreData o Pfam) : ResidCore o Pfam :=
  fun G t hn hlo hhi => streamCoreOfCore (h G t hn hlo hhi).core

#print axioms QMCLeafB.CoresM1.residCore_of_coreData

/-- **The verbatim `d9f601e5` sentence from the reduced residual** — the closing stroke, applied. -/
theorem solution_of_coreData
    (h : ResidCoreData (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_residCore (residCore_of_coreData h)

#print axioms QMCLeafB.CoresM1.solution_of_coreData

/-- **The leaf's own statement shape from the reduced residual.** -/
theorem solution_statement_of_coreData
    (h : ResidCoreData (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_residH (residH_of_coreData h)

#print axioms QMCLeafB.CoresM1.solution_statement_of_coreData

/-- **`CoreData` delivers the `BundleH`** — the corrected residual's own shape. -/
def bundleH_of_coreData {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} (D : CoreData o G t P hn Q) :
    BundleH o G t P hn :=
  bundleH_of_core (streamCoreOfCore D)

#print axioms QMCLeafB.CoresM1.bundleH_of_coreData

/-- **`CoreData` delivers the `RunParts` payload** — i.e. the `hd` slot of the endgame, with the
rounding budget and the ceiling side conditions supplied as in `FlagsM5.runParts_of_bundleH`. -/
def runParts_of_coreData (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} (D : CoreData o G t P hn Q) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  runParts_of_bundleH o G t P hn hrmaxPos hrmax1 hbudP (bundleH_of_coreData D)

#print axioms QMCLeafB.CoresM1.runParts_of_coreData

/-- **`hd` at the campaign's `round` family from the reduced residual** — the endgame's soundness
payload, with `CoreData` as the only content. -/
def hd_of_coreData
    (h : ResidCoreData (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  QMCLeafB.FlagsM5.hd_of_residH (residH_of_coreData h)

#print axioms QMCLeafB.CoresM1.hd_of_coreData
/-! ## 3.  Where the canonical centre is a member, the round costs nothing

`flagOf` is the membership decision (`FlagsM5.flagOf`), so a round whose canonical centre is
provably inside the relaxation has

* `cutOf = defaultCut` — the record's normal is `0` (`flatQ_normal_of_relaxMem`),
* hence `cn = lam • flatQ 1`, which is nonzero as soon as the dilation direction is
  (`flatQ_one_ne_zero'`),
* and all four cut-side slots (`hlam1`, `hlam2`, `hdriftc`, `hdriftd`) are vacuous.

That is the whole content of a degenerate round; the two machine-checked sources of membersez are §4
and §5. -/

/-- **Membership is the canonical flag.**  Conversely to `FlagsM5.relaxMem_of_flagOf_true`: with a
`RelaxMem` certificate in hand the flag is `true` by definition. -/
theorem flagOf_true_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    flagOf G t P cX k = true := by
  simp only [flagOf]
  exact if_pos h

#print axioms QMCLeafB.CoresM1.flagOf_true_of_relaxMem

/-- **A `true` flag and a `false` flag cannot both hold** — the shape `CoreData`'s cut-side slots
consume. -/
theorem flag_true_ne_false {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : flagOf G t P cX k = true) (hf : flagOf G t P cX k = false) : False := by
  rw [h] at hf
  exact Bool.noConfusion hf

/-- **At a member the canonical cut is the trivial one**: `cutOf` returns `defaultCut`, whose normal
is `0`.  (Nothing about the *cut* side is needed when the centre is inside.) -/
theorem cutOf_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    cutOf G t P cX k
      = defaultCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
          (t - QMCLeafB.RundataCert.eps G) P.dq := by
  simp only [cutOf]
  exact dif_pos h

#print axioms QMCLeafB.CoresM1.cutOf_of_relaxMem

/-- **The member side has no normal**: `flatQ` of the canonical record's normal vanishes. -/
theorem flatQ_normal_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq) :
    QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal = 0 := by
  rw [cutOf_of_relaxMem h]
  show QMCLeafB.RelaxOracle.flatQ (0 : Matrix (Fin G.n) (Fin G.n) ℚ) = 0
  exact flatQ_zero

#print axioms QMCLeafB.CoresM1.flatQ_normal_of_relaxMem

/-- `anyOk` of an all-`true` stream over a positive round count. -/
theorem anyOk_allTrue (ν : ℕ) (h : 0 < ν) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) ν = true := by
  conv_lhs => rw [show ν = (ν - 1) + 1 from by omega]
  exact QMCLeafB.InhabitM5.anyOk_true_succ (ν - 1)

#print axioms QMCLeafB.CoresM1.anyOk_allTrue

/-! ## 4.  Pinch centres: a base already on the boundary is its own `diagPinch`

The pinch of phase 17 says an `ok` round's centre sits exactly at `diag = 1 − dq/4`.  Feeding that
back in, `diagPinch` is the identity, so the diagonal overwrite costs *nothing* — neither in `frob`
(hence not in `trace_le`) nor in the quadratic form.  What is left is a `RelaxMem` certificate in
the conduit's own `δ/2` currency, which is by construction the pinch data. -/

/-- `diagPinch` is the identity on a base that already sits on the boundary. -/
theorem diagPinch_eq_of_diag {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (h : ∀ i, Q i i = 1 - dq / 4) : diagPinch Q dq = Q := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [diagPinch_diag, h i]
  · rw [diagPinch_off hij]

#print axioms QMCLeafB.CoresM1.diagPinch_eq_of_diag

/-- **The pinch centre is a member** from the base's own PSD margin `dq/2` and trace test.  No
diagonal accounting appears: at a pinched base the centre *is* the base. -/
theorem relaxMem_of_pinched {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hdq : 0 < dq) (hdiag : ∀ i, Q i i = 1 - dq / 4)
    (hpsd : ∀ x : Fin n → ℚ, -(dq / 2) * (∑ i, x i ^ 2) ≤ qf Q x)
    (htr : frob A Q ≤ u + dq / 2) :
    RelaxMem A (diagPinch Q dq) u dq := by
  have hQ : diagPinch Q dq = Q := diagPinch_eq_of_diag hdiag
  refine { δ_pos := hdq, psd_margin := ?_, diag_near := ?_, trace_le := ?_ }
  · intro x
    rw [hQ]
    exact hpsd x
  · intro i
    rw [hQ, hdiag i, abs_le]
    constructor <;> linarith
  · rw [hQ]
    exact htr

#print axioms QMCLeafB.CoresM1.relaxMem_of_pinched

/-- **A pinched round's canonical flag is `true`.** -/
theorem flagOf_true_of_pinched {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (hdiag : ∀ i, Q k i i = 1 - P.dq / 4)
    (hpsd : ∀ x : Fin G.n → ℚ, -(P.dq / 2) * (∑ i, x i ^ 2) ≤ qf (Q k) x)
    (htr : frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    flagOf G t P (centreOf P Q) k = true :=
  flagOf_true_of_relaxMem
    (relaxMem_of_pinched P.hdq hdiag hpsd htr)

#print axioms QMCLeafB.CoresM1.flagOf_true_of_pinched

/-! ## 5.  Unit-diagonal states: the `dvR = 0` block

An `ok` answer forces `dvR = 0` (`CentreAdm.oracleR_ok_dvR_zero`), and `dvR = 0` forces the diagonal
to `1` (`CentreAdm.unit_diag_of_dvR_zero`, `AuditM1.diagSumV_eq_zero`).  At such a base the
`diagPinch` centre is admissible from the state's **exact** PSD (which `RunInduction.runPiv_psd`
supplies from the descent's `false` answer) and the programme's own `ok` test
(`CentreAdm.relaxMem_diagPinch`: the `dq/4` spent lowering the diagonal is the same budget). -/

/-- **A unit-diagonal round's canonical flag is `true`** from exact PSD and the `ok` test. -/
theorem flagOf_true_of_unitDiag {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hdq4 : P.dq ≤ 4)
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (hdiag : ∀ i, Q k i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf (Q k) x)
    (htr : frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    flagOf G t P (centreOf P Q) k = true :=
  flagOf_true_of_relaxMem
    (relaxMem_diagPinch P.hdq hdq4
      (fun _ => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) hdiag hpsd htr)

#print axioms QMCLeafB.CoresM1.flagOf_true_of_unitDiag
/-! ## 6.  The degenerate core: the record exists, with no drift content at all

If every round of the patch has its canonical centre provably inside the relaxation, then §3 makes
all four cut-side slots vacuous and `hcn` says `cn ≡ flatQ 1`.  Taking `lam ≡ 1`, the whole
`StreamCore` — hence the whole `BundleH`, hence `RunParts` — exists.  `hverdict` is the only
remaining input: the leaf's verdict bit must be `true`, which is what the run's read-out gives on an
all-`ok` patch.

This is the degenerate half of the phase-20 residual: everything outside it is a genuine cut round
and therefore the interior brick's business. -/

/-- **The all-member core.**  With every canonical flag `true`, `CoreData` holds at `lam ≡ 1` and
`cn ≡ flatQ 1`: the member side has no normal (§3), so the dilation direction itself carries `cn`. -/
def coreData_of_allTrue {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQsym : ∀ k i j, Q k i j = Q k j i)
    (hflag : ∀ k, flagOf G t P (centreOf P Q) k = true)
    (ho : o G t = true) (hKm : 0 < P.K * P.m) : CoreData o G t P hn Q where
  hQsym := hQsym
  lam := fun _ => 1
  cn := fun _ => QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcn := fun k => by
    have hmem : RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (centreOf P Q k)
        (t - QMCLeafB.RundataCert.eps G) P.dq :=
      relaxMem_of_flagOf_true G t P (centreOf P Q) k (hflag k)
    show QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
        = QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal
          + (1 : ℚ) • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
    rw [flatQ_normal_of_relaxMem hmem]
    simp
  hcne := fun _ => flatQ_one_ne_zero' (by omega)
  hlam0 := fun _ => by norm_num
  hlam1 := fun k hf => (flag_true_ne_false (hflag k) hf).elim
  hlam2 := fun k hf => (flag_true_ne_false (hflag k) hf).elim
  hdriftc := fun k hf => (flag_true_ne_false (hflag k) hf).elim
  hdriftd := fun k hf => (flag_true_ne_false (hflag k) hf).elim
  hverdict := by
    rw [ho, show flagOf G t P (centreOf P Q) = fun _ => true from funext hflag]
    exact (anyOk_allTrue (P.K * P.m) hKm).symm

#print axioms QMCLeafB.CoresM1.coreData_of_allTrue

/-- **The degenerate patch's `StreamCore`**: an all-member patch closes the record outright. -/
theorem streamCore_of_allTrue {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQsym : ∀ k i j, Q k i j = Q k j i)
    (hflag : ∀ k, flagOf G t P (centreOf P Q) k = true)
    (ho : o G t = true) (hKm : 0 < P.K * P.m) :
    Nonempty (StreamCore o G t P hn) :=
  ⟨streamCoreOfCore (coreData_of_allTrue hQsym hflag ho hKm)⟩

#print axioms QMCLeafB.CoresM1.streamCore_of_allTrue

/-- **The degenerate core from the per-round degenerate data.**  Each round is fed from one of the two
sources §4–§5 machine-check (`pinch centre`, `unit-diagonal state`); the common trace test is the
programme's own `ok` test at the round threshold `t − ε`, so one hypothesis covers both. -/
def coreData_of_degenerate {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQsym : ∀ k i j, Q k i j = Q k j i) (hdq4 : P.dq ≤ 4)
    (hdeg : ∀ k,
      ((∀ i, Q k i i = 1 - P.dq / 4) ∧
          (∀ x : Fin G.n → ℚ, -(P.dq / 2) * (∑ i, x i ^ 2) ≤ qf (Q k) x))
        ∨ ((∀ i, Q k i i = 1) ∧ (∀ x : Fin G.n → ℚ, 0 ≤ qf (Q k) x)))
    (htr : ∀ k, frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (ho : o G t = true) (hKm : 0 < P.K * P.m) : CoreData o G t P hn Q :=
  coreData_of_allTrue hQsym (fun k => by
    rcases hdeg k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact flagOf_true_of_pinched h1 h2 (htr k)
    · exact flagOf_true_of_unitDiag hdq4 h1 h2 (htr k)) ho hKm

#print axioms QMCLeafB.CoresM1.coreData_of_degenerate

/-- **The degenerate patch's `StreamCore`, from the per-round data.** -/
theorem streamCore_of_degenerate {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQsym : ∀ k i j, Q k i j = Q k j i) (hdq4 : P.dq ≤ 4)
    (hdeg : ∀ k,
      ((∀ i, Q k i i = 1 - P.dq / 4) ∧
          (∀ x : Fin G.n → ℚ, -(P.dq / 2) * (∑ i, x i ^ 2) ≤ qf (Q k) x))
        ∨ ((∀ i, Q k i i = 1) ∧ (∀ x : Fin G.n → ℚ, 0 ≤ qf (Q k) x)))
    (htr : ∀ k, frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (ho : o G t = true) (hKm : 0 < P.K * P.m) :
    Nonempty (StreamCore o G t P hn) :=
  ⟨streamCoreOfCore (coreData_of_degenerate hQsym hdq4 hdeg htr ho hKm)⟩

#print axioms QMCLeafB.CoresM1.streamCore_of_degenerate

/-- **The degenerate patch closes the whole `BundleH`** — the corrected residual's own shape, so a
phase-20 supplier never has to hand over a `StreamCore` by hand on a degenerate patch. -/
theorem bundleH_of_degenerate {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQsym : ∀ k i j, Q k i j = Q k j i) (hdq4 : P.dq ≤ 4)
    (hdeg : ∀ k,
      ((∀ i, Q k i i = 1 - P.dq / 4) ∧
          (∀ x : Fin G.n → ℚ, -(P.dq / 2) * (∑ i, x i ^ 2) ≤ qf (Q k) x))
        ∨ ((∀ i, Q k i i = 1) ∧ (∀ x : Fin G.n → ℚ, 0 ≤ qf (Q k) x)))
    (htr : ∀ k, frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2)
    (ho : o G t = true) (hKm : 0 < P.K * P.m) :
    Nonempty (BundleH o G t P hn) := by
  obtain ⟨S⟩ := streamCore_of_degenerate hQsym hdq4 hdeg htr ho hKm
  exact ⟨bundleH_of_core S⟩

#print axioms QMCLeafB.CoresM1.bundleH_of_degenerate
/-! ## 7.  Non-vacuity: the degenerate route reproduces the record at `(G₀, −1/2)`

m8's refutation of the phase-19 shape lives at `G₀` (one edge of weight `1/2`, `Rq = 1`) and
`t = −1/2`, inside the interior bracket.  That is exactly where the *corrected* shape must be
inhabited (`FlagsM5.bundleH_G₀_inhabited` shows it for the all-`ok` stream).  The degenerate core of
§6 reaches the same point by its own route: the pinch base `(1 − dq/4) • Q₀` has diagonal
`1 − dq/4`, so it *is* its own `diagPinch` (`diagPinch_eq_of_diag`), and `FlagsM5.relaxMem_G₀`
makes every round's canonical flag `true`.  So §6 is not a vacuous dodge: on the one patch where the
old shape provably fails, it delivers the record. -/

/-- **The degenerate core is inhabited where the phase-19 flag stream is refuted.** -/
theorem bundleH_G₀_of_degenerate :
    Nonempty (BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  set P := QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀ with hP
  have hbase : ∀ (i : Fin QMCLeafB.ResidRefute.G₀.n), ((1 - P.dq / 4) • Q₀) i i = 1 - P.dq / 4 := by
    intro i
    rw [Matrix.smul_apply, smul_eq_mul, Q₀_diag, mul_one]
  have hsym : ∀ (i j : Fin QMCLeafB.ResidRefute.G₀.n),
      ((1 - P.dq / 4) • Q₀) i j = ((1 - P.dq / 4) • Q₀) j i := by
    intro i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Q₀_symm i j]
  have hself : ∀ k : ℕ,
      centreOf P (fun _ => (1 - P.dq / 4) • Q₀) k = (1 - P.dq / 4) • Q₀ := by
    intro k
    show diagPinch ((1 - P.dq / 4) • Q₀) P.dq = (1 - P.dq / 4) • Q₀
    exact diagPinch_eq_of_diag hbase
  have hfun : centreOf P (fun _ => (1 - P.dq / 4) • Q₀) = fun _ => (1 - P.dq / 4) • Q₀ :=
    funext hself
  have hflag : ∀ k : ℕ, flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2)) P
      (centreOf P (fun _ => (1 - P.dq / 4) • Q₀)) k = true := by
    intro k
    rw [hfun]
    exact flagOf_true_of_relaxMem (G := QMCLeafB.ResidRefute.G₀) (t := -(1 / 2)) (P := P)
      (cX := fun _ => (1 - P.dq / 4) • Q₀) (k := k) (hP ▸ relaxMem_G₀)
  have hKm : 0 < P.K * P.m :=
    lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
  exact ⟨bundleH_of_core (streamCoreOfCore
    (coreData_of_allTrue (Q := fun _ => (1 - P.dq / 4) • Q₀)
      (fun _ i j => hsym i j) hflag rfl hKm))⟩

#print axioms QMCLeafB.CoresM1.bundleH_G₀_of_degenerate
/-! ## 8.  The per-round case split is total

`CoreData`'s four cut-side slots (`hlam1`, `hlam2`, `hdriftc`, `hdriftd`) are all conditioned on
`flagOf … = false`.  §4–§5 therefore say, at a degenerate round, that they never fire: the interior
brick owes nothing there, and everything there.  The two lemmas below are the form the interior
supplier consumes (it never has to prove a cut-side statement at a pinch centre or at a unit-diagonal
state); `flagOf_eq_true_or_false` records that every other round is a genuine cut round. -/

/-- The canonical flag is a `Bool`: no third case in the dispatch. -/
theorem flagOf_eq_true_or_false {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    flagOf G t P cX k = true ∨ flagOf G t P cX k = false := by
  cases flagOf G t P cX k <;> simp

#print axioms QMCLeafB.CoresM1.flagOf_eq_true_or_false

/-- **No cut side at a pinch centre**: the canonical flag is never `false` there, so a `CoreData`
supplier never has to meet `hlam1`/`hlam2`/`hdriftc`/`hdriftd` at a boundary-diagonal base. -/
theorem flagOf_ne_false_of_pinched {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (hdiag : ∀ i, Q k i i = 1 - P.dq / 4)
    (hpsd : ∀ x : Fin G.n → ℚ, -(P.dq / 2) * (∑ i, x i ^ 2) ≤ qf (Q k) x)
    (htr : frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    flagOf G t P (centreOf P Q) k ≠ false :=
  fun hf => flag_true_ne_false (flagOf_true_of_pinched hdiag hpsd htr) hf

#print axioms QMCLeafB.CoresM1.flagOf_ne_false_of_pinched

/-- **No cut side at a unit-diagonal state** — the `dvR = 0` rounds of `Check_stateDiag_m2`. -/
theorem flagOf_ne_false_of_unitDiag {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hdq4 : P.dq ≤ 4)
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (hdiag : ∀ i, Q k i i = 1)
    (hpsd : ∀ x : Fin G.n → ℚ, 0 ≤ qf (Q k) x)
    (htr : frob (QMCLeafB.Finalization.wMatrixQ G) (Q k)
      ≤ (t - QMCLeafB.RundataCert.eps G) + P.dq / 2) :
    flagOf G t P (centreOf P Q) k ≠ false :=
  fun hf => flag_true_ne_false (flagOf_true_of_unitDiag hdq4 hdiag hpsd htr) hf

#print axioms QMCLeafB.CoresM1.flagOf_ne_false_of_unitDiag
/-! ## 9.  The trace bridge: `hdriftd` *is* the trace budget

`CoreData.hdriftd` is stated in the engine's flat coordinates — `dOne ⪝ (Cat k − flat cX k) ≤ 0` —
which hides what it says.  `dOne` is the flattening of the identity, so it pairs with a flattened
matrix as its **trace**.  Hence at the canonical centre `hdriftd` at round `k` is exactly

    tr(state_k) ≤ n(1 − dq/4),

the phase-18 trace budget, with no geometry left in it.  This is the form the interior brick must
prove, and the reason the pinch patch needs nothing: at a round whose state already *is* the
(pinched) centre the inequality is `≤` of equal numbers.

`Check_centre_closure_m4.dOne_dot_flat_eq_trace` states the same identity, but that module does not
compile (`results/qmc-tm2-endgame.md`, vigilance note) and is excluded from the mirror; the proof
below is self-contained against `Check_answer_producer` + `Check_boundary_m2` only.
-/

/-- **`dOne` pairs with the flattening as the trace.** -/
theorem dOne_dot_flat {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.RunPartsStream.dOne n ⬝ᵥ QMCLeafB.AnswerProducer.flat X = ∑ i, X i i := by
  have h1 : ∀ a b : Fin n,
      QMCLeafB.RunPartsStream.dOne n (finProdFinEquiv (a, b))
        = ((if a = b then (1 : ℚ) else 0 : ℚ) : ℝ) := by
    intro a b
    simp [QMCLeafB.RunPartsStream.dOne, QMCLeafB.RelaxOracle.flatQ, Matrix.one_apply]
  have h2 : ∀ a b : Fin n,
      QMCLeafB.AnswerProducer.flat X (finProdFinEquiv (a, b)) = X a b := by
    intro a b
    simp only [QMCLeafB.AnswerProducer.flat, Equiv.symm_apply_apply]
  rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv
    (fun k => QMCLeafB.RunPartsStream.dOne n k * QMCLeafB.AnswerProducer.flat X k)]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_eq_single a]
  · rw [h1 a a, h2 a a]
    simp
  · intro b _ hb
    rw [h1 a b, h2 a b, if_neg (fun hh => hb hh.symm)]
    simp
  · intro h
    exact absurd (Finset.mem_univ a) h

#print axioms QMCLeafB.CoresM1.dOne_dot_flat

/-- **The same identity on a raw flat vector**: `dOne` reads off the trace of the unflattening. -/
theorem dOne_dot_of_flat {n : ℕ} (z : Fin (n * n) → ℝ) :
    QMCLeafB.RunPartsStream.dOne n ⬝ᵥ z
      = ∑ i, QMCLeafB.Boundary.unflat z i i := by
  conv_lhs => rw [← QMCLeafB.Boundary.flat_unflat z]
  exact dOne_dot_flat (QMCLeafB.Boundary.unflat z)

#print axioms QMCLeafB.CoresM1.dOne_dot_of_flat

/-- The diagonal sum of a cast matrix is the cast of the diagonal sum. -/
theorem sum_castMat_diag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    (∑ i, QMCLeafB.SepOracle.castMat M i i) = ((∑ i, M i i : ℚ) : ℝ) := by
  rw [show (∑ i, QMCLeafB.SepOracle.castMat M i i) = ∑ i, ((M i i : ℚ) : ℝ) from
    Finset.sum_congr rfl (fun i _ => QMCLeafB.SepOracle.castMat_apply M i i)]
  exact (map_sum (Rat.castHom ℝ) (fun i => M i i) Finset.univ).symm

#print axioms QMCLeafB.CoresM1.sum_castMat_diag

/-- **`dOne` against a rational centre** is the centre's trace, cast. -/
theorem dOne_dot_flat_castMat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RunPartsStream.dOne n ⬝ᵥ
        QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat M)
      = ((∑ i, M i i : ℚ) : ℝ) := by
  rw [dOne_dot_flat, sum_castMat_diag]

#print axioms QMCLeafB.CoresM1.dOne_dot_flat_castMat

/-- **`hdriftd` in matrix form.**  The identity direction's drift inequality at a flat point `z`
and a rational centre `M` says nothing more than `tr z ≤ tr M`. -/
theorem driftd_iff_trace {n : ℕ} (z : Fin (n * n) → ℝ) (M : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat M)) ≤ 0
      ↔ (∑ i, QMCLeafB.Boundary.unflat z i i) ≤ ((∑ i, M i i : ℚ) : ℝ) := by
  rw [dotProduct_sub, dOne_dot_of_flat, dOne_dot_flat_castMat, sub_nonpos]

#print axioms QMCLeafB.CoresM1.driftd_iff_trace

/-- The canonical centre's trace, as a real number. -/
theorem trace_centreOf {G : QuantumMaxCutEnergy.Input}
    (P : QMCLeafB.FinalStroke.RunParams G)
    (Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) :
    ((∑ i, centreOf P Q k i i : ℚ) : ℝ) = (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by
  rw [centreOf_trace]
  push_cast
  ring

#print axioms QMCLeafB.CoresM1.trace_centreOf

/-- **`hdriftd` at the canonical centres is the trace budget** `tr(state_k) ≤ n(1 − dq/4)`, on the
run's own flat state vector.  This is the machine-checked dictionary for the interior brick: no
geometry of the ellipsoid survives. -/
theorem driftd_iff_traceBudget {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ) :
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (centreOf P Q k))) ≤ 0
      ↔ (∑ i, QMCLeafB.Boundary.unflat (n := G.n)
            (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k) i i)
          ≤ (G.n : ℝ) * (1 - ((P.dq : ℚ) : ℝ) / 4) := by
  rw [driftd_iff_trace, trace_centreOf]

#print axioms QMCLeafB.CoresM1.driftd_iff_traceBudget

/-- **The steady (pinch) round owes no drift**: if the run's flat state at round `k` already *is* the
canonical centre, `hdriftd` is `tr ≤ tr`.  That is the degenerate content of the direction, in the
one inequality the conduit reads. -/
theorem driftd_of_state_eq_centre {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    {cn : ℕ → Fin (G.n * G.n) → ℚ} (hcne : ∀ k, cn k ≠ 0) {k : ℕ}
    (h : QMCLeafB.Boundary.unflat
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k)
        = QMCLeafB.SepOracle.castMat (centreOf P Q k)) :
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (centreOf P Q k))) ≤ 0 := by
  rw [driftd_iff_trace, h, sum_castMat_diag]

#print axioms QMCLeafB.CoresM1.driftd_of_state_eq_centre
/-! ## 10.  The cut-functional bridge: `hdriftc` in matrix form

The same dictionary for the *normal* direction: the flat pairing of `flatQ normal` against
`state − centre` is `frob (castMat normal) (state − centre)`, the cut's own separation functional.
So `hdriftc` at round `k` reads

    frob (castMat normal_k) (state_k − centre_k) ≤ margin_k / 2,

i.e. the queried centre does not sit more than half a margin *above* the current state in the cut's
own direction — the centre-tracking inequality, with no ellipsoid in it.  At a steady round
(state = centre) it is `0 ≤ margin/2`, so `hdriftc` is free: with §9 this discharges *both* drift
slots of `CoreData` on the degenerate locus. -/

/-- The real flattening of `flatQ M` is the flattening of `castMat M`. -/
theorem flatQ_cast_eq_flat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) (k : Fin (n * n)) :
    ((QMCLeafB.RelaxOracle.flatQ M k : ℚ) : ℝ) = QMCLeafB.AnswerProducer.flat
      (QMCLeafB.SepOracle.castMat M) k := by
  simp [QMCLeafB.RelaxOracle.flatQ, QMCLeafB.AnswerProducer.flat, QMCLeafB.SepOracle.castMat]

#print axioms QMCLeafB.CoresM1.flatQ_cast_eq_flat

/-- **`hdriftc` in matrix form**: the flat pairing with the normal *is* the cut's Frobenius
functional at `state − centre`. -/
theorem flatNormal_dot_eq_frob {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ)
    (z : Fin (n * n) → ℝ) (M : Matrix (Fin n) (Fin n) ℚ) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ N i : ℚ) : ℝ))
        ⬝ᵥ (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat M))
      = QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat N)
          (QMCLeafB.Boundary.unflat (n := n) z - QMCLeafB.SepOracle.castMat M) := by
  rw [QMCLeafB.RelaxOracle.frob_eq_flat_dot, QMCLeafB.Boundary.flat_sub,
    QMCLeafB.Boundary.flat_unflat, dotProduct]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [flatQ_cast_eq_flat N k]

#print axioms QMCLeafB.CoresM1.flatNormal_dot_eq_frob

/-- **A steady round owes no cut-side drift either**: with the run's state equal to the canonical
centre, `hdriftc` holds — from `margin > 0` alone. -/
theorem driftc_of_state_eq_centre {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    {Q : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ}
    {cn : ℕ → Fin (G.n * G.n) → ℚ} (hcne : ∀ k, cn k ≠ 0) {k : ℕ}
    (h : QMCLeafB.Boundary.unflat (n := G.n)
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k)
        = QMCLeafB.SepOracle.castMat (centreOf P Q k)) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (cutOf G t P (centreOf P Q) k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (centreOf P Q k)))
      ≤ ((((cutOf G t P (centreOf P Q) k).margin : ℚ)) : ℝ) / 2 := by
  rw [flatNormal_dot_eq_frob, h, sub_self]
  have hpos := (cutOf G t P (centreOf P Q) k).margin_pos
  have hnn : (0 : ℚ) ≤ (cutOf G t P (centreOf P Q) k).margin / 2 := by linarith
  have hcast : (0 : ℝ) ≤ ((((cutOf G t P (centreOf P Q) k).margin / 2 : ℚ)) : ℝ) := by
    exact_mod_cast hnn
  have hhalf : ((((cutOf G t P (centreOf P Q) k).margin : ℚ)) : ℝ) / 2
      = ((((cutOf G t P (centreOf P Q) k).margin / 2 : ℚ)) : ℝ) := by
    push_cast
    ring
  rw [hhalf]
  simpa [QMCLeafB.SepOracle.frob] using hcast

#print axioms QMCLeafB.CoresM1.driftc_of_state_eq_centre

/-! ## 11.  Consolidated axiom audit -/

#print axioms QMCLeafB.CoresM1.centreOf
#print axioms QMCLeafB.CoresM1.centreOf_apply
#print axioms QMCLeafB.CoresM1.centreOf_symm
#print axioms QMCLeafB.CoresM1.centreOf_trace
#print axioms QMCLeafB.CoresM1.centreOf_trace_le
#print axioms QMCLeafB.CoresM1.frob_centreOf
#print axioms QMCLeafB.CoresM1.flatQ_zero
#print axioms QMCLeafB.CoresM1.streamCoreOfCore
#print axioms QMCLeafB.CoresM1.residH_of_coreData
#print axioms QMCLeafB.CoresM1.residCore_of_coreData
#print axioms QMCLeafB.CoresM1.solution_of_coreData
#print axioms QMCLeafB.CoresM1.solution_statement_of_coreData
#print axioms QMCLeafB.CoresM1.flagOf_true_of_relaxMem
#print axioms QMCLeafB.CoresM1.flag_true_ne_false
#print axioms QMCLeafB.CoresM1.cutOf_of_relaxMem
#print axioms QMCLeafB.CoresM1.flatQ_normal_of_relaxMem
#print axioms QMCLeafB.CoresM1.anyOk_allTrue
#print axioms QMCLeafB.CoresM1.diagPinch_eq_of_diag
#print axioms QMCLeafB.CoresM1.relaxMem_of_pinched
#print axioms QMCLeafB.CoresM1.flagOf_true_of_pinched
#print axioms QMCLeafB.CoresM1.flagOf_true_of_unitDiag
#print axioms QMCLeafB.CoresM1.coreData_of_allTrue
#print axioms QMCLeafB.CoresM1.streamCore_of_allTrue
#print axioms QMCLeafB.CoresM1.coreData_of_degenerate
#print axioms QMCLeafB.CoresM1.streamCore_of_degenerate
#print axioms QMCLeafB.CoresM1.bundleH_of_degenerate
#print axioms QMCLeafB.CoresM1.bundleH_G₀_of_degenerate
#print axioms QMCLeafB.CoresM1.flagOf_eq_true_or_false
#print axioms QMCLeafB.CoresM1.flagOf_ne_false_of_pinched
#print axioms QMCLeafB.CoresM1.flagOf_ne_false_of_unitDiag
#print axioms QMCLeafB.CoresM1.dOne_dot_flat
#print axioms QMCLeafB.CoresM1.dOne_dot_of_flat
#print axioms QMCLeafB.CoresM1.sum_castMat_diag
#print axioms QMCLeafB.CoresM1.dOne_dot_flat_castMat
#print axioms QMCLeafB.CoresM1.driftd_iff_trace
#print axioms QMCLeafB.CoresM1.trace_centreOf
#print axioms QMCLeafB.CoresM1.driftd_iff_traceBudget
#print axioms QMCLeafB.CoresM1.driftd_of_state_eq_centre
#print axioms QMCLeafB.CoresM1.CoreAt
#print axioms QMCLeafB.CoresM1.bundleH_of_coreData
#print axioms QMCLeafB.CoresM1.runParts_of_coreData
#print axioms QMCLeafB.CoresM1.hd_of_coreData
end QMCLeafB.CoresM1



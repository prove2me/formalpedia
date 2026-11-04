-- Prove2me | Definitions.Def_QMCLeafB_residb_m7
-- name    : QMCLeafB_residb_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:13:15.970894+00:00
-- url     : https://prove2.me/theorems/43e35b9c-04df-402b-949c-8045c729fba6
-- title:
--   QMCLeafB residb_m7
-- statement:
--   # leaf B phase 21 — the HORIZON-BOUNDED residual (swarm `smw1m5nkm`, member m7, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
/-
# leaf B phase 21 — the HORIZON-BOUNDED residual (swarm `smw1m5nkm`, member m7, direction d5)

Phase 20's residual is `RecordsM2.CoreDataF`, whose field

```
hcutfin : ∀ k, flagOf G t P (cXst G.n X P.dq) k = false → k < P.K * P.m
```

says that every `false` flag is below the run's horizon `K·m`.  A `Bool` is `false` or `true`, so
that is the same as saying that **every round at or past the horizon has a member centre** — which an
interior `(G, t)` with an *empty* relaxed body cannot supply.  This module does two things.

**§9 isolates the defect as a theorem, for an arbitrary `(G, t)`, with no input instance and no
arithmetic.**  `member_beyond_horizon_of_hcutfin` exhibits the member centre that every `CoreDataF`
carries past the horizon; `not_nonempty_coreDataF_of_emptyBody` and `not_residFinite_of_emptyBody`
turn an empty relaxed body at an interior point into `¬Nonempty (CoreDataF …)` /
`ResidFinite ... → False`.  The numeric half — that `G₀` at `t = −99999/100000` has an empty body — is a
separate computation, and composing the two is one `exact`.

**§1–§8, §12–§15 supply the successor shape and its closing stroke.**  The flag stream is
**clipped at the horizon** (`okClip`); every flag-conditioned budget/trace slot loses its `k ≥ K·m`
range; `hcutfin` is deleted.  The clip is invisible to the verdict
(`anyOk (okClip Km f) Km = anyOk f Km`), and the parts of `BundleH` that are not flag-conditioned
(`cX`, `lam`, `cn`, `hcn`, `hcne`, `hlam0`, `hlam1`, `hlam2`, `hTrc`) are carried unchanged — the first
six are *constructed* flag-independently by `RecordM2.lamInd`/`cnInd`, `hTrc` is unconditional at the
pinched centres.  So the successor feeds **`FlagsM5.BundleH` verbatim**, and the whole downstream
cone (`DriftExact.runParts_of_exact_trace` → `AssemblyM5.endgame_of_hd` →
`FlagsM5.solution_of_residH`) is untouched: nothing in `FlagsM5`, `RecordM2` or `RecordsM2` is changed
or recompiled, and this is one new module.

The chain is

```
CoreDataB ──► StreamCoreB ──► BundleH ──► RunParts ──► SolutionStatement ──► d9f601e5
```

and the old shapes embed into the new ones (`coreDataB_of_finite`, `coreDataScalarB_of_scalar`,
`streamCoreB_of_core`, `residFiniteB_of_finite`, `residCoreB_of_core`), so every phase-20 producer at
the `∀k` shape is *still* a producer at the bounded shape: the successor is strictly weaker, never
stronger.

Contents by section:

* §1 `okClip` and its three facts;
* §2 `StreamCoreB` (stream core, drifts below the horizon) + embedding from `StreamCore`;
* §3 `bundleH_of_coreB : StreamCoreB → FlagsM5.BundleH` — the restate's whole cost;
* §4 `streamCoreB_of_drifts`, `streamCoreB_of_coreDataB` (the multiplier block from `RecordM2`);
* §5 `CoreDataB` — `CoreDataF` minus `hcutfin`, and nothing else;
* §6 `ResidFiniteB` and `solution_of_finiteB`;
* §7 bridges (`coreDataB_of_finite`, `coreDataF_of_bounded`, `residFiniteB_of_finite`);
* §8 statement lock against `FinishLine.SolutionStatement`;
* §9 the refutation: `hcutfin` is a member-existence demand past the horizon;
* §10 non-vacuity at the ok point `(G₀, −1/2)`;
* §11 the honest limit;
* §12 the collapsed (scalar) bounded residual `CoreDataScalarB` / `ResidScalarB`;
* §13 the API at an **empty-body** point (`coreDataB_of_allFalse`);
* §14 the same in scalar form (`coreDataScalarB_of_allFalse`);
* §15 the stream-core bounded residual `ResidCoreB` and its closing strokes;
* §16 the trace slot with the centre eliminated (`hdriftd_centre_free`): `hdriftd` is
  `diagSum (Cat k) ≤ (1 − dq/4)·n`, i.e. the scalar itself, with no `Q` in it;
* §17 where the ceiling lives (`bundleH_forces_engine_trace`): at every cut round `BundleH`
  forces `diagSum (Cat k) ≤ n·(1 − dq/4)` on the engine's own centre, so the ceiling is
  intrinsic to the closing chain and no restatement at the residual level can widen it.

House discipline: `set_option autoImplicit false`; a `#print axioms` audit after every declaration
(every set is `[propext, Classical.choice, Quot.sound]` or a subset); none of the disallowed
proof-escape tokens of the library discipline occurs anywhere in this file; the strict-subset symbol
is not used.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 1.  The horizon clip

The run has `K·m` rounds; the verdict is `anyOk · (K·m)`.  Everything the streaming residual says
about round `k ≥ K·m` is therefore unobservable — but phase 20's shape still demands it, and the
engine has no round there to supply a witness.  The clip makes those slots vacuous. -/

/-- **The horizon clip of a bit stream**: verbatim below the horizon `K·m`, `true` beyond it. -/
def okClip (Km : ℕ) (f : ℕ → Bool) : ℕ → Bool :=
  fun k => if k < Km then f k else true

theorem okClip_apply_lt {Km : ℕ} {f : ℕ → Bool} {k : ℕ} (h : k < Km) :
    okClip Km f k = f k := if_pos h

#print axioms QMCLeafB.ResidB_M7.okClip_apply_lt

theorem okClip_apply_ge {Km : ℕ} {f : ℕ → Bool} {k : ℕ} (h : Km ≤ k) :
    okClip Km f k = true := if_neg (by omega)

#print axioms QMCLeafB.ResidB_M7.okClip_apply_ge

/-- **Where the clipped stream is `false`**: exactly below the horizon, exactly where the raw stream
is.  This is the whole content of the restate: every flag-conditioned slot is quoted at a round where
the flag is `false`, and after the clip those rounds are confined to `k < K·m`. -/
theorem okClip_eq_false_iff {Km : ℕ} {f : ℕ → Bool} {k : ℕ} :
    okClip Km f k = false ↔ k < Km ∧ f k = false := by
  by_cases h : k < Km <;> simp [okClip, h]

#print axioms QMCLeafB.ResidB_M7.okClip_eq_false_iff

/-- **The clip is invisible to the verdict**: `anyOk` reads only the first `K·m` bits. -/
theorem anyOk_okClip (Km : ℕ) (f : ℕ → Bool) :
    QMCLeafB.SimLoop.anyOk (okClip Km f) Km = QMCLeafB.SimLoop.anyOk f Km :=
  QMCLeafB.RecordsM2.anyOk_congr (f := okClip Km f) (g := f) (N := Km)
    (fun k hk => okClip_apply_lt hk)

#print axioms QMCLeafB.ResidB_M7.anyOk_okClip

/-! ## 2.  `StreamCoreB`: the stream core with horizon-bounded drift slots

Field for field `FlagsM5.StreamCore` except `hdriftc`/`hdriftd`, which are quoted at `k < K·m`
only.  The multiplier block (`hcn`, `hcne`, `hlam0`, `hlam1`, `hlam2`) and the trace slot `hTrc` are
*not* flag-accumulating quantities — `RecordM2.lamInd`/`cnInd` produce them flag-independently at
every `k` — so they keep the `∀ k` form verbatim. -/
structure StreamCoreB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
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
  /-- **the canonical normal's centre mismatch, below the horizon only** -/
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P cX k = false →
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (cutOf G t P cX k).normal i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((((cutOf G t P cX k).margin : ℚ)) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget, below the horizon only** -/
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P cX k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m)

/-- **Every phase-20 `StreamCore` is a `StreamCoreB`** — the bounded shape is strictly weaker, so no
producer of the old shape is lost by the restate. -/
def streamCoreB_of_core {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (S : StreamCore o G t P hn) : StreamCoreB o G t P hn where
  cX := S.cX
  lam := S.lam
  cn := S.cn
  hCsym := S.hCsym
  hcn := S.hcn
  hcne := S.hcne
  hlam0 := S.hlam0
  hlam1 := S.hlam1
  hlam2 := S.hlam2
  hTrc := S.hTrc
  hdriftc := fun k _ hk => S.hdriftc k hk
  hdriftd := fun k _ hk => S.hdriftd k hk
  hverdict := S.hverdict

#print axioms QMCLeafB.ResidB_M7.streamCoreB_of_core

/-! ## 3.  `StreamCoreB` gives `FlagsM5.BundleH` — the whole point of the restate

The only change against `FlagsM5.bundleH_of_core` is `ok := okClip (K·m) (flagOf …)` instead of
`ok := flagOf …`; everything else is the canonical construction, and the three `false`-conditioned
slots (`hlam1`, `hlam2`, `hdriftc`/`hdriftd` on the bundle side) are discharged from the clipped
flag, which is `false` only below the horizon. -/
def bundleH_of_coreB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (S : StreamCoreB o G t P hn) : BundleH o G t P hn where
  ok := okClip (P.K * P.m) (flagOf G t P S.cX)
  marg := fun k => (cutOf G t P S.cX k).margin
  cX := S.cX
  lam := S.lam
  c := fun k => QMCLeafB.RelaxOracle.flatQ (cutOf G t P S.cX k).normal
  cn := S.cn
  C := fun k _ => cutOf G t P S.cX k
  hmarg := fun k _ => rfl
  hmem := fun k hk htrue => QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P S.cX k (by
    simpa [okClip, hk] using htrue)
  hCsym := S.hCsym
  hcEq := fun k _ => rfl
  hcn := S.hcn
  hcne := S.hcne
  hlam0 := S.hlam0
  hlam1 := fun k hk => S.hlam1 k (okClip_eq_false_iff.1 hk).2
  hlam2 := fun k hk => S.hlam2 k (okClip_eq_false_iff.1 hk).2
  hTrc := S.hTrc
  hdriftc := fun k hk =>
    S.hdriftc k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hdriftd := fun k hk =>
    S.hdriftd k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hverdict := by rw [S.hverdict, anyOk_okClip]

#print axioms QMCLeafB.ResidB_M7.bundleH_of_coreB

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 4.  `StreamCoreB` from the run's own centres — the multiplier block is untouched

The multiplier block of the stream (`lam`, `cn`, `hcne`, `hlam0`, `hlam1`, `hlam2`) is produced by
`RecordM2.lamInd`/`cnInd` **flag-independently at every round**, so it is carried over from
`RecordsM2.streamCore_of_drifts` verbatim; the only fields that change are the two drift slots. -/

/-- **The constructed multiplier block plus the two horizon-bounded drift slots.** -/
def streamCoreB_of_drifts (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmax : 0 < P.rmax)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hTrc : ∀ k, ∑ i, cX k i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hdriftc : ∀ k, k < P.K * P.m → flagOf G t P cX k = false →
      (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P cX k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t P hn cX) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((QMCLeafB.RecordsM2.margOf G t P cX k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m → flagOf G t P cX k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t P hn cX) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m)) :
    StreamCoreB o G t P hn where
  cX := cX
  lam := QMCLeafB.RecordsM2.lamOf G t P hn cX
  cn := QMCLeafB.RecordsM2.cnOf G t P hn cX
  hCsym := hCsym
  hcn := fun _ => rfl
  hcne := QMCLeafB.RecordsM2.cnOf_ne G t P hn cX
  hlam0 := QMCLeafB.RecordM2.lamInd_nonneg (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordsM2.nrmOf G t P cX)
    (QMCLeafB.RecordsM2.margOf G t P cX) P.rmax
  hlam1 := fun k _ => QMCLeafB.RecordM2.lamInd_ge_one (A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordsM2.nrmOf G t P cX)
    (QMCLeafB.RecordsM2.margOf G t P cX) P.rmax k
  hlam2 := fun k _ => QMCLeafB.RecordsM2.lamOf_spec G t P hn cX hrmax k
  hTrc := hTrc
  hdriftc := hdriftc
  hdriftd := hdriftd
  hverdict := hverdict

#print axioms QMCLeafB.ResidB_M7.streamCoreB_of_drifts

/-! ## 5.  The reduced horizon-bounded residual

`CoreDataB` is `RecordsM2.CoreDataF` **minus `hcutfin`** and nothing else: same state stream, same
symmetry slot, same two drift slots *already* at `k < K·m`, same verdict bit.  `CoreDataF` is
recovered by adding `hcutfin` back (§7), so the restate is exactly one deleted field. -/

/-- **The horizon-bounded residual at one interior `(G, t)`.** -/
structure CoreDataB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- the cut normal's centre mismatch, below the horizon -/
  hdriftc : ∀ k, k < P.K * P.m →
    flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
    (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
      ≤ ((QMCLeafB.RecordsM2.margOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- the identity direction's cumulative trace budget, below the horizon -/
  hdriftd : ∀ k, k < P.K * P.m →
    flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk
    (flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) (P.K * P.m)

/-- **`StreamCoreB` from the reduced horizon-bounded data** — the pinched centre family `cXst`, whose
symmetry and trace slots are `RecordsM2.cXst_symm`/`hTrc_cXst` (the trace one unconditionally). -/
def streamCoreB_of_coreDataB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n} (hrmax : 0 < P.rmax)
    (D : CoreDataB o G t P hn) : StreamCoreB o G t P hn :=
  streamCoreB_of_drifts o G t P hn hrmax (QMCLeafB.RecordsM2.cXst G.n D.X P.dq)
    (QMCLeafB.RecordsM2.cXst_symm G.n D.X P.dq D.hsym)
    (QMCLeafB.RecordsM2.hTrc_cXst G.n D.X P.dq) D.hdriftc D.hdriftd D.hverdict

#print axioms QMCLeafB.ResidB_M7.streamCoreB_of_coreDataB

/-! ## 6.  The closing stroke: the verbatim `d9f601e5` sentence from the bounded residual

`FlagsM5.solution_of_residH` is the untouched end of the chain; all this section does is build its
`ResidH` input out of the bounded data. -/

/-- **The horizon-bounded residual**: one `CoreDataB` per interior `(G, t)`. -/
abbrev ResidFiniteB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataB o G t (Pfam G) hn

/-- **`ResidH` from the horizon-bounded residual.** -/
def residH_of_finiteB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (H : ResidFiniteB o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_coreB (streamCoreB_of_coreDataB (hrmax G hn) (H G t hn hlo hhi))

#print axioms QMCLeafB.ResidB_M7.residH_of_finiteB

/-- **The verbatim `d9f601e5` sentence from the horizon-bounded residual.**  Statement and proof are
the shelf's: the `∃ L, Nonempty (TM2ComputableInPolyTime …) ∧ ∀ G, ∃ S, IsMaxcutSDPValue … ∧ L G ≤ S
∧ S − L G ≤ (∑ e, w e)/10000` form is `FlagsM5.solution_of_residH`, quoted at the same
`loopBit init0 round verdict Tbc2` and `paramsKbc2` as phase 20. -/
theorem solution_of_finiteB
    (H : ResidFiniteB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.FlagsM5.solution_of_residH
    (residH_of_finiteB (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB

/-! ## 7.  Bridges: the old shape embeds into the new one, and `hcutfin` is exactly what is deleted -/

/-- **`CoreDataB` from phase 20's `CoreDataF`** — forget the single finite-cut field. -/
def coreDataB_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) : CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := fun k hk hkf => D.hdriftc k hk hkf
  hdriftd := fun k hk hkf => D.hdriftd k hk hkf
  hverdict := D.hverdict

#print axioms QMCLeafB.ResidB_M7.coreDataB_of_finite

/-- **Phase 20's `CoreDataF` is `CoreDataB` plus `hcutfin`** — the restate deletes exactly one field. -/
def coreDataF_of_bounded {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataB o G t P hn)
    (hcutfin : ∀ k, flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k = false →
      k < P.K * P.m) :
    QMCLeafB.RecordsM2.CoreDataF o G t P hn where
  X := D.X
  hsym := D.hsym
  hcutfin := hcutfin
  hdriftc := fun k hk hkf => D.hdriftc k hk hkf
  hdriftd := fun k hk hkf => D.hdriftd k hk hkf
  hverdict := D.hverdict

#print axioms QMCLeafB.ResidB_M7.coreDataF_of_bounded

/-- **Every phase-20 producer is a bounded producer.** -/
def residFiniteB_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : QMCLeafB.RecordsM2.ResidFinite o Pfam) : ResidFiniteB o Pfam :=
  fun G t hn hlo hhi => coreDataB_of_finite (H G t hn hlo hhi)

#print axioms QMCLeafB.ResidB_M7.residFiniteB_of_finite

/-- The same for the closing strokes: the verbatim sentence follows from the phase-20 residual
through the bounded one, so the two are interchangeable at the top. -/
theorem solution_of_finiteB_of_finite
    (H : QMCLeafB.RecordsM2.ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.RecordsM2.solution_of_finite H

#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB_of_finite

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 8.  Statement lock: the bounded stroke proves the *same* sentence

`QMCLeafB.FinishLine.SolutionStatement` is verbatim `d9f601e5`
(`Solutions/Check_brick_finish_line.lean`, with `solutionStatement_iff_wMatrix` an `Iff.rfl`).  That
the bounded residual concludes it, *and* that the `∃ L` sentence above follows from it, is the
statement lock: the two statements are definitionally equal, so nothing was weakened in transit. -/

/-- **`d9f601e5` in the shelf's own name, from the horizon-bounded residual.** -/
theorem solution_statement_of_finiteB
    (H : ResidFiniteB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH
    (residH_of_finiteB (fun G hn => QMCLeafB.RecordsM2.rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.ResidB_M7.solution_statement_of_finiteB

/-- **The statement lock**: the `∃ L` sentence of `solution_of_finiteB` is *the same* `Prop` as the
shelf's `SolutionStatement`, since it is derived from it by `exact`.  So the restated chain concludes
`d9f601e5` verbatim, not a variant of it. -/
theorem lock_solution_of_finiteB
    (H : ResidFiniteB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_statement_of_finiteB H

#print axioms QMCLeafB.ResidB_M7.lock_solution_of_finiteB

/-- **The two strokes are interchangeable at the top**: the bounded one and phase 20's conclude the
same `Prop` from their respective residuals. -/
theorem solution_of_finiteB_eq_solution_of_finite :
    (ResidFiniteB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2 →
      QMCLeafB.FinishLine.SolutionStatement)
    ∧ (QMCLeafB.RecordsM2.ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2 →
      QMCLeafB.FinishLine.SolutionStatement) :=
  ⟨solution_statement_of_finiteB, QMCLeafB.RecordsM2.solution_statement_of_finite⟩

#print axioms QMCLeafB.ResidB_M7.solution_of_finiteB_eq_solution_of_finite

/-! ## 9.  The isolated defect: `hcutfin` *is* a member-existence demand beyond the horizon

This is the general half of the phase-21 refutation candidate, stated for an **arbitrary**
`(G, t)` — no input instance, no arithmetic, no `dq` value.  Phase 20's `hcutfin` says "every
`false` flag is below the horizon"; a `Bool` is either `false` or `true`, so it says "every round at
or past the horizon has a `true` flag", i.e. **a member centre at every `k ≥ K·m`**.  So an empty
relaxed body at an interior point kills `CoreDataF` outright, hence `ResidFinite`. -/

/-- **`hcutfin` carries a member centre past the horizon at every round.** -/
theorem member_beyond_horizon_of_hcutfin {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataF o G t P hn) {k : ℕ} (hk : P.K * P.m ≤ k) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G)
      (QMCLeafB.RecordsM2.cXst G.n D.X P.dq k) (t - QMCLeafB.RundataCert.eps G) P.dq := by
  by_contra h
  have hf : flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k = false :=
    QMCLeafB.FlagsM5.flagOf_false_of_not_mem G t P _ k h
  have hlt := D.hcutfin k hf
  omega

#print axioms QMCLeafB.ResidB_M7.member_beyond_horizon_of_hcutfin

/-- **An empty relaxed body kills phase 20's shape at that point.** -/
theorem not_nonempty_coreDataF_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    ¬ Nonempty (QMCLeafB.RecordsM2.CoreDataF o G t P hn) := by
  rintro ⟨D⟩
  exact hbody _ (member_beyond_horizon_of_hcutfin D (Nat.le_refl (P.K * P.m)))

#print axioms QMCLeafB.ResidB_M7.not_nonempty_coreDataF_of_emptyBody

/-- **An empty relaxed body at an interior point refutes `ResidFinite`.**  This is the reduction from
the phase-21 candidate to a single numeric fact about one input and one threshold. -/
theorem not_residFinite_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {hn : 2 ≤ G.n}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq) :
    (QMCLeafB.RecordsM2.ResidFinite o Pfam) → False := by
  intro H
  exact not_nonempty_coreDataF_of_emptyBody hbody ⟨H G t hn hlo hhi⟩

#print axioms QMCLeafB.ResidB_M7.not_residFinite_of_emptyBody

/-- **The bounded shape does not carry that demand**: the stream it hands to `BundleH` reads `true`
at every round at or past the horizon, so no round there asks the engine for a witness. -/
theorem bundleH_of_coreB_ok_ge {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (S : StreamCoreB o G t P hn) {k : ℕ} (hk : P.K * P.m ≤ k) :
    (bundleH_of_coreB S).ok k = true :=
  okClip_apply_ge hk

#print axioms QMCLeafB.ResidB_M7.bundleH_of_coreB_ok_ge

/-! ## 10.  Non-vacuity of the bounded shape

Phase 20's anchor sits at the `ok` point `(G₀, −1/2)`; the bounded shape is inhabited there too, by
the bridge of §7.  (The complementary anchor — the *refuted* point — is an inhabitation of `CoreDataB`
with an all-`false` flag stream, which needs the empty body and hence the numeric half of the
refutation; it is the refuted-production lane, not this one.) -/

/-- **`CoreDataB` is inhabited at `(G₀, −1/2)`.** -/
theorem coreDataB_G₀_inhabited :
    Nonempty (CoreDataB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨D⟩ := QMCLeafB.RecordsM2.coreDataF_G₀_inhabited
  exact ⟨coreDataB_of_finite D⟩

#print axioms QMCLeafB.ResidB_M7.coreDataB_G₀_inhabited

/-- **`StreamCoreB` is inhabited at `(G₀, −1/2)`.** -/
theorem streamCoreB_G₀_inhabited :
    Nonempty (StreamCoreB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨S⟩ := QMCLeafB.RecordsM2.streamCore_G₀_inhabited
  exact ⟨streamCoreB_of_core S⟩

#print axioms QMCLeafB.ResidB_M7.streamCoreB_G₀_inhabited

/-- **`BundleH` from the bounded shape at `(G₀, −1/2)`** — the shape really is non-vacuous at the
point where the phase-19 stream is refuted. -/
theorem bundleH_G₀_of_bounded :
    Nonempty (BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨S⟩ := streamCoreB_G₀_inhabited
  exact ⟨bundleH_of_coreB S⟩

#print axioms QMCLeafB.ResidB_M7.bundleH_G₀_of_bounded

/-! ## 11.  The honest limit

What this file does **not** claim: that the bounded shape is inhabited at a refuted empty-body point.
It is uninhabited at every point where the *drift budgets* fail below the horizon, and those are
exactly the two numbers of phase 21's remaining scalar work (`hbud` in
`RecordsM2.CoreDataScalar`, and the normal budget there): the deleted field `hcutfin` is the only
slot the restate removes, and the two drift slots below the horizon are carried over verbatim from
phase 20's shape.  So the restate does not touch the analytic content of the residual — it only
stops demanding it past the horizon, which is where phase 20 demanded member centres. -/

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 12.  The scalar form of the bounded residual

Phase 20's `RecordsM2.CoreDataScalar` states the trace budget `∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n`
and the normal budget at **every** `k` where the flag is `false` — so it carries the same
beyond-horizon demand as `CoreDataF`, and is refuted at an empty-body interior point as well.  The
bounded version quotes both at `k < K·m`, which is the shape `simulate_refuted_sound`'s `K·m`-window
certificate actually uses, and is what the cut-budget lane produces.  `coreDataB_of_scalarB` closes
the loop through `RecordsM2.hdriftd_diagPinch_iff`/`hdriftc_diagPinch_iff`. -/

/-- **The horizon-bounded residual in collapsed (scalar) form.** -/
structure CoreDataScalarB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **the one scalar**, below the horizon -/
  hbud : ∀ k, k < P.K * P.m → flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
      (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (G.n * G.n)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j
          * QMCLeafB.DriftExact.diagSum
              (QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)
  /-- the cut normal's per-round budget, below the horizon -/
  hnorm : ∀ k, k < P.K * P.m → flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
    (∑ j ∈ Finset.range k,
        QMCLeafB.CentreTrack.lam (G.n * G.n)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j
          * ((fun i => ((QMCLeafB.RecordsM2.nrmOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i
              : ℚ) : ℝ))
              ⬝ᵥ QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j))
      ≤ (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i
            : ℚ) : ℝ))
            ⬝ᵥ QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k))
          + ((QMCLeafB.RecordsM2.margOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk
    (flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) (P.K * P.m)

/-- **`CoreDataB` from the bounded scalar form** — the two drifts come from phase 20's equivalences
at the run's own stream, quoted only below the horizon. -/
def coreDataB_of_scalarB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataScalarB o G t P hn) : CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftd := fun k hk hkf =>
    (QMCLeafB.RecordsM2.hdriftd_diagPinch_iff
      (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k)) k).2 (D.hbud k hk hkf)
  hdriftc := fun k hk hkf =>
    (QMCLeafB.RecordsM2.hdriftc_diagPinch_iff
      (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k))
      (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k i
        : ℚ) : ℝ)) k).2 (D.hnorm k hk hkf)
  hverdict := D.hverdict

#print axioms QMCLeafB.ResidB_M7.coreDataB_of_scalarB

/-- **Every phase-20 `CoreDataScalar` is a bounded scalar record** — the collapsed shape weakens the
same way, so a phase-20 scalar producer is not lost. -/
def coreDataScalarB_of_scalar {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : QMCLeafB.RecordsM2.CoreDataScalar o G t P hn) : CoreDataScalarB o G t P hn where
  X := D.X
  hsym := D.hsym
  hbud := fun k _ hkf => D.hbud k hkf
  hnorm := fun k _ hkf => D.hnorm k hkf
  hverdict := D.hverdict

#print axioms QMCLeafB.ResidB_M7.coreDataScalarB_of_scalar

/-- **The bounded scalar residual.** -/
abbrev ResidScalarB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataScalarB o G t (Pfam G) hn

/-- **The bounded residual from the bounded scalar residual.** -/
def residFiniteB_of_scalarB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidScalarB o Pfam) : ResidFiniteB o Pfam :=
  fun G t hn hlo hhi => coreDataB_of_scalarB (H G t hn hlo hhi)

#print axioms QMCLeafB.ResidB_M7.residFiniteB_of_scalarB

/-- **The verbatim `d9f601e5` sentence from the bounded scalar residual** — the form the cut-budget
lane hands to the closing stroke. -/
theorem solution_of_scalarB
    (H : ResidScalarB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_finiteB (residFiniteB_of_scalarB H)

#print axioms QMCLeafB.ResidB_M7.solution_of_scalarB

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 13.  The API of the bounded shape at an **empty-body** point

At an interior `(G, t)` where no centre at all is a member, every canonical flag is `false`
(`FlagsM5.flagOf_all_false`), so `hverdict` degenerates to `o G t = false` and every flag-conditioned
slot loses its premise.  `coreDataB_of_allFalse` is therefore the *whole* obligation of the refuted
branch: the state stream, its symmetry, and the two drift budgets at the run's own stream — with
`hcutfin` gone.  This is the shape the refuted-point producer has to hit. -/

/-- The all-`false` stream reads `false`. -/
theorem anyOk_false_fun (N : ℕ) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => false) N = false := by
  induction N with
  | zero => rfl
  | succ k ih => rw [QMCLeafB.SimLoop.anyOk_succ, ih]; rfl

#print axioms QMCLeafB.ResidB_M7.anyOk_false_fun

/-- **`CoreDataB` at an empty-body point**: nothing but the stream, its symmetry and the two drift
budgets below the horizon.  There is no member centre anywhere, and the bounded shape never asks for
one. -/
def coreDataB_of_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hdriftc : ∀ k, k < P.K * P.m →
      (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
        ≤ ((QMCLeafB.RecordsM2.margOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
        ≤ 0)
    (hbit : o G t = false) : CoreDataB o G t P hn where
  X := X
  hsym := hsym
  hdriftc := fun k hk _ => hdriftc k hk
  hdriftd := fun k hk _ => hdriftd k hk
  hverdict := by
    have hf : (flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) = (fun _ : ℕ => false) :=
      funext (QMCLeafB.FlagsM5.flagOf_all_false G t P hbody _)
    rw [hbit, hf, anyOk_false_fun]

#print axioms QMCLeafB.ResidB_M7.coreDataB_of_allFalse

/-- **And it feeds the unchanged `BundleH`**: at an empty-body point the produced stream is `false`
below the horizon and `true` beyond it — `hmem` is vacuous, and the three `false`-conditioned slots of
`BundleH` are confined below the horizon. -/
theorem bundleH_of_coreB_at_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n} (hrmax : 0 < P.rmax)
    (D : CoreDataB o G t P hn)
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    ∀ k, k < P.K * P.m → (bundleH_of_coreB (streamCoreB_of_coreDataB hrmax D)).ok k = false := by
  intro k hk
  have hf : (bundleH_of_coreB (streamCoreB_of_coreDataB hrmax D)).ok k
      = flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k := by
    show okClip (P.K * P.m)
        (flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq)) k = _
    exact okClip_apply_lt hk
  rw [hf]
  exact QMCLeafB.FlagsM5.flagOf_all_false G t P hbody _ k

#print axioms QMCLeafB.ResidB_M7.bundleH_of_coreB_at_allFalse

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 14.  The scalar form at an empty-body point: five slots, all of them real

Same as §13 one level down.  After the (constructed) multiplier block, `CoreDataScalarB`'s only
content is the stream, its symmetry, the two scalars below the horizon, and the bit.  At an
empty-body point the bit is forced to `false`. -/

/-- **`CoreDataScalarB` at an empty-body point.** -/
def coreDataScalarB_of_allFalse {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ)
    (hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k))
    (hbody : ∀ Q : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hbud : ∀ k, k < P.K * P.m →
      (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (G.n * G.n)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j
          * QMCLeafB.DriftExact.diagSum
              (QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ))
    (hnorm : ∀ k, k < P.K * P.m →
      (∑ j ∈ Finset.range k,
          QMCLeafB.CentreTrack.lam (G.n * G.n)
              (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j
            * ((fun i => ((QMCLeafB.RecordsM2.nrmOf G t P
                (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i : ℚ) : ℝ))
                ⬝ᵥ QMCLeafB.EngineIterates.cutPR
                  (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) j))
        ≤ (fun i => ((QMCLeafB.RecordsM2.nrmOf G t P
              (QMCLeafB.RecordsM2.cXst G.n X P.dq) k i : ℚ) : ℝ))
              ⬝ᵥ QMCLeafB.AnswerProducer.flat
                  (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k))
            + ((QMCLeafB.RecordsM2.margOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k : ℚ) : ℝ) / 2)
    (hbit : o G t = false) : CoreDataScalarB o G t P hn where
  X := X
  hsym := hsym
  hbud := fun k hk _ => hbud k hk
  hnorm := fun k hk _ => hnorm k hk
  hverdict := by
    have hf : (flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq)) = (fun _ : ℕ => false) :=
      funext (QMCLeafB.FlagsM5.flagOf_all_false G t P hbody _)
    rw [hbit, hf, anyOk_false_fun]

#print axioms QMCLeafB.ResidB_M7.coreDataScalarB_of_allFalse

/-! ## 15.  The stream-core form of the bounded residual

For producers that work one level up from the record data — the ok-branch record (`X` = the run's
states, frozen past the first `ok` round) and the verdict bridges — the bounded residual in
`StreamCoreB` form, with its own closing stroke. -/

/-- **The bounded residual at the stream-core shape.** -/
abbrev ResidCoreB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    StreamCoreB o G t (Pfam G) hn

/-- **`ResidH` from the bounded stream-core residual.** -/
def residH_of_coreB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidCoreB o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_coreB (h G t hn hlo hhi)

#print axioms QMCLeafB.ResidB_M7.residH_of_coreB

/-- **Every phase-20 `ResidCore` is a bounded one.** -/
def residCoreB_of_core {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : QMCLeafB.FlagsM5.ResidCore o Pfam) : ResidCoreB o Pfam :=
  fun G t hn hlo hhi => streamCoreB_of_core (h G t hn hlo hhi)

#print axioms QMCLeafB.ResidB_M7.residCoreB_of_core

/-- **`d9f601e5` in the shelf's own name, from the bounded stream-core residual.** -/
theorem solution_statement_of_residCoreB
    (h : ResidCoreB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH (residH_of_coreB h)

#print axioms QMCLeafB.ResidB_M7.solution_statement_of_residCoreB

/-- **The verbatim `∃ L` sentence from the bounded stream-core residual.** -/
theorem solution_of_residCoreB
    (h : ResidCoreB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.FlagsM5.solution_of_residH (residH_of_coreB h)

#print axioms QMCLeafB.ResidB_M7.solution_of_residCoreB

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 16.  The trace slot is free of the centre

`RecordsM2.dOne_flat_diagPinch` says the trace direction pairs with the *pinched* centre as
`(1 − dq/4)·n` for **every** base matrix.  So the bounded residual's `hdriftd`, which is stated as a
`Cat`-inequality against the centre, is *equivalent* to a statement about the run's stream alone:
`dOne n ⬝ Cat k ≤ (1 − dq/4)·n`.  This is the form the cut-budget lane hands in (it is
`RecordsM2.hdriftd_diagPinch_iff`'s right-hand side with the centre substituted away), and it makes
plain that the trace slot asks the engine for one inequality per round of the window and nothing
else. -/

/-- **The trace slot, with the centre eliminated.** -/
theorem hdriftd_centre_free {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    (QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))) ≤ 0)
      ↔ QMCLeafB.DriftExact.diagSum
            (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k)
          ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
  rw [QMCLeafB.DriftExact.stated_iff_trace]
  have h : (∑ i : Fin n, ((QMCLeafB.CentreAdm.diagPinch Q dq) i i : ℝ))
      = ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ) := by
    rw [← Rat.cast_sum, QMCLeafB.CentreAdm.sum_diagPinch]
    push_cast
    ring
  rw [h]

#print axioms QMCLeafB.ResidB_M7.hdriftd_centre_free

/-- **The bounded trace slot at the run's own centres, centre-free**: the engine centre's diagonal
read-out is dominated by `(1 − dq/4)·n` — which by `DriftExact.diagSum_cat` is exactly the scalar
`∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n`. -/
theorem coreDataB_hdriftd_centre_free {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataB o G t P hn) :
    ∀ k, k < P.K * P.m → flagOf G t P (QMCLeafB.RecordsM2.cXst G.n D.X P.dq) k = false →
      QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n D.X P.dq)) k)
        ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) :=
  fun k hk hkf =>
    (hdriftd_centre_free _ (QMCLeafB.StateDiag.stMat G.n (D.X k)) k).1 (D.hdriftd k hk hkf)

#print axioms QMCLeafB.ResidB_M7.coreDataB_hdriftd_centre_free

/-- **And back**: the centre-free trace bound is the residual's `hdriftd`. -/
theorem hdriftd_of_centre_free {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (X : ℕ → List ℚ)
    (hfree : ∀ k, k < P.K * P.m →
      flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
      QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k)
        ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)) :
    ∀ k, k < P.K * P.m → flagOf G t P (QMCLeafB.RecordsM2.cXst G.n X P.dq) k = false →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RecordsM2.cutStream G t P hn (QMCLeafB.RecordsM2.cXst G.n X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (QMCLeafB.RecordsM2.cXst G.n X P.dq k)))
        ≤ 0 :=
  fun k hk hkf =>
    (hdriftd_centre_free _ (QMCLeafB.StateDiag.stMat G.n (X k)) k).2 (hfree k hk hkf)

#print axioms QMCLeafB.ResidB_M7.hdriftd_of_centre_free

end QMCLeafB.ResidB_M7

namespace QMCLeafB.ResidB_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)

/-! ## 17.  Where the trace ceiling lives — and why the restate cannot move it

`BundleH` (`FlagsM5`) states its two slots independently:

```
hTrc    : ∀ k, ∑ i, cX k i i ≤ n·(1 − dq/4)
hdriftd : ∀ k, ok k = false → dOne ⬝ (Cat k − flat (castMat (cX k))) ≤ 0
```

Composing them with `DriftExact.stated_iff_trace` gives a statement about the **engine's** centre
alone: at every cut round, `diagSum (Cat k) ≤ n·(1 − dq/4)`.  This is the whole analytic content the
trace side of the residual carries, and it is **intrinsic to `BundleH`**: no restatement at the
`StreamCore`/`CoreData`/`CoreDataF` level — and in particular none of this file's `…B` shapes — can
weaken it, because `FlagsM5.runParts_of_bundleH` (hence `DriftExact.runParts_of_exact_trace`, hence
`AssemblyM5.endgame_of_hd`) consumes `BundleH` itself.  Whatever ceiling the closing chain can carry
is `(1 − dq/4)·n`, and a producer that can only reach a horizon-growing constant must widen it in
`BundleH`/`DriftExact`, not in the residual. -/

/-- **`BundleH` forces the engine centre's trace under `n·(1 − dq/4)` at every cut round.** -/
theorem bundleH_forces_engine_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : BundleH o G t P hn) {k : ℕ} (hok : B.ok k = false) :
    QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn B.cn B.hcne) k)
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
  have h1 : QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn B.cn B.hcne) k)
      ≤ ∑ i : Fin G.n, ((B.cX k i i : ℚ) : ℝ) :=
    (QMCLeafB.DriftExact.stated_iff_trace _ (B.cX k)).1 (B.hdriftd k hok)
  have h2 : (∑ i : Fin G.n, ((B.cX k i i : ℚ) : ℝ))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
    have htr := B.hTrc k
    have hcast : ((∑ i, B.cX k i i : ℚ) : ℝ)
        ≤ (((G.n : ℚ) * (1 - P.dq / 4) : ℚ) : ℝ) := by exact_mod_cast htr
    rw [Rat.cast_sum] at hcast
    push_cast at hcast ⊢
    linarith
  linarith

#print axioms QMCLeafB.ResidB_M7.bundleH_forces_engine_trace

/-- **The same at the bounded stream core**: at every cut round of the window the engine's centre
satisfies `diagSum (Cat k) ≤ n·(1 − dq/4)`.  This is `coreDataB_hdriftd_centre_free` (§16) read as a
statement about `BundleH`, and it is what a refuted-point producer has to meet. -/
theorem streamCoreB_forces_engine_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (S : StreamCoreB o G t P hn) {k : ℕ} (hk : k < P.K * P.m)
    (hkf : flagOf G t P S.cX k = false) :
    QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn S.cn S.hcne) k)
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
  have h1 : QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn S.cn S.hcne) k)
      ≤ ∑ i : Fin G.n, ((S.cX k i i : ℚ) : ℝ) :=
    (QMCLeafB.DriftExact.stated_iff_trace _ (S.cX k)).1 (S.hdriftd k hk hkf)
  have h2 : (∑ i : Fin G.n, ((S.cX k i i : ℚ) : ℝ))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
    have htr := S.hTrc k
    have hcast : ((∑ i, S.cX k i i : ℚ) : ℝ)
        ≤ (((G.n : ℚ) * (1 - P.dq / 4) : ℚ) : ℝ) := by exact_mod_cast htr
    rw [Rat.cast_sum] at hcast
    push_cast at hcast ⊢
    linarith
  linarith

#print axioms QMCLeafB.ResidB_M7.streamCoreB_forces_engine_trace

end QMCLeafB.ResidB_M7



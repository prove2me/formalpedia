-- Prove2me | Definitions.Def_QMCLeafB_residbundle_m7
-- name    : QMCLeafB_residbundle_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:16:02.139212+00:00
-- url     : https://prove2.me/theorems/4fe78f3b-bf2f-4db4-bda0-c0d5f49a09d1
-- title:
--   QMCLeafB residbundle_m7
-- statement:
--   # leaf B phase 21 — the HORIZON-BOUNDED BUNDLE residual (swarm `smw1m5nkm`, member m7, direction d5)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_residb_m7
/-
# leaf B phase 21 — the HORIZON-BOUNDED BUNDLE residual (swarm `smw1m5nkm`, member m7, direction d5)

Two defects were machine-checked on the phase-20 residual, by two other lanes, and this file repairs
both at once at the level where they can be repaired.

1. **`hcutfin` demands a member past the horizon** (`RecordsM2.CoreDataF`; d1/m5's receipt, and
   `Check_residb_m7` §9 for the general form): at an interior `(G, t)` with an empty relaxed body the
   shape is uninhabited, so `solution_of_finite`'s hypothesis is empty.
2. **`cutOf` is opaque** (d4/m6's receipt, `Check_okprod_m6` §7–§8): `RelaxCut.separates` is
   one-sided, so `defaultCut` is a valid cut record at *every* centre, the cut disjunct of
   `relaxMem_or_cut` is unconditional, and `FlagsM5.cutOf` is a `Classical.choice` over an
   always-inhabited `Nonempty`.  Nothing can be proved about `nrmOf`/`margOf`, hence about `cnOf`,
   `cutStream`, `Cat`, `lamOf`.  So the two drift budgets of `StreamCore`/`CoreData`/`CoreDataF` —
   which are stated *at* `cutOf` — are not provable as stated, and neither are their phase-21
   horizon-bounded versions in `Check_residb_m7` §12/§16.

The repair for (2) is to put the cut records back as **data** (the phase-18 `BundleH` shape); the
repair for (1) is to **clip the `ok` stream at the horizon**.  `BundleH`'s member slot is already
horizon-indexed (`hmem : ∀ k, k < P.K * P.m → ok k = true → RelaxMem …`), so with `ok` supplied
rather than canonical there is nothing past the horizon to satisfy at all: `BundleH` itself is
already the right shape, and this file's `BundleHB` only makes the two accumulating drift slots
explicitly horizon-bounded so that a producer states them exactly where it can prove them.

```
BundleHB ──► BundleH ──► RunParts ──► SolutionStatement ──► d9f601e5
```

The conversion is always the same: keep every field, replace `ok` by `okClip (K·m) ok`.
`FlagsM5.runParts_of_bundleH` and everything below it are untouched, so again this is one new module
and no recompile of the cone.

Contents by section:

* §1 `BundleHB` — `FlagsM5.BundleH` with the two accumulating drift slots at `k < K·m`;
  `bundleHB_of_bundleH` embeds the phase-18/19/20 bundle, so no producer is lost.
* §2 `BundleHWin` — **the producer target**: every slot on the run's window, `ok` free, cut
  records supplied.  `bundleH_of_window : BundleHWin → FlagsM5.BundleH` is the whole conversion;
  `window_of_bundleHB` and `bundleHB_of_window` close the triangle.
* §3 `ResidWin` (one `BundleHWin` per interior `(G, t)`), `residH_of_window`,
  `solution_statement_of_window`, `solution_of_window`, `lock_solution_of_window`, and the embeddings
  `residWin_of_residH`, `residBundleB_of_window`.
* §4 the anchor at the ok point `(G₀, −1/2)`: `window_G₀_inhabited`.
* §5 the honest limit: `window_forces_engine_trace` — **no restate relaxes the trace ceiling**.
  At every cut round of the window the engine's own centre satisfies `diagSum (Cat k) ≤ n·(1 − dq/4)`;
  that single number is the whole analytic content left on the trace side, and a producer that can only
  reach a horizon-growing constant has to widen it in `FlagsM5.BundleH`/`DriftExact`, not here.

House discipline: `set_option autoImplicit false`; a `#print axioms` audit after every declaration
(every set is `[propext, Classical.choice, Quot.sound]` or a subset); none of the disallowed
proof-escape tokens of the library discipline occurs in this file; the strict-subset symbol is not
used.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.ResidBundle_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)
open QMCLeafB.ResidB_M7 (okClip okClip_apply_lt okClip_apply_ge okClip_eq_false_iff anyOk_okClip
  anyOk_false_fun)

/-! ## 1.  `BundleHB`: the bundle residual with the accumulating slots horizon-bounded

Field for field `FlagsM5.BundleH` except `hdriftc`/`hdriftd`, which are quoted at `k < K·m`.  The
other flag-conditioned slots (`C`, `hmarg`, `hcEq`, `hlam1`, `hlam2`) are *not* accumulating — they
are per-round records and scalars — so they keep the `BundleH` form; after the `ok`-clip they are
only ever exercised below the horizon anyway, which is `bundleH_of_bundleHB`'s content. -/
structure BundleHB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
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
  /-- **the cut records — supplied, not chosen** -/
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin
  /-- **the `ok`-round member certificate, below the horizon only** -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the queried centre is symmetric -/
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
  /-- the trace budget at the queried centres -/
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  /-- **the oracle normal's centre mismatch, below the horizon only** -/
  hdriftc : ∀ k, k < P.K * P.m → ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget, below the horizon only** -/
  hdriftd : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **Every phase-18/19/20 `BundleH` is a `BundleHB`** — the bounded shape is strictly weaker, so no
producer of the bundle is lost by the restate. -/
def bundleHB_of_bundleH {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : BundleH o G t P hn) : BundleHB o G t P hn where
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
  hdriftc := fun k _ hok => B.hdriftc k hok
  hdriftd := fun k _ hok => B.hdriftd k hok
  hverdict := B.hverdict

#print axioms QMCLeafB.ResidBundle_M7.bundleHB_of_bundleH

end QMCLeafB.ResidBundle_M7

namespace QMCLeafB.ResidBundle_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)
open QMCLeafB.ResidB_M7 (okClip okClip_apply_lt okClip_apply_ge okClip_eq_false_iff anyOk_okClip
  anyOk_false_fun)

/-! ## 2.  `BundleHWin`: every obligation stated on the run's own window

This is the target a producer should hit.  Every slot lives at `k < P.K * P.m` — the run's `K·m`
rounds and nothing else — the cut records are **supplied** (so nothing depends on the opaque
`FlagsM5.cutOf`), and the `ok` stream is free.  Two conversions:

* `window_of_bundleHB : BundleHB → BundleHWin` — nothing is lost: a `BundleHB` already has all of
  this (its unconditional slots are quoted at the window).
* `bundleHB_of_window W` — clip `W.ok` at the horizon.  Beyond it the `ok` stream reads `true`, so
  `hmem` (already window-indexed) is vacuous and the two drift slots are vacuous too.

`bundleH_of_window` then lands directly in `FlagsM5.BundleH`, which
`FlagsM5.runParts_of_bundleH` consumes. -/
structure BundleHWin (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- did round `k` report `ok`? (free, on the run's own rounds) -/
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
  /-- **the cut records — supplied, on the window** -/
  C : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false), marg k = (C k hk hok).margin
  /-- **the `ok`-round member certificate, on the window** -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  hCsym : ∀ k, (cX k)ᵀ = cX k
  hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
    c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal
  hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ)
  hcne : ∀ k, cn k ≠ 0
  hlam0 : ∀ k, 0 ≤ lam k
  hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k
  hlam2 : ∀ k, k < P.K * P.m → ok k = false →
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
  hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4)
  /-- **the oracle normal's centre mismatch, on the window** -/
  hdriftc : ∀ k, k < P.K * P.m → ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget, on the window** -/
  hdriftd : ∀ k, k < P.K * P.m → ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **Nothing is lost**: a `BundleHB` is a window record (quote the unconditional slots at the
window). -/
def window_of_bundleHB {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (B : BundleHB o G t P hn) : BundleHWin o G t P hn where
  ok := B.ok
  marg := B.marg
  cX := B.cX
  lam := B.lam
  c := B.c
  cn := B.cn
  C := fun k _ hok => B.C k hok
  hmarg := fun k _ hok => B.hmarg k hok
  hmem := B.hmem
  hCsym := B.hCsym
  hcEq := fun k _ hok => B.hcEq k hok
  hcn := B.hcn
  hcne := B.hcne
  hlam0 := B.hlam0
  hlam1 := fun k _ hok => B.hlam1 k hok
  hlam2 := fun k _ hok => B.hlam2 k hok
  hTrc := B.hTrc
  hdriftc := fun k hk hok => B.hdriftc k hk hok
  hdriftd := fun k hk hok => B.hdriftd k hk hok
  hverdict := B.hverdict

#print axioms QMCLeafB.ResidBundle_M7.window_of_bundleHB

/-- **The window record is a `BundleHB`**: clip the `ok` stream at the horizon.  Everything past the
horizon becomes vacuous, so only the window slots are ever used. -/
def bundleHB_of_window {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (W : BundleHWin o G t P hn) : BundleHB o G t P hn where
  ok := okClip (P.K * P.m) W.ok
  marg := W.marg
  cX := W.cX
  lam := W.lam
  c := W.c
  cn := W.cn
  C := fun k hk => W.C k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hmarg := fun k hk => W.hmarg k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hmem := fun k hk htrue => W.hmem k hk (by simpa [okClip, hk] using htrue)
  hCsym := W.hCsym
  hcEq := fun k hk => W.hcEq k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hcn := W.hcn
  hcne := W.hcne
  hlam0 := W.hlam0
  hlam1 := fun k hk => W.hlam1 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hlam2 := fun k hk => W.hlam2 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hTrc := W.hTrc
  hdriftc := fun k hk hok => W.hdriftc k hk (okClip_eq_false_iff.1 hok).2
  hdriftd := fun k hk hok => W.hdriftd k hk (okClip_eq_false_iff.1 hok).2
  hverdict := by rw [W.hverdict, anyOk_okClip]

#print axioms QMCLeafB.ResidBundle_M7.bundleHB_of_window

/-- **The window record lands in `FlagsM5.BundleH`** — the conversion the closing chain consumes. -/
def bundleH_of_window {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (W : BundleHWin o G t P hn) : BundleH o G t P hn where
  ok := okClip (P.K * P.m) W.ok
  marg := W.marg
  cX := W.cX
  lam := W.lam
  c := W.c
  cn := W.cn
  C := fun k hk => W.C k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hmarg := fun k hk => W.hmarg k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hmem := fun k hk htrue => W.hmem k hk (by simpa [okClip, hk] using htrue)
  hCsym := W.hCsym
  hcEq := fun k hk => W.hcEq k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hcn := W.hcn
  hcne := W.hcne
  hlam0 := W.hlam0
  hlam1 := fun k hk => W.hlam1 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hlam2 := fun k hk => W.hlam2 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hTrc := W.hTrc
  hdriftc := fun k hk => W.hdriftc k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hdriftd := fun k hk => W.hdriftd k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2
  hverdict := by rw [W.hverdict, anyOk_okClip]

#print axioms QMCLeafB.ResidBundle_M7.bundleH_of_window

end QMCLeafB.ResidBundle_M7

namespace QMCLeafB.ResidBundle_M7

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.RunPartsDilate
open QMCLeafB.FlagsM5 (flagOf cutOf StreamCore BundleH ResidH)
open QMCLeafB.ResidB_M7 (okClip okClip_apply_lt okClip_apply_ge okClip_eq_false_iff anyOk_okClip
  anyOk_false_fun)

/-! ## 3.  The residual on the window, and its closing strokes -/

/-- **The residual on the run's window**: one `BundleHWin` per interior `(G, t)`.  This is the
target for the producers: supplied cut records, a free `ok` stream, and every budget at `k < K·m`
only. -/
abbrev ResidWin (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    BundleHWin o G t (Pfam G) hn

/-- **`ResidH` from the window residual.** -/
def residH_of_window {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidWin o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_window (H G t hn hlo hhi)

#print axioms QMCLeafB.ResidBundle_M7.residH_of_window

/-- **Every phase-18/19/20 `ResidH` is a window residual** — the two targets are interchangeable and
the window one is strictly weaker. -/
def residWin_of_residH {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (h : ResidH o Pfam) : ResidWin o Pfam :=
  fun G t hn hlo hhi => window_of_bundleHB (bundleHB_of_bundleH (h G t hn hlo hhi))

#print axioms QMCLeafB.ResidBundle_M7.residWin_of_residH

/-- **The bundle residual from the window residual.** -/
def residBundleB_of_window {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidWin o Pfam) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      BundleHB o G t (Pfam G) hn :=
  fun G t hn hlo hhi => bundleHB_of_window (H G t hn hlo hhi)

#print axioms QMCLeafB.ResidBundle_M7.residBundleB_of_window

/-- **`d9f601e5` in the shelf's own name, from the window residual.** -/
theorem solution_statement_of_window
    (H : ResidWin (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH (residH_of_window H)

#print axioms QMCLeafB.ResidBundle_M7.solution_statement_of_window

/-- **The verbatim `d9f601e5` sentence from the window residual.** -/
theorem solution_of_window
    (H : ResidWin (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  QMCLeafB.FlagsM5.solution_of_residH (residH_of_window H)

#print axioms QMCLeafB.ResidBundle_M7.solution_of_window

/-- **The statement lock**: the verbatim `∃ L` sentence follows from `SolutionStatement`, so the two
are the same `Prop` and the window residual concludes `d9f601e5` verbatim. -/
theorem lock_solution_of_window
    (H : ResidWin (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_statement_of_window H

#print axioms QMCLeafB.ResidBundle_M7.lock_solution_of_window

/-! ## 4.  Non-vacuity

At the ok point `(G₀, −1/2)` the window residual is inhabited: `RecordsM2.streamCore_G₀_inhabited`
gives a `StreamCore`, `FlagsM5.bundleH_of_core` turns it into a `BundleH`, and §2 quotes it at the
window. -/

/-- **`BundleHWin` is inhabited at `(G₀, −1/2)`.** -/
theorem window_G₀_inhabited :
    Nonempty (BundleHWin (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀) QMCLeafB.ResidKill.hnG₀) := by
  obtain ⟨S⟩ := QMCLeafB.RecordsM2.streamCore_G₀_inhabited
  exact ⟨window_of_bundleHB (bundleHB_of_bundleH
    (QMCLeafB.FlagsM5.bundleH_of_core S))⟩

#print axioms QMCLeafB.ResidBundle_M7.window_G₀_inhabited

/-! ## 5.  The ceiling, again, at the window

The window form does not move the trace ceiling either: at every cut round of the window the
engine's own centre satisfies `diagSum (Cat k) ≤ n·(1 − dq/4)`.  `Check_residb_m7` §17 gives the same
at `BundleH`; the point of repeating it here is that **this is the one slot the window restate does
not relax**, so it is the slot a falsification of the joint feasibility (a legal stream whose
accumulated trace exceeds `n`) would kill.  Everything else on the window is either supplied
(`C`, `hcEq`, `hmarg`), constructed (`cn`, `hlam0`, `hlam1`, `hlam2` follow from `RecordM2.lamInd`),
or vacuous at the refuted branch (`hmem`, `hverdict` at `o G t = false`). -/

/-- **The window record forces the engine centre's trace under `n·(1 − dq/4)`.** -/
theorem window_forces_engine_trace {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (W : BundleHWin o G t P hn) {k : ℕ} (hk : k < P.K * P.m) (hok : W.ok k = false) :
    QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn W.cn W.hcne) k)
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
  have h1 : QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G P hn W.cn W.hcne) k)
      ≤ ∑ i : Fin G.n, ((W.cX k i i : ℚ) : ℝ) :=
    (QMCLeafB.DriftExact.stated_iff_trace _ (W.cX k)).1 (W.hdriftd k hk hok)
  have h2 : (∑ i : Fin G.n, ((W.cX k i i : ℚ) : ℝ))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ) := by
    have htr := W.hTrc k
    have hcast : ((∑ i, W.cX k i i : ℚ) : ℝ)
        ≤ (((G.n : ℚ) * (1 - P.dq / 4) : ℚ) : ℝ) := by exact_mod_cast htr
    rw [Rat.cast_sum] at hcast
    push_cast at hcast ⊢
    linarith
  linarith

#print axioms QMCLeafB.ResidBundle_M7.window_forces_engine_trace

end QMCLeafB.ResidBundle_M7



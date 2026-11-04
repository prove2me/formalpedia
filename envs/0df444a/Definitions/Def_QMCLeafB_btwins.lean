-- Prove2me | Definitions.Def_QMCLeafB_btwins
-- name    : QMCLeafB_btwins
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:38:58.270225+00:00
-- url     : https://prove2.me/theorems/1eaccb4e-1d0b-4d72-a443-f2848ce5ce6e
-- title:
--   QMCLeafB btwins
-- statement:
--   # leaf B phase 22 — the horizon-bounded twins of the `RunParts` producers
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_residb_m7
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_drift_m3
import Definitions.Def_QMCLeafB_residbundle_m7
/-
# leaf B phase 22 — the horizon-bounded twins of the `RunParts` producers
(swarm `smw1ntur6`, member m1, direction d3)

Phase 21's accepted residual is horizon-bounded: `ResidB_M7.CoreDataB` /
`EndgameM2.CoreDataB` carry the two drift slots only at `k < P.K * P.m`
(`StreamCoreB` likewise).  The two producers that turn a *stream* into
`FinalStroke.RunParts` are still stated at **every** round:

* `DriftExact.runParts_of_exact_stream` / `runParts_of_exact_trace`
  (`hdiagc`/`hTrc`, `hdriftc`, `hdriftd`, `hbody`, `hlam1`, `hlam2` — all `∀ k`);
* `RunPartsDilate.runParts_of_dilated` (same slots, explicit dilation direction `dM`).

At a refuted interior point the flag stream is `false` everywhere below the
horizon, so an `∀ k` slot is an `∀ k ∈ ℕ` obligation — exactly the object m8's
`drift_overflow` refutes.  The horizon clip `okClip` (`ResidB_M7` §1) collapses
the two forms: with the clipped stream the `false`-conditioned slots are quoted
only at `k < K·m`, and `anyOk` cannot see the difference.

This file delivers the twins, with the hypotheses **re-cut to the bounded slot
family** and the conclusion type unchanged (`FinalStroke.RunParts o G t P`):

* `runParts_of_dilated_b` — bounded twin of `runParts_of_dilated`;
* `runParts_of_exact_stream_b` — bounded twin of `runParts_of_exact_stream`
  (`hdriftc` in the normal's form, body from the entrywise `hdiagc`);
* `runParts_of_exact_trace_b` — bounded twin of `runParts_of_exact_trace`
  (`hTrc` in trace form, the form `StreamCoreB.hTrc`/`CoreDataB` supply);
* `runParts_of_dilated_of_unbounded` / `runParts_of_exact_trace_of_unbounded`
  — the *no-loss* receipt: every instantiation of the `∀ k` producers is an
  instantiation of the twins, so nothing on the shelf is lost by switching;
* `runParts_of_streamCoreB` / `runParts_of_coreDataB` / `parts_of_residB` /
  `parts_of_residG` — the accepted bounded shapes reach `RunParts` directly
  (`parts_of_resid*` at an arbitrary program bit, for a bit repoint), and
  `hd_of_residB` / `hd_of_residG` put them on `AssemblyM5.HdProp`, i.e. on the
  `AssemblyM5.endgame_of_hd` conduit;
* `runParts_paramsKbc2_b` — the same slot list at the campaign family
  `UnionShallow.paramsKbc2`: the target interface of the refuted-point producer;
* §7 the consumer audit: what switches, and what the audit leaves open;
* §8 the dilation direction as a slot: the accepted chain hard-codes `dM = 1`,
  and the `dM = −1` reading of both slots (`hdriftd_neg_one_iff`,
  `frob_neg_one_sub`, `flatQ_neg_one`);
* §9 the window residual `BundleHWin`/`ResidWin` on the same `RunParts`/`hd`
  conduit (`runParts_of_bundleHWin`, `parts_of_residWin`, `hd_of_residWin`).

One implementation point, since it is the whole proof: the twins feed the
existing producers the **horizon-clipped** stream `okClip (P.K * P.m) ok`
(`ResidB_M7` §1).  Every `ok k = false`-conditioned slot is then confined to
`k < P.K * P.m` by `okClip_eq_false_iff`, and `anyOk` cannot see the clip
(`anyOk_okClip`).  The `RunParts` handed back therefore carries the clipped
stream in its `ok` *field* — the same type, with all slots identical below the
horizon, and `reOk_runParts` upgrades it to any below-horizon-equivalent
stream.

House discipline: `set_option autoImplicit false`; a `#print axioms` audit after
every declaration (each is `[propext, Classical.choice, Quot.sound]` or a
subset); no proof-escape token of the library discipline; `⊊` is not used.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.BTwins_M1

open QuantumMaxCutEnergy
open QMCLeafB.RunPartsStream (dOne)
open QMCLeafB.ResidB_M7 (okClip okClip_apply_lt okClip_eq_false_iff anyOk_okClip)

/-! ## 1.  Transporting a `RunParts` to another `ok` stream

`RunParts`'s slots are all guarded by `k < P.K * P.m` and conditioned on
`ok k = false` (or `= true`), so the *only* observable content of the `ok` field
is its first `K·m` bits.  `reOk_runParts` therefore lets a producer deliver its
own stream: give a bit stream agreeing below the horizon and the verdict
equation at that stream, and every recorded slot transports.  This is what
makes the clip lossless in §2–§4. -/

/-- **Change the `ok` field of a `RunParts` below-horizon-equivalently.**  Every
`false`/`true`-conditioned slot is re-quoted at the new stream. -/
def reOk_runParts {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (ok' : ℕ → Bool)
    (hok : ∀ k, k < P.K * P.m → ok' k = B.ok k)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok' (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P where
  ok := ok'
  cd := B.cd
  del := B.del
  hcert := fun k hk hk' => B.hcert k hk (by rw [hok k hk] at hk'; exact hk')
  hwit := fun k hk hk' => B.hwit k hk (by rw [hok k hk] at hk'; exact hk')
  hrho := fun k hk hk' => B.hrho k hk (by rw [hok k hk] at hk'; exact hk')
  hcne := fun k hk hk' => B.hcne k hk (by rw [hok k hk] at hk'; exact hk')
  hdel0 := fun k hk hk' => B.hdel0 k hk (by rw [hok k hk] at hk'; exact hk')
  hcheck := fun k hk hk' => B.hcheck k hk (by rw [hok k hk] at hk'; exact hk')
  hle := fun k hk hk' => B.hle k hk (by rw [hok k hk] at hk'; exact hk')
  hcut := fun k hk hk' => B.hcut k hk (by rw [hok k hk] at hk'; exact hk')
  hverdict := hverdict

#print axioms QMCLeafB.BTwins_M1.reOk_runParts

/-- The transport keeps the recorded cut sequence, so the `RunData` glue is
unaffected. -/
theorem reOk_runParts_cd {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (ok' : ℕ → Bool)
    (hok : ∀ k, k < P.K * P.m → ok' k = B.ok k)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok' (P.K * P.m)) (k : ℕ) :
    (reOk_runParts B ok' hok hverdict).cd k = B.cd k := rfl

#print axioms QMCLeafB.BTwins_M1.reOk_runParts_cd

/-- The transport keeps the recorded margins. -/
theorem reOk_runParts_del {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts o G t P) (ok' : ℕ → Bool)
    (hok : ∀ k, k < P.K * P.m → ok' k = B.ok k)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok' (P.K * P.m)) (k : ℕ) :
    (reOk_runParts B ok' hok hverdict).del k = B.del k := rfl

#print axioms QMCLeafB.BTwins_M1.reOk_runParts_del

section Bounded

variable {G : QuantumMaxCutEnergy.Input} {t : ℚ}
  {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-! ## 2.  The bounded twin of `runParts_of_dilated`

Hypothesis list of `RunPartsDilate.runParts_of_dilated` with every
`ok k = false`-conditioned slot additionally restricted to `k < P.K * P.m`.
The four flag-free slots (`hCsym`, `hcne`, `hlam0`, `hcne` of the normal, and
`hmem` which is already bounded) keep their `∀ k` form — they are
`RecordM2.lamInd`/`cnOf`-shaped and carry no round content. -/

/-- **`RunParts o G t P` from data supplied only below the horizon** (dilation
form).  Every `false`-conditioned slot — the cut records `C` and their margins,
the recorded-normal identifications, the body condition, both drift budgets and
the two dilation bounds — is asked at `k < P.K * P.m` only. -/
def runParts_of_dilated_b
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hrmax : 0 < P.rmax)
    (hbud : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hdM : dM ≠ 0)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      marg k = (C k hk hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal)
    (hcn : ∀ k, k < P.K * P.m → ok k = false →
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k, k < P.K * P.m → ok k = false → ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((P.dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftc : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m → ok k = false →
      |(c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ dM) k)
          + (QMCLeafB.RelaxOracle.flatQ dM ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn
              cn hcne (c k) k)|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ dM
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ dM) k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  classical
  -- the clipped stream: `false` only below the horizon
  exact QMCLeafB.RunPartsDilate.runParts_of_dilated
    (o := o) (G := G) (t := t) (P := P) (hn := hn) hrmax hbud
    (okClip (P.K * P.m) ok) marg cX dM hdM lam c cn
    (fun k hk => C k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hmarg k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk htrue => hmem k hk (by rw [okClip_apply_lt hk] at htrue; exact htrue))
    hCsym
    (fun k hk => hcEq k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hcn k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    hcne hlam0
    (fun k hk => hbody k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hdriftc k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hdriftd k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hlam1 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (fun k hk => hlam2 k (okClip_eq_false_iff.1 hk).1 (okClip_eq_false_iff.1 hk).2)
    (by rw [hverdict, anyOk_okClip])

#print axioms QMCLeafB.BTwins_M1.runParts_of_dilated_b

/-! ## 3.  The bounded twin at `dM = 1`: the exact-stream producer

`DriftExact.runParts_of_exact_stream` is §2 at the identity direction with the
body condition proved from the entrywise centre diagonal `hdiagc`; and
`runParts_of_exact_trace` is §2 at the identity direction with the body proved
from the rational trace bound `hTrc` (the `centre-closure` reduction).  Both
carry the same two drift slots; below we only re-cut them, and the body slot,
to `k < K·m`. -/

/-- **Bounded twin of `DriftExact.runParts_of_exact_stream`.**  The entrywise
centre bound `hdiagc` is asked only at cut rounds below the horizon (it feeds
`hbody` and nothing else), and likewise for the two drift slots. -/
def runParts_of_exact_stream_b
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      marg k = (C k hk hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal)
    (hcn : ∀ k, k < P.K * P.m → ok k = false →
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m → ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, k < P.K * P.m → ok k = false → ∀ i, (cX k) i i ≤ 1 - P.dq / 4)
    (hdriftc : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m → ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  have hne : (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ≠ 0 := by
    intro hzero
    have hidx : 0 < G.n := by omega
    have h1 := congrFun (congrFun hzero ⟨0, hidx⟩) ⟨0, hidx⟩
    simp at h1
  refine runParts_of_dilated_b (G := G) (t := t) (P := P) (hn := hn) o hrmaxPos hbudP
    ok marg cX (1 : Matrix (Fin G.n) (Fin G.n) ℚ) hne lam c cn C hmarg hmem hCsym hcEq
    hcn hcne hlam0 ?_ hdriftc ?_ hlam1 hlam2 hverdict
  · -- the body condition at the identity direction, from the bounded centre diagonal
    intro k hk hok X hX
    have hd' : ∀ i, ((cX k i i : ℚ) : ℝ) ≤ 1 - ((P.dq : ℚ) : ℝ) / 4 := by
      intro i
      have h := hdiagc k hk hok i
      have h2 : ((1 - P.dq / 4 : ℚ) : ℝ) = 1 - ((P.dq : ℚ) : ℝ) / 4 := by
        push_cast
        ring
      calc ((cX k i i : ℚ) : ℝ)
          ≤ ((1 - P.dq / 4 : ℚ) : ℝ) := by exact_mod_cast h
        _ = 1 - ((P.dq : ℚ) : ℝ) / 4 := h2
    simpa using QMCLeafB.RunPartsStream.hbody_of_diag_body hd' X hX
  · -- the identity direction's drift is the trace read-out
    intro k hk hok
    exact hdriftd k hk hok

#print axioms QMCLeafB.BTwins_M1.runParts_of_exact_stream_b

/-- **Bounded twin of `DriftExact.runParts_of_exact_trace`.**  Here the body
comes from the single rational trace inequality `hTrc` (the `centre-closure`
reduction), which is the form `StreamCoreB.hTrc` and `CoreDataB` supply. -/
def runParts_of_exact_trace_b
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      marg k = (C k hk hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hk : k < P.K * P.m) (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal)
    (hcn : ∀ k, k < P.K * P.m → ok k = false →
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < P.K * P.m → ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, k < P.K * P.m → ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hTrc : ∀ k, k < P.K * P.m → ok k = false →
      ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hdriftc : ∀ k, k < P.K * P.m → ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < P.K * P.m → ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  have hne : (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ≠ 0 := by
    intro hzero
    have hidx : 0 < G.n := by omega
    have h1 := congrFun (congrFun hzero ⟨0, hidx⟩) ⟨0, hidx⟩
    simp at h1
  refine runParts_of_dilated_b (G := G) (t := t) (P := P) (hn := hn) o hrmaxPos hbudP
    ok marg cX (1 : Matrix (Fin G.n) (Fin G.n) ℚ) hne lam c cn C hmarg hmem hCsym hcEq
    hcn hcne hlam0 ?_ hdriftc ?_ hlam1 hlam2 hverdict
  · -- the body condition at the identity direction, from the bounded centre trace
    intro k hk hok X hX
    simpa using QMCLeafB.DriftExact.hbody_of_trace (hTrc k hk hok) X hX
  · intro k hk hok
    exact hdriftd k hk hok

#print axioms QMCLeafB.BTwins_M1.runParts_of_exact_trace_b

/-! ## 4.  No loss: the `∀ k` producers are instances of the twins

A producer holding the *unbounded* slot list of phase 17/18 gets the twin's
bounded slot list by restriction.  So switching the shelf to the twins loses no
inhabitant — in particular every phase-21 anchor at the ok point `(G₀, -1/2)`
survives, and the restate is a strict weakening (the converse fails: below the
horizon is all the horizon-clipped shapes can pay for). -/

/-- **Bounded twin from the unbounded `runParts_of_dilated` slot list.** -/
def runParts_of_dilated_of_unbounded
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hrmax : 0 < P.rmax)
    (hbud : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (dM : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hdM : dM ≠ 0)
    (lam : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ) (cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k (hok : ok k = false),
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ dM)
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hbody : ∀ k (hok : ok k = false), ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat
          (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
        ((P.dq : ℚ) : ℝ) X →
      -(((0 : ℚ)) : ℝ) ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat dM)
        (X - QMCLeafB.SepOracle.castMat (cX k)))
    (hdriftc : ∀ k (hok : ok k = false),
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k (hok : ok k = false),
      (fun i => ((QMCLeafB.RelaxOracle.flatQ dM i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |(c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ dM) k)
          + (QMCLeafB.RelaxOracle.flatQ dM ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn
              cn hcne (c k) k)|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ dM
            ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ dM) k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  runParts_of_dilated_b (G := G) (t := t) (P := P) (hn := hn) o hrmax hbud ok marg cX dM
    hdM lam c cn (fun k _ => C k) (fun k _ => hmarg k) hmem hCsym (fun k _ => hcEq k)
    (fun k _ => hcn k) hcne hlam0 (fun k _ => hbody k) (fun k _ => hdriftc k)
    (fun k _ => hdriftd k) (fun k _ => hlam1 k) (fun k _ => hlam2 k) hverdict

#print axioms QMCLeafB.BTwins_M1.runParts_of_dilated_of_unbounded

/-- **Bounded twin from the unbounded `runParts_of_exact_trace` slot list** — the
phase-17/18 producer verbatim, cut to the horizon. -/
def runParts_of_exact_trace_of_unbounded
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k,
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k (hok : ok k = false), 1 ≤ lam k)
    (hlam2 : ∀ k (hok : ok k = false),
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (c k) k|
        + 9 * (marg k) ^ 2 / (4 * (P.rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hTrc : ∀ k, ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - P.dq / 4))
    (hdriftc : ∀ k (hok : ok k = false),
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k (hok : ok k = false),
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  runParts_of_exact_trace_b (G := G) (t := t) (P := P) (hn := hn) o hrmaxPos hrmax1 hbudP
    ok marg cX lam c cn (fun k _ => C k) (fun k _ => hmarg k) hmem hCsym
    (fun k _ => hcEq k) (fun k _ _ => hcn k) hcne hlam0 (fun k _ => hlam1 k)
    (fun k _ => hlam2 k) (fun k _ _ => hTrc k) (fun k _ => hdriftc k) (fun k _ => hdriftd k)
    hverdict

#print axioms QMCLeafB.BTwins_M1.runParts_of_exact_trace_of_unbounded

end Bounded

/-! ## 5.  The accepted bounded shapes reach `RunParts` directly

`ResidB_M7.bundleH_of_coreB` and `EndgameM2.bundleH_of_data` already build the
`FlagsM5.BundleH` of the closing chain out of the bounded residual (via the
`okClip`/`okHor` streams).  Composing with `FlagsM5.runParts_of_bundleH` puts
those shapes on the `hd` conduit too, so the `FinalStroke.RunParts` route needs
no `∀ k` stream obligation either. -/

/-- **The run half from the accepted bounded stream core.** -/
def runParts_of_streamCoreB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (S : QMCLeafB.ResidB_M7.StreamCoreB o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.FlagsM5.runParts_of_bundleH o G t P hn hrmaxPos hrmax1 hbudP
    (QMCLeafB.ResidB_M7.bundleH_of_coreB S)

#print axioms QMCLeafB.BTwins_M1.runParts_of_streamCoreB

/-- **The run half from the accepted bounded residual** (`EndgameM2.CoreDataB`). -/
def runParts_of_coreDataB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (D : QMCLeafB.EndgameM2.CoreDataB o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.FlagsM5.runParts_of_bundleH o G t P hn hrmaxPos hrmax1 hbudP
    (QMCLeafB.EndgameM2.bundleH_of_data hrmaxPos D)

#print axioms QMCLeafB.BTwins_M1.runParts_of_coreDataB

/-- **The `RunParts` family from the horizon-bounded residual at *any* program
bit** — the form a program-bit repoint (e.g. to `OkLower.roundW`) can consume
directly, without re-deriving the parameter plumbing. -/
def parts_of_residB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (H : QMCLeafB.EndgameM2.ResidB o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact runParts_of_coreDataB o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (H G t hn hlo hhi)

#print axioms QMCLeafB.BTwins_M1.parts_of_residB

/-- The same at the supplier-friendly `ResidG`. -/
def parts_of_residG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (H : QMCLeafB.EndgameM2.ResidG o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact QMCLeafB.FlagsM5.runParts_of_bundleH o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (QMCLeafB.EndgameM2.residH_of_supplied
      (fun G' hn' => QMCLeafB.ClosingAssembly.rmaxOf_pos G' hn') H G t hn hlo hhi)

#print axioms QMCLeafB.BTwins_M1.parts_of_residG

/-- **`hd` from the horizon-bounded residual**: the `AssemblyM5.endgame_of_hd`
conduit is fed by `EndgameM2.ResidB` with no unbounded stream slot anywhere. -/
def hd_of_residB
    (H : QMCLeafB.EndgameM2.ResidB
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  parts_of_residB _ H

#print axioms QMCLeafB.BTwins_M1.hd_of_residB

/-- **The same at the supplier-friendly `ResidG`** (`EndgameM2`'s own `ok`
stream, records supplied) — the shape the crater producer will inhabit. -/
def hd_of_residG
    (H : QMCLeafB.EndgameM2.ResidG
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  parts_of_residG _ H

#print axioms QMCLeafB.BTwins_M1.hd_of_residG


/-- **`d9f601e5` from the bounded residual through the `hd` conduit** — the
verbatim sentence, obtained from `ResidB` by `hd_of_residB` and
`AssemblyM5.endgame_of_hd`.  This is the consumer audit's receipt: the `hd`
stroke switches to the bounded shapes with no side condition added. -/
theorem solution_via_hd_of_residB
    (H : QMCLeafB.EndgameM2.ResidB
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
  QMCLeafB.AssemblyM5.endgame_of_hd (hd_of_residB H)

#print axioms QMCLeafB.BTwins_M1.solution_via_hd_of_residB

/-! ## 6.  The campaign-family bounded producer

The slot list above is `runParamsShallow`-shaped; the closing chain runs at
`UnionShallow.paramsKbc2` (`paramsShallowKf` at `Kbc2 (mHalve (n·n))`), whose
three scalar side conditions are on the shelf (`paramsKbc2_rmax_pos`,
`rmaxOf_le_one`, `paramsKbc2_budget`).  This is therefore the *target interface*
of the refuted-point producer: one `RunParts` at `paramsKbc2 G` from data below
`(paramsKbc2 G).K * (paramsKbc2 G).m` only. -/

/-- **`RunParts` at the campaign family from below-horizon data only.** -/
def runParts_paramsKbc2_b (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hmarg : ∀ k (hk : k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) (hok : ok k = false),
      marg k = (C k hk hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hk : k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
          * (QMCLeafB.UnionShallow.paramsKbc2 G).m) (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hk hok).normal)
    (hcn : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
            cn hcne (c k) k|
        + 9 * (marg k) ^ 2
            / (4 * ((QMCLeafB.UnionShallow.paramsKbc2 G).rmax) ^ 2) + 1
        ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
              cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hTrc : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      ∑ i, (cX k) i i ≤ (G.n : ℚ) * (1 - (QMCLeafB.UnionShallow.paramsKbc2 G).dq / 4))
    (hdriftc : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
                cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ ((marg k : ℚ) : ℝ) / 2)
    (hdriftd : ∀ k, k < (QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m → ok k = false →
      dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.UnionShallow.paramsKbc2 G) hn
                cn hcne) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.UnionShallow.paramsKbc2 G).K
        * (QMCLeafB.UnionShallow.paramsKbc2 G).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  runParts_of_exact_trace_b (G := G) (t := t) (P := QMCLeafB.UnionShallow.paramsKbc2 G)
    (hn := hn) o (QMCLeafB.UnionShallow.paramsKbc2_rmax_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq)
    ok marg cX lam c cn C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2
    hTrc hdriftc hdriftd hverdict

#print axioms QMCLeafB.BTwins_M1.runParts_paramsKbc2_b

/-! ## 7.  The consumer audit

Machine-checked above; the inventory below is the prose half of the direction's
second obligation ("which of the assembly's consumers switch to them"), with the
reading of the shelf it rests on.

**What a `RunParts` consumer can see.**  Every slot of `FinalStroke.RunParts`
(`Check_final_stroke_m7.lean` §5) is guarded by `k < P.K * P.m` and, apart from
`ok`/`cd`/`del`, conditioned on `ok k = true`/`ok k = false` at such a `k`.
Consequently

* the value of the `ok` field beyond the horizon is unobservable — this is why
  §2–§3 may hand back the clipped stream, and m7's `anyOk_okClip` already
  proves the verdict equation is blind to it;
* a producer that supplies its data below the horizon loses no information by
  going through §2–§4 (`runParts_of_dilated_of_unbounded` /
  `runParts_of_exact_trace_of_unbounded` make the `∀ k` slot lists a special
  case, so no phase-17/18 inhabitant is cut off).

**Consumers that switch.**  `RunParts` is consumed by
`RunParts.toRunData` → `VerdictSound.RunData` → `solution_of_loop_via_runData`,
by `AssemblyM5.endgame_of_hd`/`endgame_of_parts` through `HdProp`, by
`FlagsM5.hd_of_residH`, and by the window re-aimings of `Check_closing_m6`
(`runParts_window_le`, which carries `R.ok` over verbatim and therefore composes
with the clipped stream unchanged).  All of them receive the *same type*, so
switching a producer to a `_b` form is invisible to them.  The wiring is
delivered in §5: `runParts_of_streamCoreB` / `runParts_of_coreDataB` /
`parts_of_residB` / `parts_of_residG` (the last two at an *arbitrary* program
bit `o`, so a repoint of the leaf's bit needs no re-derivation of the parameter
plumbing) and the `HdProp` specialisations `hd_of_residB` / `hd_of_residG`.

**Producers that must switch.**  `runParts_of_exact_stream`,
`runParts_of_exact_trace` and `runParts_of_dilated` are the live producers used
by `Check_centreCore`, `Check_runparts_stream_m4`, `Check_drift_m3` §6 and
`Check_closingAssembly_m3`'s `Bundle`; all of them quote the two drift slots and
the body condition at **every** `k`, which is uninhabited as soon as the flag
stream is `false` at arbitrarily large `k` (m8's `drift_overflow`).  Their
bounded replacements are §2–§3.  `Check_closingAssembly_m3.Bundle` itself is the
superseded phase-18 shape (`hokAll`, unbounded drift slots); the live corrected
shape is `FlagsM5.BundleH`, and `residH_to_residFull`/`residFull_to_residH`
keep the two interchangeable at the residual level, so nothing in that file
needs re-cutting for this direction.

**What the audit leaves open is only the crater.**  With this file's bridges in
place, the whole `RunParts`/`hd` route consumes exactly the bounded slot list of
`EndgameM2.CoreDataB`, whose refuted-point content is already named by
`EndgameM2.coreDataB_at_empty`: both drift budgets at `k < P.K * P.m` and the
verdict bit `false`, and *no obligation at any round past the horizon*.  So the
bounded twins do not shrink the crater (m8's overflow fires at round 4, far
inside the window) — what they remove is the whole class of "beyond the
horizon" side conditions that the `∀ k` producers used to impose on it. -/

/-! ## 8.  The dilation direction is a slot, not a constant

The accepted closing chain reaches `RunParts` through `FlagsM5.BundleH` and
`FlagsM5.runParts_of_bundleH`, i.e. through `DriftExact.runParts_of_exact_trace`,
which hard-codes the identity direction `dM := 1`.  In that chain the two
identity slots are

* `hTrc : ∀ k, ∑ i, (cX k) i i ≤ n·(1 − dq/4)` — the centre's trace ceiling, and
* `hdriftd : dOne ⬝ (Cat k − flat (cX k)) ≤ 0` — i.e. `diagSum (Cat k) ≤ tr (cX k)`
  (`DriftExact.stated_iff_trace`).

Together they force `diagSum (Cat k) ≤ n·(1 − dq/4)` at every cut round — the
object m8's `drift_overflow` refutes for the trace-direction drill.  Note where
the ceiling comes from: it is `hTrc`, and `hTrc` occurs in that chain **only**
to pay the body slot `hbody` through `hbody_of_trace` at `dM = 1`.  §2, by
contrast, takes `dM` as a parameter and `hbody` as an explicit hypothesis, so it
never mentions `hTrc` at all.

The identity choice is therefore a *choice*, and the two slots trade against
each other.  The algebra below makes the trade exact for the opposite choice
`dM = −1`: the drift slot becomes the **reversed** trace budget (which the
overflow itself satisfies), and the body slot becomes a *lower* bound on the
centre's trace instead of an upper one.  Neither choice is free; what matters is
that the campaign's refuted form is the `dM = 1` specialisation of §2, and §2 is
the only bounded producer on the shelf whose direction slot is open. -/

/-- **The negative identity flattens to minus the trace direction.** -/
theorem flatQ_neg_one (n : ℕ) :
    QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ)
      = -QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) := by
  funext k
  simp only [QMCLeafB.RelaxOracle.flatQ, Pi.neg_apply, Matrix.neg_apply]

#print axioms QMCLeafB.BTwins_M1.flatQ_neg_one

/-- **The drift slot at `dM = −1` is the reversed trace budget**: the recorded
direction is `−dOne`, so the inequality asks the engine centre to have the
*larger* diagonal read-out.  (Compare `DriftExact.stated_iff_trace`, which is the
`dM = 1` reading.) -/
theorem hdriftd_neg_one_iff {n : ℕ} (z : Fin (n * n) → ℝ)
    (Y : Matrix (Fin n) (Fin n) ℚ) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
        ⬝ᵥ (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y)) ≤ 0
      ↔ ∑ i, (Y i i : ℝ) ≤ QMCLeafB.DriftExact.diagSum z := by
  have hvec : (fun i => ((QMCLeafB.RelaxOracle.flatQ (-1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
      = -QMCLeafB.RunPartsStream.dOne n := by
    rw [flatQ_neg_one]
    funext k
    simp only [Pi.neg_apply, QMCLeafB.RunPartsStream.dOne]
    push_cast
    ring
  have hsub : QMCLeafB.DriftExact.diagSum
      (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Y))
      = QMCLeafB.DriftExact.diagSum z - ∑ i, (Y i i : ℝ) := by
    simp only [QMCLeafB.DriftExact.diagSum, Pi.sub_apply, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QMCLeafB.DriftExact.flat_finProdFinEquiv, QMCLeafB.SepOracle.castMat_apply]
  rw [hvec, neg_dotProduct, QMCLeafB.DriftExact.dOne_dot, hsub, neg_nonpos]
  constructor <;> intro h <;> linarith

#print axioms QMCLeafB.BTwins_M1.hdriftd_neg_one_iff

/-- **The body slot at `dM = −1` is the reversed trace bound**: the Frobenius
pairing with `−1` is `tr Q − tr X`, so `hbody` asks the centre to sit *above* the
whole body in trace. -/
theorem frob_neg_one_sub {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ))
        (X - QMCLeafB.SepOracle.castMat Q)
      = (∑ i, (Q i i : ℝ)) - ∑ i, X i i := by
  have hneg : QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ)
      = -(1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [← QMCLeafB.RunPartsStream.castMat_one]
    ext i j
    simp [QMCLeafB.SepOracle.castMat_apply, Matrix.neg_apply]
  have hnegfrob : ∀ C Z : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.SepOracle.frob (-C) Z = -QMCLeafB.SepOracle.frob C Z := by
    intro C Z
    simp only [QMCLeafB.SepOracle.frob, Matrix.neg_apply, neg_mul]
    simp_rw [Finset.sum_neg_distrib]
  have hQ : (∑ i, QMCLeafB.SepOracle.castMat Q i i) = ∑ i, (Q i i : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QMCLeafB.SepOracle.castMat_apply]
  rw [hneg, hnegfrob, QMCLeafB.SepOracle.frob_sub, QMCLeafB.RunPartsStream.frob_one_eq_trace,
    QMCLeafB.RunPartsStream.frob_one_eq_trace, hQ]
  ring

#print axioms QMCLeafB.BTwins_M1.frob_neg_one_sub

/-! ## 9.  The window residual (`BundleHWin`/`ResidWin`) reaches `RunParts` too

`ResidBundle_M7.BundleHWin` is the most likely landing shape for the crater
producer: cut records **supplied**, `ok` free, and every budget `k < K·m`.  Its
slot list is exactly §2's at `dM = 1` *plus* `hTrc` — i.e. the identity slice.
The bridges below put it on the `hd` conduit, so whichever residual shape lands
(m7's `StreamCoreB`, m2's `CoreDataB`/`CoreDataG`, m7's `BundleHWin`) the
`AssemblyM5.endgame_of_hd` ending is available without further plumbing. -/

/-- **The run half from the window residual.** -/
def runParts_of_bundleHWin (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (W : QMCLeafB.ResidBundle_M7.BundleHWin o G t P hn) :
    QMCLeafB.FinalStroke.RunParts o G t P :=
  QMCLeafB.FlagsM5.runParts_of_bundleH o G t P hn hrmaxPos hrmax1 hbudP
    (QMCLeafB.ResidBundle_M7.bundleH_of_window W)

#print axioms QMCLeafB.BTwins_M1.runParts_of_bundleHWin

/-- **The `RunParts` family from the window residual at any program bit.** -/
def parts_of_residWin (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (H : QMCLeafB.ResidBundle_M7.ResidWin o QMCLeafB.UnionShallow.paramsKbc2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hlo hhi
  exact runParts_of_bundleHWin o G t (QMCLeafB.UnionShallow.paramsKbc2 G) hn
    (QMCLeafB.ClosingAssembly.rmaxOf_pos G hn)
    (QMCLeafB.ClosingAssembly.rmaxOf_le_one G hn)
    (QMCLeafB.ClosingAssembly.budget_dqShallow G hn
      (QMCLeafB.AssemblyM5.Rq_pos_of_interior_bracket G t hlo hhi))
    (H G t hn hlo hhi)

#print axioms QMCLeafB.BTwins_M1.parts_of_residWin

/-- **`hd` from the window residual.** -/
def hd_of_residWin
    (H : QMCLeafB.ResidBundle_M7.ResidWin
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.AssemblyM5.HdProp :=
  parts_of_residWin _ H

#print axioms QMCLeafB.BTwins_M1.hd_of_residWin

end QMCLeafB.BTwins_M1



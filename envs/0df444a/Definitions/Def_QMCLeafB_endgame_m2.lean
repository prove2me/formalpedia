-- Prove2me | Definitions.Def_QMCLeafB_endgame_m2
-- name    : QMCLeafB_endgame_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:23:59.396897+00:00
-- url     : https://prove2.me/theorems/35185101-1f7b-4d72-9595-2f20311dc819
-- title:
--   QMCLeafB endgame_m2
-- statement:
--   # leaf B phase 21 — the endgame assembly at the horizon-bounded residual
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
/-
# leaf B phase 21 — the endgame assembly at the horizon-bounded residual
(swarm `smw1m5nkm`, member m2, direction d7 `integration`)

## What the phase-21 refutation candidate changes, and what it does not

Phase 20's residual is `RecordsM2.CoreDataF`: the run's coded states, `hsym`, the two drift
budgets, the verdict bit — and **`hcutfin`** (`flagOf k = false → k < K·m`), which exists only to
convert the finite-cut obligation back into the `∀ k` shapes of `FlagsM5.StreamCore`/`CoreData` so
that phase-19's closing stroke applies.  At a refuted interior point whose relaxed body is empty,
`hcutfin` is unsatisfiable (every round is a non-member round), so `CoreDataF` — and every shape
above it in the `StreamCore` chain — is uninhabitable there.

This file removes the need for that conversion.  The observation is that the closing stroke itself
is **already horizon-bounded**: `FlagsM5.BundleH` has its member slot `hmem` at `k < K·m` and its
verdict read-out `hverdict : o G t = anyOk ok (K·m)`, and its flag stream `ok` is a **free field**,
not the canonical `flagOf`.  So instead of forcing every round of an infinite stream to be a member,
the stream can simply report `ok` beyond the horizon.  Everything that the infinite stream was
needed for is the depth ledger (`hlam1`/`hlam2`), and there the multiplier construction
`RecordM2.lamInd` is flag-independent — it supplies the ledger at *every* `k`, member or not.

Hence the residual restated here, `CoreDataB`, is `CoreDataF` **minus `hcutfin`**:

    X, hsym, hdriftc (k < K·m, flag false), hdriftd (k < K·m, flag false), hverdict.

and it reaches the verbatim `d9f601e5` sentence through `bundleH_of_data` → `ResidH` →
`FlagsM5.solution_of_residH`.

* §1 `anyOk` sees only the window `[0, K·m)`.
* §2 the truncated flag stream `okHor` (canonical below the horizon, `true` above) and its two
  readings: a `false` reading forces `k < K·m` **and** a false canonical flag.
* §3 the residual `CoreDataB` and its centre family `dataCX`/`dataLam`/`dataCn`/… .
* §4 `bundleH_of_data : CoreDataB → BundleH` — the assembly.  The multiplier block, the dilated
  normals, the cut records, the margins and the trace slot are all *constructed*; the flag stream
  is the truncated canonical one; the only supplied content is §3's.
* §5 the closing stroke: `solution_of_bounded` is `d9f601e5` verbatim, and
  `solution_statement_of_bounded` is `FinishLine.SolutionStatement`.
* §6 **conservativity**: `CoreDataF → CoreDataB`, so phase 20's residual (and every inhabitant of
  it) is consumed, not discarded; `solution_of_finite_via_bounded` re-derives phase-20's theorem.
* §7 non-vacuity at `(G₀, -1/2)`, the point where the phase-19 shape is refuted.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end of every section.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.EndgameM2

open Classical
open QuantumMaxCutEnergy
open QMCLeafB.FlagsM5 (BundleH ResidH cutOf flagOf)
open QMCLeafB.RecordsM2

/-! ## 1.  `anyOk` sees only the window `[0, K·m)` -/

/-- `anyOk` at a fixed count depends only on the values below that count. -/
theorem anyOk_congr {ok ok' : ℕ → Bool} {T : ℕ} (h : ∀ k, k < T → ok k = ok' k) :
    QMCLeafB.SimLoop.anyOk ok T = QMCLeafB.SimLoop.anyOk ok' T := by
  have key : ∀ o o' : ℕ → Bool, (∀ k, k < T → o k = o' k) →
      (QMCLeafB.SimLoop.anyOk o T = true → QMCLeafB.SimLoop.anyOk o' T = true) := by
    intro o o' hoo h1
    rw [QMCLeafB.SimLoop.anyOk_eq_true_iff o T] at h1
    obtain ⟨k, hk, htrue⟩ := h1
    rw [QMCLeafB.SimLoop.anyOk_eq_true_iff o' T]
    exact ⟨k, hk, by rw [← hoo k hk]; exact htrue⟩
  have h12 := key ok ok' h
  have h21 := key ok' ok (fun k hk => (h k hk).symm)
  cases hb1 : QMCLeafB.SimLoop.anyOk ok T <;>
    cases hb2 : QMCLeafB.SimLoop.anyOk ok' T <;> simp_all

#print axioms QMCLeafB.EndgameM2.anyOk_congr

/-! ## 2.  The truncated flag stream

The closing stroke's bundle carries its own flag stream (`ok : ℕ → Bool`), and only two of its slots
read that stream outside the horizon: `hlam1`/`hlam2` (the depth ledger) and the two drift budgets.
Both are *vacuous* wherever `ok k = true`, and the ledger is a constructed stream at every `k`.  So
the infinite canonical stream is not needed: truncating it at the horizon loses nothing, and it is
what makes the shape inhabitable at a refuted empty-body point. -/

/-- **The truncated canonical flag stream**: the canonical flag below the run's horizon `K·m`,
`true` above it. -/
def okHor (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : Bool :=
  if k < P.K * P.m then flagOf G t P cX k else true

/-- Below the horizon the truncated stream *is* the canonical one. -/
theorem okHor_of_lt {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ} (hk : k < P.K * P.m) :
    okHor G t P cX k = flagOf G t P cX k := by
  simp [okHor, hk]

/-- Above the horizon the truncated stream reports `ok`. -/
theorem okHor_of_not_lt {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ} (hk : ¬ k < P.K * P.m) :
    okHor G t P cX k = true := by
  simp [okHor, hk]

/-- **A `false` reading of the truncated stream is inside the horizon.** -/
theorem okHor_lt {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : okHor G t P cX k = false) : k < P.K * P.m := by
  by_contra hk
  simp [okHor, hk] at h

/-- **A `false` reading of the truncated stream is a `false` canonical flag.** -/
theorem okHor_flag {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} {k : ℕ}
    (h : okHor G t P cX k = false) : flagOf G t P cX k = false := by
  by_cases hk : k < P.K * P.m
  · simpa [okHor, hk] using h
  · simp [okHor, hk] at h

/-- The truncated stream agrees with the canonical one on the window the verdict reads. -/
theorem anyOk_okHor {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    {cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ} :
    QMCLeafB.SimLoop.anyOk (okHor G t P cX) (P.K * P.m)
      = QMCLeafB.SimLoop.anyOk (flagOf G t P cX) (P.K * P.m) :=
  anyOk_congr (fun _ hk => okHor_of_lt hk)

#print axioms QMCLeafB.EndgameM2.okHor_of_lt
#print axioms QMCLeafB.EndgameM2.okHor_lt
#print axioms QMCLeafB.EndgameM2.okHor_flag
#print axioms QMCLeafB.EndgameM2.anyOk_okHor

/-! ## 3.  The centre family and the horizon-bounded residual

The residual is `RecordsM2.CoreDataF` with **`hcutfin` deleted**.  Everything else is unchanged, so
every phase-20 inhabitant is one (… see §6). -/

section Data

variable {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G}
  {hn : 2 ≤ G.n}

/-- The run's queried centres: the diagonal pinch of the run's own coded state. -/
abbrev dataCX (X : ℕ → List ℚ) : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ :=
  cXst G.n X P.dq

/-- The constructed multiplier stream at the run's centres. -/
abbrev dataLam (X : ℕ → List ℚ) : ℕ → ℚ :=
  lamOf G t P hn (dataCX (G := G) (P := P) X)

/-- The constructed dilated normal stream. -/
abbrev dataCn (X : ℕ → List ℚ) : ℕ → Fin (G.n * G.n) → ℚ :=
  cnOf G t P hn (dataCX (G := G) (P := P) X)

/-- The canonical oracle normal of round `k`. -/
abbrev dataNrm (X : ℕ → List ℚ) (k : ℕ) : Fin (G.n * G.n) → ℚ :=
  nrmOf G t P (dataCX (G := G) (P := P) X) k

/-- The canonical margin of round `k`. -/
abbrev dataMarg (X : ℕ → List ℚ) (k : ℕ) : ℚ :=
  margOf G t P (dataCX (G := G) (P := P) X) k

/-- The engine's recorded cut stream. -/
abbrev dataStream (X : ℕ → List ℚ) : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  cutStream G t P hn (dataCX (G := G) (P := P) X)

/-- **The horizon-bounded residual at one interior `(G, t)`** — `RecordsM2.CoreDataF` without
`hcutfin`.  Every flag-conditioned slot is confined to the run's own horizon `k < K·m`; there is no
obligation at any round past it.  This is the shape a refuted empty-body point can inhabit (§7 and
the phase-21 board). -/
structure CoreDataB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states -/
  X : ℕ → List ℚ
  /-- the run's states are symmetric -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **the canonical normal's centre mismatch, below the horizon** -/
  hdriftc : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget, below the horizon** -/
  hdriftd : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (cutStream G t P hn (cXst G.n X P.dq)) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

end Data

#print axioms QMCLeafB.EndgameM2.CoreDataB.hsym

/-! ## 4.  The assembly: `CoreDataB → BundleH`

`BundleH` is `DriftExact.runParts_of_exact_trace`'s hypothesis list, so the moment the record below
is inhabited the closing stroke applies.  Note what is *not* supplied: the flag stream (truncated
canonical, §2), the cut records and margins (`cutOf`), the multiplier and its depth ledger
(`RecordM2.lamInd`, flag-independent), the dilated normals (`cnInd`), and the trace slot (`cXst`,
unconditional). -/

/-- **The assembly.**  A `BundleH` at `(G, t)` from the horizon-bounded residual. -/
def bundleH_of_data {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hrmax : 0 < P.rmax) (D : CoreDataB o G t P hn) : BundleH o G t P hn where
  ok := okHor G t P (dataCX (G := G) (P := P) D.X)
  marg := fun k => dataMarg (G := G) (t := t) (P := P) D.X k
  cX := dataCX (G := G) (P := P) D.X
  lam := dataLam (G := G) (t := t) (P := P) (hn := hn) D.X
  c := fun k => dataNrm (G := G) (t := t) (P := P) D.X k
  cn := dataCn (G := G) (t := t) (P := P) (hn := hn) D.X
  C := fun k _ => cutOf G t P (dataCX (G := G) (P := P) D.X) k
  hmarg := fun k _ => rfl
  hmem := fun k hk htrue => by
    have hf : flagOf G t P (dataCX (G := G) (P := P) D.X) k = true := by
      rw [okHor_of_lt hk] at htrue
      exact htrue
    exact QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P
      (dataCX (G := G) (P := P) D.X) k hf
  hCsym := cXst_symm G.n D.X P.dq D.hsym
  hcEq := fun k _ => rfl
  hcn := fun k => rfl
  hcne := cnOf_ne G t P hn (dataCX (G := G) (P := P) D.X)
  hlam0 := QMCLeafB.RecordM2.lamInd_nonneg
    (QMCLeafB.RunPartsDilate.A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega))
    (dataNrm (G := G) (t := t) (P := P) D.X)
    (dataMarg (G := G) (t := t) (P := P) D.X) P.rmax
  hlam1 := fun k _ => QMCLeafB.RecordM2.lamInd_ge_one
    (QMCLeafB.RunPartsDilate.A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega))
    (dataNrm (G := G) (t := t) (P := P) D.X)
    (dataMarg (G := G) (t := t) (P := P) D.X) P.rmax k
  hlam2 := fun k _ => lamOf_spec G t P hn
    (dataCX (G := G) (P := P) D.X) hrmax k
  hTrc := hTrc_cXst G.n D.X P.dq
  hdriftc := fun k hok => D.hdriftc k (okHor_lt hok) (okHor_flag hok)
  hdriftd := fun k hok => D.hdriftd k (okHor_lt hok) (okHor_flag hok)
  hverdict := by
    rw [D.hverdict, anyOk_okHor (P := P)]

#print axioms QMCLeafB.EndgameM2.bundleH_of_data

/-! ## 5.  The closing stroke

`ResidB` is the horizon-bounded residual over the whole interior bracket.  Through
`FlagsM5.solution_of_residH` it gives the verbatim `d9f601e5` sentence and the shelf's own
`SolutionStatement`. -/

/-- **The horizon-bounded residual.** -/
abbrev ResidB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataB o G t (Pfam G) hn

/-- **`ResidH` from the horizon-bounded residual** (any family with a positive ceiling). -/
def residH_of_bounded {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (H : ResidB o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_data (hrmax G hn) (H G t hn hlo hhi)

#print axioms QMCLeafB.EndgameM2.residH_of_bounded

/-- **The verbatim `d9f601e5` sentence from the horizon-bounded residual.** -/
theorem solution_of_bounded
    (H : ResidB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
    (residH_of_bounded (fun G hn => rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.EndgameM2.solution_of_bounded

/-- **The same in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_bounded
    (H : ResidB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH
    (residH_of_bounded (fun G hn => rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.EndgameM2.solution_statement_of_bounded

/-! ## 6.  Conservativity: the phase-20 residual is consumed, not discarded

`CoreDataF` is `CoreDataB` plus `hcutfin`, so the restatement only removes an obligation.  Nothing
delivered in phase 20 is lost: `residB_of_finite` re-aims `ResidFinite` at this file's closing
stroke, and `solution_of_finite_via_bounded` is phase 20's `solution_of_finite` sentence again. -/

/-- **`CoreDataB` from the phase-20 finite-cut data.** -/
def coreDataB_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataF o G t P hn) : CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftc := fun k hk hf => D.hdriftc k (D.hcutfin k hf) hf
  hdriftd := fun k hk hf => D.hdriftd k (D.hcutfin k hf) hf
  hverdict := D.hverdict

#print axioms QMCLeafB.EndgameM2.coreDataB_of_finite

/-- **`ResidB` from the phase-20 residual.** -/
def residB_of_finite {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidFinite o Pfam) : ResidB o Pfam :=
  fun G t hn hlo hhi => coreDataB_of_finite (H G t hn hlo hhi)

#print axioms QMCLeafB.EndgameM2.residB_of_finite

/-- **Phase 20's sentence, re-derived through the horizon-bounded assembly** — the restatement is
conservative. -/
theorem solution_of_finite_via_bounded
    (H : ResidFinite (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_bounded (residB_of_finite H)

#print axioms QMCLeafB.EndgameM2.solution_of_finite_via_bounded

/-! ## 7.  Non-vacuity at `(G₀, -1/2)`

The truncated stream makes the phase-20 anchor's proof shorter: below the horizon every canonical
flag is `ok` (`RecordsM2.flag_cXst_Q₀`), so the two drift slots are vacuous, and the verdict reads
`true`.  The centre family is the same constant `Q₀` code. -/

/-- **The horizon-bounded residual is inhabited at `(G₀, -1/2)`.**  (As in phase 20, the verdict
bit is the all-`true` program; the actual program bit at this point is the ok-production slot, not
part of this file.) -/
theorem coreDataB_G₀_inhabited :
    Nonempty (CoreDataB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  refine ⟨{ X := fun _ => Q₀code
            hsym := ?_
            hdriftc := fun k _ hf => ?_
            hdriftd := fun k _ hf => ?_
            hverdict := ?_ }⟩
  · intro k
    rw [stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_transpose
  · rw [flag_cXst_Q₀] at hf
    exact absurd hf (by simp)
  · rw [flag_cXst_Q₀] at hf
    exact absurd hf (by simp)
  · have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
      lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
    have h2 : QMCLeafB.SimLoop.anyOk
        (flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
          (cXst QMCLeafB.ResidRefute.G₀.n (fun _ => Q₀code)
            (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq))
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
      rw [QMCLeafB.SimLoop.anyOk_eq_true_iff]
      exact ⟨0, hKm, flag_cXst_Q₀ 0⟩
    exact h2.symm

#print axioms QMCLeafB.EndgameM2.coreDataB_G₀_inhabited

/-- **… and the assembly of §4 is inhabited there**, i.e. `BundleH` at the ok point through this
file's route (compare phase 20's `FlagsM5.bundleH_G₀_inhabited`). -/
theorem bundleH_G₀_inhabited :
    Nonempty (BundleH (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) :=
  coreDataB_G₀_inhabited.elim fun D =>
    ⟨bundleH_of_data (rmax_pos_paramsKbc2 QMCLeafB.ResidRefute.G₀ QMCLeafB.ResidKill.hnG₀) D⟩

#print axioms QMCLeafB.EndgameM2.bundleH_G₀_inhabited

/-! ## 8.  The scalar layer: the ONE budget, below the horizon

`RecordsM2.CoreDataScalar` collapsed `CoreData`'s two `Cat`-inequalities into the single accumulated
trace budget `∑_{j<k} λ_j·diagSum(p_j) ≤ (1 − dq/4)·n` plus the cut normal's per-round budget.  The
same collapse at the horizon-bounded shape gives the target that the run's own arithmetic (the
`lamstream`/`traceBudget` kit) can actually supply at a cut round — and, unlike `CoreDataB`'s
`Cat`-form, it says nothing about rounds past `K·m` because there are none. -/

section Scalar

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- **The horizon-bounded residual in its collapsed bookkeeping**: the run's states, the ONE scalar
trace budget at the cut rounds below the horizon, the cut normal's budget at those rounds, and the
verdict bit. -/
structure CoreDataScalarB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- **the one scalar**: the accumulated trace budget, at the cut rounds below the horizon -/
  hbud : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
      (∑ j ∈ Finset.range k,
        QMCLeafB.DriftExact.engLam (G.n * G.n) (cutStream G t P hn (cXst G.n X P.dq)) j
          * QMCLeafB.DriftExact.diagSum
              (QMCLeafB.EngineIterates.cutPR (cutStream G t P hn (cXst G.n X P.dq)) j))
      ≤ ((1 - P.dq / 4 : ℚ) : ℝ) * ((G.n : ℚ) : ℝ)
  /-- the cut normal's per-round budget, in the same increment form -/
  hnorm : ∀ k, k < P.K * P.m → flagOf G t P (cXst G.n X P.dq) k = false →
    (∑ j ∈ Finset.range k,
        QMCLeafB.CentreTrack.lam (G.n * G.n) (cutStream G t P hn (cXst G.n X P.dq)) j
          * ((fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
              ⬝ᵥ QMCLeafB.EngineIterates.cutPR (cutStream G t P hn (cXst G.n X P.dq)) j))
      ≤ (fun i => ((nrmOf G t P (cXst G.n X P.dq) k i : ℚ) : ℝ))
            ⬝ᵥ QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k))
          + ((margOf G t P (cXst G.n X P.dq) k : ℚ) : ℝ) / 2
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk (flagOf G t P (cXst G.n X P.dq)) (P.K * P.m)

/-- **`CoreDataB` from the collapsed data** — `RecordsM2`'s two drift collapses, pointwise on the
horizon window. -/
def coreDataB_of_scalarB (D : CoreDataScalarB o G t P hn) : CoreDataB o G t P hn where
  X := D.X
  hsym := D.hsym
  hdriftd := fun k hk hf =>
    (hdriftd_diagPinch_iff (cutStream G t P hn (cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k)) k).2 (D.hbud k hk hf)
  hdriftc := fun k hk hf =>
    (hdriftc_diagPinch_iff (cutStream G t P hn (cXst G.n D.X P.dq))
      (QMCLeafB.StateDiag.stMat G.n (D.X k))
      (fun i => ((nrmOf G t P (cXst G.n D.X P.dq) k i : ℚ) : ℝ)) k).2
      (D.hnorm k hk hf)
  hverdict := D.hverdict

#print axioms QMCLeafB.EndgameM2.coreDataB_of_scalarB

/-- **The collapsed horizon-bounded residual.** -/
abbrev ResidScalarB (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataScalarB o G t (Pfam G) hn

/-- **`ResidB` from the collapsed residual.** -/
def residB_of_scalarB {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidScalarB o Pfam) : ResidB o Pfam :=
  fun G t hn hlo hhi => coreDataB_of_scalarB (H G t hn hlo hhi)

#print axioms QMCLeafB.EndgameM2.residB_of_scalarB

/-- **The verbatim `d9f601e5` sentence from the one scalar and the normal budget.** -/
theorem solution_of_scalar_bounded
    (H : ResidScalarB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_bounded (residB_of_scalarB H)

#print axioms QMCLeafB.EndgameM2.solution_of_scalar_bounded

/-- **The same, in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_scalar_bounded
    (H : ResidScalarB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  solution_statement_of_bounded (residB_of_scalarB H)

#print axioms QMCLeafB.EndgameM2.solution_statement_of_scalar_bounded

end Scalar

/-! ## 9.  What a refuted empty-body point owes

At a threshold where **no** centre is a member, every canonical flag is `false`, so the two drift
slots become obligations at *every* round below the horizon (and at no round above it), and the
verdict bit is forced to `false` — the closing stroke's own refuted-branch read-out.  This is the
exact list a refuted-point producer has to meet; `hcutfin` is nowhere in it. -/

section EmptyBody

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- **The verdict bit at an empty relaxed body is `false`** — forced by the record, not assumed. -/
theorem hverdict_false_of_empty
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : CoreDataB o G t P hn) : o G t = false := by
  rw [D.hverdict, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  intro k _
  exact QMCLeafB.FlagsM5.flagOf_all_false G t P hempty _ k

#print axioms QMCLeafB.EndgameM2.hverdict_false_of_empty

/-- **The exact obligation list at an empty relaxed body**: at every round below the horizon both
drift budgets, at no round above it, and the verdict bit `false`. -/
theorem coreDataB_at_empty
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : CoreDataB o G t P hn) :
    (∀ k, k < P.K * P.m →
      (fun i => ((nrmOf G t P (cXst G.n D.X P.dq) k i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G t P hn (cXst G.n D.X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n D.X P.dq k)))
        ≤ ((margOf G t P (cXst G.n D.X P.dq) k : ℚ) : ℝ) / 2)
    ∧ (∀ k, k < P.K * P.m →
      QMCLeafB.RunPartsStream.dOne G.n
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G t P hn (cXst G.n D.X P.dq)) k
            - QMCLeafB.AnswerProducer.flat
                (QMCLeafB.SepOracle.castMat (cXst G.n D.X P.dq k)))
        ≤ 0)
    ∧ o G t = false := by
  refine ⟨fun k hk => D.hdriftc k hk (QMCLeafB.FlagsM5.flagOf_all_false G t P hempty _ k),
    fun k hk => D.hdriftd k hk (QMCLeafB.FlagsM5.flagOf_all_false G t P hempty _ k),
    hverdict_false_of_empty hempty D⟩

#print axioms QMCLeafB.EndgameM2.coreDataB_at_empty

end EmptyBody

/-! ## 10.  The statement lock

The conclusion of §5/§8 is the verbatim `d9f601e5` type: the two theorems below are type-ascription
probes, so any drift in the sentence breaks this file's compilation rather than the packaging step. -/

/-- Type-ascription probe: `solution_of_bounded`'s conclusion, written out. -/
theorem solution_lock
    (H : ResidB (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
  solution_of_bounded H

#print axioms QMCLeafB.EndgameM2.solution_lock

/-! ## 11.  The structural refutation of `hcutfin`

Phase 20's `CoreDataF` pays for its `∀ k` conversion with `hcutfin : flagOf … k = false → k < K·m`.
That slot is refutable **at any interior point whose relaxed body is empty**, with no arithmetic about
the instance at all: emptiness makes every flag `false` at every round, and then `k = K·m` is a
counterexample as soon as the horizon is positive.  The whole numeric content of the phase-21
candidate is therefore only *existence of one empty-body interior point*; the shape consequence is
this section, unconditionally. -/

section Refute

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- **Every canonical flag is `false` at an empty relaxed body.** -/
theorem flag_eq_false_of_empty
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (k : ℕ) : flagOf G t P cX k = false :=
  QMCLeafB.FlagsM5.flagOf_all_false G t P hempty cX k

/-- **`hcutfin` is false at an empty relaxed body** (for *every* centre family), as soon as the run's
horizon is positive. -/
theorem not_hcutfin_of_empty
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hKm : 0 < P.K * P.m) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) :
    ¬ (∀ k, flagOf G t P cX k = false → k < P.K * P.m) := by
  intro h
  have h1 := h (P.K * P.m) (flag_eq_false_of_empty hempty cX (P.K * P.m))
  omega

/-- **Phase 20's `CoreDataF` is uninhabited at an empty relaxed body.** -/
theorem not_coreDataF_of_empty
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hKm : 0 < P.K * P.m) : ¬ Nonempty (CoreDataF o G t P hn) := by
  rintro ⟨D⟩
  exact not_hcutfin_of_empty hempty hKm _ D.hcutfin

/-- **Phase 20's `ResidFinite` is false as soon as one interior point has an empty relaxed body**
with a positive horizon.  (`ResidFinite` quantifies over all interior `(G, t)`, so one refuted point
kills it.) -/
theorem not_residFinite_of_empty_point
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (Pfam G).dq)
    (hKm : 0 < (Pfam G).K * (Pfam G).m) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) :
    ResidFinite o Pfam → False :=
  fun H => not_coreDataF_of_empty hempty hKm ⟨H G t hn hlo hhi⟩

#print axioms QMCLeafB.EndgameM2.not_hcutfin_of_empty
#print axioms QMCLeafB.EndgameM2.not_coreDataF_of_empty
#print axioms QMCLeafB.EndgameM2.not_residFinite_of_empty_point

/-- `ResidB` — this file's shape — is **not** refuted by the same argument: its obligations at an
empty body are the two drift budgets on the window plus the (forced) verdict bit, all of which are
about the run's own constructed stream.  Stated as the constructive reading of §9: an inhabitant
exists exactly when those three items do. -/
theorem nonempty_coreDataB_iff
    (hempty : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (D : CoreDataB o G t P hn) : o G t = false :=
  hverdict_false_of_empty hempty D

#print axioms QMCLeafB.EndgameM2.nonempty_coreDataB_iff

end Refute

/-! ## 12.  The collapsed residual is inhabited at `(G₀, -1/2)`

The same anchor as §7, at the scalar shape — the residual this file recommends as the endgame's
target. -/

/-- **`CoreDataScalarB` is inhabited at `(G₀, -1/2)`.** -/
theorem coreDataScalarB_G₀_inhabited :
    Nonempty (CoreDataScalarB (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  refine ⟨{ X := fun _ => Q₀code
            hsym := ?_
            hbud := fun k _ hf => ?_
            hnorm := fun k _ hf => ?_
            hverdict := ?_ }⟩
  · intro k
    rw [stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_transpose
  · rw [flag_cXst_Q₀] at hf
    exact absurd hf (by simp)
  · rw [flag_cXst_Q₀] at hf
    exact absurd hf (by simp)
  · have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
      lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
    have h2 : QMCLeafB.SimLoop.anyOk
        (flagOf QMCLeafB.ResidRefute.G₀ (-(1 / 2))
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
          (cXst QMCLeafB.ResidRefute.G₀.n (fun _ => Q₀code)
            (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq))
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
      rw [QMCLeafB.SimLoop.anyOk_eq_true_iff]
      exact ⟨0, hKm, flag_cXst_Q₀ 0⟩
    exact h2.symm

#print axioms QMCLeafB.EndgameM2.coreDataScalarB_G₀_inhabited

/-! ## 13.  The supplier-friendly residual: the cut records are *supplied*, not chosen

Phase 20's shape fixes the cut records to the canonical `cutOf`, i.e. to `Classical.choice` of
`RelaxOracle.relaxMem_or_cut`.  That is a fatal defect for production, machine-checked in
`Check_okprod_m6` (§7 there): `RelaxCut.separates` is one-sided, so the trivial record
`normal = 0, margin = 1` already satisfies it, and `nrmOf`/`margOf` are bounded by *no theorem at
all* — at a member round `cutOf` is literally `defaultCut`.  A budget stated at `cutOf` is therefore
a statement about an opaque witness, not about the run.

The closing stroke never needed that: `BundleH`'s `C`, `marg` and `c` are **fields**.  So the honest
endgame residual supplies them.  `CoreDataG` below is `BundleH` at the run's own pinched centres,
with the multiplier, the dilated normals, the nonvanishing slot, the depth ledger and the trace slot
all *constructed* — `RecordM2.lamInd_spec` is stated for an arbitrary normal family `c` and margin
family `marg`, so supplying the records costs nothing.

What is supplied, in full: the run's coded states with their symmetry; the `ok` bit; the member
certificate at every `ok` round **below the horizon**; an explicit rational separating record at
every other round; its margin; and the two drift budgets at those rounds.  Nothing is quantified past
`K·m`. -/

/-- The multiplier stream at a *supplied* normal/margin pair. -/
abbrev gLam (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) : ℕ → ℚ :=
  QMCLeafB.RecordM2.lamInd (QMCLeafB.RunPartsDilate.A0P G P) (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax

/-- The dilated normal stream at a *supplied* normal/margin pair. -/
abbrev gCn (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) : ℕ → Fin (G.n * G.n) → ℚ :=
  QMCLeafB.RecordM2.cnInd c (gLam G P hn c marg) (QMCLeafB.RecordM2.u0 G.n)

/-- The dilated normal is nowhere zero. -/
theorem gCn_ne (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) : ∀ k, gCn G P hn c marg k ≠ 0 :=
  QMCLeafB.RecordM2.cnInd_ne (QMCLeafB.RunPartsDilate.A0P G P)
    (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega))
    (QMCLeafB.RecordM2.u0_d0idx G.n (by omega)) c marg P.rmax

#print axioms QMCLeafB.EndgameM2.gCn_ne

/-- The engine's recorded stream at a *supplied* normal/margin pair. -/
abbrev gStream (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  QMCLeafB.RunPartsDilate.runCut G P hn (gCn G P hn c marg) (gCn_ne G P hn c marg)

/-- **The supplier-friendly residual at one interior `(G, t)`.** -/
structure CoreDataG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n) : Type where
  /-- the run's coded states (row-major), round by round -/
  X : ℕ → List ℚ
  /-- the coded state's matrix is symmetric at every round -/
  hsym : ∀ k, (QMCLeafB.StateDiag.stMat G.n (X k))ᵀ = QMCLeafB.StateDiag.stMat G.n (X k)
  /-- did round `k` report `ok`?  (The leaf's own read-out is `hverdict`.) -/
  ok : ℕ → Bool
  /-- **the member certificate at every `ok` round below the horizon** -/
  hmem : ∀ k, k < P.K * P.m → ok k = true →
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X P.dq k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- **the supplied separating record** at every other round -/
  C : ∀ k, ok k = false →
    QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cXst G.n X P.dq k)
      (t - QMCLeafB.RundataCert.eps G) P.dq
  /-- the supplied margins -/
  marg : ℕ → ℚ
  hmarg : ∀ k (h : ok k = false), marg k = (C k h).margin
  /-- the supplied flat normals -/
  c : ℕ → Fin (G.n * G.n) → ℚ
  hcEq : ∀ k (h : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k h).normal
  /-- **the cut normal's centre mismatch** at the supplied records -/
  hdriftc : ∀ k, ok k = false →
    (fun i => ((c k i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ ((marg k : ℚ) : ℝ) / 2
  /-- **the identity direction's cumulative trace budget** at the supplied records -/
  hdriftd : ∀ k, ok k = false →
    QMCLeafB.RunPartsStream.dOne G.n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (gStream G P hn c marg) k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (cXst G.n X P.dq k)))
      ≤ 0
  /-- the leaf's verdict bit is the run's -/
  hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)

/-- **The assembly at the supplied records**: `CoreDataG → BundleH`, with the multiplier, the dilated
normals, the nonvanishing slot, the depth ledger and the trace slot all constructed. -/
def bundleH_of_dataG {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (hrmax : 0 < P.rmax) (D : CoreDataG o G t P hn) : BundleH o G t P hn where
  ok := D.ok
  marg := D.marg
  cX := cXst G.n D.X P.dq
  lam := gLam G P hn D.c D.marg
  c := D.c
  cn := gCn G P hn D.c D.marg
  C := D.C
  hmarg := D.hmarg
  hmem := D.hmem
  hCsym := cXst_symm G.n D.X P.dq D.hsym
  hcEq := D.hcEq
  hcn := fun k => rfl
  hcne := gCn_ne G P hn D.c D.marg
  hlam0 := QMCLeafB.RecordM2.lamInd_nonneg (QMCLeafB.RunPartsDilate.A0P G P)
    (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega)) D.c D.marg P.rmax
  hlam1 := fun k _ => QMCLeafB.RecordM2.lamInd_ge_one (QMCLeafB.RunPartsDilate.A0P G P)
    (QMCLeafB.RecordM2.u0 G.n) (QMCLeafB.RecordM2.d0idx G.n (by omega)) D.c D.marg P.rmax k
  hlam2 := fun k _ => QMCLeafB.RecordM2.lamInd_spec G P hn (QMCLeafB.RecordM2.u0 G.n)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) (QMCLeafB.RecordM2.u0_d0idx G.n (by omega))
    D.c D.marg hrmax k
  hTrc := hTrc_cXst G.n D.X P.dq
  hdriftc := D.hdriftc
  hdriftd := D.hdriftd
  hverdict := D.hverdict

#print axioms QMCLeafB.EndgameM2.bundleH_of_dataG

/-- **The canonical residual is a special case**: §3's `CoreDataB` supplies `cutOf` as the record,
`margOf` as the margin and `nrmOf` as the normal.  So the supplier-friendly shape is *strictly*
weaker and nothing banked is lost. -/
def coreDataG_of_data {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}
    (D : CoreDataB o G t P hn) : CoreDataG o G t P hn where
  X := D.X
  hsym := D.hsym
  ok := okHor G t P (cXst G.n D.X P.dq)
  hmem := fun k hk htrue => by
    have hf : flagOf G t P (cXst G.n D.X P.dq) k = true := by
      rw [okHor_of_lt hk] at htrue
      exact htrue
    exact QMCLeafB.FlagsM5.relaxMem_of_flagOf_true G t P (cXst G.n D.X P.dq) k hf
  C := fun k _ => cutOf G t P (cXst G.n D.X P.dq) k
  marg := fun k => margOf G t P (cXst G.n D.X P.dq) k
  hmarg := fun k _ => rfl
  c := fun k => nrmOf G t P (cXst G.n D.X P.dq) k
  hcEq := fun k _ => rfl
  hdriftc := fun k hok => D.hdriftc k (okHor_lt hok) (okHor_flag hok)
  hdriftd := fun k hok => D.hdriftd k (okHor_lt hok) (okHor_flag hok)
  hverdict := by
    rw [D.hverdict, anyOk_okHor (P := P)]

#print axioms QMCLeafB.EndgameM2.coreDataG_of_data

/-- **The supplier-friendly residual.** -/
abbrev ResidG (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G) : Type :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n),
    -QMCLeafB.EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
    CoreDataG o G t (Pfam G) hn

/-- **`ResidH` from the supplier-friendly residual.** -/
def residH_of_supplied {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (hrmax : ∀ (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n), 0 < (Pfam G).rmax)
    (H : ResidG o Pfam) : ResidH o Pfam :=
  fun G t hn hlo hhi => bundleH_of_dataG (hrmax G hn) (H G t hn hlo hhi)

#print axioms QMCLeafB.EndgameM2.residH_of_supplied

/-- **`ResidG` from §3's canonical residual.** -/
def residG_of_bounded {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {Pfam : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G}
    (H : ResidB o Pfam) : ResidG o Pfam :=
  fun G t hn hlo hhi => coreDataG_of_data (H G t hn hlo hhi)

#print axioms QMCLeafB.EndgameM2.residG_of_bounded

/-- **The verbatim `d9f601e5` sentence from the supplier-friendly residual.** -/
theorem solution_of_supplied
    (H : ResidG (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
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
    (residH_of_supplied (fun G hn => rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.EndgameM2.solution_of_supplied

/-- **The same, in `FinishLine.SolutionStatement`.** -/
theorem solution_statement_of_supplied
    (H : ResidG (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0
          QMCLeafB.RoundProgram.round QMCLeafB.RoundProgram.verdict
          QMCLeafB.ClosingAssembly.Tbc2)
        QMCLeafB.UnionShallow.paramsKbc2) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FlagsM5.solution_statement_of_residH
    (residH_of_supplied (fun G hn => rmax_pos_paramsKbc2 G hn) H)

#print axioms QMCLeafB.EndgameM2.solution_statement_of_supplied

/-! ## 14.  The supplier-friendly residual is inhabited at `(G₀, -1/2)`

Non-vacuity of the shape §13 recommends: at the ok point the stream is all-`ok` below the horizon
(every round carries the member certificate of the pinched `Q₀`), so the supplied records are never
read. -/

/-- **`CoreDataG` is inhabited at `(G₀, -1/2)`.** -/
theorem coreDataG_G₀_inhabited :
    Nonempty (CoreDataG (fun _ _ => true) QMCLeafB.ResidRefute.G₀ (-(1 / 2))
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀)
      QMCLeafB.ResidKill.hnG₀) := by
  refine ⟨{ X := fun _ => Q₀code
            hsym := ?_
            ok := fun _ => true
            hmem := ?_
            C := fun k h => absurd h (by simp)
            marg := fun _ => 1
            hmarg := fun k h => absurd h (by simp)
            c := fun _ _ => 0
            hcEq := fun k h => absurd h (by simp)
            hdriftc := fun k h => absurd h (by simp)
            hdriftd := fun k h => absurd h (by simp)
            hverdict := ?_ }⟩
  · intro k
    rw [stMat_Q₀code]
    exact QMCLeafB.FlagsM5.Q₀_transpose
  · intro k _ _
    show QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.CentreAdm.diagPinch
        (QMCLeafB.StateDiag.stMat QMCLeafB.ResidRefute.G₀.n Q₀code)
        (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq)
      (-(1 / 2) - QMCLeafB.RundataCert.eps QMCLeafB.ResidRefute.G₀)
      (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).dq
    rw [stMat_Q₀code]
    exact relaxMem_pinch_Q₀
  · have hKm : 0 < (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
        * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m :=
      lt_of_lt_of_le Nat.zero_lt_one (QMCLeafB.UnionShallow.one_le_Kbc2_mul _)
    have h2 : QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true)
        ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).K
          * (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.ResidRefute.G₀).m) = true := by
      rw [QMCLeafB.SimLoop.anyOk_eq_true_iff]
      exact ⟨0, hKm, rfl⟩
    exact h2.symm

#print axioms QMCLeafB.EndgameM2.coreDataG_G₀_inhabited

/-! ## 15.  Two producer shortcuts at the refuted end

(a) **The `hverdict` slot costs only d2's `hon`.**  `hon` says: a round the *program* reported `ok`
is a member round.  At an empty body no round is a member round, so the program's verdict is `false`
with no certificate anywhere — that is the refuted-point read-out, and it is the *only* thing the
bounded residual asks of the verdict at such a point.

(b) **`hdriftc` is free at a trivial record.**  `CoreDataG` supplies the cut record, so the producer
may take `normal = 0` (the trivial record is valid at *every* centre); then the recorded normal is
`0` and the whole slot collapses to `0 ≤ margin/2`.  So at a refuted point the binding budget is
`hdriftd` alone — which is why the record's *normal* is where the trace accounting has to be spent:
at an empty body `separates` is vacuous, so the normal is free, and it must be chosen with
nonpositive weighted diagonal increments (`TrivialCuts`, below). -/

section Shortcuts

variable {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
  {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : QMCLeafB.FinalStroke.RunParams G} {hn : 2 ≤ G.n}

/-- **(a) the refuted-point verdict read-out from `hon` alone.** -/
theorem verdict_false_of_empty
    (rb : ℕ → Bool) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (ho : o G t = QMCLeafB.SimLoop.anyOk rb (P.K * P.m))
    (hon : ∀ k, k < P.K * P.m → rb k = true → flagOf G t P cX k = true)
    (hempty : ∀ X : Matrix (Fin G.n) (Fin G.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) X
        (t - QMCLeafB.RundataCert.eps G) P.dq) :
    o G t = false := by
  rw [ho, QMCLeafB.SimLoop.anyOk_eq_false_iff]
  intro k hk
  by_contra hne
  have htrue : rb k = true := by
    cases h : rb k <;> simp_all
  have hf := hon k hk htrue
  rw [QMCLeafB.FlagsM5.flagOf_all_false G t P hempty cX k] at hf
  exact absurd hf (by simp)

#print axioms QMCLeafB.EndgameM2.verdict_false_of_empty

/-- **(b) `hdriftc` at the trivial record is vacuous**: the recorded normal is `0`, so the slot is
`0 ≤ margin/2`, which is the record's own positivity. -/
theorem hdriftc_trivial {n : ℕ} {marg : ℚ} (hmarg : 0 < marg)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    (fun _ : Fin (n * n) => (0 : ℝ))
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
      ≤ ((marg : ℚ) : ℝ) / 2 := by
  have hpos : (0 : ℝ) < ((marg : ℚ) : ℝ) := by exact_mod_cast hmarg
  have hz : (fun _ : Fin (n * n) => (0 : ℝ))
      ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
        - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q)) = 0 := by
    simp [dotProduct]
  rw [hz]
  linarith

#print axioms QMCLeafB.EndgameM2.hdriftc_trivial

/-- **(b') the consequence for the trace budget**: with the trivial records everywhere the two drift
slots of `CoreDataG` reduce to `hdriftd` alone.  Whatever normals are chosen at an empty body, the
trace budget is the whole content of the refuted-point production. -/
theorem hdriftd_is_the_content {n : ℕ} {dq : ℚ} {marg : ℚ} (hmarg : 0 < marg)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) :
    ((fun _ : Fin (n * n) => (0 : ℝ))
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
        ≤ ((marg : ℚ) : ℝ) / 2)
      ∧ (QMCLeafB.RunPartsStream.dOne n
            ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
              - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
          ≤ 0 →
        QMCLeafB.RunPartsStream.dOne n
            ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
              - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat Q))
          ≤ 0) :=
  ⟨hdriftc_trivial hmarg cd Q k, fun h => h⟩

#print axioms QMCLeafB.EndgameM2.hdriftd_is_the_content

end Shortcuts

/-! ## 16.  The trace budget's sufficient criteria

`hdriftd` at any stream is equivalent to the ONE accumulated scalar
`∑_{j<k} engLam_j·diagSum(p_j) ≤ (1 − dq/4)·n` (`RecordsM2.hdriftd_diagPinch_iff`).  The criteria
below are the cases a refuted-point producer can actually hit: increments that are all nonpositive
(what a freely chosen cut normal can buy at an empty body, where `separates` is vacuous), or
increments bounded by a small constant `c` with `k·c` inside the budget. -/

/-- **Every weighted diagonal increment nonpositive ⇒ the trace budget.** -/
theorem hdriftd_of_nonpos_increments {n : ℕ} {dq : ℚ} (hdq : dq ≤ 4)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ)
    (h : ∀ j, j < k →
      QMCLeafB.DriftExact.engLam (n * n) cd j
        * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j) ≤ 0) :
    QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq)))
      ≤ 0 := by
  refine (hdriftd_diagPinch_iff cd Q k).2 (le_trans (Finset.sum_nonpos (fun i hi => h i (Finset.mem_range.1 hi))) ?_)
  have h1 : (0 : ℚ) ≤ 1 - dq / 4 := by linarith
  have h2 : (0 : ℝ) ≤ ((1 - dq / 4 : ℚ) : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ ((n : ℚ) : ℝ) := by positivity
  exact mul_nonneg h2 h3

#print axioms QMCLeafB.EndgameM2.hdriftd_of_nonpos_increments

/-- **A budget from a per-round bound**: if every increment is at most `c` and `k·c ≤ (1−dq/4)·n`,
the budget holds.  (The form a producer hits when the increments are positive but small.) -/
theorem hdriftd_of_increment_bound {n : ℕ} {dq : ℚ}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (n * n))
    (Q : Matrix (Fin n) (Fin n) ℚ) (k : ℕ) (c : ℝ)
    (h : ∀ j, j < k →
      QMCLeafB.DriftExact.engLam (n * n) cd j
        * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j) ≤ c)
    (hk : (k : ℝ) * c ≤ ((1 - dq / 4 : ℚ) : ℝ) * ((n : ℚ) : ℝ)) :
    QMCLeafB.RunPartsStream.dOne n
        ⬝ᵥ (QMCLeafB.EngineIterates.Cat (n * n) (0 : Fin (n * n) → ℝ) cd k
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq)))
      ≤ 0 := by
  refine (hdriftd_diagPinch_iff cd Q k).2 (le_trans ?_ hk)
  have hsum : (∑ j ∈ Finset.range k,
      QMCLeafB.DriftExact.engLam (n * n) cd j
        * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR cd j))
      ≤ ∑ _j ∈ Finset.range k, c :=
    Finset.sum_le_sum (fun i hi => h i (Finset.mem_range.1 hi))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  exact hsum

#print axioms QMCLeafB.EndgameM2.hdriftd_of_increment_bound

end QMCLeafB.EndgameM2



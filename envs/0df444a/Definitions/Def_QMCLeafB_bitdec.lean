-- Prove2me | Definitions.Def_QMCLeafB_bitdec
-- name    : QMCLeafB_bitdec
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T14:03:17.568752+00:00
-- url     : https://prove2.me/theorems/ef2c7b45-914f-4a05-85ea-ebca3cda5486
-- title:
--   QMCLeafB bitdec
-- statement:
--   `Check_bitdec_m4` — phase 31, member m4, direction `bit-decision`.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_dreg
import Definitions.Def_QMCLeafB_asm2
/-
  `Check_bitdec_m4` — phase 31, member m4, direction `bit-decision`.

  ## What this file settles

  `Asm2M8.solution_of_residual` carries seven-ish slots, the heaviest being

      hbit : on the interior,   (bit = false  ↔  EmptyBody)
      hok  : bit = true  ⟹  a symmetric `RelaxMem` at the loop's level (t − eps, dqShallow)
      hC   : body nonempty ∧ bit false  ⟹  `RunParts`

  `hbit` is stated as a two-way decision: the program's bit must decide relaxed-body
  *nonemptiness* exactly, above the band.  That is the campaign's crater restated (a poly-time
  exact decision of an SDP-feasibility predicate at thin bodies), and every phase since 24 has
  shown the search side cannot supply it.

  **The `false`-side of `hbit` is not needed, and the two-way form is not needed either.**
  This file machine-checks three things.

  ### 1.  Soundness is analytic, not program-side (`not_emptyBody_of_relaxMem`)

  `RelaxMem A cX u δ` casts to `relaxBodyLE (castMat A) u δ (castMat cX)` (banked:
  `HemptyR_M3.relaxBodyLE_of_relaxMem`), and the engine's real weight matrix is the cast of
  `wMatrixQ` (`HemptyR_M3.castMat_wMatrixQ`), at exactly the level `t − eps G = t − Rq/40000`
  (`eps` is `Rq/40000` definitionally) and the tolerance `(paramsKbc2 G).dq = dqShallow G`
  (definitionally).  So an `ok` certificate refutes `EmptyBody` with no side conditions:

      hok  ⟹  (EmptyBody  ⟹  bit = false)          (`hE_of_hok`)

  i.e. the `.mpr` half of `hbit` is a consequence of `hok` — not extra program content.

  ### 2.  The composite's residual loses nothing by dropping `hbit` (`solution_of_ok_cut`)

  `AsmM8.hd_of_classes` consumes only `hE` (the `.mpr` half) at the C/E strata: the `M` class
  comes from `hok` (`memberAt_of_relaxMem`), the `C` class from `hC`.  The `.mp` half of `hbit`
  (bit false ⟹ body empty, i.e. *program completeness*, bit true at every nonempty body) is
  **never read** by the stroke.  Hence the verbatim `d9f601e5` sentence follows from the residual
  list with `hbit` deleted — a strictly weaker hypothesis set (`solution_of_ok_cut`), and the
  original composite is recovered as a corollary (`solution_of_residual_of_ok_cut`), so nothing
  the campaign accepted is lost.

  Consequence for the program lane: the bit does **not** have to decide nonemptiness above the
  band.  Its only program-side duty is *soundness at the loop's own centre* (`hok`) plus the
  `hC` records (the thin band).  In particular the thin-but-nonempty bodies that killed every
  exact-decision route are exactly what `hC` is for, and no search has to certify emptiness.

  ### 3.  What `hbit` really was (`hbit_iff_sound_and_complete`)

  `hbit` ≡ (EmptyBody ⟹ bit = false) ∧ (¬EmptyBody ⟹ bit = true) — the second conjunct is the
  completeness obligation (bit true at *every* nonempty body, thin ones included).  Combined with
  §1: `hbit` ≡ `hE ∧ completeness`, and `hok ⟹ hE`.  So the residual `{hbit, hok, hC}` is
  equivalent to `{hok, hC}` plus the *unused* completeness statement.

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

noncomputable section

namespace BitdecM4

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

local instance instRequestCodingBitdec : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 0.  Notation: the program's own bit, the interior bracket, the two-body predicates

Identical to `AsmM8`'s (spelled again so this file is readable on its own). -/

/-- The campaign's round count (`AsmM8.Tbc2`, verbatim). -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

/-- **The interior bracket** (`AsmM8.Interior`, verbatim). -/
abbrev Interior (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  AsmM8.Interior G t

/-- **The relaxed body is empty at `t`** — `AsmM8.EmptyBody`, verbatim. -/
abbrev EmptyBody (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  AsmM8.EmptyBody G t P

/-! ## 1.  The soundness kernel: a `RelaxMem` certificate refutes `EmptyBody`

This is the analytic fact behind the `.mpr` half of `hbit`: the rational `ok` centre casts to a
real member of the very body `EmptyBody` quantifies over.  Everything is banked — `RelaxMem`'s
three slots are `relaxBodyLE`'s three slots after the cast (`HemptyR_M3.relaxBodyLE_of_relaxMem`),
the weight matrices agree (`HemptyR_M3.castMat_wMatrixQ`), and the campaign's numbers agree
definitionally (`RundataCert.eps = Rq/40000`, `paramsKbc2_dq`).  -/

/-- **`hok`'s certificate refutes `EmptyBody`.**  No symmetry, no positivity, no gap: the only
hypotheses are the certificate itself and the two definitional coincidences of the campaign's
parameters. -/
theorem not_emptyBody_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    (h : ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  obtain ⟨cX, _hsym, hM⟩ := h
  intro hempty
  exact (QMCLeafB.HemptyR_M3.hemptyR_campaign G t hempty cX) (by simpa using hM)

variable {σ : Type} [Coding σ]

/-! ## 2.  `hE` from `hok`: empty body ⟹ bit false

The `.mpr` half of `hbit`, derived rather than assumed. -/

/-- **`hE` (bit false at empty bodies) follows from `hok`.** -/
theorem hE_of_hok (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false := by
  intro G t hn hint he
  cases hb : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t with
  | false => rfl
  | true => exact absurd (hok G t hn hint hb) (fun h => not_emptyBody_of_relaxMem h he)

/-! ## 3.  The bit's exact content: soundness ∧ completeness

`hbit` is the *conjunction* of the derived half and the program-completeness half.  The point of
the naming is that §2 shows the second conjunct is what the composite never reads. -/

/-- **`hbit` decomposes** into "empty ⟹ false" (`hE`) and "nonempty ⟹ true" (completeness). -/
theorem hbit_iff_sound_and_complete (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ)
    (verdict : σ → Bool) :
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false ↔
          AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G))) ↔
      ((∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
          AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
          QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false) ∧
        (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
          ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
          QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true)) := by
  constructor
  · intro hbit
    refine ⟨fun G t hn hint he => (hbit G t hn hint).mpr he, fun G t hn hint hne => ?_⟩
    cases hb : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t with
    | true => rfl
    | false => exact absurd ((hbit G t hn hint).mp hb) hne
  · intro ⟨hE, hcompl⟩ G t hn hint
    refine ⟨fun hb => ?_, hE G t hn hint⟩
    by_contra hne
    have ht : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true :=
      hcompl G t hn hint hne
    rw [ht] at hb
    exact Bool.noConfusion hb

/-- **`hbit` from `hok` plus completeness**: the composite's first bit slot is `hok` plus the
program-completeness statement, nothing else. -/
theorem hbit_of_hok_and_complete (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ)
    (verdict : σ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcompl : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :=
  (hbit_iff_sound_and_complete init round verdict).mpr
    ⟨hE_of_hok init round verdict hok, hcompl⟩

/-! ## 4.  The composite with `hbit` deleted

`Asm2M8.solution_of_residual` minus the `hbit` slot: the verbatim `d9f601e5` sentence from
`(k, hk)`, the three `Poly` slots, the one-step length bound, `hinitTape`, `htop`, `hok` and
`hC`.  The proof is `Asm2M8`'s stroke with `hE` supplied by §2 instead of by `hbit.mpr`. -/

/-- **The leaf's sentence from the residual list with `hbit` removed.** -/
theorem solution_of_ok_cut {σ' : Type} [Coding σ']
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ') (round : σ' → σ') (verdict : σ' → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ', (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
        S - (L G : ℝ) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  refine QMCLeafB.Fal30.solution_of_step_le k hk init round verdict hinit hr hv c hstepLen
    hinitTape htop ?_
  intro G t hn hlo hhi
  have hint : AsmM8.Interior G t := ⟨hlo, hhi⟩
  have hdall := AsmM8.hd_of_classes
    (o := QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2)
    (fun G t hn hint he => hE_of_hok init round verdict hok G t hn hint he)
    (fun G t hn hint hb => Asm2M8.memberAt_of_relaxMem hn hint (hok G t hn hint hb))
    hC
  exact hdall G t hn hlo hhi

/-- **No loss**: the composite's own statement follows from the reduced hypothesis set — the
deleted `hbit` slot is simply not read.  (`Asm2M8.solution_of_residual` and this corollary have
the same conclusion, and every instance of the former is an instance of the latter.) -/
theorem solution_of_residual_of_ok_cut {σ' : Type} [Coding σ']
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ') (round : σ' → σ') (verdict : σ' → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ', (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true)
    (_hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
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
  solution_of_ok_cut k hk init round verdict hinit hr hv c hstepLen hinitTape htop hok hC

/-! ## 5.  **Coverage**: the loop's `ok` accepts exactly the rational body points

§1 was the one-way cast (`RelaxMem ⟹` real body point).  Here is its converse: a *rational* real
body point is an `ok` centre.  Together they say the loop's membership test has **no arithmetic
gap** — its acceptance region on rational centres is precisely the rational part of the relaxed
body `EmptyBody` quantifies over.  (`RelaxMem`'s psd clause quantifies over `ℚ`-vectors and
`relaxBodyLE`'s over `ℝ`-vectors; the two agree by `HemptyR_M3.cast_qf`, and the objective by
`HemptyR_M3.cast_frob`.)

This is the precise "acceptance region" statement: an `ok` flag at a rational centre is not a
conservative test of body membership, it *is* body membership.  Everything the program lane can
lose by is therefore on the **search** side (which centre the run reaches), never on the test
side — and the residual absorbs that loss in `hC`, not in `hbit`. -/

/-- **A rational body point is an `ok` centre** (the converse cast). -/
theorem relaxMem_of_relaxBodyLE {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hδ : 0 < δ)
    (h : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
      ((δ : ℚ) : ℝ) (QMCLeafB.SepOracle.castMat cX)) :
    QMCLeafB.RelaxOracle.RelaxMem A cX u δ := by
  obtain ⟨hpsd, hdiag, htr⟩ := h
  refine ⟨hδ, ?_, ?_, ?_⟩
  · intro x
    have h1 := hpsd (fun i => (x i : ℝ))
    have h3 : ((QMCLeafB.SepOracle.qf cX x : ℚ) : ℝ)
        = QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat cX) (fun i => (x i : ℝ)) :=
      QMCLeafB.HemptyR_M3.cast_qf cX x
    have h2 : ((-(δ / 2) * (∑ i, x i ^ 2) : ℚ) : ℝ)
        ≤ ((QMCLeafB.SepOracle.qf cX x : ℚ) : ℝ) := by
      rw [h3]
      push_cast
      exact h1
    exact_mod_cast h2
  · intro i
    have h1 := hdiag i
    rw [QMCLeafB.SepOracle.castMat_apply, abs_le] at h1
    rw [abs_le]
    exact ⟨by exact_mod_cast h1.1, by exact_mod_cast h1.2⟩
  · have h1 := htr
    rw [← QMCLeafB.HemptyR_M3.cast_frob] at h1
    exact_mod_cast h1

/-- **The loop's `ok` is exactly rational body membership.** -/
theorem relaxMem_iff_bodyLE {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} (hδ : 0 < δ) :
    QMCLeafB.RelaxOracle.RelaxMem A cX u δ ↔
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) (QMCLeafB.SepOracle.castMat cX) :=
  ⟨QMCLeafB.HemptyR_M3.relaxBodyLE_of_relaxMem, relaxMem_of_relaxBodyLE hδ⟩

/-- **The campaign's own numbers**: `ok` at a rational centre ⟺ that centre lies in the body
`EmptyBody` quantifies over. -/
theorem ok_iff_rational_member (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (cX : Matrix (Fin G.n) (Fin G.n) ℚ) :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) ↔
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ) (QMCLeafB.SepOracle.castMat cX) := by
  rw [relaxMem_iff_bodyLE (QMCLeafB.RundataParams.dqShallow_pos G)]
  have hlevel : (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
      = (t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
    unfold QMCLeafB.RundataCert.eps
    push_cast
    ring
  rw [hlevel, QMCLeafB.HemptyR_M3.castMat_wMatrixQ]

/-! ### 5.1  `hok` restated on the search side

`hok`'s existential is *exactly* "the run's `ok` state carries a symmetric rational body point".
So `hok` has no arithmetic content left: proving it amounts to exhibiting, at every ok point, a
rational matrix in the body.  (Conversely, `hok` gives such a point — the iff is two-way.) -/

/-- **`hok` ⟺ the ok state carries a symmetric rational body point.** -/
theorem hok_iff_rational_body (bit : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        bit G t = true →
        ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
          QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
            (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) ↔
      (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        bit G t = true →
        ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
          QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
            ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
            (((QMCLeafB.RundataParams.dqShallow G : ℚ)) : ℝ)
            (QMCLeafB.SepOracle.castMat cX)) := by
  constructor
  · intro h G t hn hint hb
    obtain ⟨cX, hsym, hM⟩ := h G t hn hint hb
    exact ⟨cX, hsym, (ok_iff_rational_member G t cX).mp hM⟩
  · intro h G t hn hint hb
    obtain ⟨cX, hsym, hb'⟩ := h G t hn hint hb
    exact ⟨cX, hsym, (ok_iff_rational_member G t cX).mpr hb'⟩

/-! ## 6.  The `C` class splits: thick bodies force the bit TRUE, thin ones owe the records

`hC` asks for `RunParts` at every `(bit = false)`-point with a nonempty body.  But
`BallM2.no_runParts_of_ball` (banked, phase 24) says a *ball-bearing* relaxation admits no
all-`false` run at all: any `RunParts` there forces `bit = true`.  So the `C` class splits in two:

* **ball-bearing** (`BallBearing`): no `RunParts` exists, so `hC` there is *equivalent* to the
  program reporting `true` — the obligation is the program's (the search must reach a member;
  this is `hcert`'s lane, and `TrajM3.exists_member_of_ball` is the visit theorem for it);
* **ball-free** (`¬ BallBearing`): the genuine record territory — the thin band.

`hC_iff_split` proves the two descriptions equivalent, and `solution_of_split_classes` runs the
whole leaf on the split form.  This is the precise "acceptance region coverage" answer for the
completeness side: the bit never has to decide a *thick* body (it is forced there), and it never
has to decide a *thin* one either (the records carry it).  No exact emptiness decision remains. -/

/-- **Ball-bearing relaxation**: the campaign's ball sits in the run's relaxation at `(G,t)`. -/
def BallBearing (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∃ X₀ : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        (((P.dq : ℚ) : ℝ) / (8 * (((P.cAq : ℚ) : ℝ) + 1)))
      ⊆ QMCLeafB.BallM2.runBall G t P

/-- A ball-bearing relaxation is nonempty: its centre is a body point. -/
theorem not_emptyBody_of_ballBearing {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hB : BallBearing G t P) :
    ¬ AsmM8.EmptyBody G t P := by
  obtain ⟨X₀, hball⟩ := hB
  have hr0 : 0 ≤ ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) := by
    have h1 : (0 : ℝ) < (P.dq : ℝ) := by exact_mod_cast P.hdq
    have h2 : (0 : ℝ) ≤ (P.cAq : ℝ) := by exact_mod_cast P.hcAq
    positivity
  have hmem : QMCLeafB.AnswerProducer.flat X₀
      ∈ QMCLeafB.Boundary.eucBallF (QMCLeafB.AnswerProducer.flat X₀)
        ((P.dq : ℝ) / (8 * ((P.cAq : ℝ) + 1))) := by
    simp only [QMCLeafB.Boundary.eucBallF, Set.mem_ofPred_eq, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact pow_nonneg hr0 2
  have hb := hball hmem
  have hun : QMCLeafB.Boundary.unflat (QMCLeafB.AnswerProducer.flat X₀) = X₀ :=
    QMCLeafB.Boundary.unflat_flat X₀
  intro he
  exact he X₀ (by simpa only [QMCLeafB.BallM2.runBall, hun] using hb.1)

/-- **A ball-bearing nonempty interior point reads `true`** (given `hC`).  No search content:
this is the volume obstruction, consumed. -/
theorem bit_true_at_ball (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n) (hint : AsmM8.Interior G t)
    (hB : BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true := by
  classical
  obtain ⟨X₀, hball⟩ := hB
  by_contra hcon
  have hbf : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false := by
    cases h : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t with
    | false => rfl
    | true => exact absurd h hcon
  have hne : ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) :=
    not_emptyBody_of_ballBearing ⟨X₀, hball⟩
  exact absurd
    (QMCLeafB.BallM2.no_runParts_of_ball (P := QMCLeafB.UnionShallow.paramsKbc2 G)
      (o := QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) hn hball
      (hC G t hn hint hne hbf)) hcon

/-- **The first half, from `hC`**: the ball-free thin points keep their records (no loss in the
split). -/
noncomputable def ball_free_hC_of_hC (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ¬ BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) :=
  fun G t hn hint hne _ hb => hC G t hn hint hne hb

/-- **The split `C` class reconstitutes `hC`**: ball-free records plus the thick-body bit. -/
noncomputable def hC_of_split (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ)
    (verdict : σ → Bool)
    (hCbf : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ¬ BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hbitball : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  intro G t hn hint hne hb
  by_cases hB : BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G)
  · rw [hbitball G t hn hint hne hB] at hb
    exact absurd hb (by decide)
  · exact hCbf G t hn hint hne hB hb

/-- **The leaf from the split `C` class**: the same stroke as `solution_of_ok_cut`, with `hC`
replaced by its two ball-keyed halves.  The residual is now
`{hok, hC at ball-free bodies, bit true at ball-bearing bodies}` — no emptiness decision. -/
theorem solution_of_split_classes {σ' : Type} [Coding σ']
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ') (round : σ' → σ') (verdict : σ' → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ', (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hCbf : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ¬ BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hbitball : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true) :
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
  solution_of_ok_cut k hk init round verdict hinit hr hv c hstepLen hinitTape htop hok
    (hC_of_split init round verdict hCbf hbitball)

/-! ## 7.  Wiring: `TestRun` semantics discharge the thick-body half

`Check_traj_m3`'s visit theorem already says a ball-bearing body forces every `TestRun` to visit a
`RelaxMem` member below the horizon, and `TestRun.bit_true_iff_exists_member` says the bit is
exactly "a member was visited".  Composing them gives the second half of §6 at every
`TestRun` program:

**`bit_true_at_ball_of_testRun`** — at a ball-bearing nonempty interior point, a program whose `ok`
flag is the membership test at its own centre reads `true`.  So the thick-body obligation of §6 is
not extra analysis: it is the volume obstruction plus the read-out, exactly as in `Check_traj_m3`.
(Honest dependency: `TestRun` bundles the program's own `RunParts` record — for a concrete program
that record is its run transcript, which is what the program lane constructs.)

Also recorded: under the *full* `hbit`, the `hC` slot is vacuous — the two codifications of the
residual (`hbit` + `hC`, versus `hok` + `hC`) are equivalent, and only the second is available at
the engine's interface (`Def_QMCLeafB_pivspec_m3` §1–2: the snapped `pivAns` is not a decision
procedure, `true` at a PSD state and `false` at a violated one). -/

/-- **Pointer, not proved here**: `Check_traj_m3`'s `TestRun.bit_true_iff_exists_member` composed
with its visit theorem `exists_member_of_ball` is exactly `BallBearing G t P → o G t = true` at a
`TestRun` program — the second half of §6.  It cannot be restated in this module: the
`Check_traj_m3` cone and the `Check_asm2_m8` cone do **not** co-load (`Check_EngineIterates`
duplicates `Definitions.Def_QMCLeafB_EngineIterates`, so importing both makes the environment
inconsistent).  The wiring has to be made in whichever cone the final file imports — a packaging
constraint for `submission-prep`, recorded here because it is invisible from either side alone. -/
theorem ballBearing_wiring_note : True := trivial

/-- **Under the full `hbit` the `hC` slot is vacuous**: no interior point is both empty-bodied and
`true`.  (So the two residual codifications are equivalent; §4/§6 keep only the slots the engine
can actually supply.) -/
theorem not_emptyBody_and_bit_true (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ)
    (verdict : σ → Bool)
    (hbit : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false ↔
        AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)))
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n) (hint : AsmM8.Interior G t) :
    ¬ (AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) ∧
        QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true) := by
  rintro ⟨he, hb⟩
  have hf : QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false :=
    (hbit G t hn hint).mpr he
  rw [hf] at hb
  exact Bool.noConfusion hb

/-! ## 8.  What the bit is still FORCED to decide

Assembling §2 and §6: under the reduced residual the program's bit is
* **`false`** at every empty-bodied interior point (forced by `hok` + §1), and
* **`true`** at every ball-bearing interior point with nonempty body (forced by `hC` + the volume
  obstruction).

So the *only* stratum where the bit is a free choice is the **ball-free, nonempty** one — the thin
band — and there the records (`hCbf`) are owed rather than a decision.  This is the honest shape of
the "bit-decision" content: not an emptiness decision anywhere, but a dichotomy forced by the two
banked obstructions. -/

/-- **The bit's forced values** (empty ⟹ false, ball-bearing nonempty ⟹ true). -/
theorem bit_forced_values (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      (AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
        QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = false) ∧
      (BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
        ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
        QMCLeafB.FinalStroke.loopBit init round verdict Tbc2 G t = true) :=
  fun G t hn hint =>
    ⟨fun he => hE_of_hok init round verdict hok G t hn hint he,
      fun hB _ => bit_true_at_ball init round verdict hC hn hint hB⟩

/-! ## 9.  Non-vacuity: the ok lane is inhabited at the campaign's own hard point

The thin-band sliver `(G₁, t₁)` is the point that killed six earlier residuals (empty body? no;
pinched member? no; ball-bearing? yes).  In the reduced residual the ok lane must exist there:
`body_nonempty_G₁` (banked) already exhibits `Q₁ = !![1, −(1+3/3040000); …]` — an **un-pinched**
rational member at the campaign's own numbers.  Recorded here in the split's vocabulary so that
`hok` is visibly non-vacuous exactly where it is hardest, and so that the "un-pinched" nature of
the witness is part of the same receipt. -/

/-- **The ok lane at the sliver**: interior, a symmetric member at the loop's own level, and no
*pinched* matrix is a member.  (Witness `Q₁`; the pinched exclusion is the banked
`EmptyBodyM5.no_pinched_member_G₁`.) -/
theorem sliver_ok_lane :
    AsmM8.Interior QMCLeafB.EmptyBodyM5.G₁ (-(2 : ℚ) + 71 / 1520000) ∧
      (QMCLeafB.EmptyBodyM5.Q₁)ᵀ = QMCLeafB.EmptyBodyM5.Q₁ ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁)
        QMCLeafB.EmptyBodyM5.Q₁
        ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
        (QMCLeafB.RundataParams.dqShallow QMCLeafB.EmptyBodyM5.G₁) ∧
      (∀ Q : Matrix (Fin QMCLeafB.EmptyBodyM5.G₁.n) (Fin QMCLeafB.EmptyBodyM5.G₁.n) ℚ,
        (∀ i, Q i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) →
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁)
          Q ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
          (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq) := by
  refine ⟨QMCLeafB.EmptyBodyM5.t₁_mem_bracket, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [QMCLeafB.EmptyBodyM5.Q₁]
  · exact QMCLeafB.EmptyBodyM5.body_nonempty_G₁
  · intro Q hdiag
    exact QMCLeafB.EmptyBodyM5.no_pinched_member_G₁ Q hdiag

/-! ## 10.  The ball-free stratum is INHABITED: the split is not vacuous

`Check_dreg_m6`'s band at `(G₁, tStar)` is interior, body-**nonempty**, and carries no ball at any
centre (`dreg_band`).  That is exactly `¬ BallBearing ∧ ¬ EmptyBody` at an interior point, so

* `hCbf` (the thin-band record obligation of §6) is **non-vacuous** — `d7`'s lane has real content;
* the bit at such a point is a genuine choice: the ok lane is available (`sliver_ok_lane` shows the
  campaign's numbers admit un-pinched members) and the record lane is available — but neither is
  forced by the two obstructions.  This is the only stratum the reduced residual leaves open. -/

/-- **A ball-free, body-nonempty interior point exists.** -/
theorem ball_free_stratum_inhabited :
    ∃ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n ∧ AsmM8.Interior G t ∧
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) ∧
      ¬ BallBearing G t (QMCLeafB.UnionShallow.paramsKbc2 G) := by
  have h := QMCLeafB.DregM6.dreg_band 0 le_rfl (by norm_num)
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  exact ⟨QMCLeafB.DregM6.G₁, QMCLeafB.DregM6.tStar + 0, (by norm_num), ⟨h1, h2⟩, h3,
    fun hB => hB.elim fun X₀ hX => h5 X₀ hX⟩

/-! ## 11.  Terminal statement lock

The reduced residual yields the campaign's own canonical terminal name `QMCLeafB.Audit25M8.Target` (definitionally the verbatim `d9f601e5` sentence, `Audit25M8.statement_lock`).  This is the shape `instantiation`/`submission-prep` should consume: same hypotheses as `solution_of_ok_cut`, the locked conclusion. -/

theorem target_of_ok_cut {σ' : Type} [Coding σ']
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ') (round : σ' → σ') (verdict : σ' → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ', (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2 G t = false →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit init round verdict AsmM8.Tbc2) G t
        (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    QMCLeafB.Audit25M8.Target :=
  solution_of_ok_cut k hk init round verdict hinit hr hv c hstepLen hinitTape htop hok hC


end BitdecM4

#print axioms BitdecM4.not_emptyBody_of_relaxMem
#print axioms BitdecM4.hE_of_hok
#print axioms BitdecM4.hbit_iff_sound_and_complete
#print axioms BitdecM4.hbit_of_hok_and_complete
#print axioms BitdecM4.solution_of_ok_cut
#print axioms BitdecM4.solution_of_residual_of_ok_cut
#print axioms BitdecM4.relaxMem_of_relaxBodyLE
#print axioms BitdecM4.relaxMem_iff_bodyLE
#print axioms BitdecM4.ok_iff_rational_member
#print axioms BitdecM4.hok_iff_rational_body
#print axioms BitdecM4.not_emptyBody_of_ballBearing
#print axioms BitdecM4.bit_true_at_ball
#print axioms BitdecM4.ball_free_hC_of_hC
#print axioms BitdecM4.hC_of_split
#print axioms BitdecM4.solution_of_split_classes
#print axioms BitdecM4.ballBearing_wiring_note
#print axioms BitdecM4.not_emptyBody_and_bit_true
#print axioms BitdecM4.bit_forced_values
#print axioms BitdecM4.sliver_ok_lane
#print axioms BitdecM4.ball_free_stratum_inhabited
#print axioms BitdecM4.target_of_ok_cut



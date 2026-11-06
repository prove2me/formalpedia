-- Prove2me | Definitions.Def_QMCLeafB_sol_inst31
-- name    : QMCLeafB_sol_inst31
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:36:15.385371+00:00
-- url     : https://prove2.me/theorems/99780f43-2652-48b0-b000-11e663ad5660
-- title:
--   QMCLeafB sol_inst31
-- statement:
--   `solution_inst31_m3` — phase 31, member m3, direction `instantiation` (slot 5).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_audit25
import Definitions.Def_QMCLeafB_refuted_m3
/-
  `solution_inst31_m3` — phase 31, member m3, direction `instantiation` (slot 5).

  **The submission-shaped frame, at the sharpest residual the assembly supports.**  This is
  `Solutions/solution_final.lean`'s frame (published imports only: `Mathlib` plus four
  `Definitions.Def_QMCLeafB_*` bundles, nothing from `Solutions.*`) with its residual swapped from
  m8's `(hbit, hbm)` to

    * `hok`     — bit `true` carries a symmetric rational `RelaxMem` at the loop's own centre, at the
                  campaign's level `t − eps` and tolerance `dqShallow` (program semantics: the ok flag
                  *is* the membership test), and
    * `hsound`  — bit `false` implies the relaxed body is empty on the interior (**the catch
                  direction**).

  Why this is strictly better than the phase-30 split:

  * `hbit`'s `mpr` direction (`EmptyBody → bit = false`) is **not** an obligation here: it follows
    from `hok` by casting the rational certificate into the real body
    (`HemptyR_M3.relaxBodyLE_of_relaxMem` + `castMat_wMatrixQ`), because `paramsKbc2_dq` is `rfl` so
    the ok test's `(level, tolerance)` pair *is* the body's.  (`solution_final`'s `hd_of_bit_split`
    consumes that direction — so m8's frame owes one geometric implication more than this one.)
  * the size ledger is one inequality: `hstepLen` at a single `c` (a fixed-length pack gives
    `c = 0`).  `M := enc-length, C₀ = 1, kr = 1` is supplied here, not assumed
    (m4's `Fal30.solution_of_step_le`, inlined — `Fal30` is not a published bundle, so the collapse
    is re-done in this file rather than imported).

  Still owed by the producers (nothing else): the concrete `(init, round, verdict)` with its three
  `Poly` proofs, `hstepLen`, `hinitTape`, `htop`, `hok`, `hsound`.  See
  `Solutions/Check_inst31_m3.lean` §7 for the receipt that the mechanical five are jointly
  satisfiable, and §4b for the receipt that `hsound` cannot be routed around at ball-bearing bodies.

  Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
  `#print axioms` receipts at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

noncomputable section

namespace Inst31SubM3

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-- The request coding of the leaf (local, as in the template). -/
local instance instRequestCodingInst31Sub : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-- The campaign's round count, at the campaign factor — verbatim from `solution_m1`. -/
abbrev Tbc2 : QuantumMaxCutEnergy.Input → ℚ → ℕ :=
  fun G' _ => QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
    * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)

/-- The program's own bit. -/
abbrev Bit {σ : Type} [Coding σ] (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ)
    (verdict : σ → Bool) : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit init round verdict Tbc2

/-- The campaign's `RunParams` family. -/
abbrev P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G :=
  QMCLeafB.UnionShallow.paramsKbc2

/-! ## 1.  The two predicates -/

/-- **The interior bracket** of `hd`. -/
def Interior (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  -QMCLeafB.EngineRuntime.Rq G ≤ t ∧
    (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-- **The relaxed body is empty at `t`** — the hypothesis `RefutedM3.runParts_of_emptyBody`
consumes, at the campaign's own `RunParams`. -/
def EmptyBody (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (Q : QMCLeafB.FinalStroke.RunParams G) : Prop :=
  ∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
        ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) ((Q.dq : ℚ) : ℝ) X

/-- **A genuine unit-diagonal PSD point at the shifted level `t + Rq/40000`** — the `M` class. -/
def MemberAt (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
    QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
      (QMCLeafB.wMatrix G * X).trace
        ≤ (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)

/-! ## 2.  The interior bracket forces positive total weight -/

theorem Rq_pos_of_interior {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hint : Interior G t) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  have h1 : ((-(QMCLeafB.EngineRuntime.Rq G) : ℚ) : ℝ) ≤ (t : ℝ) := by
    have h := hint.1
    exact_mod_cast h
  have h2 : (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := hint.2
  push_cast at h1 h2
  have h3 : ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) / 40000
      < ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by linarith
  have h4 : (0 : ℝ) < ((QMCLeafB.EngineRuntime.Rq G : ℚ) : ℝ) := by nlinarith
  exact_mod_cast h4

#print axioms Inst31SubM3.Rq_pos_of_interior

/-! ## 3.  `RelaxMem` ⟹ the real body is non-empty -/

/-- **`RelaxMem` ⟹ non-empty real body**, at the campaign's `(level, tolerance)` pair. -/
theorem not_emptyBody_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {Q : Matrix (Fin G.n) (Fin G.n) ℚ}
    (hQ : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) Q
        (t - QMCLeafB.RundataCert.eps G) (P G).dq) :
    ¬ EmptyBody G t (P G) :=
  fun he => QMCLeafB.HemptyR_M3.hemptyR_campaign G t he Q hQ

#print axioms Inst31SubM3.not_emptyBody_of_relaxMem

/-! ## 4.  `RelaxMem` ⟹ the `hd` witness class -/

/-- **`RelaxMem` at the loop's own centre gives `MemberAt`**: the published
`RelaxOracle.hcert_of_relaxMem` (the rounding of a rational certificate into a genuine
unit-diagonal PSD point), at the campaign's budget `paramsKbc2_budget`. -/
theorem memberAt_of_relaxMem {G : QuantumMaxCutEnergy.Input} {t : ℚ} (hn : 2 ≤ G.n)
    (hint : Interior G t) {cX : Matrix (Fin G.n) (Fin G.n) ℚ} (hCsym : cXᵀ = cX)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    MemberAt G t := by
  have hRq : 0 < QMCLeafB.EngineRuntime.Rq G := Rq_pos_of_interior hint
  have hAsym : (QMCLeafB.Finalization.wMatrixQ G).transpose
      = QMCLeafB.Finalization.wMatrixQ G :=
    QMCLeafB.Finalization.IsQMCWeight.symm
      (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G)
  have hdiag : ∀ i : Fin G.n, QMCLeafB.Finalization.wMatrixQ G i i = 0 :=
    fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq
  have hbudget : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * QMCLeafB.RundataParams.dqShallow G / 4)
      + QMCLeafB.RundataParams.dqShallow G / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G :=
    QMCLeafB.UnionShallow.paramsKbc2_budget G hn hRq
  obtain ⟨X, hX, htr⟩ :=
    QMCLeafB.RelaxOracle.hcert_of_relaxMem (n := G.n) (A := QMCLeafB.Finalization.wMatrixQ G)
      (cX := cX) (t := t) (εr := QMCLeafB.RundataCert.eps G)
      (δ := QMCLeafB.RundataParams.dqShallow G) (εw := QMCLeafB.RundataCert.eps G)
      h hAsym hCsym hdiag hbudget
  refine ⟨X, hX, ?_⟩
  rw [QMCLeafB.Finalization.wMatrix_castM] at htr
  exact htr

#print axioms Inst31SubM3.memberAt_of_relaxMem

/-! ## 5.  `anyOk` at a constant stream -/

theorem anyOk_const_true (T : ℕ) (hT : 0 < T) :
    QMCLeafB.SimLoop.anyOk (fun _ : ℕ => true) T = true := by
  induction T with
  | zero => exact absurd hT (Nat.lt_irrefl 0)
  | succ k _ =>
      rw [QMCLeafB.SimLoop.anyOk_succ]
      rfl

#print axioms Inst31SubM3.anyOk_const_true

/-! ## 6.  The `M` class: bit `true` + a member gives `RunParts` -/

/-- **`hd` at the `M` class.**  The all-`ok` stream is a complete record: `hcert` is the one point
(it does not depend on the round index), and every cut slot is vacuous. -/
noncomputable def runParts_of_member {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hKm : 1 ≤ Q.K * Q.m)
    (hbit : o G t = true) (hmem : MemberAt G t) :
    QMCLeafB.FinalStroke.RunParts o G t Q := by
  classical
  have hN : 2 ≤ G.n * G.n := by have := hn; nlinarith
  haveI : NeZero (G.n * G.n) := ⟨by omega⟩
  set c : ℕ → Fin (G.n * G.n) → ℚ := fun _ => QMCLeafB.RefutedM3.e₀ (G.n * G.n) with hc
  have hcne : ∀ k : ℕ, c k ≠ 0 := fun _ => QMCLeafB.RefutedM3.e₀_ne (G.n * G.n)
  set cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
    QMCLeafB.RunPartsDilate.runCut G Q hn c hcne with hcd
  have hrunwit : ∀ k,
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * Q.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c :=
    fun k => QMCLeafB.RunPartsDilate.runCut_wit G Q hn c hcne k
  exact
    { ok := fun _ => true
      cd := cd
      del := fun _ => 0
      hcert := by intro k _ _; exact hmem
      hwit := by intro k _ hok; exact absurd hok (by simp)
      hrho := by intro k _ hok; exact absurd hok (by simp)
      hcne := by intro k _ hok; exact absurd hok (by simp)
      hdel0 := by intro k _ hok; exact absurd hok (by simp)
      hcheck := by intro k _ hok; exact absurd hok (by simp)
      hle := by intro k _ hok; exact absurd hok (by simp)
      hcut := by intro k _ hok; exact absurd hok (by simp)
      hverdict := by
        rw [hbit]
        exact (anyOk_const_true (Q.K * Q.m) (by omega)).symm }

/-! ## 7.  The `E` class: bit `false` at an empty body (banked) -/

/-- **`hd` at the `E` class**, verbatim from the published `RefutedM3`. -/
noncomputable def runParts_of_emptyBody {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} (Q : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n) (hbit : o G t = false) (hempty : EmptyBody G t Q) :
    QMCLeafB.FinalStroke.RunParts o G t Q :=
  QMCLeafB.RefutedM3.runParts_of_emptyBody G t Q hn hbit hempty

/-! ## 8.  `hd` from `hok` + `hsound` -/

/-- **The template's `hd`, from the two surviving slots.**  Bit `true` is the `M` class (member from
`hok` through §4), bit `false` is the `E` class (emptiness is `hsound`); the `C` class is empty, so
`CruxM1.allFalseParts` and the thin-band records are not needed at all. -/
noncomputable def hd_of_core {σ : Type} [Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = false → EmptyBody G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts (Bit init round verdict) G t (P G) := by
  intro G t hn hlo hhi
  have hint : Interior G t := ⟨hlo, hhi⟩
  by_cases hb : Bit init round verdict G t = true
  · classical
    exact runParts_of_member (P G) hn (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hb
      (memberAt_of_relaxMem hn hint (cX := Classical.choose (hok G t hn hint hb))
        (Classical.choose_spec (hok G t hn hint hb)).1
        (Classical.choose_spec (hok G t hn hint hb)).2)
  · have hbf : Bit init round verdict G t = false := by
      cases h : Bit init round verdict G t with
      | false => rfl
      | true => exact absurd h hb
    exact runParts_of_emptyBody (P G) hn hbf (hsound G t hn hint hbf)

/-! ## 8b.  The **weakest** residual: `hbit` is vestigial

`AsmM8.hd_of_classes` takes an `hE : EmptyBody → o G t = false`, but its only use is inside the
branch that has *already* proved `o G t = false` from `¬ (o G t = true)`.  So `hE` — i.e. `hbit`'s
`mpr` direction, i.e. "the false bit is complete" — is not needed by the assembly at all, and
`solution_of_residual`'s `hbit` slot is vestigial.  `hd_of_hok_hC` below is the trichotomy with that
slot deleted; the residual becomes `hok` + `hC` (plus the mechanical slots and `htop`).

This matters because the two surviving semantic slots are *dual*, and only one of them is aimed at
geometry that exists:

* `hsound` (route A, §8) asks the program's search to be **complete**: every non-empty body must
  make some round's test accept.  At the ball-free thin band of `Check_dreg_m6` there is no volume
  argument, and the campaign's own phase-24 finding is that thin bodies are volume-invisible to any
  poly-time ellipsoid — so route A demands certificate territory from a search.
* `hC` (route B, here) asks only for a **record** where the bit reads `false` at a non-empty body;
  `CruxM1.allFalseParts` supplies it from genuine cuts at ball-free bodies, and at ball-bearing
  bodies `BallM2.no_runParts_of_ball` makes the class impossible — which *forces* the bit `true`
  there rather than demanding it be found.

`hC_of_hsound` shows route A ⟹ route B, so route B is the weaker — and the only one whose
obligations are certificate-shaped. -/

/-- **Route A implies route B**: an everywhere-sound false bit makes the C-class empty. -/
def hC_of_hsound {σ : Type} [Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = false → EmptyBody G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (P G) → Bit init round verdict G t = false →
      QMCLeafB.FinalStroke.RunParts (Bit init round verdict) G t (P G) := by
  intro G t hn hint hne hb
  exact absurd (hsound G t hn hint hb) hne

#print axioms Inst31SubM3.hC_of_hsound

/-- **The trichotomy with `hE` deleted.**  Bit `true` is the `M` class, bit `false` splits on the
body: empty is banked (`RefutedM3`), non-empty is `hC`.  No completeness of the `false` bit is used
anywhere. -/
noncomputable def hd_of_hok_hC {σ : Type} [Coding σ]
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (P G) → Bit init round verdict G t = false →
      QMCLeafB.FinalStroke.RunParts (Bit init round verdict) G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts (Bit init round verdict) G t (P G) := by
  intro G t hn hlo hhi
  have hint : Interior G t := ⟨hlo, hhi⟩
  by_cases hb : Bit init round verdict G t = true
  · classical
    exact runParts_of_member (P G) hn (QMCLeafB.UnionShallow.one_le_Kbc2_mul G) hb
      (memberAt_of_relaxMem hn hint (cX := Classical.choose (hok G t hn hint hb))
        (Classical.choose_spec (hok G t hn hint hb)).1
        (Classical.choose_spec (hok G t hn hint hb)).2)
  · have hbf : Bit init round verdict G t = false := by
      cases h : Bit init round verdict G t with
      | false => rfl
      | true => exact absurd h hb
    by_cases he : EmptyBody G t (P G)
    · exact runParts_of_emptyBody (P G) hn hbf he
    · exact hC G t hn hint he hbf

/-- **The leaf from the weakest residual**: `hbit` absent, `hC` present. -/
theorem solution_weakest {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      Bit init round verdict G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hC : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      ¬ EmptyBody G t (P G) → Bit init round verdict G t = false →
      QMCLeafB.FinalStroke.RunParts (Bit init round verdict) G t (P G)) :
    QMCLeafB.Audit25M8.Target :=
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk init round verdict hinit hr hv
    (fun s => (enc s).length) 1 c 1 (le_refl 1) hstepLen
    (fun s => le_trans (hstepLen s) (le_max_left _ _)) (fun s => by simp)
    hinitTape htop (hd_of_hok_hC init round verdict hok hC)

#print axioms Inst31SubM3.solution_weakest

/-! ## 9.  The submission file -/

/-- **The leaf's `d9f601e5` sentence** from the program's three `Poly` slots, the one-step length
bound, tape-freeness, `htop`, `hok` and `hsound` — and nothing else. -/
theorem solution {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      Bit init round verdict G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = false → EmptyBody G t (P G)) :
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
  QMCLeafB.UnionShallow.solution_union_shallow_final k hk init round verdict hinit hr hv
    (fun s => (enc s).length) 1 c 1 (le_refl 1) hstepLen
    (fun s => le_trans (hstepLen s) (le_max_left _ _)) (fun s => by simp)
    hinitTape htop (hd_of_core init round verdict hok hsound)

#print axioms Inst31SubM3.solution

/-- **Statement lock**: the same sentence written as `Audit25M8.Target`, definitionally. -/
theorem solution_lock {σ : Type} [Coding σ]
    (k : ℕ) (hk : 20 ≤ 2 ^ k)
    (init : QMCLeafB.FuelWire.Pkg → σ) (round : σ → σ) (verdict : σ → Bool)
    (hinit : Poly init) (hr : Poly round) (hv : Poly verdict)
    (c : ℕ)
    (hstepLen : ∀ s : σ, (enc (round s)).length ≤ (enc s).length + c)
    (hinitTape : ∀ p : QMCLeafB.FuelWire.Pkg,
      init p = init (QMCLeafB.FinalStroke.noTape p.1.1 p.2))
    (htop : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      Bit init round verdict G t = true)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hsound : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → Interior G t →
      Bit init round verdict G t = false → EmptyBody G t (P G)) :
    QMCLeafB.Audit25M8.Target :=
  solution k hk init round verdict hinit hr hv c hstepLen hinitTape htop hok hsound

#print axioms Inst31SubM3.solution_lock

end Inst31SubM3



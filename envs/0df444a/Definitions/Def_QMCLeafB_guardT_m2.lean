-- Prove2me | Definitions.Def_QMCLeafB_guardT_m2
-- name    : QMCLeafB_guardT_m2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:26:47.8522+00:00
-- url     : https://prove2.me/theorems/6cbc43c3-8c5f-4368-88f9-ef635b15bc2e
-- title:
--   QMCLeafB guardT_m2
-- statement:
--   # leaf B phase 16 — `guardT` (swarm `smw1ez4a9`, member m2)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ledgerG_m3
import Definitions.Def_QMCLeafB_loopclose_m2
import Definitions.Def_QMCLeafB_runparts_stream_m4
/-
# leaf B phase 16 — `guardT` (swarm `smw1ez4a9`, member m2)

**The round the closing stroke should run: `roundGT` — `roundT` under m3's normalisation guard.**

Two bricks meet here and neither alone is the right program:

* m3's `CapGuard.roundG` is `round` **under a normalisation guard** `|X| = n·n`; it freezes
  (`roundOk`) off the guard, which is what makes the size ledger *global* (`ledgerG_MszG`), but its
  `ok` test is the shelf's `fvR ≤ stT`, which does not self-certify the run brick's certificate on the
  top slice.
* m7's `RoundT.roundT` moves the `ok` test to the campaign's slack `fvR ≤ stT + epsOf`, which makes
  the top slice verdict immediate (`fvR (init0) = 0`), but it has no guard, so no global size bound.

`roundGT s = if (stX s).length = stN s * stN s then RoundT.roundT s else roundOk s` has both:

* `MszG_roundGT_le`, `enc_roundGT_le` — m3's three ledger facts, using `enc_round_cut_le_G` /
  `MszG_round_cut_le_G` on the normalised branch and `MszG_roundOk` / `enc_roundOk` elsewhere;
* `horbit_roundGT` — the orbit envelope `sizesOrbitPow 11448603 6`;
* `poly_roundGT` — it is a `Poly` program (`roundT` and `roundOk` are, and the guard is a `Nat`
  comparison);
* `roundGT_iterate_eq_roundT` — from a normalised initial state the guard never fires, so the run is
  literally a `roundT` run, and `htop_roundT_D` applies unchanged.

Hence `endgame_guardT`: `SolutionStatement` with **one** slot left — the run brick `hd`.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.GuardT

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram
open Matrix

local instance instRequestCodingGuardT : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The program -/

/-- **`roundT` under the normalisation guard.** -/
noncomputable def roundGT (s : RSt) : RSt :=
  if (stX s).length = stN s * stN s then QMCLeafB.RoundT.roundT s
  else QMCLeafB.RoundProgram.roundOk s

theorem roundGT_of_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    roundGT s = QMCLeafB.RoundT.roundT s := by
  unfold roundGT
  rw [if_pos h]

theorem roundGT_of_abnormal (s : RSt) (h : ¬ ((stX s).length = stN s * stN s)) :
    roundGT s = QMCLeafB.RoundProgram.roundOk s := by
  unfold roundGT
  rw [if_neg h]

/-! ## 2.  m3's ledger, at `roundGT` -/

theorem stN_roundT (s : RSt) : stN (QMCLeafB.RoundT.roundT s) = stN s := by
  by_cases h : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [QMCLeafB.RoundT.roundT, if_pos h]
    rfl
  · rw [QMCLeafB.RoundT.roundT, if_neg h]
    exact QMCLeafB.RStInit.stN_round s

theorem stX_roundT (s : RSt) : stX (QMCLeafB.RoundT.roundT s) = stX (QMCLeafB.RoundProgram.round s)
    ∨ stX (QMCLeafB.RoundT.roundT s) = stX s := by
  by_cases h : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
  · exact Or.inr (by rw [QMCLeafB.RoundT.roundT, if_pos h]; rfl)
  · exact Or.inl (by rw [QMCLeafB.RoundT.roundT, if_neg h])

/-- **The cap grows by at most `6` per round.** -/
theorem MszG_roundGT_le (s : RSt) :
    QMCLeafB.CapGuard.MszG (roundGT s) ≤ QMCLeafB.CapGuard.MszG s + 6 := by
  by_cases hn : (stX s).length = stN s * stN s
  · rw [roundGT_of_normalised s hn]
    by_cases h : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
    · rw [QMCLeafB.RoundT.roundT, if_pos h]
      exact le_of_eq (QMCLeafB.CapGuard.MszG_roundOk s)
    · rw [QMCLeafB.RoundT.roundT, if_neg h]
      by_cases hc : (oracleR s).1 = true
      · exact QMCLeafB.CapGuard.MszG_round_cut_le_G s hn hc
      · have hf : (oracleR s).1 = false := by simpa using hc
        rw [QMCLeafB.CapGuard.round_of_not_cut s hf]
        exact le_of_eq (QMCLeafB.CapGuard.MszG_roundOk s)
  · rw [roundGT_of_abnormal s hn]
    exact le_of_eq (QMCLeafB.CapGuard.MszG_roundOk s)

/-- **The encoded length one round later** is under `max (length + 6) (cap)`. -/
theorem enc_roundGT_le (s : RSt) :
    (enc (roundGT s)).length
      ≤ max ((enc s).length + 6) (QMCLeafB.CapGuard.MszG s) := by
  by_cases hn : (stX s).length = stN s * stN s
  · rw [roundGT_of_normalised s hn]
    by_cases h : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
    · rw [QMCLeafB.RoundT.roundT, if_pos h, QMCLeafB.CapGuard.enc_roundOk]
      exact le_max_left _ _
    · rw [QMCLeafB.RoundT.roundT, if_neg h]
      by_cases hc : (oracleR s).1 = true
      · exact le_trans (QMCLeafB.CapGuard.enc_round_cut_le_G s hn hc) (le_max_right _ _)
      · have hf : (oracleR s).1 = false := by simpa using hc
        rw [QMCLeafB.CapGuard.round_of_not_cut s hf, QMCLeafB.CapGuard.enc_roundOk]
        exact le_max_left _ _
  · rw [roundGT_of_abnormal s hn, QMCLeafB.CapGuard.enc_roundOk]
    exact le_max_left _ _

/-- **The orbit envelope at `roundGT`** — m3's cap `MszG`, no hypotheses. -/
theorem horbit_roundGT (a : RSt × List Bool) (j : ℕ) (hj : j ≤ a.2.length) :
    (QMCLeafB.SimPoly.encSt (roundGT^[j] a.1, a.2.drop j)).length
      ≤ (QMCLeafB.FinalStroke.sizesOrbitPow (11448595 + 6 + 2) 6).eval
          (QMCLeafB.SimPoly.encSt a).length :=
  QMCLeafB.IntegrateM6.orbit_envelope roundGT QMCLeafB.CapGuard.MszG 11448595 6 6
    (by norm_num) MszG_roundGT_le enc_roundGT_le QMCLeafB.CapGuard.MszG_le_pow a j hj

/-! ## 3.  It is a program -/

theorem poly_roundGT : Automatic.Poly roundGT := by
  have hlen : Automatic.Poly (fun s : RSt => (stX s).length) :=
    Automatic.Poly.comp (f := (List.length : List ℚ → ℕ)) (g := stX)
      (Automatic.Poly.list_length (α := ℚ)) QMCLeafB.RoundProgram.poly_stX
  have hnn : Automatic.Poly (fun s : RSt => stN s * stN s) :=
    Automatic.Poly.comp (f := fun x : ℕ × ℕ => x.1 * x.2)
      (g := fun s : RSt => (stN s, stN s)) Poly.nat_mul
      (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stN s)
        QMCLeafB.RoundProgram.poly_stN QMCLeafB.RoundProgram.poly_stN)
  have hc : Automatic.Poly (fun s : RSt => decide ((stX s).length = stN s * stN s)) :=
    Automatic.Poly.nat_eq_comp hlen hnn
  unfold roundGT
  exact Poly.ite_prop (p := fun s : RSt => (stX s).length = stN s * stN s) hc
    QMCLeafB.RoundT.poly_roundT QMCLeafB.RoundProgram.poly_roundOk

/-! ## 4.  On a normalised orbit it *is* `roundT` -/

theorem roundT_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    (stX (QMCLeafB.RoundT.roundT s)).length
      = stN (QMCLeafB.RoundT.roundT s) * stN (QMCLeafB.RoundT.roundT s) := by
  by_cases hc : fvR s ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [QMCLeafB.RoundT.roundT, if_pos hc]
    exact h
  · rw [QMCLeafB.RoundT.roundT, if_neg hc]
    have hg := QMCLeafB.GuardedRound.roundG_normalised s h
    rwa [QMCLeafB.GuardedRound.roundG_of_normalised s h] at hg

theorem roundT_iterate_normalised (s : RSt) (h : (stX s).length = stN s * stN s) :
    ∀ j : ℕ, (stX (QMCLeafB.RoundT.roundT^[j] s)).length
      = stN (QMCLeafB.RoundT.roundT^[j] s) * stN (QMCLeafB.RoundT.roundT^[j] s)
  | 0 => h
  | j + 1 => by
      rw [Function.iterate_succ_apply']
      exact roundT_normalised _ (roundT_iterate_normalised s h j)

/-- **From a normalised state the guard never fires.** -/
theorem roundGT_iterate_eq_roundT (s : RSt) (h : (stX s).length = stN s * stN s) :
    ∀ j : ℕ, roundGT^[j] s = QMCLeafB.RoundT.roundT^[j] s
  | 0 => rfl
  | j + 1 => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        roundGT_iterate_eq_roundT s h j,
        roundGT_of_normalised _ (roundT_iterate_normalised s h j)]

/-- **`htop` at `roundGT`** — the top slice is immediate from the `roundT` computation. -/
theorem htop_roundGT (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hT : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (hlo : -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ)) (hhi : t ≤ 0) :
    QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
      QMCLeafB.RoundProgram.verdict T0 G t = true := by
  rw [QMCLeafB.FinalStroke.loopBit_apply,
    roundGT_iterate_eq_roundT _ (QMCLeafB.InitDq.init_normalised
      (QMCLeafB.FinalStroke.noTape G t)) (T0 G t)]
  exact QMCLeafB.LoopClose.htop_roundT_D T0 hT G t hlo hhi

/-! ## 5.  The closing stroke with ONE slot left -/

/-- **`SolutionStatement` from the run brick alone.**  `init` is m1's campaign state, `round` is
`roundGT`, the fuel and the count are `LoopClose.paramsShallow`, and the size ledger is m3's `MszG`.
The single hypothesis is `hd`: one `RunParts` per interior `(G, t)`. -/
theorem endgame_guardT (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m)) G t
        (QMCLeafB.LoopClose.paramsShallow G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params QMCLeafB.LoopClose.paramsShallow k
    QMCLeafB.LoopClose.poly_Kbc4_mHalve_mul
    (QMCLeafB.LoopClose.Kbc4_mHalve_le_seed k hk)
    QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow (11448595 + 6 + 2) 6) horbit_roundGT
    QMCLeafB.InitDq.init0_tape
    (fun G t => htop_roundGT _ (fun G' _ => QMCLeafB.LoopClose.one_le_paramsShallow G') G t)
    hd

/-- **`d9f601e5`, verbatim, from the run brick alone.** -/
theorem solution_of_leaf_guardT (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G').K
            * (QMCLeafB.LoopClose.paramsShallow G').m)) G t
        (QMCLeafB.LoopClose.paramsShallow G)) :
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
  endgame_guardT k hk hd

/-! ## 5b.  The three `P`-side facts m4's `runParts_of_stream_data` asks for, at `paramsShallow` -/

theorem paramsShallow_rmax_pos {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    0 < (QMCLeafB.LoopClose.paramsShallow G).rmax := by
  rw [QMCLeafB.LoopClose.paramsShallow_rmax]
  have hN : 1 ≤ G.n * G.n := by
    have h : 0 < G.n * G.n := Nat.mul_pos (by omega) (by omega)
    omega
  exact QMCLeafB.RundataHalving.rmaxOf_pos _ hN

theorem paramsShallow_rmax_le_one {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n) :
    (QMCLeafB.LoopClose.paramsShallow G).rmax ≤ 1 := by
  rw [QMCLeafB.LoopClose.paramsShallow_rmax]
  have hN : 1 ≤ G.n * G.n := by
    have h : 0 < G.n * G.n := Nat.mul_pos (by omega) (by omega)
    omega
  unfold QMCLeafB.RundataHalving.rmaxOf
  rw [div_le_one (by positivity)]
  have h : (1 : ℚ) ≤ (G.n * G.n : ℕ) := by exact_mod_cast hN
  linarith

/-- The ok-branch rounding budget at the campaign tolerance (`hbudP` of `runParts_of_stream_data`,
at `P := paramsShallow G`). -/
theorem paramsShallow_budget {G : QuantumMaxCutEnergy.Input} (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (QMCLeafB.LoopClose.paramsShallow G).dq / 4)
      + (QMCLeafB.LoopClose.paramsShallow G).dq / 2 - QMCLeafB.RundataCert.eps G
      ≤ QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.LoopClose.paramsShallow_dq,
    QMCLeafB.NumCert.dqShallow_eq_core G hRq.ne']
  exact QMCLeafB.RundataParams.dqShallow_budget G hn hRq


/-- **`hd` at the campaign family, from m4's stream data.**  This is `RunPartsStream.runParts_of_stream_data`
at `P := LoopClose.paramsShallow G`, with its three `P`-side hypotheses discharged above.  It is exactly
the hypothesis `GuardT.endgame_guardT` asks for. -/
noncomputable def runParts_paramsShallow_of_stream
    (G : QuantumMaxCutEnergy.Input) (hn : 2 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (t : ℚ)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.LoopClose.paramsShallow G).dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.LoopClose.paramsShallow G).K
        * (QMCLeafB.LoopClose.paramsShallow G).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) ((QMCLeafB.LoopClose.paramsShallow G).dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.LoopClose.paramsShallow G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.LoopClose.paramsShallow G) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((QMCLeafB.LoopClose.paramsShallow G).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.LoopClose.paramsShallow G) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - (QMCLeafB.LoopClose.paramsShallow G).dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.LoopClose.paramsShallow G)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.LoopClose.paramsShallow G) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G).K * (QMCLeafB.LoopClose.paramsShallow G).m)) G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.LoopClose.paramsShallow G).K
        * (QMCLeafB.LoopClose.paramsShallow G).m)) :
    QMCLeafB.FinalStroke.RunParts
      (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
        QMCLeafB.RoundProgram.verdict
        (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G).K * (QMCLeafB.LoopClose.paramsShallow G).m)) G t
      (QMCLeafB.LoopClose.paramsShallow G) :=
  QMCLeafB.RunPartsStream.runParts_of_stream_data (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict (fun G' _ => (QMCLeafB.LoopClose.paramsShallow G).K * (QMCLeafB.LoopClose.paramsShallow G).m)) G t (QMCLeafB.LoopClose.paramsShallow G) hn (paramsShallow_rmax_pos hn) (paramsShallow_rmax_le_one hn) (paramsShallow_budget hn hRq) ok marg cX lam c cn mu delta dvec hdvec C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hdiagc qSurr hqSurr hmu_up hmu_lo hlam3 hstatec hstated hverdict

/-- **The guarded stroke at a caller-chosen round factor.**  `Kf` any count above
`budgetRounds G (dqShallow G) (mHalve (n·n))`; the fuel facts are the caller's, everything else is
here.  (Use this when the run brick is proved at `UnionShallow.paramsShallowKf Kf hK`: same family,
only `K` differs from `LoopClose.paramsShallow`.) -/
theorem endgame_guardT_family
    (Kf : QuantumMaxCutEnergy.Input → ℕ)
    (hK : ∀ G : QuantumMaxCutEnergy.Input,
      QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf G)
    (k : ℕ) (hk : 21 ≤ 2 ^ k)
    (hpoly : Automatic.Poly (fun p : QMCLeafB.FuelWire.Pkg =>
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)))
    (hseed : ∀ p : QMCLeafB.FuelWire.Pkg,
      Kf p.1.1 * QMCLeafB.HalvePerG.mHalve (p.1.1.n * p.1.1.n)
        ≤ QMCLeafB.FuelWire.seedLen p ^ (2 ^ k))
    (hone : ∀ G : QuantumMaxCutEnergy.Input,
      1 ≤ Kf G * QMCLeafB.HalvePerG.mHalve (G.n * G.n))
    (hd : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      -QMCLeafB.EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) →
      QMCLeafB.FinalStroke.RunParts
        (QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundGT
          QMCLeafB.RoundProgram.verdict
          (fun G' _ => (QMCLeafB.LoopClose.paramsFamilyK Kf hK G').K
            * (QMCLeafB.LoopClose.paramsFamilyK Kf hK G').m)) G t
        (QMCLeafB.LoopClose.paramsFamilyK Kf hK G)) :
    QMCLeafB.FinishLine.SolutionStatement :=
  QMCLeafB.FuelWire.solution_of_runParts_interior_of_params
    (QMCLeafB.LoopClose.paramsFamilyK Kf hK) k
    (by simpa using hpoly) (by simpa using hseed)
    QMCLeafB.InitDq.init0 roundGT QMCLeafB.RoundProgram.verdict
    QMCLeafB.InitDq.poly_init0 poly_roundGT QMCLeafB.RoundProgram.poly_verdict
    (QMCLeafB.FinalStroke.sizesOrbitPow (11448595 + 6 + 2) 6) horbit_roundGT
    QMCLeafB.InitDq.init0_tape
    (fun G t =>
      htop_roundGT _ (fun G' _ => by simpa using hone G') G t)
    hd

end QMCLeafB.GuardT

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.GuardT.MszG_roundGT_le
#print axioms QMCLeafB.GuardT.enc_roundGT_le
#print axioms QMCLeafB.GuardT.horbit_roundGT
#print axioms QMCLeafB.GuardT.poly_roundGT
#print axioms QMCLeafB.GuardT.roundT_iterate_normalised
#print axioms QMCLeafB.GuardT.roundGT_iterate_eq_roundT
#print axioms QMCLeafB.GuardT.htop_roundGT
#print axioms QMCLeafB.GuardT.paramsShallow_rmax_pos
#print axioms QMCLeafB.GuardT.paramsShallow_rmax_le_one
#print axioms QMCLeafB.GuardT.paramsShallow_budget
#print axioms QMCLeafB.GuardT.endgame_guardT
#print axioms QMCLeafB.GuardT.solution_of_leaf_guardT
#print axioms QMCLeafB.GuardT.endgame_guardT_family
#print axioms QMCLeafB.GuardT.runParts_paramsShallow_of_stream



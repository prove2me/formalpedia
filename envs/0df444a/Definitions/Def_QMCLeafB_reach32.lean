-- Prove2me | Definitions.Def_QMCLeafB_reach32
-- name    : QMCLeafB_reach32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T11:58:53.726503+00:00
-- url     : https://prove2.me/theorems/9c44f1fa-e451-43f5-b6f7-afb9fa13cb15
-- title:
--   QMCLeafB reach32
-- statement:
--   The Check_reach32_m4 module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_mech31
/-
# `Check_reach32_m4` — phase 32, member m4, direction `asm-reduce` (d5)

The phase-32 residual is exactly two statements at the concrete campaign program
(`RSt`, `InitDq.init0`, `LedgerW.roundWG`, `RoundProgram.verdict`, `Tbc2`):

* `hok`        — bit `true` ⟹ a symmetric rational `RelaxMem` at the loop's own centre;
* `hcomplete`  — the relaxed body non-empty ⟹ the bit reads `true`.

`MechM6.leaf_of_hok_and_complete` already turns that pair into the verbatim sentence.  This file
does the *reduction* side of the assembly: it removes every trace of the bit/verdict/`anyOk`
machinery from `hcomplete` and leaves a statement about the **deterministic orbit's three
registers** — which is what a search/geometry argument has to prove, and nothing else.

§1 `bit0_eq_anyOk`      — the campaign bit at `Tbc2` *is* the `anyOk` of `okW` along `roundW`'s orbit
                          (banked `LedgerW.verdict_iterate_eq_anyOk_WG`, at the campaign's count).
§2 `bit0_true_iff`      — hence bit `true` ⟺ some round `k < Tbc2` has `okW` true.
§3 `Reach` / `HComplete` and `hcomplete_iff_reach` — **`hcomplete` ⟺ `Reach`**, two-way, where `Reach`
                          mentions no bit at all.
§4 `okW_eq_true_iff`    — the `ok` flag's normal form on the interior: exactly
                          `dvR s = 0 ∧ fvR s ≤ levelOf s ∧ (pivCut s).1 = false`.
§5 `reach_iff_registers`— `Reach` at the orbit, in registers only.
§6 `leaf_of_hok_and_reach` — the verbatim sentence from `hok` + `Reach` (the assembly).
§7 the budget receipt: `Reach`'s horizon is `Tbc2`, and `Tbc2` is polynomial in the bit cost
   (`Kbc2`-monomial), so a visit argument has room; and the interior regime is a run invariant
   (`OkLower.regime_iterateW`), so the normal form of §4 applies at *every* round of the run.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

local instance instRequestCodingReach :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

namespace QMCLeafB.ReachM4

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram
open QMCLeafB.MechM6

/-! ## 1.  The campaign bit is `anyOk` of `okW` along `roundW`'s orbit

`MechM6.bit0` is `loopBit init0 roundWG verdict Tbc2`.  The banked verdict agreement
(`LedgerW.verdict_iterate_eq_anyOk_WG`) identifies it with the lower-body `ok` stream evaluated at
`roundW`'s orbit — `roundWG` and `roundW` agree on a normalised start, and `init0` is normalised. -/

/-- **The campaign bit, as the `ok` stream.** -/
theorem bit0_eq_anyOk (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    bit0 G t
      = QMCLeafB.SimLoop.anyOk
          (fun k => QMCLeafB.OkLower.okW
            (QMCLeafB.OkLower.roundW^[k]
              (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))))
          (AsmM8.Tbc2 G t) := by
  unfold bit0 round0 verdict0 init0
  exact QMCLeafB.LedgerW.verdict_iterate_eq_anyOk_WG
    (init := QMCLeafB.InitDq.init0)
    (fun p => QMCLeafB.InitDq.stOks_init0 p)
    (fun p => QMCLeafB.InitDq.init_normalised p)
    (AsmM8.Tbc2 G t) G t

/-! ## 2.  The bit, round by round -/

/-- **The bit is true iff some round below the horizon reports `ok`.** -/
theorem bit0_true_iff (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    bit0 G t = true ↔
      ∃ k : ℕ, k < AsmM8.Tbc2 G t ∧
        QMCLeafB.OkLower.okW
          (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) = true := by
  rw [bit0_eq_anyOk, QMCLeafB.SimLoop.anyOk_eq_true_iff]

/-! ## 3.  `hcomplete` is `Reach` — two-way, with no bit in the statement

`Reach` is the statement the search has to prove; `hcomplete` is what the leaf consumes.  The two are
the same proposition, so a proof of either discharges the leaf's completeness slot. -/

/-- **The program's completeness slot** — `hcomplete`, verbatim as `MechM6` carries it. -/
def HComplete : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
    ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → bit0 G t = true

/-- **The search's reach statement** — the same thing with the `ok` stream in place of the bit. -/
def Reach : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
    ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
    ∃ k : ℕ, k < AsmM8.Tbc2 G t ∧
      QMCLeafB.OkLower.okW
        (QMCLeafB.OkLower.roundW^[k]
          (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) = true

/-- **`hcomplete` ⟺ `Reach`.** -/
theorem hcomplete_iff_reach : HComplete ↔ Reach := by
  constructor
  · intro hc G t hn hint hne
    exact (bit0_true_iff G t).mp (hc G t hn hint hne)
  · intro hr G t hn hint hne
    exact (bit0_true_iff G t).mpr (hr G t hn hint hne)

/-- `hcomplete` from `Reach` — the direction the leaf consumes. -/
theorem hcomplete_of_reach (hr : Reach) : HComplete := hcomplete_iff_reach.mpr hr

/-- `Reach` from `hcomplete` — the direction a search argument would use in reverse. -/
theorem reach_of_hcomplete (hc : HComplete) : Reach := hcomplete_iff_reach.mp hc

/-! ## 4.  The `ok` flag's normal form on the interior

`okW s = if 0 ≤ stT s + epsOf s then true else !((oracleV s).1)`, and the lower-body oracle is

    oracleV s = if dvR s = 0 then (if fvR s ≤ levelOf s then pivCut s else (true, stA s))
                              else (true, diagSignF …)

so below the top slice the flag is `true` **exactly** when the state's diagonal sums to `1`
(`dvR = 0`), its trace pairing is under the lower-body level (`fvR ≤ levelOf`), and the snapped pivot
descent reports no negative pivot.  These are the three registers a search argument must control. -/

/-- **The `ok` flag in registers** (below the campaign slack). -/
theorem okW_eq_true_iff (s : RSt) (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :
    QMCLeafB.OkLower.okW s = true ↔
      (dvR s = 0 ∧ fvR s ≤ QMCLeafB.OkLower.levelOf s ∧ (pivCut s).1 = false) := by
  unfold QMCLeafB.OkLower.okW QMCLeafB.OkLower.oracleV QMCLeafB.OkLower.threshV
  rw [if_neg h]
  by_cases hd : dvR s = 0
  · rw [if_pos hd]
    by_cases hf : fvR s ≤ QMCLeafB.OkLower.levelOf s
    · rw [if_pos hf]
      simp [hd, hf]
    · rw [if_neg hf]
      simp [hd, hf]
  · rw [if_neg hd]
    simp [hd]

/-- **The `ok` flag is false exactly when one of the three registers fails.** -/
theorem okW_eq_false_iff (s : RSt) (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :
    QMCLeafB.OkLower.okW s = false ↔
      ¬ (dvR s = 0 ∧ fvR s ≤ QMCLeafB.OkLower.levelOf s ∧ (pivCut s).1 = false) := by
  constructor
  · intro hf hconj
    have ht := (okW_eq_true_iff s h).mpr hconj
    rw [hf] at ht
    exact Bool.noConfusion ht
  · intro hconj
    cases hb : QMCLeafB.OkLower.okW s with
    | false => rfl
    | true => exact absurd ((okW_eq_true_iff s h).mp hb) hconj

/-! ## 5.  `Reach` in registers

The interior regime is a run invariant (`OkLower.regime_iterateW`: `stT` and `stA` are frozen by every
branch of the round, and `epsOf` reads only `stA`), so §4's normal form applies at **every** round of
the run, not merely at round `0`.  That makes `Reach` a statement about the orbit's registers. -/

/-- **The regime at the orbit, from the interior bracket.** -/
theorem regime_orbit (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hint : AsmM8.Interior G t)
    (k : ℕ) :
    ¬ (0 ≤ stT (QMCLeafB.OkLower.roundW^[k]
          (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
        + QMCLeafB.RoundT.epsOf (QMCLeafB.OkLower.roundW^[k]
          (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))) := by
  have hrat : (t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) < 0 := by
    have h2 : (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) < 0 := by
      have h3 := hint.2
      linarith
    have h1 : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ) < 0 := by
      have hc : ((t + QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ)
          = (t : ℝ) + (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) := by
        push_cast
        ring
      rw [hc]
      exact h2
    exact_mod_cast h1
  have hreg := QMCLeafB.OkLower.regime_iterateW
    (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)) k
  rw [QMCLeafB.InitDq.stT_init0, QMCLeafB.AssemblyM5.epsOf_init0_any] at hreg
  simp only [QMCLeafB.FinalStroke.noTape_snd, QMCLeafB.FinalStroke.noTape_fst] at hreg
  rw [hreg]
  linarith

/-- **`Reach`, in the orbit's registers.** -/
theorem reach_iff_registers :
    Reach ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
        ∃ k : ℕ, k < AsmM8.Tbc2 G t ∧
          dvR (QMCLeafB.OkLower.roundW^[k]
              (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) = 0 ∧
          fvR (QMCLeafB.OkLower.roundW^[k]
              (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
            ≤ QMCLeafB.OkLower.levelOf (QMCLeafB.OkLower.roundW^[k]
              (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) ∧
          (pivCut (QMCLeafB.OkLower.roundW^[k]
              (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))).1 = false := by
  constructor
  · intro hr G t hn hint hne
    obtain ⟨k, hk, hok⟩ := hr G t hn hint hne
    exact ⟨k, hk, (okW_eq_true_iff _ (regime_orbit G t hint k)).mp hok⟩
  · intro hr G t hn hint hne
    obtain ⟨k, hk, h1, h2, h3⟩ := hr G t hn hint hne
    exact ⟨k, hk, (okW_eq_true_iff _ (regime_orbit G t hint k)).mpr ⟨h1, h2, h3⟩⟩

/-! ## 6.  The assembly: the verbatim sentence from `hok` + `Reach`

Nothing new is needed beyond `MechM6.leaf_of_hok_and_complete`: `hcomplete` is `Reach` (§3).  This is
the shape the submission frame consumes — one analytic slot (`hok`) and one search slot (`Reach`). -/

/-- **The leaf from `hok` + `Reach`.** -/
theorem leaf_of_hok_and_reach
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hreach : Reach) :
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
  leaf_of_hok_and_complete hok (hcomplete_of_reach hreach)

/-- **The leaf from `hok` + the register form of `Reach`.** -/
theorem leaf_of_hok_and_registers
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hreg : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∃ k : ℕ, k < AsmM8.Tbc2 G t ∧
        dvR (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) = 0 ∧
        fvR (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))
          ≤ QMCLeafB.OkLower.levelOf (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t))) ∧
        (pivCut (QMCLeafB.OkLower.roundW^[k]
            (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G t)))).1 = false) :
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
  leaf_of_hok_and_reach hok (reach_iff_registers.mpr hreg)

/-! ## 7.  Receipts on the horizon and on the residual's shape

Two bookkeeping facts the residual needs, restated here so the reduction is self-contained:

* the horizon `Tbc2` is the `Kbc2` monomial (`UnionShallow.Kbc2` at `mHalve (n·n)`, times
  `mHalve (n·n)`), linear in the bit cost — so a visit argument whose round count is
  `C·n²·(log n + log(1/dq))` has room (`budgetRounds_dqShallow_le_Kbc2` is the banked form);
* `Reach`'s hypothesis is `¬ EmptyBody` at the campaign's own family `paramsKbc2`, so the slot is
  exactly "nonempty ⟹ visited", with no reference to the level test's tolerance. -/

/-- **`Tbc2` is the `Kbc2` monomial.**  Definitional receipt for the horizon. -/
theorem Tbc2_eq (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    AsmM8.Tbc2 G t
      = QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) G
        * QMCLeafB.HalvePerG.mHalve (G.n * G.n) := rfl

/-- **`Reach`'s hypothesis is non-emptiness of the campaign's own relaxed body** — the same predicate
`hcomplete` carries, at the same family.  Restated so a producer cannot drift to another `dq`. -/
theorem reach_hypothesis_shape (G : QuantumMaxCutEnergy.Input) (t : ℚ) :
    (¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) ↔
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
          (((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℚ) : ℝ) X := by
  unfold AsmM8.EmptyBody
  simp only [not_forall, not_not]

end QMCLeafB.ReachM4

/-! ## 8.  Axiom audit -/

#print axioms QMCLeafB.ReachM4.bit0_eq_anyOk
#print axioms QMCLeafB.ReachM4.bit0_true_iff
#print axioms QMCLeafB.ReachM4.hcomplete_iff_reach
#print axioms QMCLeafB.ReachM4.hcomplete_of_reach
#print axioms QMCLeafB.ReachM4.reach_of_hcomplete
#print axioms QMCLeafB.ReachM4.okW_eq_true_iff
#print axioms QMCLeafB.ReachM4.okW_eq_false_iff
#print axioms QMCLeafB.ReachM4.regime_orbit
#print axioms QMCLeafB.ReachM4.reach_iff_registers
#print axioms QMCLeafB.ReachM4.leaf_of_hok_and_reach
#print axioms QMCLeafB.ReachM4.leaf_of_hok_and_registers
#print axioms QMCLeafB.ReachM4.Tbc2_eq
#print axioms QMCLeafB.ReachM4.reach_hypothesis_shape



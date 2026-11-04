-- Prove2me | Definitions.Def_QMCLeafB_htop_oklower_m7
-- name    : QMCLeafB_htop_oklower_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:11:36.210642+00:00
-- url     : https://prove2.me/theorems/20cd83a5-e0d5-40ea-a107-a8887714a1e8
-- title:
--   QMCLeafB htop_oklower_m7
-- statement:
--   # leaf B phase 16 — the round whose `ok` branch is the *lower body* (m7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_finish_m7
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 16 — the round whose `ok` branch is the *lower body* (m7)

`Check_htop_okorient_m7` shows that the program's `ok` bit (`RoundProgram.oracleR`) is the UPPER
event (`stT s ≤ fvR s`) while `RelaxOracle.RelaxMem` — which `RunParts`' `hcert` is built from — is
the LOWER body (`frob ≤ u + δ/2`).  This file supplies the round that matches the lower body, so the
`ok` branch *is* a relaxation point and `hcert` needs no extra certificate:

    dqOf s    ≔ epsOf s / (9·massV s + 1)          -- the campaign's `dqShallow`, read off the state
    levelOf s ≔ stT s − epsOf s + dqOf s / 2       -- `t − εw + dq/2`
    oracleV s ≔ if dvR s = 0 then (if fvR s ≤ levelOf s then pivCut s else (true, stA s))
                                else (true, diagSignF …)

The three branches are exactly m5's `RelaxOracle` dichotomy:

* `dvR = 0 ∧ fvR ≤ levelOf s ∧ ¬pivAns`: **`RelaxMem`** at `(stT s − εw, dqOf s)` — the unit-diagonal
  clause is `dvR = 0`, the trace clause is `fvR ≤ levelOf s`, the PSD clause is the pivot test;
* `dvR = 0 ∧ levelOf s < fvR s`: the trace cut `(true, A)`, a genuine `RelaxCut` with margin
  `fvR s − levelOf s > 0`;
* `dvR ≠ 0`: the diagonal cut `(true, diagSignF)`.

`htop` cannot come from this round (at the top of the bracket `levelOf (init0 …) < 0 = fvR`), so the
reported round splits the two regimes by the sign of `stT + epsOf`, which the round freezes:

    roundW s ≔ if 0 ≤ stT s + epsOf s then roundOk s else roundV s

On the top slice `roundW` is `roundOk`, which freezes the state and reports `ok` for ever, so `htop`
is immediate; on the interior `roundW` is `roundV`, whose `ok` stream is the relaxation one.

Both are `Automatic.Poly` programs with no hypothesis.  The size ledger for `roundW` reduces to m3's
two `MszG` branch facts for `roundOk` plus the same cap bounds for `roundV`'s cut branch (its normals
are the same three as `oracleR`'s, so `MszG`'s bounds transport).

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.OkLower

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

/-! ## 1.  The campaign's tolerance, read off the state -/

/-- **`dqShallow`, on the state**: `εw/(9·Rq+1)` with `εw = massV/40000`, `Rq = massV`. -/
def dqOf (s : RSt) : ℚ := QMCLeafB.RoundT.epsOf s / (9 * QMCLeafB.RoundT.massV s + 1)

/-- **The lower-body level** `t − εw + dq/2`. -/
def levelOf (s : RSt) : ℚ :=
  stT s - QMCLeafB.RoundT.epsOf s + dqOf s / 2

theorem poly_dqOf : Poly dqOf := by
  unfold dqOf
  have h1 : Poly (fun s : RSt => (9 * QMCLeafB.RoundT.massV s + 1 : ℚ)) := by
    have h9 : Poly (fun s : RSt => 9 * QMCLeafB.RoundT.massV s) :=
      Poly.comp (f := fun q : ℚ × ℚ => q.1 * q.2)
        (g := fun s : RSt => ((9 : ℚ), QMCLeafB.RoundT.massV s)) Poly.rat_mul
        (Poly.pair (f := fun s : RSt => (9 : ℚ))
          (g := fun s : RSt => QMCLeafB.RoundT.massV s) (Automatic.Poly.const 9)
          QMCLeafB.RoundT.poly_massV)
    have h2 : Poly (fun s : RSt => (9 * QMCLeafB.RoundT.massV s, (1 : ℚ))) :=
      Poly.pair (f := fun s : RSt => 9 * QMCLeafB.RoundT.massV s)
        (g := fun _ : RSt => (1 : ℚ)) h9 (Automatic.Poly.const 1)
    exact Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
      (g := fun s : RSt => (9 * QMCLeafB.RoundT.massV s, (1 : ℚ))) Poly.rat_add h2
  have hp : Poly (fun s : RSt => (QMCLeafB.RoundT.epsOf s,
      9 * QMCLeafB.RoundT.massV s + 1)) :=
    Poly.pair QMCLeafB.RoundT.poly_epsOf h1
  exact Poly.comp (f := fun q : ℚ × ℚ => q.1 / q.2)
    (g := fun s : RSt => (QMCLeafB.RoundT.epsOf s, 9 * QMCLeafB.RoundT.massV s + 1))
    Poly.rat_div hp

theorem poly_levelOf : Poly levelOf := by
  unfold levelOf
  have hd : Poly (fun s : RSt =>
      (stT s - QMCLeafB.RoundT.epsOf s, dqOf s / 2)) :=
    Poly.pair
      (Poly.comp (f := fun q : ℚ × ℚ => q.1 - q.2)
        (g := fun s : RSt => (stT s, QMCLeafB.RoundT.epsOf s)) Poly.rat_sub
        (Poly.pair (f := fun s : RSt => stT s) (g := fun s : RSt => QMCLeafB.RoundT.epsOf s)
          poly_stT QMCLeafB.RoundT.poly_epsOf))
      (Poly.comp (f := fun q : ℚ × ℚ => q.1 / q.2)
        (g := fun s : RSt => (dqOf s, (2 : ℚ))) Poly.rat_div
        (Poly.pair (f := fun s : RSt => dqOf s) (g := fun _ : RSt => (2 : ℚ)) poly_dqOf
          (Automatic.Poly.const 2)))
  exact Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
    (g := fun s : RSt => (stT s - QMCLeafB.RoundT.epsOf s, dqOf s / 2)) Poly.rat_add hd

/-! ## 2.  The oracle with the lower-body `ok` branch -/

/-- The threshold branch at the lower-body level: inside the body ask the PSD test, above it take the
trace cut. -/
def threshV (s : RSt) : Bool × List ℚ := if fvR s ≤ levelOf s then pivCut s else (true, stA s)

/-- **The lower-body oracle.**  Branch order as m3's `oracleR`: diagonal repair first, then the
threshold branch. -/
def oracleV (s : RSt) : Bool × List ℚ :=
  if dvR s = 0 then threshV s else (true, diagSignF (stN s, stX s))

theorem poly_threshV : Poly threshV := by
  have hle : Poly (fun s : RSt => decide (fvR s ≤ levelOf s)) :=
    Poly.rat_le_comp poly_fvR poly_levelOf
  unfold threshV
  exact Poly.ite_prop (p := fun s : RSt => fvR s ≤ levelOf s) hle poly_pivCut
    (Poly.pair (f := fun _ : RSt => (true : Bool)) (g := fun s : RSt => stA s)
      (Automatic.Poly.const true) poly_stA)

theorem poly_oracleV : Poly oracleV := by
  have hd : Poly (fun s : RSt => decide (dvR s = 0)) :=
    Poly.rat_eq_comp poly_dvR (Automatic.Poly.const (0 : ℚ))
  have hdg : Poly (fun s : RSt => (true, diagSignF (stN s, stX s))) :=
    Poly.pair (f := fun _ : RSt => (true : Bool))
      (g := fun s : RSt => diagSignF (stN s, stX s)) (Automatic.Poly.const true)
      (Poly.comp (f := fun p : ℕ × List ℚ => diagSignF p)
        (g := fun s : RSt => (stN s, stX s)) poly_diagSignF
        (Poly.pair (f := fun s : RSt => stN s) (g := fun s : RSt => stX s) poly_stN poly_stX))
  unfold oracleV
  exact Poly.ite_prop (p := fun s : RSt => dvR s = 0) hd poly_threshV hdg

/-! ## 3.  The two rounds -/

/-- The cut branch at the lower-body oracle. -/
def roundCutV (s : RSt) : RSt :=
  mkSt (stN s) (stA s) (snapY s) (stT s) (stMu s) (stD s) (stOks s ++ [false]) (oracleV s).2

/-- **The engine round of the lower body.** -/
def roundV (s : RSt) : RSt := if (oracleV s).1 then roundCutV s else roundOk s

/-- **The reported round**: `ok`-and-freeze above the campaign slack, the lower-body engine below it.
`stT` and `stA` are frozen by both branches, so the regime is a run invariant. -/
def roundW (s : RSt) : RSt :=
  if 0 ≤ stT s + QMCLeafB.RoundT.epsOf s then roundOk s else roundV s

theorem poly_roundCutV : Poly roundCutV := by
  have hoks : Poly (fun s : RSt => stOks s ++ ([false] : List Bool)) :=
    Poly.comp (f := fun z : List Bool × List Bool => z.1 ++ z.2)
      (g := fun s : RSt => (stOks s, ([false] : List Bool)))
      (Poly.list_append (α := Bool))
      (Poly.pair (f := fun s : RSt => stOks s) (g := fun s : RSt => ([false] : List Bool))
        poly_stOks (Automatic.Poly.const [false]))
  have hrec : Poly (fun s : RSt => (oracleV s).2) :=
    Poly.comp (f := fun z : Bool × List ℚ => z.2) (g := oracleV) (by fun_prop) poly_oracleV
  exact poly_mkSt_c poly_stN poly_stA poly_snapY poly_stT poly_stMu poly_stD hoks hrec

theorem poly_cutFlagV : Poly (fun s : RSt => (oracleV s).1) :=
  Poly.comp (f := fun z : Bool × List ℚ => z.1) (g := oracleV) (by fun_prop) poly_oracleV

theorem poly_roundV : Poly roundV :=
  Poly.ite (p := fun s : RSt => (oracleV s).1) poly_cutFlagV poly_roundCutV poly_roundOk

theorem poly_regimeW : Poly (fun s : RSt =>
    decide (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :=
  Poly.rat_le_comp (Automatic.Poly.const (0 : ℚ))
    (Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
      (g := fun s : RSt => (stT s, QMCLeafB.RoundT.epsOf s)) Poly.rat_add
      (Poly.pair (f := fun s : RSt => stT s) (g := fun s : RSt => QMCLeafB.RoundT.epsOf s)
        poly_stT QMCLeafB.RoundT.poly_epsOf))

theorem poly_roundW : Poly roundW :=
  Poly.ite_prop (p := fun s : RSt => 0 ≤ stT s + QMCLeafB.RoundT.epsOf s) poly_regimeW
    poly_roundOk poly_roundV


/-! ## 4.  The flag stream, the regime invariance, and `htop` -/

theorem stT_roundV (s : RSt) : stT (roundV s) = stT s := by
  unfold roundV
  by_cases h : (oracleV s).1
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

theorem stA_roundV (s : RSt) : stA (roundV s) = stA s := by
  unfold roundV
  by_cases h : (oracleV s).1
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

theorem stT_roundW (s : RSt) : stT (roundW s) = stT s := by
  unfold roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    exact stT_roundV s

theorem stA_roundW (s : RSt) : stA (roundW s) = stA s := by
  unfold roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    exact stA_roundV s

theorem stT_iterateW (s : RSt) (k : ℕ) : stT (roundW^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundW, ih]

theorem stA_iterateW (s : RSt) (k : ℕ) : stA (roundW^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundW, ih]

/-- The regime is a run invariant. -/
theorem regime_iterateW (s : RSt) (k : ℕ) :
    (0 ≤ stT (roundW^[k] s) + QMCLeafB.RoundT.epsOf (roundW^[k] s))
      ↔ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s) := by
  have hst : stT (roundW^[k] s) = stT s := stT_iterateW s k
  have heps : QMCLeafB.RoundT.epsOf (roundW^[k] s) = QMCLeafB.RoundT.epsOf s :=
    QMCLeafB.HtopFinish.epsOf_congr (stA_iterateW s k)
  rw [hst, heps]

theorem stT_roundOk (s : RSt) : stT (roundOk s) = stT s := rfl
theorem stA_roundOk (s : RSt) : stA (roundOk s) = stA s := rfl
theorem stOks_roundOk (s : RSt) : stOks (roundOk s) = stOks s ++ [true] := rfl

theorem stT_iterateOk (s : RSt) (k : ℕ) : stT (roundOk^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundOk, ih]

theorem stA_iterateOk (s : RSt) (k : ℕ) : stA (roundOk^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundOk, ih]

/-- The regime, read at a `roundOk` orbit. -/
theorem regime_iterateOk (s : RSt) (k : ℕ) :
    stT (roundOk^[k] s) + QMCLeafB.RoundT.epsOf (roundOk^[k] s)
      = stT s + QMCLeafB.RoundT.epsOf s := by
  rw [stT_iterateOk, QMCLeafB.HtopFinish.epsOf_congr (stA_iterateOk s k)]

theorem stT_iterateV (s : RSt) (k : ℕ) : stT (roundV^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundV, ih]

theorem stA_iterateV (s : RSt) (k : ℕ) : stA (roundV^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundV, ih]

/-- The regime, read at a `roundV` orbit. -/
theorem regime_iterateV (s : RSt) (k : ℕ) :
    stT (roundV^[k] s) + QMCLeafB.RoundT.epsOf (roundV^[k] s)
      = stT s + QMCLeafB.RoundT.epsOf s := by
  rw [stT_iterateV, QMCLeafB.HtopFinish.epsOf_congr (stA_iterateV s k)]

/-- **Above the campaign slack `roundW` is `roundOk` on the whole orbit.** -/
theorem roundW_iterate_eq_roundOk (s : RSt)
    (h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s) :
    ∀ k : ℕ, roundW^[k] s = roundOk^[k] s := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hreg : 0 ≤ stT (roundOk^[j] s) + QMCLeafB.RoundT.epsOf (roundOk^[j] s) := by
        rw [regime_iterateOk s j]; exact h
      have hr : roundW (roundOk^[j] s) = roundOk (roundOk^[j] s) := by
        unfold roundW
        rw [if_pos hreg]
      rw [hr]

/-- **Below it, `roundW` is `roundV` on the whole orbit.** -/
theorem roundW_iterate_eq_roundV (s : RSt)
    (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :
    ∀ k : ℕ, roundW^[k] s = roundV^[k] s := by
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      have hreg : ¬ (0 ≤ stT (roundV^[j] s) + QMCLeafB.RoundT.epsOf (roundV^[j] s)) := by
        rw [regime_iterateV s j]; exact h
      have hr : roundW (roundV^[j] s) = roundV (roundV^[j] s) := by
        unfold roundW
        rw [if_neg hreg]
      rw [hr]

/-- The flag `roundW` appends. -/
def okW (s : RSt) : Bool := if 0 ≤ stT s + QMCLeafB.RoundT.epsOf s then true else !((oracleV s).1)

theorem stOks_roundV (s : RSt) : stOks (roundV s) = stOks s ++ [!((oracleV s).1)] := by
  unfold roundV
  by_cases h : (oracleV s).1
  · have hf : (oracleV s).1 = true := h
    rw [if_pos h, hf]
    rfl
  · have hf : (oracleV s).1 = false := by simpa using h
    rw [if_neg h, hf]
    rfl

theorem stOks_roundW (s : RSt) : stOks (roundW s) = stOks s ++ [okW s] := by
  unfold roundW okW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]
    exact stOks_roundV s

theorem stOks_iterateW (s : RSt) (T : ℕ) :
    stOks (roundW^[T] s) = stOks s ++ (List.range T).map (fun k => okW (roundW^[k] s)) := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundW, ih, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, List.append_assoc]

/-- **`hverdict` at the reported round.** -/
theorem verdict_iterate_eq_anyOk_W (s : RSt) (hs : stOks s = []) (T : ℕ) :
    verdict (roundW^[T] s) = QMCLeafB.SimLoop.anyOk (fun k => okW (roundW^[k] s)) T := by
  unfold verdict
  rw [stOks_iterateW, hs, List.nil_append]
  exact QMCLeafB.RStInit.decide_pos_filter_map_range _ T

/-- **Below the campaign slack the flag is the lower-body oracle's answer.** -/
theorem okW_eq_engine (s : RSt) (k : ℕ)
    (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) :
    okW (roundW^[k] s) = !((oracleV (roundW^[k] s)).1) := by
  unfold okW
  rw [if_neg (fun hh => h ((regime_iterateW s k).mp hh))]

/-- `roundOk` appends `true` for ever. -/
theorem stOks_roundOk_iterate (s : RSt) (T : ℕ) :
    stOks (roundOk^[T] s) = stOks s ++ List.replicate T true := by
  induction T with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', stOks_roundOk, ih, List.replicate_succ',
        List.append_assoc]

theorem verdict_roundOk_of_one_le (s : RSt) (hs : stOks s = []) {T : ℕ} (hT : 1 ≤ T) :
    verdict (roundOk^[T] s) = true := by
  unfold verdict
  rw [stOks_roundOk_iterate, hs, List.nil_append]
  have hlen : ((List.replicate T true).filter id).length = T := by simp
  rw [hlen]
  exact decide_eq_true (by omega)

/-- **`htop` at the reported round, from an abstract initial state**: above the campaign slack the
orbit is `roundOk`'s, which reports `ok` for ever. -/
theorem htop_roundW (init : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ) → RSt)
    (hoks : ∀ p, stOks (init p) = [])
    (hstT : ∀ p, stT (init p) = p.2)
    (hmass : ∀ p, QMCLeafB.RoundT.epsOf (init p)
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
    (T0 : QuantumMaxCutEnergy.Input → ℚ → ℕ)
    (hpos : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 1 ≤ T0 G t) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ),
      -(((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) ≤ (t : ℝ) → t ≤ 0 →
      QMCLeafB.FinalStroke.loopBit init roundW verdict T0 G t = true := by
  intro G t hlo _
  have hlo' : -(QMCLeafB.EngineRuntime.Rq G / 40000) ≤ t := by exact_mod_cast hlo
  set p := QMCLeafB.FinalStroke.noTape G t with hp
  have hpG : p.1.1 = G := rfl
  have hpt : p.2 = t := rfl
  have hslack : 0 ≤ stT (init p) + QMCLeafB.RoundT.epsOf (init p) := by
    rw [hstT p, hmass p, hpG, hpt]
    linarith
  unfold QMCLeafB.FinalStroke.loopBit
  rw [roundW_iterate_eq_roundOk _ hslack]
  exact verdict_roundOk_of_one_le _ (hoks p) (hpos G t)

/-! ## 5.  What the lower-body `ok` branch gives -/

/-- **At an `ok` answer the state is inside the lower body, unit-diagonal, and passes the pivot test.** -/
theorem oracleV_ok (s : RSt) (hok : (oracleV s).1 = false) :
    dvR s = 0 ∧ fvR s ≤ levelOf s ∧ (pivAns s).1 = false := by
  unfold oracleV at hok
  by_cases hd : dvR s = 0
  · rw [if_pos hd] at hok
    unfold threshV at hok
    by_cases hl : fvR s ≤ levelOf s
    · rw [if_pos hl] at hok
      unfold pivCut pivCutF at hok
      by_cases hp : (pivAns s).1
      · rw [if_pos hp] at hok
        exact absurd hok (by simp)
      · exact ⟨hd, hl, by simpa using hp⟩
    · rw [if_neg hl] at hok
      exact absurd hok (by simp)
  · rw [if_neg hd] at hok
    exact absurd hok (by simp)

/-- **`RelaxMem` at the shifted level, from an `ok` answer** — the three clauses are `dvR = 0`,
`fvR ≤ levelOf s` and the pivot/PSD input; the trace clause is `levelOf s = stT s − εw + dq/2`. -/
theorem relaxMem_of_oracleV_ok {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {s : RSt}
    (hF : fvR s = QMCLeafB.SepOracle.frob A cX) (hok : (oracleV s).1 = false)
    (hpos : 0 < QMCLeafB.RoundT.massV s)
    (hpsd : ∀ x : Fin n → ℚ,
      -(dqOf s / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf cX x)
    (hdiag : ∀ i, |cX i i - 1| ≤ dqOf s / 4) :
    QMCLeafB.RelaxOracle.RelaxMem A cX (stT s - QMCLeafB.RoundT.epsOf s) (dqOf s) := by
  obtain ⟨-, hle, -⟩ := oracleV_ok s hok
  have hε : 0 < QMCLeafB.RoundT.epsOf s := by
    unfold QMCLeafB.RoundT.epsOf
    have : (0 : ℚ) < QMCLeafB.RoundT.massV s := hpos
    positivity
  have hden : (0 : ℚ) < 9 * QMCLeafB.RoundT.massV s + 1 := by
    have := le_of_lt hpos
    linarith
  have hdq : 0 < dqOf s := by
    unfold dqOf
    positivity
  refine ⟨hdq, hpsd, hdiag, ?_⟩
  rw [← hF]
  exact hle

/-! ## 6.  The campaign's tolerance at `init0` -/

theorem dqOf_init0 (p : ((QuantumMaxCutEnergy.Input × List Bool) × ℚ)) :
    dqOf (QMCLeafB.RStInit.init0 p)
      = (QMCLeafB.EngineRuntime.Rq p.1.1 / 40000)
          / (9 * QMCLeafB.EngineRuntime.Rq p.1.1 + 1) := by
  unfold dqOf
  rw [QMCLeafB.HtopFinish.epsOf_init0, QMCLeafB.HtopFinish.massV_init0]

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.OkLower.poly_dqOf
#print axioms QMCLeafB.OkLower.poly_levelOf
#print axioms QMCLeafB.OkLower.poly_threshV
#print axioms QMCLeafB.OkLower.poly_oracleV
#print axioms QMCLeafB.OkLower.poly_roundCutV
#print axioms QMCLeafB.OkLower.poly_roundV
#print axioms QMCLeafB.OkLower.poly_roundW
#print axioms QMCLeafB.OkLower.stT_roundW
#print axioms QMCLeafB.OkLower.stA_roundW
#print axioms QMCLeafB.OkLower.regime_iterateW
#print axioms QMCLeafB.OkLower.roundW_iterate_eq_roundOk
#print axioms QMCLeafB.OkLower.roundW_iterate_eq_roundV
#print axioms QMCLeafB.OkLower.stOks_roundW
#print axioms QMCLeafB.OkLower.stOks_iterateW
#print axioms QMCLeafB.OkLower.verdict_iterate_eq_anyOk_W
#print axioms QMCLeafB.OkLower.okW_eq_engine
#print axioms QMCLeafB.OkLower.verdict_roundOk_of_one_le
#print axioms QMCLeafB.OkLower.htop_roundW
#print axioms QMCLeafB.OkLower.oracleV_ok
#print axioms QMCLeafB.OkLower.relaxMem_of_oracleV_ok
#print axioms QMCLeafB.OkLower.dqOf_init0

end QMCLeafB.OkLower



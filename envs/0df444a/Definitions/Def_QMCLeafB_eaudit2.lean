-- Prove2me | Definitions.Def_QMCLeafB_eaudit2
-- name    : QMCLeafB_eaudit2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T10:55:42.123359+00:00
-- url     : https://prove2.me/theorems/bfb6418a-e920-4ced-8178-5c477d2b915a
-- title:
--   QMCLeafB eaudit2
-- statement:
--   `Check_eaudit2_m7` — phase 31, member m7, direction `engine-audit` (part 2).
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_guard
import Definitions.Def_QMCLeafB_htop_oklower_m7
import Definitions.Def_QMCLeafB_unionShallow
import Definitions.Def_QMCLeafB_MatQ
/-
  `Check_eaudit2_m7` — phase 31, member m7, direction `engine-audit` (part 2).

  `Check_eaudit_m7` audited the seven slots of `Asm2M8.solution_of_residual` and named what `hok`
  still needs at a visited `ok` state `s = roundW^[k] (init0 (noTape G t))`:

    (i)   `stN s = G.n`, `stD`/`stMu`/`stA`/`stT` frozen;             -- rfl-level, THIS FILE
    (ii)  `stN s ≤ (stX s).length` (the descent test's `hlen`);         -- THIS FILE, `stX_length_orbitW`
    (iii) `hsym`, `hbox`, `hdiag`, `hpsd` — not stated anywhere yet.

  This file discharges (i) and (ii) for `OkLower.roundW` on the orbit of `RStInit.init0`, and reads
  off the campaign parameters along that orbit (`dqOf`/`epsOf`/`massV`), so a program-lane file that
  wants `RelaxApiM3.relaxMem_at_campaign_of_grid` or `OkLower.relaxMem_of_oracleV_ok` needs only the
  remaining four pointwise facts.

  The one length lemma is not new mathematics: `GuardedRound.snapY_length_eq`
  (`Check_guard_m1`) already shows `(snapY s).length = stN s * stN s` for a normalised `s`; the work
  here is transporting it through `roundW`'s regime split (which `Guard`'s `roundG` does not have).

  **Prior art.**  `Check_prog_m2` (m2, phase 30) already has the orbit facts at the *campaign* init
  `QMCLeafB.InitDq.init0` (`stN_iterateP`, `massV/epsOf/dqOf_iterateP`, `stSN`), and
  `Check_stateDiag_m2` (m2, phase 18) already proves §5's content (`stMat_diag_abs_le`,
  `relaxMem_of_oracleV_ok_state`: "`dvR = 0` gives the `diag_near` clause for free").  §2/§3/§5 here
  are an independent re-derivation at `RStInit.init0`, kept because `hlen`/`hD`/`massV`/`dqOf` are
  needed in exactly this shape by `RelaxApiM3.relaxMem_at_campaign_of_grid`, which m2's lane states at
  its own spellings.

  Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace EAudit2M7

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

local instance instRequestCodingEAudit2 : Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

/-! ## 1.  The regime split of `roundW`, field by field -/

theorem stN_roundW (s : RSt) : stN (QMCLeafB.OkLower.roundW s) = stN s := by
  unfold QMCLeafB.OkLower.roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · rw [if_neg h]
    unfold QMCLeafB.OkLower.roundV
    by_cases hc : (QMCLeafB.OkLower.oracleV s).1 = true
    · rw [if_pos hc]; rfl
    · rw [if_neg hc]; rfl

theorem stD_roundW (s : RSt) : stD (QMCLeafB.OkLower.roundW s) = stD s := by
  unfold QMCLeafB.OkLower.roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · rw [if_neg h]
    unfold QMCLeafB.OkLower.roundV
    by_cases hc : (QMCLeafB.OkLower.oracleV s).1 = true
    · rw [if_pos hc]; rfl
    · rw [if_neg hc]; rfl

theorem stMu_roundW (s : RSt) : stMu (QMCLeafB.OkLower.roundW s) = stMu s := by
  unfold QMCLeafB.OkLower.roundW
  by_cases h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [if_pos h]; rfl
  · rw [if_neg h]
    unfold QMCLeafB.OkLower.roundV
    by_cases hc : (QMCLeafB.OkLower.oracleV s).1 = true
    · rw [if_pos hc]; rfl
    · rw [if_neg hc]; rfl

theorem stA_roundW' (s : RSt) : stA (QMCLeafB.OkLower.roundW s) = stA s :=
  QMCLeafB.OkLower.stA_roundW s

theorem stT_roundW' (s : RSt) : stT (QMCLeafB.OkLower.roundW s) = stT s :=
  QMCLeafB.OkLower.stT_roundW s

/-! ## 2.  The normalisation invariant `|X| = n·n` is preserved by `roundW` -/

theorem stX_roundW_regime (s : RSt) (h : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s) :
    stX (QMCLeafB.OkLower.roundW s) = stX s := by
  unfold QMCLeafB.OkLower.roundW
  rw [if_pos h]
  rfl

theorem stX_roundW_cut (s : RSt) (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s))
    (hc : (QMCLeafB.OkLower.oracleV s).1 = true) :
    stX (QMCLeafB.OkLower.roundW s) = snapY s := by
  unfold QMCLeafB.OkLower.roundW QMCLeafB.OkLower.roundV
  rw [if_neg h, if_pos hc]
  rfl

theorem stX_roundW_ok (s : RSt) (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s))
    (hc : (QMCLeafB.OkLower.oracleV s).1 = false) :
    stX (QMCLeafB.OkLower.roundW s) = stX s := by
  unfold QMCLeafB.OkLower.roundW QMCLeafB.OkLower.roundV
  rw [if_neg h, if_neg (by simpa using hc)]
  rfl

/-- **`roundW` preserves the normalisation `|X| = n·n`.**  `RoundProgram.roundOk` freezes `X`; the
cut branch replaces it by `snapY s`, whose length is `n·n` at a normalised state
(`GuardedRound.snapY_length_eq`, i.e. `stepFun_length` + `smulRaw_length`). -/
theorem stX_length_roundW (s : RSt) (h : (stX s).length = stN s * stN s) :
    (stX (QMCLeafB.OkLower.roundW s)).length
      = stN (QMCLeafB.OkLower.roundW s) * stN (QMCLeafB.OkLower.roundW s) := by
  rw [stN_roundW]
  by_cases hreg : 0 ≤ stT s + QMCLeafB.RoundT.epsOf s
  · rw [stX_roundW_regime s hreg]; exact h
  · by_cases hc : (QMCLeafB.OkLower.oracleV s).1 = true
    · rw [stX_roundW_cut s hreg hc]
      exact QMCLeafB.GuardedRound.snapY_length_eq s h
    · rw [stX_roundW_ok s hreg (by simpa using hc)]
      exact h

/-! ## 3.  The orbit: frozen parameters and the normalisation -/

theorem stN_orbitW (s : RSt) (k : ℕ) :
    stN (QMCLeafB.OkLower.roundW^[k] s) = stN s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stN_roundW, ih]

theorem stD_orbitW (s : RSt) (k : ℕ) :
    stD (QMCLeafB.OkLower.roundW^[k] s) = stD s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stD_roundW, ih]

theorem stMu_orbitW (s : RSt) (k : ℕ) :
    stMu (QMCLeafB.OkLower.roundW^[k] s) = stMu s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stMu_roundW, ih]

theorem stA_orbitW (s : RSt) (k : ℕ) :
    stA (QMCLeafB.OkLower.roundW^[k] s) = stA s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stA_roundW', ih]

theorem stT_orbitW (s : RSt) (k : ℕ) :
    stT (QMCLeafB.OkLower.roundW^[k] s) = stT s := by
  induction k with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', stT_roundW', ih]

/-- **The normalisation holds at every visited state of the run.** -/
theorem stX_length_orbitW (s : RSt) (h : (stX s).length = stN s * stN s) (k : ℕ) :
    (stX (QMCLeafB.OkLower.roundW^[k] s)).length
      = stN (QMCLeafB.OkLower.roundW^[k] s) * stN (QMCLeafB.OkLower.roundW^[k] s) := by
  induction k with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact stX_length_roundW _ ih

/-! ## 4.  At `init0`: the state data `hok` reads -/

/-- **`hlen` at every visited state**: `stN ≤ (stX).length` — the descent test's side condition. -/
theorem hlen_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))
      ≤ (stX (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))).length := by
  have h := stX_length_orbitW (QMCLeafB.RStInit.init0 p)
    (QMCLeafB.RStInit.stX_length p) k
  rw [h]
  exact Nat.le_mul_self _

/-- **`hD` at every visited state**: the grid denominator is positive. -/
theorem hD_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    0 < stD (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)) := by
  rw [stD_orbitW, QMCLeafB.RStInit.stD_init0_eq]
  unfold QMCLeafB.InitVerdict.gridOf
  positivity

/-- **`hn` at every visited state**: the order is the request's. -/
theorem hn_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    stN (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)) = p.1.1.n := by
  rw [stN_orbitW, QMCLeafB.RStInit.stN_init0]

/-- **`stT` at every visited state**: the threshold is the request's. -/
theorem ht_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    stT (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p)) = p.2 := by
  rw [stT_orbitW, QMCLeafB.RStInit.stT_init0]

/-- **The mass along the orbit** — `massV = Rq G`, so the state's own tolerance `dqOf` is the
campaign's `dqShallow`. -/
theorem massV_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    QMCLeafB.RoundT.massV (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))
      = QMCLeafB.EngineRuntime.Rq p.1.1 := by
  have h : QMCLeafB.RoundT.massV (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))
      = QMCLeafB.RoundT.massV (QMCLeafB.RStInit.init0 p) := by
    unfold QMCLeafB.RoundT.massV
    rw [stA_orbitW]
  rw [h, QMCLeafB.HtopFinish.massV_init0]

theorem epsOf_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ) :
    QMCLeafB.RoundT.epsOf (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))
      = QMCLeafB.EngineRuntime.Rq p.1.1 / 40000 := by
  unfold QMCLeafB.RoundT.epsOf
  rw [massV_orbitW]
  ring

/-- **`dqOf` along the orbit is the campaign's `dqShallow`** (at `Rq ≠ 0`, where the campaign
definition is the honest formula and not its `Rq = 0` fallback). -/
theorem dqOf_orbitW (p : QMCLeafB.FuelWire.Pkg) (k : ℕ)
    (hRq : QMCLeafB.EngineRuntime.Rq p.1.1 ≠ 0) :
    QMCLeafB.OkLower.dqOf (QMCLeafB.OkLower.roundW^[k] (QMCLeafB.RStInit.init0 p))
      = QMCLeafB.RundataParams.dqShallow p.1.1 := by
  unfold QMCLeafB.OkLower.dqOf
  rw [epsOf_orbitW, massV_orbitW]
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg hRq]
  rfl


/-! ## 5.  `hdiag` is FREE at an `ok` round

The `ok` branch of `OkLower.oracleV` is gated on `dvR s = 0`, and

    dvR s = diagSumV (stN s, stX s) = ∑_{i < min n |X|} |Xᵢᵢ − 1| .

A sum of nonnegative terms is `0` only if every term is, so `|Xᵢᵢ − 1| = 0 ≤ dq/4` — and `entV` is
*definitionally* `MatQ.entry`, so no code-coherence hypothesis is needed.  With §4's `hlen` this makes
`hdiag` — the one clause of the `ok` test that the phase-21 audit compared to `hdiagc` — free. -/

theorem list_sum_nonneg : ∀ {l : List ℚ}, (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum
  | [], _ => by simp
  | a :: t, h => by
      have ha : 0 ≤ a := h a (List.mem_cons_self ..)
      have ht : ∀ y ∈ t, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      simpa using add_nonneg ha (list_sum_nonneg ht)

theorem list_eq_zero_of_sum_eq_zero : ∀ {l : List ℚ}, (∀ x ∈ l, 0 ≤ x) → l.sum = 0 →
    ∀ x ∈ l, x = 0
  | [], _, _, x, hx => by simp at hx
  | a :: t, h, hz, x, hx => by
      have ha : 0 ≤ a := h a (List.mem_cons_self ..)
      have ht : ∀ y ∈ t, 0 ≤ y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hs : a + t.sum = 0 := by simpa using hz
      have hts : t.sum = 0 := by
        have := list_sum_nonneg ht
        linarith
      rcases List.mem_cons.mp hx with rfl | hmem
      · linarith
      · exact list_eq_zero_of_sum_eq_zero ht hts x hmem

/-- **At `dvR s = 0` the coded diagonal is exactly `1`.** -/
theorem entV_diag_eq_one_of_dvR_zero (s : RSt) (h : dvR s = 0)
    (hlen : stN s ≤ (stX s).length) {i : ℕ} (hi : i < stN s) :
    entV (stN s, stX s) i i = 1 := by
  have hk : i < ((stX s).take (stN s)).length := by
    rw [List.length_take]
    omega
  have hmem : absq (entV (stN s, stX s) i i - 1)
      ∈ (idxs (stN s, stX s)).map (fun i => absq (entV (stN s, stX s) i i - 1)) := by
    refine List.mem_map.mpr ⟨i, ?_, rfl⟩
    simpa only [QMCLeafB.RoundProgram.idxs] using List.mem_range.mpr hk
  have hnn : ∀ x ∈ (idxs (stN s, stX s)).map
      (fun i => absq (entV (stN s, stX s) i i - 1)), 0 ≤ x := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
    rw [QMCLeafB.RoundProgram.absq_eq]
    exact abs_nonneg _
  have hz : ((idxs (stN s, stX s)).map
      (fun i => absq (entV (stN s, stX s) i i - 1))).sum = 0 := h
  have h0 := list_eq_zero_of_sum_eq_zero hnn hz _ hmem
  rw [QMCLeafB.RoundProgram.absq_eq, abs_eq_zero] at h0
  linarith

/-- **`hdiag` at an `ok` round, free.**  `entV` on the diagonal *is* `MatQ.entry`, hence the matrix
entry of `MatQ.toMatrix`, so the clause `|Xᵢᵢ − 1| ≤ δ/4` holds with room to spare. -/
theorem hdiag_free (s : RSt) (h : dvR s = 0) (hlen : stN s ≤ (stX s).length)
    {δ : ℚ} (hδ : 0 ≤ δ) (i : Fin (stN s)) :
    |MatQ.toMatrix (stN s) (stX s) i i - 1| ≤ δ / 4 := by
  have h1 : entV (stN s, stX s) i.val i.val = 1 :=
    entV_diag_eq_one_of_dvR_zero s h hlen i.isLt
  have h2 : MatQ.toMatrix (stN s) (stX s) i i = entV (stN s, stX s) i.val i.val := rfl
  rw [h2, h1]
  simp only [sub_self, abs_zero]
  linarith

end EAudit2M7

/-! ## Axiom audit -/

#print axioms EAudit2M7.stN_roundW
#print axioms EAudit2M7.stD_roundW
#print axioms EAudit2M7.stX_length_roundW
#print axioms EAudit2M7.stN_orbitW
#print axioms EAudit2M7.stD_orbitW
#print axioms EAudit2M7.stA_orbitW
#print axioms EAudit2M7.stT_orbitW
#print axioms EAudit2M7.stX_length_orbitW
#print axioms EAudit2M7.hlen_orbitW
#print axioms EAudit2M7.hD_orbitW
#print axioms EAudit2M7.hn_orbitW
#print axioms EAudit2M7.massV_orbitW
#print axioms EAudit2M7.epsOf_orbitW
#print axioms EAudit2M7.dqOf_orbitW
#print axioms EAudit2M7.list_sum_nonneg
#print axioms EAudit2M7.list_eq_zero_of_sum_eq_zero
#print axioms EAudit2M7.entV_diag_eq_one_of_dvR_zero
#print axioms EAudit2M7.hdiag_free



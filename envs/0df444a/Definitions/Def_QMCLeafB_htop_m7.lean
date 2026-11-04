-- Prove2me | Definitions.Def_QMCLeafB_htop_m7
-- name    : QMCLeafB_htop_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:07:50.322453+00:00
-- url     : https://prove2.me/theorems/6d8abcb4-fed4-43b3-8f8e-0fb3d35fab37
-- title:
--   QMCLeafB htop_m7
-- statement:
--   # leaf B phase 14 — `htop` (swarm `smw17fqzz`, member m7, direction d14)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_round_program_m3
/-
# leaf B phase 14 — `htop` (swarm `smw17fqzz`, member m7, direction d14)

The `htop` slot of `FuelAssembly.solution_RSt` is

    htop : ∀ G t, -εr ≤ t → t ≤ 0 → loopBitRSt G t = true

with `loopBitRSt G t = verdict (round^[K*m] (init0 (noTape G t)))`, and `verdict s` is `true` exactly
when the state's `ok` flags contain a `true`.  So `htop` factors into two independent obligations:

1. **flag monotonicity** — once a round reports `ok`, the flag is never lost, so the verdict is
   `true` from that round on.  Proved here unconditionally: `stOks_round_append` (both branches of
   `RoundProgram.round` append exactly one flag), `stOks_prefix_iterate` (so the flag lists are
   nested), `verdict_of_mem`, and `verdict_of_first_ok`;
2. **one `ok` on the top slice** — the first round takes the `ok` branch when `t` is in
   `[-Rq G/40000, 0]`.  This is the analytic part and it is *not* a property of
   `RoundProgram.round` as it stands: `init0` writes the box point `M·I`, so `dvR ≠ 0` and `oracleR`
   takes the cut branch, and `threshB`'s test is `stT s ≤ fvR s`, i.e. feasibility at level `t`,
   whereas `RunData.hcert` needs feasibility at level `t + Rq G/40000` — an `εw`-mismatch.  The fix
   is to test at `t + εw`:

       oracleT s := if fvR s ≤ stT s + epsOf s then (false, []) else oracleR s

   Then the first round is `ok` on the top slice because `fvR (init0 (noTape G t)) = 0` (the
   diagonal of `wMatrix G` is zero, so the box point pairs to `0`) and `0 ≤ t + εw` there.  Both are
   separate, provable facts about `init0` / `wMatrix G`, and they are the whole residual of `htop`.

`verdict_of_first_ok` is the reduction: `htop` = "the loop reports `ok` at round `j₀ < K*m`" plus
this file.  No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.Htop

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

/-! ## 1.  The verdict reads the flag list -/

/-- The verdict is `true` as soon as some recorded round reported `ok`. -/
theorem verdict_of_mem {s : QMCLeafB.RoundProgram.RSt} (h : true ∈ QMCLeafB.RoundProgram.stOks s) :
    QMCLeafB.RoundProgram.verdict s = true := by
  have hmem : true ∈ (QMCLeafB.RoundProgram.stOks s).filter id :=
    List.mem_filter.mpr ⟨h, rfl⟩
  have hne : (QMCLeafB.RoundProgram.stOks s).filter id ≠ [] := List.ne_nil_of_mem hmem
  have hpos : 0 < ((QMCLeafB.RoundProgram.stOks s).filter id).length := List.length_pos_iff.mpr hne
  simp [QMCLeafB.RoundProgram.verdict, hpos]

/-! ## 2.  Both branches append exactly one flag -/

/-- `RoundProgram.round` appends exactly one flag to the record. -/
theorem stOks_round_append (s : QMCLeafB.RoundProgram.RSt) :
    ∃ b : Bool, QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round s)
      = QMCLeafB.RoundProgram.stOks s ++ [b] := by
  by_cases h : (QMCLeafB.RoundProgram.oracleR s).1 = true
  · refine ⟨false, ?_⟩
    rw [QMCLeafB.RoundProgram.round_eq, if_pos h]
    rfl
  · refine ⟨true, ?_⟩
    rw [QMCLeafB.RoundProgram.round_eq, if_neg (by simpa using h)]
    rfl

/-- The flag list is a prefix of the next round's. -/
theorem stOks_prefix_succ (s : QMCLeafB.RoundProgram.RSt) (j : ℕ) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[j] s)
      <+: QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[j + 1] s) := by
  obtain ⟨b, hb⟩ := stOks_round_append (QMCLeafB.RoundProgram.round^[j] s)
  rw [Function.iterate_succ_apply', hb]
  exact List.prefix_append _ _

/-- The flag lists along the orbit are nested. -/
theorem stOks_prefix_iterate (s : QMCLeafB.RoundProgram.RSt) {j₀ j : ℕ} (h : j₀ ≤ j) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[j₀] s)
      <+: QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[j] s) := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih => exact ih.trans (stOks_prefix_succ s j)

/-! ## 3.  `htop`'s second half

If the loop reports `ok` at any round strictly before `K*m`, the verdict is `true` there.  So `htop`
reduces to producing one `ok` round, which is obligation (2) of the module docstring. -/

/-- **An `ok` at round `j₀ < j` forces a `true` verdict at round `j`.** -/
theorem verdict_of_first_ok (s : QMCLeafB.RoundProgram.RSt) {j₀ j : ℕ} (hle : j₀ ≤ j)
    (hok : true ∈ QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[j₀] s)) :
    QMCLeafB.RoundProgram.verdict (QMCLeafB.RoundProgram.round^[j] s) = true :=
  verdict_of_mem ((stOks_prefix_iterate s hle).mem hok)

/-- The same at `j = 1`: a first round that reports `ok` makes the verdict `true` at every later
round.  This is the form `htop` consumes, since the loop's count `K*m` is at least `1`. -/
theorem verdict_of_first_ok_of_one (s : QMCLeafB.RoundProgram.RSt) {j : ℕ} (h1 : 1 ≤ j)
    (hok : true ∈ QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round s)) :
    QMCLeafB.RoundProgram.verdict (QMCLeafB.RoundProgram.round^[j] s) = true := by
  have hok' : true ∈ QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round^[1] s) := by
    rwa [Function.iterate_one]
  exact verdict_of_first_ok s (j₀ := 1) h1 hok'

end QMCLeafB.Htop

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.Htop.verdict_of_mem
#print axioms QMCLeafB.Htop.stOks_round_append
#print axioms QMCLeafB.Htop.stOks_prefix_succ
#print axioms QMCLeafB.Htop.stOks_prefix_iterate
#print axioms QMCLeafB.Htop.verdict_of_first_ok
#print axioms QMCLeafB.Htop.verdict_of_first_ok_of_one



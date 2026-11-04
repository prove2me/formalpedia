-- Prove2me | Definitions.Def_QMCLeafB_roundT_m7
-- name    : QMCLeafB_roundT_m7
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T01:20:53.864191+00:00
-- url     : https://prove2.me/theorems/8749b5cd-53ac-4ab5-a367-bb6415c35f7f
-- title:
--   QMCLeafB roundT_m7
-- statement:
--   # leaf B phase 14 — `roundT`: the round whose `ok` test is at the campaign's own slack (m7, d14)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_htop_m7
import Definitions.Def_QMCLeafB_htop_init_m7
/-
# leaf B phase 14 — `roundT`: the round whose `ok` test is at the campaign's own slack (m7, d14)

`RoundProgram.round` takes its `ok` branch when `threshB` sees `stT s ≤ fvR s`, i.e. when the current
point is feasible at level `t`.  But `RunData.hcert`'s conclusion is
`tr (wMatrix G · X) ≤ t + εw` with `εw = Rq G / 40000`, so the `ok` branch as m3 wrote it does not
certify itself, and `init0`'s box point can never take it (`dvR ≠ 0`).

`roundT` moves the test to the campaign's own slack:

    epsOf s  ≔ (∑_{q ∈ stA s} |q|) / 40000        -- this is exactly `Rq G / 40000` at `init0`
    roundT s ≔ if fvR s ≤ stT s + epsOf s then roundOk s else round s

Then:
* on the top slice `[-Rq G/40000, 0]` the first round is `ok`, because `fvR (init0 …) = 0`
  (`HtopInit.fvR_init0`) and `0 ≤ t + εw`; combined with `Htop.verdict_of_first_ok_of_one` this is
  `htop`;
* on the interior the `ok` branch is certified by exactly the inequality `hcert` asks for.

This file builds `massV`/`epsOf`/`roundT` and their `Poly` proofs.

No `sorry`, no `axiom`; audits at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section
namespace QMCLeafB.RoundT

open QuantumMaxCutEnergy
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic
open QMCLeafB.RoundProgram

/-! ## 1.  The state's own `ℓ¹` mass, and the slack -/

/-- The `ℓ¹` mass of the state's weight code — `Rq G` at `init0`. -/
def massV (s : RSt) : ℚ := ((stA s).map absq).sum

/-- The campaign's slack, read off the state: `εw = Rq G / 40000`. -/
def epsOf (s : RSt) : ℚ := massV s * (1 / 40000)

theorem poly_massV : Poly massV := by
  unfold massV
  have hf : Poly (fun x : RSt × ℚ => absq x.2) :=
    Poly.comp (f := absq) (g := (Prod.snd : RSt × ℚ → ℚ)) poly_absq Poly.snd
  have hlist : Poly (fun s : RSt => (stA s).map absq) :=
    Poly.list_map (f := fun (_ : RSt) (q : ℚ) => absq q) (as := stA) hf poly_stA
  exact Poly.comp (f := List.sum) (g := fun s : RSt => (stA s).map absq)
    PivotProgram.poly_rat_sum hlist

theorem poly_epsOf : Poly epsOf := by
  unfold epsOf
  have h1 : Poly (fun s : RSt => (massV s, (1 / 40000 : ℚ))) :=
    Poly.pair (f := fun s : RSt => massV s) (g := fun _ : RSt => (1 / 40000 : ℚ))
      poly_massV (Automatic.Poly.const (1 / 40000))
  exact Poly.comp (f := fun q : ℚ × ℚ => q.1 * q.2)
    (g := fun s : RSt => (massV s, (1 / 40000 : ℚ))) Poly.rat_mul h1

/-! ## 2.  The round -/

/-- One round whose `ok` test is at the campaign's slack `t + εw`. -/
def roundT (s : RSt) : RSt :=
  if fvR s ≤ stT s + epsOf s then roundOk s else round s

theorem poly_roundT : Poly roundT := by
  have hsum : Poly (fun s : RSt => stT s + epsOf s) := by
    have h1 : Poly (fun s : RSt => (stT s, epsOf s)) :=
      Poly.pair (f := fun s : RSt => stT s) (g := fun s : RSt => epsOf s) poly_stT poly_epsOf
    exact Poly.comp (f := fun q : ℚ × ℚ => q.1 + q.2)
      (g := fun s : RSt => (stT s, epsOf s)) Poly.rat_add h1
  have hc : Poly (fun s : RSt => decide (fvR s ≤ stT s + epsOf s)) :=
    Poly.rat_le_comp poly_fvR hsum
  unfold roundT
  exact Poly.ite_prop (p := fun s : RSt => fvR s ≤ stT s + epsOf s) hc poly_roundOk poly_round

/-! ## 3.  `roundT` takes the `ok` branch whenever the slack condition holds -/

theorem stOks_roundT_append (s : RSt) :
    ∃ b : Bool, stOks (roundT s) = stOks s ++ [b] := by
  by_cases h : fvR s ≤ stT s + epsOf s
  · refine ⟨true, ?_⟩
    rw [roundT, if_pos h]
    rfl
  · obtain ⟨b, hb⟩ := QMCLeafB.Htop.stOks_round_append s
    exact ⟨b, by rw [roundT, if_neg h]; exact hb⟩

theorem stOks_prefix_iterateT (s : RSt) {j₀ j : ℕ} (h : j₀ ≤ j) :
    stOks (roundT^[j₀] s) <+: stOks (roundT^[j] s) := by
  induction j, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j _ ih =>
      refine ih.trans ?_
      obtain ⟨b, hb⟩ := stOks_roundT_append (roundT^[j] s)
      rw [Function.iterate_succ_apply', hb]
      exact List.prefix_append _ _

/-- **`htop` for `roundT`, modulo the one scalar condition.**  If the initial slack is non-negative,
the first round reports `ok` and the verdict is `true` at every later round. -/
theorem htop_roundT (G : QuantumMaxCutEnergy.Input) (t : ℚ) {j : ℕ} (hj : 1 ≤ j)
    (hslack : 0 ≤ t + epsOf (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) :
    QMCLeafB.RoundProgram.verdict
      (roundT^[j] (QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t))) = true := by
  set s := QMCLeafB.RStInit.init0 (QMCLeafB.FinalStroke.noTape G t) with hs
  have hfv : fvR s = 0 := QMCLeafB.HtopInit.fvR_init0 G t
  have ht : stT s = t := QMCLeafB.RStInit.stT_init0 _
  have hbranch : fvR s ≤ stT s + epsOf s := by rw [hfv, ht]; exact hslack
  have hok : QMCLeafB.RoundProgram.stOks (roundT s) = stOks s ++ [true] := by
    rw [roundT, if_pos hbranch]
    rfl
  have hmem : true ∈ stOks (roundT^[1] s) := by
    rw [Function.iterate_one, hok]
    exact List.mem_append_right _ (List.mem_singleton_self true)
  have hle : (1 : ℕ) ≤ j := hj
  have := (stOks_prefix_iterateT s hle).mem hmem
  exact QMCLeafB.Htop.verdict_of_mem this

end QMCLeafB.RoundT

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.RoundT.poly_massV
#print axioms QMCLeafB.RoundT.poly_epsOf
#print axioms QMCLeafB.RoundT.poly_roundT
#print axioms QMCLeafB.RoundT.stOks_roundT_append
#print axioms QMCLeafB.RoundT.stOks_prefix_iterateT
#print axioms QMCLeafB.RoundT.htop_roundT



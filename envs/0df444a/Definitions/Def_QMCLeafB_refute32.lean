-- Prove2me | Definitions.Def_QMCLeafB_refute32
-- name    : QMCLeafB_refute32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:01:07.315855+00:00
-- url     : https://prove2.me/theorems/f8c94ebc-4823-4aef-9e31-e5039dd48374
-- title:
--   QMCLeafB refute32
-- statement:
--   The Check_refute32_m4 module of the QMCLeafB library.
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_mech31
import Definitions.Def_QMCLeafB_reach32
/-
# `Check_refute32_m4` — phase 32, member m4, direction `asm-reduce` (d5)

**`hcomplete` fails at the campaign's own exemplar, and the failure reduces to ONE scalar orbit
statement.**  Take `G₀` (`n = 2`, one edge of weight `1/2`, `Rq = 1`) and `t = -1/2`: the point is
interior and its relaxed body is **non-empty** (§1).  The campaign run's diagonal defect

    dvR s = ∑ᵢ |Xᵢᵢ − 1|

never vanishes along that run (§3's hypothesis), and `okW` needs `dvR = 0` — so no round reports `ok`,
the bit reads `false`, and `hcomplete`'s demanded implication fails (§4).  Consequently
`MechM6.leaf_of_hok_and_complete` is unfireable at `(RSt, InitDq.init0, LedgerW.roundWG,
RoundProgram.verdict, Tbc2)`.

## Why `dvR` never vanishes: the run stalls on the phase-26 defect

`init0`'s primal code is `M⁻¹ • I` (diagonal `1/M`, *not* the identity), so `dvR (init0 ·) = 2(1 − 1/M)`.
Every cut round computes `nrmRow mu d (α⁻¹ • stepY)`, and `stepY` reads the oracle's normal — an
`n²`-code — as an `n`-vector.  At a diagonal state `(a,0,0,b)` the normal is `diagSignF`'s first two
entries, so the live directions are `(a,0)` and `(0,3b)`: only the first diagonal is cut, and
`a ↦ nrmQ a` has the exact fixed point `a = 10/81`.  `#reduce` (kernel/meta reduction, which — unlike
`decide` — sees through `snapTrunc`'s well-founded recursion) gives, at `t = -1/2`,

    X₀ = [1/M,0,0,1/M] → X₁ = [10/81,0,0,10/27] → X₂ = [10/81,0,0,10/9]
      → X₃ = [10/81,0,0,10/3] → X₄ = [10/81,0,0,0] → X₄ → X₄ → …

with `dvR = 1120000000002/640000000001, 122/81, 80/81, 260/81, 152/81, 152/81` — never `0`, and the
off-diagonals identically `0`.  So the hypothesis of §3 is exactly the statement `#reduce` verifies; a
fully `decide`-free kernel proof of it needs m8's `snapTrunc_of_nonneg/_of_neg` route at these five
snap points (a mechanical follow-up, not a mathematical one).

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

local instance instRequestCodingRefute32 :
    Coding (QuantumMaxCutEnergy.Input × List Bool) :=
  ⟨QuantumMaxCutEnergy.encodeRequest⟩

namespace QMCLeafB.RefuteM4

open QuantumMaxCutEnergy
open QMCLeafB.RoundProgram

/-! ## 0.  The counterexample's point -/

/-- **The refuting input**: two vertices, one edge of weight `1/2`, so `Rq G₀ = 1`. -/
abbrev G₀ : QuantumMaxCutEnergy.Input := QMCLeafB.ResidRefute.G₀

/-- The interior threshold `t = -1/2`. -/
def t₀ : ℚ := -(1 / 2)

/-- The tape-free request the loop is run on. -/
def p₀ : QMCLeafB.FuelWire.Pkg := QMCLeafB.FinalStroke.noTape G₀ t₀

/-- **The campaign's initial state at the counterexample's point.** -/
def s₀ : RSt := QMCLeafB.InitDq.init0 p₀

/-! ## 1.  The body at `(G₀,-1/2)` is non-empty, and the point is interior -/

theorem eps_G₀ : QMCLeafB.RundataCert.eps G₀ = 1 / 40000 := by
  unfold QMCLeafB.RundataCert.eps
  rw [QMCLeafB.ResidRefute.Rq_G₀]

theorem dqShallow_G₀ : QMCLeafB.RundataParams.dqShallow G₀ = 1 / 400000 := by
  unfold QMCLeafB.RundataParams.dqShallow QMCLeafB.RundataParams.dqShallowCore
  rw [if_neg (by rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num)]
  unfold QMCLeafB.RundataCert.eps
  rw [QMCLeafB.ResidRefute.Rq_G₀]
  norm_num

theorem wMatrixQ_G₀_00 :
    QMCLeafB.Finalization.wMatrixQ G₀ (0 : Fin 2) (0 : Fin 2) = 0 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num

theorem wMatrixQ_G₀_01 :
    QMCLeafB.Finalization.wMatrixQ G₀ (0 : Fin 2) (1 : Fin 2) = 1 / 2 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrixQ_G₀_10 :
    QMCLeafB.Finalization.wMatrixQ G₀ (1 : Fin 2) (0 : Fin 2) = 1 / 2 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num [QMCLeafB.ResidRefute.G₀]

theorem wMatrixQ_G₀_11 :
    QMCLeafB.Finalization.wMatrixQ G₀ (1 : Fin 2) (1 : Fin 2) = 0 := by
  unfold QMCLeafB.Finalization.wMatrixQ
  norm_num

/-- The pin matrix's pairing with `A` is exactly `-1`. -/
theorem frob_G₀_pin :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₀)
      (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) = -1 := by
  rw [QMCLeafB.SepOracle.frob]
  simp only [Fin.sum_univ_two, wMatrixQ_G₀_00, wMatrixQ_G₀_01, wMatrixQ_G₀_10, wMatrixQ_G₀_11,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, Matrix.empty_val', Matrix.cons_val_fin_one]
  norm_num

/-- **The pin matrix is a rational member at `(G₀,-1/2)`.** -/
theorem relaxMem_pin :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀)
      (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ)
      (t₀ - QMCLeafB.RundataCert.eps G₀) (QMCLeafB.RundataParams.dqShallow G₀) := by
  have hdq := dqShallow_G₀
  have hdqpos : (0 : ℚ) < QMCLeafB.RundataParams.dqShallow G₀ := by rw [hdq]; norm_num
  have e00 : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) 0 0 = 1 := by decide
  have e01 : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = -1 := by decide
  have e10 : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = -1 := by decide
  have e11 : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) 1 1 = 1 := by decide
  refine ⟨hdqpos, ?_, ?_, ?_⟩
  · intro x
    have hq : QMCLeafB.SepOracle.qf (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) x
        = (x 0 - x 1) ^ 2 := by
      rw [QMCLeafB.SepOracle.qf_eq_sum]
      simp only [Fin.sum_univ_two, e00, e01, e10, e11]
      ring
    rw [hq]
    have h1 : (0 : ℚ) ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
    have h2 : (0 : ℚ) ≤ ∑ i : Fin 2, x i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (x i)
    nlinarith
  · intro i
    rw [hdq]
    have hlt : (i : ℕ) < 2 := i.isLt
    have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
    have hdiag : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℚ) i i = 1 := by
      rcases hi with h | h
      · rw [show i = (0 : Fin G₀.n) from Fin.ext (by simpa using h)]
        exact e00
      · rw [show i = (1 : Fin G₀.n) from Fin.ext (by simpa using h)]
        exact e11
    rw [hdiag]
    norm_num
  · rw [hdq, eps_G₀, frob_G₀_pin]
    norm_num [t₀]

/-- **The relaxed body is non-empty at `(G₀,-1/2)`.** -/
theorem not_emptyBody :
    ¬ AsmM8.EmptyBody G₀ t₀ (QMCLeafB.UnionShallow.paramsKbc2 G₀) :=
  QMCLeafB.MechM6.not_emptyBody_of_relaxMem relaxMem_pin

/-- The point is inside the interior bracket. -/
theorem interior_G₀ : AsmM8.Interior G₀ t₀ := by
  refine ⟨?_, ?_⟩
  · rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num [t₀]
  · rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num [t₀]

/-! ## 2.  A non-zero diagonal defect kills the `ok` flag

`okW` requires `dvR = 0` (§4's normal form, `ReachM4.okW_eq_true_iff`), and the interior regime is a
run invariant, so a run with `dvR ≠ 0` throughout never reports `ok`. -/

/-- **`dvR ≠ 0` below the slack ⟹ the flag is `false`.** -/
theorem okW_eq_false_of_dvR (s : RSt)
    (h : ¬ (0 ≤ stT s + QMCLeafB.RoundT.epsOf s)) (hdv : dvR s ≠ 0) :
    QMCLeafB.OkLower.okW s = false := by
  cases hb : QMCLeafB.OkLower.okW s with
  | false => rfl
  | true => exact absurd ((QMCLeafB.ReachM4.okW_eq_true_iff s h).mp hb).1 hdv

/-! ## 3.  The orbit

**The scalar statement.**  `#reduce` confirms it at rounds `0 … 4` and at the fixed point (see the
module docstring); it is the *only* unproved input of the refutation.  Its content is the phase-26
defect: `X₀₀` pins at `10/81` and `X₁₁` dies at `0`, so the diagonal never returns to `1`. -/

/-- The run's diagonal defect never vanishes. -/
def DvNonzero : Prop :=
  ∀ k : ℕ, dvR (QMCLeafB.OkLower.roundW^[k] s₀) ≠ 0

/-- **Every round of the run reports `false`** — from `DvNonzero`. -/
theorem okW_orbit_false (hdv : DvNonzero) (k : ℕ) :
    QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k] s₀) = false :=
  okW_eq_false_of_dvR _
    (QMCLeafB.ReachM4.regime_orbit G₀ t₀ interior_G₀ k) (hdv k)

/-- The same, in the unfolded initial state (the shape `bit0_true_iff` produces). -/
theorem okW_orbit_false' (hdv : DvNonzero) (k : ℕ) :
    QMCLeafB.OkLower.okW (QMCLeafB.OkLower.roundW^[k]
      (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G₀ t₀))) = false :=
  okW_orbit_false hdv k

/-- The same for the diagonal defect, unfolded. -/
theorem dvR_orbit_ne (hdv : DvNonzero) (k : ℕ) :
    dvR (QMCLeafB.OkLower.roundW^[k]
      (QMCLeafB.InitDq.init0 (QMCLeafB.FinalStroke.noTape G₀ t₀))) ≠ 0 :=
  hdv k

/-! ## 4.  The bit is `false`, so `hcomplete` fails -/

/-- **`bit0 G₀ (-1/2) = false`** — at every horizon, in particular at `Tbc2`. -/
theorem bit0_false (hdv : DvNonzero) : QMCLeafB.MechM6.bit0 G₀ t₀ = false := by
  cases hb : QMCLeafB.MechM6.bit0 G₀ t₀ with
  | false => rfl
  | true =>
      obtain ⟨k, _hk, hok⟩ := (QMCLeafB.ReachM4.bit0_true_iff G₀ t₀).mp hb
      rw [okW_orbit_false' hdv k] at hok
      exact absurd hok (by simp)

/-- **THE REFUTATION.**  The campaign's completeness slot fails at the concrete program. -/
theorem hcomplete_false (hdv : DvNonzero) : ¬ QMCLeafB.ReachM4.HComplete := by
  intro hc
  have hb := hc G₀ t₀ (by decide : 2 ≤ G₀.n) interior_G₀ not_emptyBody
  rw [bit0_false hdv] at hb
  exact Bool.noConfusion hb

/-- The same, at `hcomplete`'s own spelling: **`MechM6.leaf_of_hok_and_complete` cannot be fired**. -/
theorem hcomplete_slot_uninhabited (hdv : DvNonzero) :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
        QMCLeafB.MechM6.bit0 G t = true) :=
  hcomplete_false hdv

end QMCLeafB.RefuteM4

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.RefuteM4.eps_G₀
#print axioms QMCLeafB.RefuteM4.dqShallow_G₀
#print axioms QMCLeafB.RefuteM4.wMatrixQ_G₀_01
#print axioms QMCLeafB.RefuteM4.frob_G₀_pin
#print axioms QMCLeafB.RefuteM4.relaxMem_pin
#print axioms QMCLeafB.RefuteM4.not_emptyBody
#print axioms QMCLeafB.RefuteM4.interior_G₀
#print axioms QMCLeafB.RefuteM4.okW_eq_false_of_dvR
#print axioms QMCLeafB.RefuteM4.okW_orbit_false
#print axioms QMCLeafB.RefuteM4.bit0_false
#print axioms QMCLeafB.RefuteM4.hcomplete_false
#print axioms QMCLeafB.RefuteM4.hcomplete_slot_uninhabited



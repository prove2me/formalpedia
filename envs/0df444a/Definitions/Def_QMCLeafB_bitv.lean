-- Prove2me | Definitions.Def_QMCLeafB_bitv
-- name    : QMCLeafB_bitv
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:38:33.330095+00:00
-- url     : https://prove2.me/theorems/34a3b8d7-edcb-4e63-b667-7c0f79b4d1a7
-- title:
--   QMCLeafB bitv
-- statement:
--   # `Check_bitv_m2` — phase 27, member m2, direction `repaired-bit`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_falsify26
import Definitions.Def_QMCLeafB_traj_m3
/-
# `Check_bitv_m2` — phase 27, member m2, direction `repaired-bit`

**The question this file settles.**  Phase 26 (`Check_falsify26_m8`) proved that the frozen campaign
bit `Audit2M5.campaignBit` reads `false` at the sliver `(G₁, t₁)` because the cut normal `diagSignF`
is an `n²`-length matrix code read by `mulVec` as an `n`-vector.  The phase-27 plan is to repair the
direction pipeline (emit a length-`n` normal) and then read the bit again.  **This file machine-checks
that the mechanical repair does not flip the bit**: at the sliver the repaired run is an *exact*
expanding linear map, exits the state's box at round 5, is clipped to the zero matrix, and then cuts
for ever.  `campaignBitV G₁ t₁ = false`, at every horizon.

What is built, in order.

* **§1 The repaired normal `diagVecF`** (length `n`, the diagonal sign vector), its `Poly` fact, its
  reading by `mulVecRaw` — and the defect it repairs, machine-checked in the shape both sides see:
  `diagSignF (2, X)` has length `4`, its first two entries are `(s, 0)`, so `mulVecRaw` acts on the
  first *column* of `X` scaled by `s = sign (1 − X₀₀)`.
* **§2 The repaired round `roundNV`** — `RoundProgram.round` with `oracleR`'s cut branch replaced by
  the length-`n` normal; everything else (Sherman–Morrison `stepFun`, the `α⁻¹ = (n+1)/(n−1)`
  scaling, the box clip + grid snap, the `ok` freeze, the `0`/`1` flag ledger) is the frozen code.
  `campaignBitV` is `loopBit init0 roundNV verdict Tbc2`.
* **§3 THE ONE-STEP FORMULA AT SYMMETRIC STATES.**  At a state whose primal code is `[p,q,q,p]` the
  repaired round is **exactly linear**: `stX (roundNV s) = snap [2p − q, 2q − p, 2q − p, 2p − q]`.
  The diagonal sum `p + q` is invariant and the gap `p − q` **triples** per round.
* **§4 THE ORBIT AT THE SLIVER.**  `(c₀,c₀) → (20,−10,−10,20)/81 → (50,−40,−40,50)/81 →
  (140,−130,−130,140)/81 → (410,−400,−400,410)/81 → 0`, and `0` is absorbing (`σ = 0 ⟹ μ = 0`).
* **§5 THE BIT.**  Every round is a cut (`dvR ≠ 0` at every orbit state), so the `ok` ledger is
  `replicate T false`, so `verdict = false` at every horizon; hence `campaignBitV G₁ t₁ = false`.
* **§6 WHY, STRUCTURALLY.**  (i) The `ok` branch of the repaired round still *requires* `dvR = 0`,
  i.e. an exactly unit-diagonal primal code — the mechanical repair cannot touch the stop test, and
  on `dvR = 0` the repaired and frozen rounds are the *same* function (`roundNV_eq_round_of_dvR_zero`).
  (ii) At the sliver, an exactly unit-diagonal **member** is strictly non-positive-semidefinite
  (`member_neg_qf`: `qf Q 1 < 0`), so `no_member_of_psd_unitdiag`: no PSD unit-diagonal centre is a
  member.  A run whose centre is a PSD-normalised iterate can therefore never certify an `ok` round
  at the sliver — the read-`true` there needs an *outward*, non-PSD centre.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, expected `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.BitVM2

open QuantumMaxCutEnergy

/-! ## 0.  The sliver's names -/

abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.Falsify26M8.G₁
abbrev t₁ : ℚ := QMCLeafB.Falsify26M8.t₁
abbrev M₀ : ℚ := QMCLeafB.Falsify26M8.M₀
abbrev c₀ : ℚ := QMCLeafB.Falsify26M8.c₀
abbrev p₀ : (QuantumMaxCutEnergy.Input × List Bool) × ℚ := QMCLeafB.Falsify26M8.p₀
abbrev s0 : QMCLeafB.RoundProgram.RSt := QMCLeafB.Falsify26M8.s0
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁
abbrev Tm : ℕ := QMCLeafB.Falsify26M8.Tm

theorem range_two : (List.range 2) = [0, 1] := by decide

/-! ## 1.  The repaired normal: length `n`, not `n²` -/

/-- **The repaired cut normal**: the diagonal sign *vector*. -/
def diagVecF (p : ℕ × List ℚ) : List ℚ :=
  (QMCLeafB.RoundProgram.idxs p).map
    (fun i => QMCLeafB.RoundProgram.sgnOf (1 - QMCLeafB.RoundProgram.entV p i i))

/-- At a `2 × 2` code the repaired normal is the pair of diagonal signs. -/
theorem diagVecF_two (a b c d : ℚ) :
    diagVecF (2, [a, b, c, d])
      = [QMCLeafB.RoundProgram.sgnOf (1 - a), QMCLeafB.RoundProgram.sgnOf (1 - d)] := by
  unfold diagVecF QMCLeafB.RoundProgram.idxs QMCLeafB.RoundProgram.entV
  simp [range_two]

/-- **The defect, in the shape both sides see**: the frozen normal has length `n² = 4`. -/
theorem diagSignF_length_four (a b c d : ℚ) :
    (QMCLeafB.RoundProgram.diagSignF (2, [a, b, c, d])).length = 4 := by
  unfold QMCLeafB.RoundProgram.diagSignF QMCLeafB.RoundProgram.idxs
    QMCLeafB.RoundProgram.entV
  simp [range_two]

/-- The frozen normal's code, entry by entry: `[s, 0, 0, s']`. -/
theorem diagSignF_four (a b c d : ℚ) :
    QMCLeafB.RoundProgram.diagSignF (2, [a, b, c, d])
      = [QMCLeafB.RoundProgram.sgnOf (1 - a), 0, 0, QMCLeafB.RoundProgram.sgnOf (1 - d)] := by
  unfold QMCLeafB.RoundProgram.diagSignF QMCLeafB.RoundProgram.idxs
    QMCLeafB.RoundProgram.entV
  simp [range_two]

/-- The first `n = 2` entries of the frozen normal: the first diagonal's sign and a **zero**. -/
theorem diagSignF_take_two (a b c d : ℚ) :
    (QMCLeafB.RoundProgram.diagSignF (2, [a, b, c, d])).take 2
      = [QMCLeafB.RoundProgram.sgnOf (1 - a), 0] := by
  rw [diagSignF_four]
  rfl

/-- **`mulVec` of a length-`n` normal is the matrix–vector product.** -/
theorem mulVecRaw_vec (p q r v0 v1 : ℚ) :
    MatQ.Runtime.mulVecRaw (2, ([p, q, q, r], [v0, v1]))
      = [p * v0 + q * v1, q * v0 + r * v1] := by
  simp [MatQ.Runtime.mulVecRaw, range_two]

/-- **What the frozen pipeline actually computed**: only the first *column* of `X`, scaled by the
first diagonal's sign. -/
theorem mulVecRaw_diagSignF (a b c d : ℚ) :
    MatQ.Runtime.mulVecRaw (2, ([a, b, c, d],
        QMCLeafB.RoundProgram.diagSignF (2, [a, b, c, d])))
      = [a * QMCLeafB.RoundProgram.sgnOf (1 - a), c * QMCLeafB.RoundProgram.sgnOf (1 - a)] := by
  rw [diagSignF_four]
  simp [MatQ.Runtime.mulVecRaw, range_two]

/-- The repaired normal is still a program. -/
theorem poly_diagVecF : Poly diagVecF := by
  unfold diagVecF
  have hf : Poly (fun x : (ℕ × List ℚ) × ℕ =>
      QMCLeafB.RoundProgram.sgnOf (1 - QMCLeafB.RoundProgram.entV x.1 x.2 x.2)) := by
    have he : Poly (fun x : (ℕ × List ℚ) × ℕ =>
        QMCLeafB.RoundProgram.entV x.1 x.2 x.2) :=
      Poly.comp (f := fun z : (ℕ × List ℚ) × ℕ => QMCLeafB.RoundProgram.entV z.1 z.2 z.2)
        (g := fun x : (ℕ × List ℚ) × ℕ => x) QMCLeafB.RoundProgram.poly_entV2 (by fun_prop)
    have hsub : Poly (fun x : (ℕ × List ℚ) × ℕ =>
        (1 : ℚ) - QMCLeafB.RoundProgram.entV x.1 x.2 x.2) := by
      have hp : Poly (fun x : (ℕ × List ℚ) × ℕ =>
          ((1 : ℚ), QMCLeafB.RoundProgram.entV x.1 x.2 x.2)) :=
        Poly.pair (Automatic.Poly.const 1) he
      exact Poly.comp (f := fun w : ℚ × ℚ => w.1 - w.2)
        (g := fun x : (ℕ × List ℚ) × ℕ =>
          ((1 : ℚ), QMCLeafB.RoundProgram.entV x.1 x.2 x.2)) Poly.rat_sub hp
    exact Poly.comp (f := QMCLeafB.RoundProgram.sgnOf)
      (g := fun x : (ℕ × List ℚ) × ℕ =>
        1 - QMCLeafB.RoundProgram.entV x.1 x.2 x.2)
      QMCLeafB.RoundProgram.poly_sgnOf hsub
  exact Poly.list_map (f := fun (p : ℕ × List ℚ) (i : ℕ) =>
      QMCLeafB.RoundProgram.sgnOf (1 - QMCLeafB.RoundProgram.entV p i i))
    (as := fun p : ℕ × List ℚ => QMCLeafB.RoundProgram.idxs p) hf
    QMCLeafB.RoundProgram.poly_idxs

/-! ## 2.  The repaired round -/

/-- **The repaired oracle**: diagonal repair first, threshold branch second, as `oracleR`. -/
def oracleNV (s : QMCLeafB.RoundProgram.RSt) : Bool × List ℚ :=
  if QMCLeafB.RoundProgram.dvR s = 0 then QMCLeafB.RoundProgram.threshB s
  else (true, diagVecF (QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s))

/-- The Sherman–Morrison output under the repaired oracle. -/
noncomputable def stepYV (s : QMCLeafB.RoundProgram.RSt) : List ℚ :=
  QMCLeafB.MatQUpdate.Step.stepFun
    ((QMCLeafB.RoundProgram.stN s, QMCLeafB.RoundProgram.stX s),
      ((oracleNV s).2,
        QMCLeafB.RoundProgram.lamOf
          (QMCLeafB.RoundProgram.stN s,
            (QMCLeafB.RoundProgram.stX s, (oracleNV s).2))))

/-- The depth-`1` GLS scaling. -/
noncomputable def scaleYV (s : QMCLeafB.RoundProgram.RSt) : List ℚ :=
  QMCLeafB.MatQUpdate.smulRaw
    ((QMCLeafB.RoundProgram.stN s, stepYV s), QMCLeafB.RoundProgram.alphInv
      (QMCLeafB.RoundProgram.stN s))

/-- The clip into the state's box, then the grid snap. -/
noncomputable def snapYV (s : QMCLeafB.RoundProgram.RSt) : List ℚ :=
  QMCLeafB.RoundProgram.nrmRow (QMCLeafB.RoundProgram.stMu s)
    (QMCLeafB.RoundProgram.stD s) (scaleYV s)

/-- The cut branch under the repaired oracle. -/
noncomputable def roundCutNV (s : QMCLeafB.RoundProgram.RSt) : QMCLeafB.RoundProgram.RSt :=
  QMCLeafB.RoundProgram.mkSt (QMCLeafB.RoundProgram.stN s) (QMCLeafB.RoundProgram.stA s)
    (snapYV s) (QMCLeafB.RoundProgram.stT s) (QMCLeafB.RoundProgram.stMu s)
    (QMCLeafB.RoundProgram.stD s) (QMCLeafB.RoundProgram.stOks s ++ [false]) (oracleNV s).2

/-- **The repaired round.** -/
noncomputable def roundNV (s : QMCLeafB.RoundProgram.RSt) : QMCLeafB.RoundProgram.RSt :=
  if (oracleNV s).1 then roundCutNV s else QMCLeafB.RoundProgram.roundOk s

theorem roundNV_eq (s : QMCLeafB.RoundProgram.RSt) :
    roundNV s = if (oracleNV s).1 then roundCutNV s else QMCLeafB.RoundProgram.roundOk s := rfl

/-- **The repaired campaign bit**: the frozen loop with the repaired round. -/
noncomputable def campaignBitV : QuantumMaxCutEnergy.Input → ℚ → Bool :=
  QMCLeafB.FinalStroke.loopBit QMCLeafB.InitDq.init0 roundNV QMCLeafB.RoundProgram.verdict
    (fun G' _ => QMCLeafB.UnionShallow.Kbc2
      (QMCLeafB.HalvePerG.mHalve (G'.n * G'.n)) G'
      * QMCLeafB.HalvePerG.mHalve (G'.n * G'.n))

/-! ### 2.1  The state's own fields are frozen by every round -/

theorem stN_roundNV (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stN (roundNV s) = QMCLeafB.RoundProgram.stN s := by
  rw [roundNV_eq]; split <;> rfl

theorem stA_roundNV (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (roundNV s) = QMCLeafB.RoundProgram.stA s := by
  rw [roundNV_eq]; split <;> rfl

theorem stT_roundNV (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (roundNV s) = QMCLeafB.RoundProgram.stT s := by
  rw [roundNV_eq]; split <;> rfl

theorem stMu_roundNV (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stMu (roundNV s) = QMCLeafB.RoundProgram.stMu s := by
  rw [roundNV_eq]; split <;> rfl

theorem stD_roundNV (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stD (roundNV s) = QMCLeafB.RoundProgram.stD s := by
  rw [roundNV_eq]; split <;> rfl

theorem stOks_roundNV_cut {s : QMCLeafB.RoundProgram.RSt}
    (h : (oracleNV s).1 = true) :
    QMCLeafB.RoundProgram.stOks (roundNV s) = QMCLeafB.RoundProgram.stOks s ++ [false] := by
  rw [roundNV_eq, if_pos h]
  rfl

theorem stX_roundNV_cut {s : QMCLeafB.RoundProgram.RSt}
    (h : (oracleNV s).1 = true) :
    QMCLeafB.RoundProgram.stX (roundNV s) = snapYV s := by
  rw [roundNV_eq, if_pos h]
  rfl

/-! ### 2.2  `dvR` on a symmetric code -/

theorem dvR_sym_state {A : List ℚ} {τ M : ℚ} {d : ℕ} {oks : List Bool} {rec : List ℚ}
    {p q : ℚ} :
    QMCLeafB.RoundProgram.dvR (QMCLeafB.RoundProgram.mkSt 2 A [p, q, q, p] τ M d oks rec)
      = QMCLeafB.RoundProgram.absq (p - 1) + QMCLeafB.RoundProgram.absq (p - 1) := by
  unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
  simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
  rw [show QMCLeafB.RoundProgram.idxs (2, [p, q, q, p]) = [0, 1] by
    simp [QMCLeafB.RoundProgram.idxs, range_two]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    QMCLeafB.RoundProgram.entV, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceMul, zero_add]
  ring

theorem dvR_zero_state {A : List ℚ} {τ M : ℚ} {d : ℕ} {oks : List Bool} {rec : List ℚ} :
    QMCLeafB.RoundProgram.dvR (QMCLeafB.RoundProgram.mkSt 2 A [0, 0, 0, 0] τ M d oks rec)
      = 2 := by
  unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
  simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
  rw [show QMCLeafB.RoundProgram.idxs (2, [0, 0, 0, 0]) = [0, 1] by
    simp [QMCLeafB.RoundProgram.idxs, range_two]]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    QMCLeafB.RoundProgram.entV, List.getD_cons_zero, List.getD_cons_succ,
    Nat.reduceAdd, Nat.reduceMul, zero_add]
  unfold QMCLeafB.RoundProgram.absq
  norm_num

/-- `dvR ≠ 0` at a symmetric code with `p ≠ 1`. -/
theorem dvR_sym_ne {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ p q : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [p, q, q, p]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (hp : p ≠ 1) : QMCLeafB.RoundProgram.dvR s ≠ 0 := by
  rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD, dvR_sym_state]
  have h0 : p - 1 ≠ 0 := sub_ne_zero.mpr hp
  have hpos : 0 < QMCLeafB.RoundProgram.absq (p - 1) :=
    QMCLeafB.Falsify26M8.absq_pos_of_ne h0
  have hnn : 0 ≤ QMCLeafB.RoundProgram.absq (p - 1) := le_of_lt hpos
  intro h
  linarith

/-! ## 3.  The one-step formula at a symmetric state -/

/-- `smulRaw` of a four-entry code. -/
theorem smulRaw_four (a b c d t : ℚ) :
    QMCLeafB.MatQUpdate.smulRaw ((2, [a, b, c, d]), t) = [t * a, t * b, t * c, t * d] := by
  unfold QMCLeafB.MatQUpdate.smulRaw
  simp [range_two]

/-- `updFun` of a four-entry code against a two-vector. -/
theorem updFun_four (p q r w0 w1 μ : ℚ) :
    QMCLeafB.MatQUpdate.Upd.updFun ((2, [p, q, q, r]), ([w0, w1], μ))
      = [p - μ * w0 * w0, q - μ * w0 * w1, q - μ * w1 * w0, r - μ * w1 * w1] := by
  unfold QMCLeafB.MatQUpdate.Upd.updFun QMCLeafB.MatQUpdate.Upd.rowFun
  simp [range_two]

/-- **The step machine at a four-entry code.** -/
theorem stepFun_four (p q r v0 v1 lam : ℚ) :
    QMCLeafB.MatQUpdate.Step.stepFun ((2, [p, q, q, r]), ([v0, v1], lam))
      = [p - (lam / (1 + lam * (v0 * (p * v0 + q * v1) + v1 * (q * v0 + r * v1))))
            * (p * v0 + q * v1) * (p * v0 + q * v1),
         q - (lam / (1 + lam * (v0 * (p * v0 + q * v1) + v1 * (q * v0 + r * v1))))
            * (p * v0 + q * v1) * (q * v0 + r * v1),
         q - (lam / (1 + lam * (v0 * (p * v0 + q * v1) + v1 * (q * v0 + r * v1))))
            * (q * v0 + r * v1) * (p * v0 + q * v1),
         r - (lam / (1 + lam * (v0 * (p * v0 + q * v1) + v1 * (q * v0 + r * v1))))
            * (q * v0 + r * v1) * (q * v0 + r * v1)] := by
  rw [QMCLeafB.Falsify26M8.stepFun_form, mulVecRaw_vec]
  have hzip : ((([v0, v1] : List ℚ).zip [p * v0 + q * v1, q * v0 + r * v1]).map
      (fun z : ℚ × ℚ => z.1 * z.2)).sum
      = v0 * (p * v0 + q * v1) + v1 * (q * v0 + r * v1) := by
    simp
  rw [hzip, updFun_four]

/-- `v² = 1` from `v·v = 1`. -/
theorem sq_of_mul (v : ℚ) (hv : v * v = 1) : v ^ 2 = 1 := by
  rw [pow_two]; exact hv

/-- `σ = cᵀ X c` at a symmetric code with the symmetric normal. -/
theorem sigOf_sym (p q v : ℚ) :
    QMCLeafB.RoundProgram.sigOf (2, ([p, q, q, p], [v, v]))
      = v * (p * v + q * v) + v * (q * v + p * v) := by
  unfold QMCLeafB.RoundProgram.sigOf QMCLeafB.RoundProgram.dotZ
  rw [mulVecRaw_vec]
  simp [List.sum_cons, List.sum_nil]

/-- `σ = 2(p+q)` at a symmetric code with a unit normal. -/
theorem sigOf_sym_eq (p q v : ℚ) (hv : v * v = 1) :
    v * (p * v + q * v) + v * (q * v + p * v) = 2 * (p + q) := by
  have hv2 : v ^ 2 = 1 := sq_of_mul v hv
  calc v * (p * v + q * v) + v * (q * v + p * v)
      = v ^ 2 * (p + q) + v ^ 2 * (q + p) := by ring
    _ = 2 * (p + q) := by rw [hv2]; ring

/-- `λ = β/σ = 1/(p+q)` at a symmetric code with a unit normal. -/
theorem lamOf_sym (p q v : ℚ) (hv : v * v = 1) (hsum : p + q ≠ 0) :
    QMCLeafB.RoundProgram.lamOf (2, ([p, q, q, p], [v, v])) = 1 / (p + q) := by
  unfold QMCLeafB.RoundProgram.lamOf QMCLeafB.RoundProgram.betaOf
  rw [sigOf_sym, sigOf_sym_eq p q v hv]
  norm_num
  field_simp

/-- `μ = λ/(1+λσ) = 1/(3(p+q))`. -/
theorem mu_sym (p q : ℚ) (hsum : p + q ≠ 0) :
    (1 / (p + q)) / (1 + (1 / (p + q)) * (2 * (p + q))) = 1 / (3 * (p + q)) := by
  have h2 : (1 : ℚ) + (1 / (p + q)) * (2 * (p + q)) = 3 := by
    field_simp
    norm_num
  rw [h2]
  field_simp

/-- The diagonal entry after the `α⁻¹ = 3` scaling: `3 (p − (p+q)²/(3(p+q))) = 2p − q`. -/
theorem entry_sym (p q v : ℚ) (hv : v * v = 1) (hsum : p + q ≠ 0) :
    3 * (p - (1 / (3 * (p + q))) * (p * v + q * v) * (p * v + q * v)) = 2 * p - q := by
  have hv2 : v ^ 2 = 1 := sq_of_mul v hv
  have hw : p * v + q * v = v * (p + q) := by ring
  have hkey : (p * v + q * v) * (p * v + q * v) = (p + q) * (p + q) := by
    rw [hw]
    rw [show v * (p + q) * (v * (p + q)) = v ^ 2 * ((p + q) * (p + q)) by ring]
    rw [hv2]; ring
  rw [show (1 / (3 * (p + q))) * (p * v + q * v) * (p * v + q * v)
      = (1 / (3 * (p + q))) * ((p * v + q * v) * (p * v + q * v)) by ring]
  rw [hkey]
  field_simp
  try ring

/-- The off-diagonal entries after the scaling. -/
theorem entry_sym_off (p q v : ℚ) (hv : v * v = 1) (hsum : p + q ≠ 0) :
    3 * (q - (1 / (3 * (p + q))) * (p * v + q * v) * (q * v + p * v)) = 2 * q - p := by
  have hv2 : v ^ 2 = 1 := sq_of_mul v hv
  have hw : p * v + q * v = v * (p + q) := by ring
  have hw2 : q * v + p * v = v * (p + q) := by ring
  have hkey : (p * v + q * v) * (q * v + p * v) = (p + q) * (p + q) := by
    rw [hw, hw2]
    rw [show v * (p + q) * (v * (p + q)) = v ^ 2 * ((p + q) * (p + q)) by ring]
    rw [hv2]; ring
  rw [show (1 / (3 * (p + q))) * (p * v + q * v) * (q * v + p * v)
      = (1 / (3 * (p + q))) * ((p * v + q * v) * (q * v + p * v)) by ring]
  rw [hkey]
  field_simp
  try ring

/-- The off-diagonal entries after the scaling, in the swapped association the machine produces for
the `(1,0)` entry. -/
theorem entry_sym_off' (p q v : ℚ) (hv : v * v = 1) (hsum : p + q ≠ 0) :
    3 * (q - (1 / (3 * (p + q))) * (q * v + p * v) * (p * v + q * v)) = 2 * q - p := by
  have hv2 : v ^ 2 = 1 := sq_of_mul v hv
  have hw : p * v + q * v = v * (p + q) := by ring
  have hw2 : q * v + p * v = v * (p + q) := by ring
  have hkey : (q * v + p * v) * (p * v + q * v) = (p + q) * (p + q) := by
    rw [hw, hw2]
    rw [show v * (p + q) * (v * (p + q)) = v ^ 2 * ((p + q) * (p + q)) by ring]
    rw [hv2]; ring
  rw [show (1 / (3 * (p + q))) * (q * v + p * v) * (p * v + q * v)
      = (1 / (3 * (p + q))) * ((q * v + p * v) * (p * v + q * v)) by ring]
  rw [hkey]
  field_simp
  try ring

/-! ### 3.1  The cut branch at a symmetric state -/

/-- **THE REPAIRED CUT STEP.**  At a state whose primal code is `[p,q,q,p]`, whose oracle answers
with the symmetric length-`n` normal `(v,v)` (`v = ±1`), the round's new primal code is
`snap [2p − q, 2q − p, 2q − p, 2p − q]` — **exactly linear in `(p,q)` before the snap**. -/
theorem roundNV_cut_sym {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ p q v : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [p, q, q, p]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (hv : v * v = 1) (hsum : p + q ≠ 0)
    (hor : oracleNV s = (true, [v, v])) :
    QMCLeafB.RoundProgram.stX (roundNV s)
      = [QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * p - q),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * q - p),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * q - p),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * p - q)] := by
  have h1 : (oracleNV s).1 = true := by rw [hor]
  have hcut : QMCLeafB.RoundProgram.stX (roundNV s) = snapYV s := stX_roundNV_cut h1
  rw [hcut]
  unfold snapYV scaleYV stepYV
  rw [hN, hX, hor]
  rw [lamOf_sym p q v hv hsum]
  rw [stepFun_four]
  rw [sigOf_sym_eq p q v hv]
  rw [mu_sym p q hsum]
  rw [hMu, hD]
  rw [show QMCLeafB.RoundProgram.alphInv 2 = 3 from QMCLeafB.Falsify26M8.alphInv_two]
  rw [smulRaw_four]
  unfold QMCLeafB.RoundProgram.nrmRow
  simp only [List.map_cons, List.map_nil]
  rw [entry_sym p q v hv hsum, entry_sym_off p q v hv hsum]
  rw [entry_sym_off' p q v hv hsum]
  rw [show 3 * (p - (1 / (3 * (p + q))) * (q * v + p * v) * (q * v + p * v)) = 2 * p - q from by
    have hv2 : v ^ 2 = 1 := sq_of_mul v hv
    have hw : q * v + p * v = v * (p + q) := by ring
    have hkey : (q * v + p * v) * (q * v + p * v) = (p + q) * (p + q) := by
      rw [hw]
      rw [show v * (p + q) * (v * (p + q)) = v ^ 2 * ((p + q) * (p + q)) by ring]
      rw [hv2]; ring
    rw [show (1 / (3 * (p + q))) * (q * v + p * v) * (q * v + p * v)
        = (1 / (3 * (p + q))) * ((q * v + p * v) * (q * v + p * v)) by ring]
    rw [hkey]
    field_simp
    try ring]

/-- **THE ONE-STEP FORMULA AT A SYMMETRIC STATE** (the repaired analogue of
`Falsify26M8.round_diag`): `[p,q,q,p] ↦ snap [2p − q, 2q − p, 2q − p, 2p − q]`. -/
theorem roundNV_pq {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ p q : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [p, q, q, p]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (hp : p ≠ 1) (hsum : p + q ≠ 0) :
    QMCLeafB.RoundProgram.stX (roundNV s)
      = [QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * p - q),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * q - p),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * q - p),
         QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * p - q)] := by
  have hdv : QMCLeafB.RoundProgram.dvR s ≠ 0 := dvR_sym_ne hN hA hX hT hMu hD hp
  rcases lt_or_gt_of_ne hp with hp' | hp'
  · have hsign : QMCLeafB.RoundProgram.sgnOf (1 - p) = 1 := by
      unfold QMCLeafB.RoundProgram.sgnOf
      rw [if_neg (by linarith : ¬ (1 - p < 0)), if_neg (by linarith : ¬ (1 - p = 0))]
    refine roundNV_cut_sym hN hA hX hT hMu hD (v := 1) (by norm_num) hsum ?_
    unfold oracleNV
    rw [if_neg hdv]
    rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD]
    simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
    rw [diagVecF_two, hsign]
  · have hsign : QMCLeafB.RoundProgram.sgnOf (1 - p) = -1 := by
      unfold QMCLeafB.RoundProgram.sgnOf
      rw [if_pos (by linarith : 1 - p < 0)]
    refine roundNV_cut_sym hN hA hX hT hMu hD (v := -1) (by norm_num) hsum ?_
    unfold oracleNV
    rw [if_neg hdv]
    rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD]
    simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
    rw [diagVecF_two, hsign]

/-- **THE LINEAR STRUCTURE.**  The repaired round's exact (pre-snap) map keeps the diagonal sum and
**triples** the gap: the iterate runs to the box wall geometrically. -/
theorem sum_invariant (p q : ℚ) : (2 * p - q) + (2 * q - p) = p + q := by ring

theorem gap_triples (p q : ℚ) : (2 * p - q) - (2 * q - p) = 3 * (p - q) := by ring

/-! ## 4.  The orbit at the sliver -/

/-- One repaired round. -/
def rndV : QMCLeafB.RoundProgram.RSt → QMCLeafB.RoundProgram.RSt := roundNV

theorem stN_iterV (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stN (rndV^[T] s) = QMCLeafB.RoundProgram.stN s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stN (roundNV (rndV^[k] s)) = QMCLeafB.RoundProgram.stN s
      rw [stN_roundNV, ih]

theorem stA_iterV (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (rndV^[T] s) = QMCLeafB.RoundProgram.stA s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stA (roundNV (rndV^[k] s)) = QMCLeafB.RoundProgram.stA s
      rw [stA_roundNV, ih]

theorem stT_iterV (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (rndV^[T] s) = QMCLeafB.RoundProgram.stT s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stT (roundNV (rndV^[k] s)) = QMCLeafB.RoundProgram.stT s
      rw [stT_roundNV, ih]

theorem stMu_iterV (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stMu (rndV^[T] s) = QMCLeafB.RoundProgram.stMu s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stMu (roundNV (rndV^[k] s)) = QMCLeafB.RoundProgram.stMu s
      rw [stMu_roundNV, ih]

theorem stD_iterV (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stD (rndV^[T] s) = QMCLeafB.RoundProgram.stD s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stD (roundNV (rndV^[k] s)) = QMCLeafB.RoundProgram.stD s
      rw [stD_roundNV, ih]

/-! ### 4.1  The grid-snap evaluations at the orbit's numbers -/

theorem nrmQ_2c₀ : QMCLeafB.RoundProgram.nrmQ M₀ 81 (2 * c₀) = 20 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, c₀, QMCLeafB.Falsify26M8.M₀,
    QMCLeafB.Falsify26M8.c₀]

theorem nrmQ_neg_c₀ : QMCLeafB.RoundProgram.nrmQ M₀ 81 (-c₀) = -(10 / 81) := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_neg, M₀, c₀, QMCLeafB.Falsify26M8.M₀,
    QMCLeafB.Falsify26M8.c₀]

theorem nrmQ_50_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (50 / 81) = 50 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_neg_40_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (-(40 / 81)) = -(40 / 81) := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_neg, M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_140_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (140 / 81) = 140 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_neg_130_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (-(130 / 81)) = -(130 / 81) := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_neg, M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_410_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (410 / 81) = 410 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_neg_400_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (-(400 / 81)) = -(400 / 81) := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_neg, M₀, QMCLeafB.Falsify26M8.M₀]

/-- **The box clip fires at round 5**: `1220/81 > M = 2n² + 2dq²`, so the entry is clipped to `0`. -/
theorem nrmQ_box_hi : QMCLeafB.RoundProgram.nrmQ M₀ 81 (1220 / 81) = 0 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, QMCLeafB.Falsify26M8.snapTrunc_zero,
    M₀, QMCLeafB.Falsify26M8.M₀]

theorem nrmQ_box_lo : QMCLeafB.RoundProgram.nrmQ M₀ 81 (-(1210 / 81)) = 0 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat
    QMCLeafB.RoundProgram.inBoxR QMCLeafB.RoundPolySnap.snapDiv
  norm_num [QMCLeafB.RoundPolySnap.snapTrunc_of_neg, QMCLeafB.Falsify26M8.snapTrunc_zero,
    M₀, QMCLeafB.Falsify26M8.M₀]

/-! ### 4.2  The orbit -/

theorem orbitV1 : QMCLeafB.RoundProgram.stX (rndV^[1] s0)
    = [20 / 81, -(10 / 81), -(10 / 81), 20 / 81] := by
  have h := roundNV_pq (s := s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (p := c₀) (q := 0) QMCLeafB.Falsify26M8.stN_s0 rfl QMCLeafB.Falsify26M8.stX_s0
    QMCLeafB.Falsify26M8.stT_s0 QMCLeafB.Falsify26M8.stMu_s0 QMCLeafB.Falsify26M8.stD_s0
    (by norm_num [c₀, QMCLeafB.Falsify26M8.c₀]) (by norm_num [c₀, QMCLeafB.Falsify26M8.c₀])
  show QMCLeafB.RoundProgram.stX (roundNV s0) = _
  rw [h, show (2 * c₀ - 0 : ℚ) = 2 * c₀ by ring, show (2 * 0 - c₀ : ℚ) = -c₀ by ring,
    nrmQ_2c₀, nrmQ_neg_c₀]

theorem stN_V1 : QMCLeafB.RoundProgram.stN (rndV^[1] s0) = 2 := by
  rw [stN_iterV, QMCLeafB.Falsify26M8.stN_s0]

theorem stA_V1 : QMCLeafB.RoundProgram.stA (rndV^[1] s0) = QMCLeafB.RoundProgram.stA s0 :=
  stA_iterV 1 s0

theorem stT_V1 : QMCLeafB.RoundProgram.stT (rndV^[1] s0) = t₁ := by
  rw [stT_iterV, QMCLeafB.Falsify26M8.stT_s0]

theorem stMu_V1 : QMCLeafB.RoundProgram.stMu (rndV^[1] s0) = M₀ := by
  rw [stMu_iterV, QMCLeafB.Falsify26M8.stMu_s0]

theorem stD_V1 : QMCLeafB.RoundProgram.stD (rndV^[1] s0) = 81 := by
  rw [stD_iterV, QMCLeafB.Falsify26M8.stD_s0]

theorem orbitV2 : QMCLeafB.RoundProgram.stX (rndV^[2] s0)
    = [50 / 81, -(40 / 81), -(40 / 81), 50 / 81] := by
  have h := roundNV_pq (s := rndV^[1] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (p := 20 / 81) (q := -(10 / 81)) stN_V1 stA_V1 orbitV1 stT_V1 stMu_V1 stD_V1
    (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (roundNV (rndV^[1] s0)) = _
  rw [h, show (2 * (20 / 81) - (-(10 / 81)) : ℚ) = 50 / 81 by norm_num,
    show (2 * (-(10 / 81)) - (20 / 81) : ℚ) = -(40 / 81) by norm_num,
    nrmQ_50_81, nrmQ_neg_40_81]

theorem stN_V2 : QMCLeafB.RoundProgram.stN (rndV^[2] s0) = 2 := by
  rw [stN_iterV, QMCLeafB.Falsify26M8.stN_s0]

theorem stA_V2 : QMCLeafB.RoundProgram.stA (rndV^[2] s0) = QMCLeafB.RoundProgram.stA s0 :=
  stA_iterV 2 s0

theorem stT_V2 : QMCLeafB.RoundProgram.stT (rndV^[2] s0) = t₁ := by
  rw [stT_iterV, QMCLeafB.Falsify26M8.stT_s0]

theorem stMu_V2 : QMCLeafB.RoundProgram.stMu (rndV^[2] s0) = M₀ := by
  rw [stMu_iterV, QMCLeafB.Falsify26M8.stMu_s0]

theorem stD_V2 : QMCLeafB.RoundProgram.stD (rndV^[2] s0) = 81 := by
  rw [stD_iterV, QMCLeafB.Falsify26M8.stD_s0]

theorem orbitV3 : QMCLeafB.RoundProgram.stX (rndV^[3] s0)
    = [140 / 81, -(130 / 81), -(130 / 81), 140 / 81] := by
  have h := roundNV_pq (s := rndV^[2] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (p := 50 / 81) (q := -(40 / 81)) stN_V2 stA_V2 orbitV2 stT_V2 stMu_V2 stD_V2
    (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (roundNV (rndV^[2] s0)) = _
  rw [h, show (2 * (50 / 81) - (-(40 / 81)) : ℚ) = 140 / 81 by norm_num,
    show (2 * (-(40 / 81)) - (50 / 81) : ℚ) = -(130 / 81) by norm_num,
    nrmQ_140_81, nrmQ_neg_130_81]

theorem stN_V3 : QMCLeafB.RoundProgram.stN (rndV^[3] s0) = 2 := by
  rw [stN_iterV, QMCLeafB.Falsify26M8.stN_s0]

theorem stA_V3 : QMCLeafB.RoundProgram.stA (rndV^[3] s0) = QMCLeafB.RoundProgram.stA s0 :=
  stA_iterV 3 s0

theorem stT_V3 : QMCLeafB.RoundProgram.stT (rndV^[3] s0) = t₁ := by
  rw [stT_iterV, QMCLeafB.Falsify26M8.stT_s0]

theorem stMu_V3 : QMCLeafB.RoundProgram.stMu (rndV^[3] s0) = M₀ := by
  rw [stMu_iterV, QMCLeafB.Falsify26M8.stMu_s0]

theorem stD_V3 : QMCLeafB.RoundProgram.stD (rndV^[3] s0) = 81 := by
  rw [stD_iterV, QMCLeafB.Falsify26M8.stD_s0]

theorem orbitV4 : QMCLeafB.RoundProgram.stX (rndV^[4] s0)
    = [410 / 81, -(400 / 81), -(400 / 81), 410 / 81] := by
  have h := roundNV_pq (s := rndV^[3] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (p := 140 / 81) (q := -(130 / 81)) stN_V3 stA_V3 orbitV3 stT_V3 stMu_V3 stD_V3
    (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (roundNV (rndV^[3] s0)) = _
  rw [h, show (2 * (140 / 81) - (-(130 / 81)) : ℚ) = 410 / 81 by norm_num,
    show (2 * (-(130 / 81)) - (140 / 81) : ℚ) = -(400 / 81) by norm_num,
    nrmQ_410_81, nrmQ_neg_400_81]

theorem stN_V4 : QMCLeafB.RoundProgram.stN (rndV^[4] s0) = 2 := by
  rw [stN_iterV, QMCLeafB.Falsify26M8.stN_s0]

theorem stA_V4 : QMCLeafB.RoundProgram.stA (rndV^[4] s0) = QMCLeafB.RoundProgram.stA s0 :=
  stA_iterV 4 s0

theorem stT_V4 : QMCLeafB.RoundProgram.stT (rndV^[4] s0) = t₁ := by
  rw [stT_iterV, QMCLeafB.Falsify26M8.stT_s0]

theorem stMu_V4 : QMCLeafB.RoundProgram.stMu (rndV^[4] s0) = M₀ := by
  rw [stMu_iterV, QMCLeafB.Falsify26M8.stMu_s0]

theorem stD_V4 : QMCLeafB.RoundProgram.stD (rndV^[4] s0) = 81 := by
  rw [stD_iterV, QMCLeafB.Falsify26M8.stD_s0]

/-- **The box exit**: both entries are clipped to `0`. -/
theorem orbitV5 : QMCLeafB.RoundProgram.stX (rndV^[5] s0) = [0, 0, 0, 0] := by
  have h := roundNV_pq (s := rndV^[4] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (p := 410 / 81) (q := -(400 / 81)) stN_V4 stA_V4 orbitV4 stT_V4 stMu_V4 stD_V4
    (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (roundNV (rndV^[4] s0)) = _
  rw [h, show (2 * (410 / 81) - (-(400 / 81)) : ℚ) = 1220 / 81 by norm_num,
    show (2 * (-(400 / 81)) - (410 / 81) : ℚ) = -(1210 / 81) by norm_num,
    nrmQ_box_hi, nrmQ_box_lo]

theorem stN_V5 : QMCLeafB.RoundProgram.stN (rndV^[5] s0) = 2 := by
  rw [stN_iterV, QMCLeafB.Falsify26M8.stN_s0]

theorem stA_V5 : QMCLeafB.RoundProgram.stA (rndV^[5] s0) = QMCLeafB.RoundProgram.stA s0 :=
  stA_iterV 5 s0

theorem stT_V5 : QMCLeafB.RoundProgram.stT (rndV^[5] s0) = t₁ := by
  rw [stT_iterV, QMCLeafB.Falsify26M8.stT_s0]

theorem stMu_V5 : QMCLeafB.RoundProgram.stMu (rndV^[5] s0) = M₀ := by
  rw [stMu_iterV, QMCLeafB.Falsify26M8.stMu_s0]

theorem stD_V5 : QMCLeafB.RoundProgram.stD (rndV^[5] s0) = 81 := by
  rw [stD_iterV, QMCLeafB.Falsify26M8.stD_s0]

/-- **The zero matrix is absorbing.**  At `stX = [0,0,0,0]` the oracle cuts, `X c = 0`, so `σ = 0`,
`λ = β/0 = 0`, `μ = 0` and the round is the identity on the primal code. -/
theorem roundNV_zero {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [0, 0, 0, 0]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81) :
    QMCLeafB.RoundProgram.stX (roundNV s) = [0, 0, 0, 0] := by
  have hdv : QMCLeafB.RoundProgram.dvR s ≠ 0 := by
    rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD, dvR_zero_state]
    norm_num
  have hor : oracleNV s = (true, [1, 1]) := by
    unfold oracleNV
    rw [if_neg hdv]
    rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD]
    simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
    rw [diagVecF_two]
    norm_num [QMCLeafB.RoundProgram.sgnOf]
  have h1 : (oracleNV s).1 = true := by rw [hor]
  rw [stX_roundNV_cut h1]
  unfold snapYV scaleYV stepYV
  rw [hN, hX, hor]
  rw [stepFun_four]
  have hlam : QMCLeafB.RoundProgram.lamOf (2, ([0, 0, 0, 0], [1, 1])) = 0 := by
    unfold QMCLeafB.RoundProgram.lamOf QMCLeafB.RoundProgram.betaOf QMCLeafB.RoundProgram.sigOf
      QMCLeafB.RoundProgram.dotZ
    rw [mulVecRaw_vec]
    norm_num
  rw [hlam]
  norm_num
  rw [hMu, hD]
  rw [show QMCLeafB.RoundProgram.alphInv 2 = 3 from QMCLeafB.Falsify26M8.alphInv_two]
  rw [smulRaw_four]
  unfold QMCLeafB.RoundProgram.nrmRow
  simp only [List.map_cons, List.map_nil]
  have h0 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (3 * 0) = 0 := by
    rw [show (3 : ℚ) * 0 = 0 by ring]
    exact QMCLeafB.Falsify26M8.nrmQ_zero
  rw [h0]

/-- The stall: from round `5` on the primal code is the zero matrix, for ever. -/
theorem stX_tailV (T : ℕ) :
    QMCLeafB.RoundProgram.stX (rndV^[T] (rndV^[5] s0)) = [0, 0, 0, 0] := by
  induction T with
  | zero => exact orbitV5
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stX (roundNV (rndV^[k] (rndV^[5] s0))) = [0, 0, 0, 0]
      refine roundNV_zero (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) ?_ ?_ ih ?_ ?_ ?_
      · rw [stN_iterV, stN_V5]
      · rw [stA_iterV, stA_V5]
      · rw [stT_iterV, stT_V5]
      · rw [stMu_iterV, stMu_V5]
      · rw [stD_iterV, stD_V5]

/-! ## 5.  Every round is a cut, so the bit is `false` at every horizon -/

/-- The flag is a cut at a symmetric state with `p ≠ 1`. -/
theorem cut_pq {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ p q : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [p, q, q, p]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (hp : p ≠ 1) :
    (oracleNV s).1 = true := by
  have hdv : QMCLeafB.RoundProgram.dvR s ≠ 0 := dvR_sym_ne hN hA hX hT hMu hD hp
  unfold oracleNV
  rw [if_neg hdv]

/-- The flag is a cut at the zero matrix. -/
theorem cut_zero {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [0, 0, 0, 0]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81) :
    (oracleNV s).1 = true := by
  have hdv : QMCLeafB.RoundProgram.dvR s ≠ 0 := by
    rw [QMCLeafB.Falsify26M8.state_ext hN hA hX hT hMu hD, dvR_zero_state]
    norm_num
  unfold oracleNV
  rw [if_neg hdv]

/-- **Every round of the repaired run at the sliver is a cut.** -/
theorem flag_cutV (T : ℕ) : (oracleNV (rndV^[T] s0)).1 = true := by
  rcases Nat.lt_or_ge T 5 with h | h
  · interval_cases T
    · exact cut_pq QMCLeafB.Falsify26M8.stN_s0 rfl QMCLeafB.Falsify26M8.stX_s0
        QMCLeafB.Falsify26M8.stT_s0 QMCLeafB.Falsify26M8.stMu_s0 QMCLeafB.Falsify26M8.stD_s0
        (by norm_num [c₀, QMCLeafB.Falsify26M8.c₀, QMCLeafB.Falsify26M8.M₀])
    · exact cut_pq stN_V1 stA_V1 orbitV1 stT_V1 stMu_V1 stD_V1 (by norm_num)
    · exact cut_pq stN_V2 stA_V2 orbitV2 stT_V2 stMu_V2 stD_V2 (by norm_num)
    · exact cut_pq stN_V3 stA_V3 orbitV3 stT_V3 stMu_V3 stD_V3 (by norm_num)
    · exact cut_pq stN_V4 stA_V4 orbitV4 stT_V4 stMu_V4 stD_V4 (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, T = 5 + j := ⟨T - 5, by omega⟩
    rw [show 5 + j = j + 5 by omega, Function.iterate_add_apply]
    exact cut_zero (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
      (by rw [stN_iterV j (rndV^[5] s0), stN_V5])
      (by rw [stA_iterV j (rndV^[5] s0), stA_V5])
      (stX_tailV j)
      (by rw [stT_iterV j (rndV^[5] s0), stT_V5])
      (by rw [stMu_iterV j (rndV^[5] s0), stMu_V5])
      (by rw [stD_iterV j (rndV^[5] s0), stD_V5])

theorem oks_replicateV : ∀ T : ℕ,
    QMCLeafB.RoundProgram.stOks (rndV^[T] s0) = List.replicate T false := by
  intro T
  induction T with
  | zero =>
      show QMCLeafB.RoundProgram.stOks s0 = List.replicate 0 false
      rw [QMCLeafB.Falsify26M8.stOks_s0]
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stOks (roundNV (rndV^[k] s0)) = List.replicate (k + 1) false
      rw [stOks_roundNV_cut (flag_cutV k), ih, List.replicate_succ']

/-- **The repaired run never reads `ok`**: the verdict is `false` at every horizon. -/
theorem verdict_falseV (T : ℕ) : QMCLeafB.RoundProgram.verdict (rndV^[T] s0) = false := by
  have hoks := oks_replicateV T
  have hnil : (List.replicate T false).filter id = [] := by
    induction T with
    | zero => rfl
    | succ k ih =>
        rw [List.replicate_succ]
        simp [ih]
  show decide (0 < ((QMCLeafB.RoundProgram.stOks (rndV^[T] s0)).filter id).length) = false
  rw [hoks, hnil]
  rfl

theorem campaignBitV_eq : campaignBitV G₁ t₁
    = QMCLeafB.RoundProgram.verdict (rndV^[Tm] s0) := rfl

/-- **THE FALSIFICATION OF THE MECHANICAL REPAIR.**  At the sliver the repaired program's bit still
reads `false` — at every horizon, hence at the campaign's `K·m` in particular. -/
theorem campaignBitV_sliver_false : campaignBitV G₁ t₁ = false := by
  rw [campaignBitV_eq]
  exact verdict_falseV Tm

/-- The same, stated as "no horizon reads `true`". -/
theorem campaignBitV_no_true (T : ℕ) : QMCLeafB.RoundProgram.verdict (rndV^[T] s0) ≠ true := by
  rw [verdict_falseV T]
  exact Bool.false_ne_true

/-! ## 6.  Why: the repair cannot reach the stop test, and the stop test cannot be certified -/

/-- **(i) the stop test is gated on the exact unit diagonal.** -/
theorem ok_requires_unit_diag {s : QMCLeafB.RoundProgram.RSt}
    (h : (oracleNV s).1 = false) : QMCLeafB.RoundProgram.dvR s = 0 := by
  unfold oracleNV at h
  by_contra hne
  rw [if_neg hne] at h
  exact Bool.noConfusion h

/-- **(i) the repair is invisible to the `ok` branch**: on `dvR = 0` the two oracles coincide. -/
theorem oracleNV_eq_oracleR_of_dvR_zero {s : QMCLeafB.RoundProgram.RSt}
    (h : QMCLeafB.RoundProgram.dvR s = 0) :
    oracleNV s = QMCLeafB.RoundProgram.oracleR s := by
  unfold oracleNV QMCLeafB.RoundProgram.oracleR
  rw [if_pos h, if_pos h]

/-- **(i) the repaired and frozen rounds are the same function on the `ok`-reachable set.** -/
theorem roundNV_eq_round_of_dvR_zero {s : QMCLeafB.RoundProgram.RSt}
    (h : QMCLeafB.RoundProgram.dvR s = 0) :
    roundNV s = QMCLeafB.RoundProgram.round s := by
  have ho := oracleNV_eq_oracleR_of_dvR_zero h
  by_cases hc : (QMCLeafB.RoundProgram.oracleR s).1 = true
  · have hc' : (oracleNV s).1 = true := by rw [ho]; exact hc
    rw [roundNV_eq, if_pos hc']
    unfold QMCLeafB.RoundProgram.round
    rw [if_pos hc]
    unfold roundCutNV QMCLeafB.RoundProgram.roundCut snapYV QMCLeafB.RoundProgram.snapY
      scaleYV QMCLeafB.RoundProgram.scaleY stepYV QMCLeafB.RoundProgram.stepY
    rw [ho]
  · have hc' : ¬ ((oracleNV s).1 = true) := by rw [ho]; exact hc
    rw [roundNV_eq, if_neg hc']
    unfold QMCLeafB.RoundProgram.round
    rw [if_neg hc]

/-- **(ii) `frob` of the campaign weight matrix at `G₁` on a `2 × 2` code.** -/
theorem frob_wMatrixQ_G₁ (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁) Q = Q 0 1 + Q 1 0 := by
  simp only [QMCLeafB.SepOracle.frob, Fin.sum_univ_two]
  rw [QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_00, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_01,
    QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_10, QMCLeafB.EmptyBodyM5.wMatrixQ_G₁_11]
  ring

/-- **(ii) the entries of `qf` at the all-ones vector.** -/
theorem qf_one_eq (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.qf Q (fun _ => 1) = Q 0 0 + Q 0 1 + Q 1 0 + Q 1 1 := by
  simp [QMCLeafB.SepOracle.qf, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- **(ii) `qf` of the all-ones vector at an exactly unit-diagonal code.** -/
theorem qf_one_of_diag_one {Q : Matrix (Fin 2) (Fin 2) ℚ} (hdiag : ∀ i, Q i i = 1) :
    QMCLeafB.SepOracle.qf Q (fun _ => 1)
      = 2 + QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁) Q := by
  rw [frob_wMatrixQ_G₁, qf_one_eq, hdiag 0, hdiag 1]
  norm_num
  ring

/-- **(ii) at the sliver, an exactly unit-diagonal member is strictly non-positive-semidefinite.** -/
theorem member_neg_qf {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hdiag : ∀ i, Q i i = 1)
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) :
    QMCLeafB.SepOracle.qf Q (fun _ => 1) < 0 := by
  rw [qf_one_of_diag_one hdiag]
  have htr := hM.trace_le
  have heps : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁
  have hdq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq
  have ht : t₁ = -(2 : ℚ) + 71 / 1520000 := rfl
  rw [heps, hdq, ht] at htr
  linarith

/-- **(ii) NO PSD unit-diagonal centre is a member at the sliver.**  The exact `qf ≥ 0` form. -/
theorem no_member_of_psd_unitdiag {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hdiag : ∀ i, Q i i = 1)
    (hpsd : ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq := by
  intro hM
  have hneg := member_neg_qf hdiag hM
  have hpos := hpsd (fun _ => 1)
  linarith

/-- **(ii) SHARP, UNCONDITIONAL: every member at the sliver is strictly non-PSD.**  No diagonal
hypothesis: `diag_near` alone gives `∑ Qᵢᵢ ≤ 2 + dq/2`, and `trace_le` gives
`Q₀₁ + Q₁₀ ≤ t₁ − ε + dq/2 = −2 − 3/1520000`, so `qf Q 1 ≤ dq/2 − 3/1520000 = −1/1520000 < 0`. -/
theorem member_qf_neg {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hM : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq) :
    QMCLeafB.SepOracle.qf Q (fun _ => 1) < 0 := by
  have hq := qf_one_eq Q
  have hf := frob_wMatrixQ_G₁ Q
  have h0 := abs_le.mp (hM.diag_near 0)
  have h1 := abs_le.mp (hM.diag_near 1)
  have htr := hM.trace_le
  have heps : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁
  have hdq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq
  have ht : t₁ = -(2 : ℚ) + 71 / 1520000 := rfl
  rw [hf] at htr
  rw [heps, hdq, ht] at htr
  rw [hdq] at h0 h1
  rw [hq]
  linarith [h0.2, h1.2]

/-- **(ii) NO PSD centre is a member at the sliver** — the unconditional form.  Every descent that
keeps its normaltzed centres inside the PSD cone is blind to the sliver's body. -/
theorem no_psd_member_at_sliver {Q : Matrix (Fin 2) (Fin 2) ℚ}
    (hpsd : ∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf Q x) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
      (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq := by
  intro hM
  have hneg := member_qf_neg hM
  have hpos := hpsd (fun _ => 1)
  linarith

/-- **(ii) THE CONSEQUENCE FOR THE TEST-RUN FAMILY.**  Every test-run at the sliver — for *any* bit —
has an `ok` round below the horizon (the visit theorem, `TrajM3.exists_member_of_ball`), and that
round's centre is **not positive semidefinite**.  So the leaf's `TestRun` family cannot be built from
PSD-normalised query centres anywhere: at the sliver the read-`true` needs an outward (near-PSD)
centre. -/
theorem testRun_ok_centre_not_psd
    {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    (T : QMCLeafB.TrajM3.TestRun o G₁ t₁ P₁) :
    ∃ k, k < P₁.K * P₁.m ∧
      ¬ (∀ x : Fin 2 → ℚ, 0 ≤ QMCLeafB.SepOracle.qf (T.cX k) x) := by
  obtain ⟨k, hk, hM⟩ := QMCLeafB.TrajM3.exists_member_of_ball (T := T)
    QMCLeafB.AnchorFactsM2.hn₁ QMCLeafB.BallM2.sliver_ball_campaign
  exact ⟨k, hk, fun hpsd => no_psd_member_at_sliver hpsd hM⟩

/-! ### 6.0  The constructive side: the maximal outward push *is* a member at the sliver

(ii) says the sliver's body lives strictly outside the PSD cone.  The certificate is nevertheless
canonical: push the off-diagonal of the unit-diagonal centre outward until the `δ/2` PSD margin is
*exactly* tight.  At `Q = !![1,s;s,1]` the margin reads `|s| ≤ 1 + dq/2` and `trace_le` reads
`s ≤ −1 − 3/3040000`, so the window is `s ∈ [−(1+dq/2), −(1+3/3040000)]` and the left endpoint — the
maximal push — is a member.  This is the centre a certifying `ok` branch has to query. -/

/-- The maximal outward push: the off-diagonal at the `δ/2` margin boundary. -/
def pushS : ℚ := -(1 + P₁.dq / 2)

theorem pushS_def : pushS = -(1 + P₁.dq / 2) := rfl

theorem qf_push (x : Fin 2 → ℚ) :
    QMCLeafB.SepOracle.qf (!![1, pushS; pushS, 1]) x
      = x 0 ^ 2 + x 1 ^ 2 + 2 * pushS * (x 0 * x 1) := by
  simp [QMCLeafB.SepOracle.qf, Matrix.mulVec, dotProduct, Fin.sum_univ_two, pushS]
  ring

/-- The pushed centre sits exactly on the `δ/2` PSD margin. -/
theorem push_psd (x : Fin 2 → ℚ) :
    -(P₁.dq / 2) * (∑ i, x i ^ 2)
      ≤ QMCLeafB.SepOracle.qf (!![1, pushS; pushS, 1]) x := by
  rw [Fin.sum_univ_two, qf_push, pushS]
  have hdq : (0 : ℚ) < P₁.dq := P₁.hdq
  nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 * x 1)]

/-- **THE PUSHED CENTRE IS A MEMBER AT THE SLIVER**: the maximal outward push, with the PSD margin
exactly tight and the objective `dq − 3/1520000 = 1/1520000` inside the level. -/
theorem push_member :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁)
      (!![1, pushS; pushS, 1]) (t₁ - QMCLeafB.RundataCert.eps G₁) P₁.dq := by
  refine ⟨P₁.hdq, ?_, ?_, ?_⟩
  · exact push_psd
  · intro i
    have hdq0 : (0 : ℚ) ≤ P₁.dq := le_of_lt P₁.hdq
    have h4 : (0 : ℚ) ≤ 4 := by norm_num
    fin_cases i <;> simp <;> exact div_nonneg hdq0 h4
  · rw [frob_wMatrixQ_G₁]
    have hpq : (!![1, pushS; pushS, 1] : Matrix (Fin 2) (Fin 2) ℚ) 0 1 = pushS := by simp
    have hqp : (!![1, pushS; pushS, 1] : Matrix (Fin 2) (Fin 2) ℚ) 1 0 = pushS := by simp
    have heps : QMCLeafB.RundataCert.eps G₁ = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁
    have hdq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq
    have ht : t₁ = -(2 : ℚ) + 71 / 1520000 := rfl
    rw [hpq, hqp, pushS, hdq, heps, ht]
    norm_num

/-! ### 6.1  Inventory: every existing round lane funnels through the `n²` code

`RoundProgram.oracleR` (the frozen campaign round) and `OkLower.oracleV` (the lower-body lane that
`roundW`/`roundWG`/`roundV` run on) both answer a cut with `diagSignF`, the `n²`-length matrix code.
So there is **no** length-correct lane to re-point the bit at: the repair has to be made, not found. -/

theorem oracleV_uses_n2_code {s : QMCLeafB.RoundProgram.RSt}
    (h : QMCLeafB.RoundProgram.dvR s ≠ 0) :
    (QMCLeafB.OkLower.oracleV s).2
      = QMCLeafB.RoundProgram.diagSignF (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s) := by
  unfold QMCLeafB.OkLower.oracleV
  rw [if_neg h]

theorem oracleR_uses_n2_code {s : QMCLeafB.RoundProgram.RSt}
    (h : QMCLeafB.RoundProgram.dvR s ≠ 0) :
    (QMCLeafB.RoundProgram.oracleR s).2
      = QMCLeafB.RoundProgram.diagSignF (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s) := by
  unfold QMCLeafB.RoundProgram.oracleR
  rw [if_neg h]

/-! ## 7.  Axiom receipts -/

#print axioms QMCLeafB.BitVM2.diagVecF_two
#print axioms QMCLeafB.BitVM2.diagSignF_length_four
#print axioms QMCLeafB.BitVM2.diagSignF_four
#print axioms QMCLeafB.BitVM2.diagSignF_take_two
#print axioms QMCLeafB.BitVM2.mulVecRaw_vec
#print axioms QMCLeafB.BitVM2.mulVecRaw_diagSignF
#print axioms QMCLeafB.BitVM2.poly_diagVecF
#print axioms QMCLeafB.BitVM2.dvR_sym_state
#print axioms QMCLeafB.BitVM2.dvR_zero_state
#print axioms QMCLeafB.BitVM2.dvR_sym_ne
#print axioms QMCLeafB.BitVM2.stepFun_four
#print axioms QMCLeafB.BitVM2.sigOf_sym
#print axioms QMCLeafB.BitVM2.sigOf_sym_eq
#print axioms QMCLeafB.BitVM2.lamOf_sym
#print axioms QMCLeafB.BitVM2.mu_sym
#print axioms QMCLeafB.BitVM2.entry_sym
#print axioms QMCLeafB.BitVM2.entry_sym_off
#print axioms QMCLeafB.BitVM2.roundNV_cut_sym
#print axioms QMCLeafB.BitVM2.roundNV_pq
#print axioms QMCLeafB.BitVM2.sum_invariant
#print axioms QMCLeafB.BitVM2.gap_triples
#print axioms QMCLeafB.BitVM2.orbitV1
#print axioms QMCLeafB.BitVM2.orbitV2
#print axioms QMCLeafB.BitVM2.orbitV3
#print axioms QMCLeafB.BitVM2.orbitV4
#print axioms QMCLeafB.BitVM2.orbitV5
#print axioms QMCLeafB.BitVM2.roundNV_zero
#print axioms QMCLeafB.BitVM2.stX_tailV
#print axioms QMCLeafB.BitVM2.flag_cutV
#print axioms QMCLeafB.BitVM2.oks_replicateV
#print axioms QMCLeafB.BitVM2.verdict_falseV
#print axioms QMCLeafB.BitVM2.campaignBitV_sliver_false
#print axioms QMCLeafB.BitVM2.ok_requires_unit_diag
#print axioms QMCLeafB.BitVM2.roundNV_eq_round_of_dvR_zero
#print axioms QMCLeafB.BitVM2.frob_wMatrixQ_G₁
#print axioms QMCLeafB.BitVM2.qf_one_eq
#print axioms QMCLeafB.BitVM2.qf_one_of_diag_one
#print axioms QMCLeafB.BitVM2.member_neg_qf
#print axioms QMCLeafB.BitVM2.no_member_of_psd_unitdiag
#print axioms QMCLeafB.BitVM2.member_qf_neg
#print axioms QMCLeafB.BitVM2.no_psd_member_at_sliver
#print axioms QMCLeafB.BitVM2.testRun_ok_centre_not_psd
#print axioms QMCLeafB.BitVM2.oracleV_uses_n2_code
#print axioms QMCLeafB.BitVM2.oracleR_uses_n2_code
#print axioms QMCLeafB.BitVM2.qf_push
#print axioms QMCLeafB.BitVM2.push_psd
#print axioms QMCLeafB.BitVM2.push_member

end QMCLeafB.BitVM2



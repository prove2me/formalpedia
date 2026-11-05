-- Prove2me | Definitions.Def_QMCLeafB_falsify26
-- name    : QMCLeafB_falsify26
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:33:45.540479+00:00
-- url     : https://prove2.me/theorems/a9fdb1d5-ef56-4ebc-a4c9-fd76c5aaab76
-- title:
--   QMCLeafB falsify26
-- statement:
--   # `Check_falsify26_m8` — phase 26, member m8, direction `falsify26`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_audit25
import Definitions.Def_QMCLeafB_dichot
/-
# `Check_falsify26_m8` — phase 26, member m8, direction `falsify26`

**The finding.**  The campaign's frozen verdict bit `Audit2M5.campaignBit` reads **`false`** at the
sliver exemplar `(G₁, t₁)`, at *every* horizon, and the reason is a stall of the shallow engine, not
a certificate desert: at `(G₁,t₁)` the run's primal code reaches the degenerate fixed point
`diag(10/81, 0)` after four rounds and stays there, with the summed-diagonal oracle cutting for ever.

The mechanism is a defect in the *cut normal* the round feeds to `mulVec`: the summed-diagonal
normal `diagSignF` has length `n² = 4` but `MatQ.Runtime.mulVecRaw` reads only its first `n = 2`
entries, so the normal acts as `e₁` and only the **first** diagonal is ever cut.  The second
diagonal therefore evolves by the `α⁻¹ = (n+1)/(n−1) = 3` scaling alone, `b ↦ 3b`, until the box
clip `|q| ≤ M = 2n² + 2dq²` throws it to `0`, after which `diag(a, 0)` is an exact fixed point of
the round (for every `a`).  Machine-checked as `round_diag` below.

**The consequences, all machine-checked here.**

* `campaignBit G₁ t₁ = false` (§4) — the campaign's own program reads `false` at the sliver.
* `ResidParts campaignBit paramsKbc2` is **uninhabited** (§6): `ResidParts` supplies a `RunParts` at
  the sliver, and the campaign ball there forces the bit `true` (`BallM2.campaign_bit_true_at_sliver`).
  This refutes the phase-25 residual — the campaign bit and the residual are incompatible.
* `Audit25M8.Package` is **uninhabited** (§6): its `parts` field is exactly that residual.  This is
  the fifth vacuity of the defect family, and unlike the first four it is *not* repairable by
  restating the residual shape: the *program* itself reads the wrong bit here.
* The certificate slot at the sliver is **not** the obstruction (§5): an un-pinched unit-diagonal
  member exists (`DichotM3.member_diag_one`), so `hok` is satisfiable — the kill is the frozen run.

Reproduction of the orbit (kernel reduction of the *concrete* run, `#reduce` on
`stX (RoundProgram.round^[k] (InitDq.init0 ((G₁, []), t₁)))`, k = 0..8):
`diag(0.125000, 0.125000) → diag(10/81, 10/27) → diag(10/81, 10/9) → diag(10/81, 10/3) →
diag(10/81, 0) → diag(10/81, 0) → …`, with the oracle flag `true` (= cut) at every step.  The
proofs below are *not* that evaluation: `round_diag` derives the general one-step formula, and the
orbit is then the arithmetic of §3.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` on every declaration, expected `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.Falsify26M8

open QuantumMaxCutEnergy

/-! ## 0.  The exemplar and the run's constants -/

/-- The sliver input (two vertices, one edge of weight `1`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.AnchorFactsM2.G₁

/-- The sliver threshold. -/
abbrev t₁ : ℚ := -(2 : ℚ) + 71 / 1520000

/-- The run's box bound at the sliver: `M = 2n² + 2dq²` at `n = 2`, `dq = 1/380000`. -/
def M₀ : ℚ := 577600000001 / 72200000000

/-- The run's snap denominator at the sliver: `gridOf 2 = 81`. -/
def D₀ : ℕ := 81

/-- The initial primal entry: `M₀⁻¹`. -/
def c₀ : ℚ := 72200000000 / 577600000001

/-- The stall point. -/
def F : List ℚ := [10 / 81, 0, 0, 0]

/-- The closing input of the campaign at the sliver. -/
def p₀ : (QuantumMaxCutEnergy.Input × List Bool) × ℚ := ((G₁, []), t₁)

/-- The campaign's initial state at the sliver. -/
def s0 : QMCLeafB.RoundProgram.RSt := QMCLeafB.InitDq.init0 p₀

/-- One round of the concrete program. -/
def rnd : QMCLeafB.RoundProgram.RSt → QMCLeafB.RoundProgram.RSt := QMCLeafB.RoundProgram.round

/-! ## 1.  The round at a diagonal state: `diag(a,b) ↦ diag(snap a, snap (3b))`

This is the defect at the heart of the falsification: the normal `diagSignF` is a *matrix* code of
length `4`, but the update's `mulVec` reads only its first `n = 2` entries, so the normal acts as
`e₁`.  Only the first diagonal is cut; the second is scaled by `α⁻¹ = 3` and clipped. -/

theorem range_two : (List.range 2) = [0, 1] := by decide

/-- `mulVec` of a diagonal code against the normal `[1,0,0,s]` is the first column. -/
theorem mv (a b s : ℚ) :
    MatQ.Runtime.mulVecRaw (2, ([a, 0, 0, b], [1, 0, 0, s])) = [a, 0] := by
  simp [MatQ.Runtime.mulVecRaw, range_two]

/-- `σ = cᵀXc` at the diagonal state: only `c₀ = 1` survives. -/
theorem sigZ (a b s : ℚ) :
    ((([1, 0, 0, s] : List ℚ).zip [a, 0]).map (fun q : ℚ × ℚ => q.1 * q.2)).sum = a := by
  simp

/-- `λ = β/σ = 2/a` at the diagonal state. -/
theorem lamOf_diag (a b s : ℚ) :
    QMCLeafB.RoundProgram.lamOf (2, ([a, 0, 0, b], [1, 0, 0, s])) = 2 / a := by
  unfold QMCLeafB.RoundProgram.lamOf QMCLeafB.RoundProgram.betaOf QMCLeafB.RoundProgram.sigOf
    QMCLeafB.RoundProgram.dotZ
  rw [mv]
  simp
  norm_num

theorem snapTrunc_zero : QMCLeafB.RoundPolySnap.snapTrunc 0 = 0 := by
  unfold QMCLeafB.RoundPolySnap.snapTrunc
  decide

/-- The grid snap of `0` is `0`. -/
theorem nrmQ_zero : QMCLeafB.RoundProgram.nrmQ M₀ 81 0 = 0 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
    QMCLeafB.RoundPolySnap.snapDiv
  norm_num [snapTrunc_zero]

/-- The step machine, unfolded on a concrete-length state. -/
theorem stepFun_form (n : ℕ) (X c : List ℚ) (lam : ℚ) :
    QMCLeafB.MatQUpdate.Step.stepFun ((n, X), (c, lam))
      = QMCLeafB.MatQUpdate.Upd.updFun ((n, X),
          (MatQ.Runtime.mulVecRaw (n, (X, c)),
            lam / (1 + lam * (((c.zip (MatQ.Runtime.mulVecRaw (n, (X, c)))).map
              (fun q : ℚ × ℚ => q.1 * q.2)).sum)))) := rfl

/-- The rank-one update at a diagonal code with the vector `[a,0]`. -/
theorem updFun_diag (a b : ℚ) (μ : ℚ) :
    QMCLeafB.MatQUpdate.Upd.updFun ((2, [a, 0, 0, b]), ([a, 0], μ))
      = [a - μ * a * a, 0, 0, b] := by
  unfold QMCLeafB.MatQUpdate.Upd.updFun QMCLeafB.MatQUpdate.Upd.rowFun
  simp [range_two]

/-- **The step machine at a diagonal state**: `X ↦ diag(a − (2/(3a))a², b) = diag(a/3, b)`. -/
theorem stepF (a b s : ℚ) (ha : a ≠ 0) :
    QMCLeafB.MatQUpdate.Step.stepFun ((2, [a, 0, 0, b]), ([1, 0, 0, s], 2 / a))
      = [a - (2 / (3 * a)) * a * a, 0, 0, b] := by
  have hmu : (2 / a) / (1 + (2 / a) * a) = 2 / (3 * a) := by
    field_simp
    ring
  have hs : ((([1, 0, 0, s] : List ℚ).zip [a, 0]).map (fun q : ℚ × ℚ => q.1 * q.2)).sum = a := by
    simp
  rw [stepFun_form, mv, hs, hmu, updFun_diag]

/-- The `α⁻¹ = 3` scaling on a diagonal code. -/
theorem smulRaw_diag (a b c : ℚ) :
    QMCLeafB.MatQUpdate.smulRaw ((2, [a, 0, 0, b]), c) = [c * a, c * 0, c * 0, c * b] := by
  unfold QMCLeafB.MatQUpdate.smulRaw
  simp [range_two]

theorem alphInv_two : QMCLeafB.RoundProgram.alphInv 2 = 3 := by
  unfold QMCLeafB.RoundProgram.alphInv
  norm_num

/-- `absq` is positive off zero. -/
theorem absq_pos_of_ne {q : ℚ} (h : q ≠ 0) : 0 < QMCLeafB.RoundProgram.absq q := by
  unfold QMCLeafB.RoundProgram.absq
  split_ifs with hq
  · linarith
  · have hq' : 0 ≤ q := le_of_not_gt hq
    by_contra hc
    have hc' : q ≤ 0 := le_of_not_gt hc
    exact h (le_antisymm hc' hq')

theorem absq_nonneg (q : ℚ) : 0 ≤ QMCLeafB.RoundProgram.absq q := by
  unfold QMCLeafB.RoundProgram.absq
  split_ifs with hq
  · linarith
  · exact le_of_not_gt hq

/-- The drift at a diagonal code. -/
theorem dvR_diag {A : List ℚ} {τ M a b : ℚ} (hb : b ≠ 1) (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.dvR
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M 81 oks rec) ≠ 0 := by
  have hb0 : b - 1 ≠ 0 := sub_ne_zero.mpr hb
  have hpos : 0 < QMCLeafB.RoundProgram.absq (b - 1) := absq_pos_of_ne hb0
  have hnn : 0 ≤ QMCLeafB.RoundProgram.absq (a - 1) := absq_nonneg _
  have key : QMCLeafB.RoundProgram.dvR
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M 81 oks rec)
      = QMCLeafB.RoundProgram.absq (a - 1) + QMCLeafB.RoundProgram.absq (b - 1) := by
    unfold QMCLeafB.RoundProgram.dvR QMCLeafB.RoundProgram.diagSumV
    simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
    rw [show QMCLeafB.RoundProgram.idxs (2, [a, 0, 0, b]) = [0, 1] by
      simp [QMCLeafB.RoundProgram.idxs, range_two]]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      QMCLeafB.RoundProgram.entV, List.getD_cons_zero, List.getD_cons_succ, List.getD_nil,
      Nat.reduceAdd, Nat.reduceMul, zero_add]
    ring
  rw [key]
  intro h
  linarith

/-- The cut normal at a diagonal code: the identity code. -/
theorem diagSignF_diag {a b : ℚ} (ha : a < 1) :
    QMCLeafB.RoundProgram.diagSignF (2, [a, 0, 0, b]) = [1, 0, 0, QMCLeafB.RoundProgram.sgnOf (1 - b)] := by
  have h1 : ¬ (1 - a < 0) := by linarith
  have h2 : ¬ (1 - a = 0) := by linarith
  unfold QMCLeafB.RoundProgram.diagSignF
  rw [show QMCLeafB.RoundProgram.idxs (2, [a, 0, 0, b]) = [0, 1] by
    simp [QMCLeafB.RoundProgram.idxs, range_two]]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, QMCLeafB.RoundProgram.entV, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil, Nat.reduceAdd, Nat.reduceMul, if_true, reduceIte,
    QMCLeafB.RoundProgram.sgnOf]
  rw [if_neg h1, if_neg h2]
  norm_num

/-- The oracle at a diagonal state reads `cut` with the identity code as normal. -/
theorem oracleR_diag {A : List ℚ} {τ M a b : ℚ} (ha : a < 1) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.oracleR (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M 81 oks rec)
      = (true, [1, 0, 0, QMCLeafB.RoundProgram.sgnOf (1 - b)]) := by
  have hdv := dvR_diag (A := A) (τ := τ) (M := M) (a := a) (b := b) hb oks rec
  unfold QMCLeafB.RoundProgram.oracleR
  rw [if_neg hdv]
  simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
  rw [diagSignF_diag (a := a) (b := b) ha]

/-- The oracle at a diagonal state is a cut. -/
theorem oracleR_cut {A : List ℚ} {τ M a b : ℚ} (ha : a < 1) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    (QMCLeafB.RoundProgram.oracleR
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M 81 oks rec)).1 = true := by
  rw [oracleR_diag (A := A) (τ := τ) (M := M) (a := a) (b := b) ha hb oks rec]

/-- `stepY` at a diagonal state. -/
theorem stepY_diag {A : List ℚ} {τ a b : ℚ} (ha : a < 1) (ha0 : a ≠ 0) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.stepY (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)
      = [a - (2 / (3 * a)) * a * a, 0, 0, b] := by
  have hO := oracleR_diag (A := A) (τ := τ) (M := M₀) (a := a) (b := b) ha hb oks rec
  have h2 : (QMCLeafB.RoundProgram.oracleR
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)).2
      = [1, 0, 0, QMCLeafB.RoundProgram.sgnOf (1 - b)] := by rw [hO]
  unfold QMCLeafB.RoundProgram.stepY
  simp only [QMCLeafB.RoundProgram.mkSt_stN, QMCLeafB.RoundProgram.mkSt_stX]
  rw [h2, lamOf_diag]
  exact stepF a b _ ha0

/-- `scaleY` at a diagonal state. -/
theorem scaleY_diag {A : List ℚ} {τ a b : ℚ} (ha : a < 1) (ha0 : a ≠ 0) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.scaleY (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)
      = [3 * (a - (2 / (3 * a)) * a * a), 0, 0, 3 * b] := by
  have hY := stepY_diag (A := A) (τ := τ) (a := a) (b := b) ha ha0 hb oks rec
  have h2 : QMCLeafB.RoundProgram.stepY
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)
      = [a - (2 / (3 * a)) * a * a, 0, 0, b] := hY
  unfold QMCLeafB.RoundProgram.scaleY
  simp only [QMCLeafB.RoundProgram.mkSt_stN]
  rw [h2, alphInv_two, smulRaw_diag]
  norm_num

/-- `snapY` at a diagonal state. -/
theorem snapY_diag {A : List ℚ} {τ a b : ℚ} (ha : a < 1) (ha0 : a ≠ 0) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.snapY (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)
      = [QMCLeafB.RoundProgram.nrmQ M₀ 81 a, 0, 0, QMCLeafB.RoundProgram.nrmQ M₀ 81 (3 * b)] := by
  have hS := scaleY_diag (A := A) (τ := τ) (a := a) (b := b) ha ha0 hb oks rec
  have h3 : 3 * (a - (2 / (3 * a)) * a * a) = a := by
    have h3a : (3 * a) ≠ 0 := by
      intro hh
      exact ha0 (by linarith [hh])
    field_simp
    ring
  unfold QMCLeafB.RoundProgram.snapY QMCLeafB.RoundProgram.nrmRow
  simp only [QMCLeafB.RoundProgram.mkSt_stMu, QMCLeafB.RoundProgram.mkSt_stD]
  rw [hS, h3]
  norm_num [nrmQ_zero]

/-- **THE ONE-STEP FORMULA.**  At any diagonal state of the run's own shape, one round maps
`diag(a,b)` to `diag(snap a, snap (3b))` — the first diagonal is cut, the second only scaled. -/
theorem round_diag {A : List ℚ} {τ a b : ℚ} (ha : a < 1) (ha0 : a ≠ 0) (hb : b ≠ 1)
    (oks : List Bool) (rec : List ℚ) :
    QMCLeafB.RoundProgram.stX
        (QMCLeafB.RoundProgram.round
          (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec))
      = [QMCLeafB.RoundProgram.nrmQ M₀ 81 a, 0, 0, QMCLeafB.RoundProgram.nrmQ M₀ 81 (3 * b)] := by
  have hfl : (QMCLeafB.RoundProgram.oracleR
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec)).1 = true :=
    oracleR_cut ha hb oks rec
  rw [QMCLeafB.RoundProgram.round_eq, if_pos hfl]
  show QMCLeafB.RoundProgram.snapY
      (QMCLeafB.RoundProgram.mkSt 2 A [a, 0, 0, b] τ M₀ 81 oks rec) = _
  exact snapY_diag (A := A) (τ := τ) (a := a) (b := b) ha ha0 hb oks rec

/-! ### 1b.  The repair receipt: a length-`n` vector normal cuts **every** diagonal

The defect is the *shape* of the normal, not the descent: `diagSignF` returns the `n²`-code of a
matrix, and `mulVec` reads it as an `n`-vector.  With a genuine length-`n` normal
`(sign(1−X₀₀), …, sign(1−X₍ₙ₋₁₎ₙ₋₁))` the rank-one update subtracts `μ·vvᵀ` with `v = (a,b)`, so
both diagonals move — which is what the summed-diagonal cut is supposed to do. -/

theorem mv_vec (a b : ℚ) :
    MatQ.Runtime.mulVecRaw (2, ([a, 0, 0, b], [1, 1])) = [a, b] := by
  simp [MatQ.Runtime.mulVecRaw, range_two]

theorem updFun_diag2 (a b μ : ℚ) :
    QMCLeafB.MatQUpdate.Upd.updFun ((2, [a, 0, 0, b]), ([a, b], μ))
      = [a - μ * a * a, -(μ * a * b), -(μ * b * a), b - μ * b * b] := by
  unfold QMCLeafB.MatQUpdate.Upd.updFun QMCLeafB.MatQUpdate.Upd.rowFun
  simp [range_two]

/-- **Repaired one-step formula**: with a length-`n` normal both diagonals are cut. -/
theorem stepF_vec (a b : ℚ) (h : a + b ≠ 0) :
    QMCLeafB.MatQUpdate.Step.stepFun ((2, [a, 0, 0, b]), ([1, 1], 2 / (a + b)))
      = [a - (2 / (3 * (a + b))) * a * a, -(2 / (3 * (a + b)) * a * b),
          -(2 / (3 * (a + b)) * b * a), b - (2 / (3 * (a + b))) * b * b] := by
  have hsig : ((([1, 1] : List ℚ).zip [a, b]).map (fun q : ℚ × ℚ => q.1 * q.2)).sum = a + b := by
    simp
  have hmu : (2 / (a + b)) / (1 + (2 / (a + b)) * (a + b)) = 2 / (3 * (a + b)) := by
    field_simp
    ring
  rw [stepFun_form, mv_vec]
  rw [show ((([1, 1] : List ℚ).zip [a, b]).map (fun q : ℚ × ℚ => q.1 * q.2)).sum = a + b from hsig]
  rw [hmu, updFun_diag2]

/-! ## 2.  Reading a state at its own fields, and the scalars' invariance -/

theorem state_ext {s : QMCLeafB.RoundProgram.RSt} {A X : List ℚ} {τ M : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = X) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M) (hD : QMCLeafB.RoundProgram.stD s = 81) :
    s = QMCLeafB.RoundProgram.mkSt 2 A X τ M 81
      (QMCLeafB.RoundProgram.stOks s) (QMCLeafB.RoundProgram.stRec s) := by
  obtain ⟨⟨⟨n, A'⟩, ⟨X', T', mu'⟩⟩, ⟨⟨d', oks⟩, rec⟩⟩ := s
  simp only [QMCLeafB.RoundProgram.stN, QMCLeafB.RoundProgram.stA, QMCLeafB.RoundProgram.stX,
    QMCLeafB.RoundProgram.stT, QMCLeafB.RoundProgram.stMu, QMCLeafB.RoundProgram.stD,
    QMCLeafB.RoundProgram.stOks, QMCLeafB.RoundProgram.stRec] at hN hA hX hT hMu hD
  subst hN; subst hA; subst hX; subst hT; subst hMu; subst hD
  rfl

theorem stN_round (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stN (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stN s := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split <;> rfl

theorem stA_round (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stA s := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split <;> rfl

theorem stT_round (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stT s := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split <;> rfl

theorem stMu_round (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stMu (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stMu s := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split <;> rfl

theorem stD_round (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stD (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stD s := by
  rw [QMCLeafB.RoundProgram.round_eq]
  split <;> rfl

theorem stOks_round_cut {s : QMCLeafB.RoundProgram.RSt}
    (h : (QMCLeafB.RoundProgram.oracleR s).1 = true) :
    QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round s) =
      QMCLeafB.RoundProgram.stOks s ++ [false] := by
  rw [QMCLeafB.RoundProgram.round_eq, if_pos h]
  rfl

theorem stN_iter (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stN (rnd^[T] s) = QMCLeafB.RoundProgram.stN s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stN (QMCLeafB.RoundProgram.round (rnd^[k] s)) =
        QMCLeafB.RoundProgram.stN s
      rw [stN_round, ih]

theorem stA_iter (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stA (rnd^[T] s) = QMCLeafB.RoundProgram.stA s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stA (QMCLeafB.RoundProgram.round (rnd^[k] s)) =
        QMCLeafB.RoundProgram.stA s
      rw [stA_round, ih]

theorem stT_iter (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stT (rnd^[T] s) = QMCLeafB.RoundProgram.stT s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stT (QMCLeafB.RoundProgram.round (rnd^[k] s)) =
        QMCLeafB.RoundProgram.stT s
      rw [stT_round, ih]

theorem stMu_iter (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stMu (rnd^[T] s) = QMCLeafB.RoundProgram.stMu s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stMu (QMCLeafB.RoundProgram.round (rnd^[k] s)) =
        QMCLeafB.RoundProgram.stMu s
      rw [stMu_round, ih]

theorem stD_iter (T : ℕ) (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stD (rnd^[T] s) = QMCLeafB.RoundProgram.stD s := by
  induction T with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stD (QMCLeafB.RoundProgram.round (rnd^[k] s)) =
        QMCLeafB.RoundProgram.stD s
      rw [stD_round, ih]

/-- One orbit step at a state read through its fields. -/
theorem step_of_fields {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ a b : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [a, 0, 0, b]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (ha : a < 1) (ha0 : a ≠ 0) (hb : b ≠ 1) :
    QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round s)
      = [QMCLeafB.RoundProgram.nrmQ M₀ 81 a, 0, 0, QMCLeafB.RoundProgram.nrmQ M₀ 81 (3 * b)] := by
  rw [state_ext hN hA hX hT hMu hD]
  exact round_diag (A := A) (τ := τ) (a := a) (b := b) ha ha0 hb _ _

/-- The oracle is a cut at any state read through a diagonal field with `b ≠ 1`. -/
theorem cut_of_fields {s : QMCLeafB.RoundProgram.RSt} {A : List ℚ} {τ a b : ℚ}
    (hN : QMCLeafB.RoundProgram.stN s = 2) (hA : QMCLeafB.RoundProgram.stA s = A)
    (hX : QMCLeafB.RoundProgram.stX s = [a, 0, 0, b]) (hT : QMCLeafB.RoundProgram.stT s = τ)
    (hMu : QMCLeafB.RoundProgram.stMu s = M₀) (hD : QMCLeafB.RoundProgram.stD s = 81)
    (ha : a < 1) (hb : b ≠ 1) :
    (QMCLeafB.RoundProgram.oracleR s).1 = true := by
  rw [state_ext hN hA hX hT hMu hD]
  exact oracleR_cut (A := A) (τ := τ) (a := a) (b := b) ha hb _ _

/-! ## 3.  The initial state at the sliver -/

theorem stN_s0 : QMCLeafB.RoundProgram.stN s0 = 2 := by
  unfold s0
  rw [QMCLeafB.InitDq.stN_init0]
  rfl

theorem stT_s0 : QMCLeafB.RoundProgram.stT s0 = t₁ := by
  unfold s0
  rw [QMCLeafB.InitDq.stT_init0]
  rfl

theorem stOks_s0 : QMCLeafB.RoundProgram.stOks s0 = [] := by
  unfold s0
  rw [QMCLeafB.InitDq.stOks_init0]

theorem stD_s0 : QMCLeafB.RoundProgram.stD s0 = 81 := by
  unfold s0
  rw [QMCLeafB.InitDq.stD_init0, QMCLeafB.InitDq.stN_init0]
  norm_num [QMCLeafB.InitVerdict.gridOf, p₀]

theorem stMu_s0 : QMCLeafB.RoundProgram.stMu s0 = M₀ := by
  unfold s0
  rw [QMCLeafB.InitDq.stMu_init0_dq]
  rw [show QMCLeafB.InitDq.dqOf p₀.1.1 = 1 / 380000 from QMCLeafB.EmptyBodyM5.dqShallow_G₁]
  norm_num [M₀, p₀]

theorem stX_s0 : QMCLeafB.RoundProgram.stX s0 = [c₀, 0, 0, c₀] := by
  have hN : QMCLeafB.InitDq.muOfD p₀ = M₀ := by
    rw [QMCLeafB.InitDq.muOfD_eq, QMCLeafB.InitDq.muOf_eq]
    rw [show QMCLeafB.InitDq.dqOf p₀.1.1 = 1 / 380000 from QMCLeafB.EmptyBodyM5.dqShallow_G₁]
    norm_num [M₀, p₀]
  have hlen : 2 ≤ (QMCLeafB.InitVerdict.doubleUp
      (QuantumMaxCutEnergy.encodeRequest (G₁, []))).length := by
    rw [QMCLeafB.InitVerdict.doubleUp_length]
    have h2 : 2 ≤ (QuantumMaxCutEnergy.encodeRequest (G₁, [])).length := by
      have h3 := QMCLeafB.InitVerdict.inputWidth_le_length
        (QuantumMaxCutEnergy.encodeRequest (G₁, []))
      have h4 : QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest (G₁, [])) = 2 := by
        have := QMCLeafB.InitDq.stN_init0 p₀
        unfold s0 at this
        exact this
      rwa [h4] at h3
    nlinarith
  show QMCLeafB.InitVerdict.identVia
      (QMCLeafB.InitVerdict.doubleUp (QuantumMaxCutEnergy.encodeRequest (G₁, [])))
      (QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest (G₁, [])))
      ((QMCLeafB.InitDq.muOfD p₀)⁻¹) = [c₀, 0, 0, c₀]
  have hN2 : QMCNumericRuntime.inputWidth (QuantumMaxCutEnergy.encodeRequest (G₁, [])) = 2 := by
    have := QMCLeafB.InitDq.stN_init0 p₀
    unfold s0 at this
    exact this
  rw [hN2]
  rw [QMCLeafB.InitVerdict.identVia_eq_mk _ _ hlen]
  rw [hN]
  have hval : (M₀)⁻¹ = c₀ := by norm_num [M₀, c₀]
  rw [hval]
  simp [MatQ.mk, range_two]


/-! ## 4.  The grid-snap evaluations at the sliver's numbers -/

theorem nrmQ_c₀ : QMCLeafB.RoundProgram.nrmQ M₀ 81 c₀ = 10 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
  norm_num [QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, c₀]

theorem nrmQ_3c₀ : QMCLeafB.RoundProgram.nrmQ M₀ 81 (3 * c₀) = 10 / 27 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
  norm_num [QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀, c₀]

theorem nrmQ_10_81 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (10 / 81) = 10 / 81 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
  norm_num [QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀]

theorem nrmQ_10_9 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (10 / 9) = 10 / 9 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
  norm_num [QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀]

theorem nrmQ_10_3 : QMCLeafB.RoundProgram.nrmQ M₀ 81 (10 / 3) = 10 / 3 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
  norm_num [QMCLeafB.RoundPolySnap.snapDiv, QMCLeafB.RoundPolySnap.snapTrunc_of_nonneg, M₀]

/-- The box clip fires: `10 > M`. -/
theorem nrmQ_ten : QMCLeafB.RoundProgram.nrmQ M₀ 81 10 = 0 := by
  unfold QMCLeafB.RoundProgram.nrmQ QMCLeafB.RoundProgram.clipRat QMCLeafB.RoundProgram.inBoxR
    QMCLeafB.RoundPolySnap.snapDiv
  norm_num [snapTrunc_zero, M₀]

/-! ## 5.  The orbit: the run stalls at `diag(10/81, 0)` -/

theorem orbit1 : QMCLeafB.RoundProgram.stX (rnd^[1] s0) = [10 / 81, 0, 0, 10 / 27] := by
  have h := step_of_fields (s := s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (a := c₀) (b := c₀) stN_s0 rfl stX_s0 stT_s0 stMu_s0 stD_s0
    (by norm_num [c₀]) (by norm_num [c₀]) (by norm_num [c₀])
  show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round s0) = _
  rw [h, nrmQ_c₀, nrmQ_3c₀]

theorem stN_1 : QMCLeafB.RoundProgram.stN (rnd^[1] s0) = 2 := by
  rw [stN_iter, stN_s0]

theorem stA_1 : QMCLeafB.RoundProgram.stA (rnd^[1] s0) = QMCLeafB.RoundProgram.stA s0 := stA_iter 1 s0

theorem stT_1 : QMCLeafB.RoundProgram.stT (rnd^[1] s0) = t₁ := by rw [stT_iter, stT_s0]
theorem stMu_1 : QMCLeafB.RoundProgram.stMu (rnd^[1] s0) = M₀ := by rw [stMu_iter, stMu_s0]
theorem stD_1 : QMCLeafB.RoundProgram.stD (rnd^[1] s0) = 81 := by rw [stD_iter, stD_s0]

theorem orbit2 : QMCLeafB.RoundProgram.stX (rnd^[2] s0) = [10 / 81, 0, 0, 10 / 9] := by
  have h := step_of_fields (s := rnd^[1] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (a := 10 / 81) (b := 10 / 27) stN_1 stA_1 orbit1 stT_1 stMu_1 stD_1
    (by norm_num) (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round (rnd^[1] s0)) = _
  rw [h]
  have h3 : (3 : ℚ) * (10 / 27) = 10 / 9 := by norm_num
  rw [h3, nrmQ_10_81, nrmQ_10_9]

theorem stN_2 : QMCLeafB.RoundProgram.stN (rnd^[2] s0) = 2 := by
  rw [stN_iter, stN_s0]

theorem stA_2 : QMCLeafB.RoundProgram.stA (rnd^[2] s0) = QMCLeafB.RoundProgram.stA s0 := stA_iter 2 s0
theorem stT_2 : QMCLeafB.RoundProgram.stT (rnd^[2] s0) = t₁ := by rw [stT_iter, stT_s0]
theorem stMu_2 : QMCLeafB.RoundProgram.stMu (rnd^[2] s0) = M₀ := by rw [stMu_iter, stMu_s0]
theorem stD_2 : QMCLeafB.RoundProgram.stD (rnd^[2] s0) = 81 := by rw [stD_iter, stD_s0]

theorem orbit3 : QMCLeafB.RoundProgram.stX (rnd^[3] s0) = [10 / 81, 0, 0, 10 / 3] := by
  have h := step_of_fields (s := rnd^[2] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (a := 10 / 81) (b := 10 / 9) stN_2 stA_2 orbit2 stT_2 stMu_2 stD_2
    (by norm_num) (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round (rnd^[2] s0)) = _
  rw [h]
  have h3 : (3 : ℚ) * (10 / 9) = 10 / 3 := by norm_num
  rw [h3, nrmQ_10_81, nrmQ_10_3]

theorem stN_3 : QMCLeafB.RoundProgram.stN (rnd^[3] s0) = 2 := by
  rw [stN_iter, stN_s0]

theorem stA_3 : QMCLeafB.RoundProgram.stA (rnd^[3] s0) = QMCLeafB.RoundProgram.stA s0 := stA_iter 3 s0
theorem stT_3 : QMCLeafB.RoundProgram.stT (rnd^[3] s0) = t₁ := by rw [stT_iter, stT_s0]
theorem stMu_3 : QMCLeafB.RoundProgram.stMu (rnd^[3] s0) = M₀ := by rw [stMu_iter, stMu_s0]
theorem stD_3 : QMCLeafB.RoundProgram.stD (rnd^[3] s0) = 81 := by rw [stD_iter, stD_s0]

theorem orbit4 : QMCLeafB.RoundProgram.stX (rnd^[4] s0) = [10 / 81, 0, 0, 0] := by
  have h := step_of_fields (s := rnd^[3] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (a := 10 / 81) (b := 10 / 3) stN_3 stA_3 orbit3 stT_3 stMu_3 stD_3
    (by norm_num) (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round (rnd^[3] s0)) = _
  rw [h]
  have h3 : (3 : ℚ) * (10 / 3) = 10 := by norm_num
  rw [h3, nrmQ_10_81, nrmQ_ten]

theorem stN_4 : QMCLeafB.RoundProgram.stN (rnd^[4] s0) = 2 := by
  rw [stN_iter, stN_s0]

theorem stA_4 : QMCLeafB.RoundProgram.stA (rnd^[4] s0) = QMCLeafB.RoundProgram.stA s0 := stA_iter 4 s0
theorem stT_4 : QMCLeafB.RoundProgram.stT (rnd^[4] s0) = t₁ := by rw [stT_iter, stT_s0]
theorem stMu_4 : QMCLeafB.RoundProgram.stMu (rnd^[4] s0) = M₀ := by rw [stMu_iter, stMu_s0]
theorem stD_4 : QMCLeafB.RoundProgram.stD (rnd^[4] s0) = 81 := by rw [stD_iter, stD_s0]

/-- **The fixed point**: from `diag(10/81, 0)` the round does not move. -/
theorem orbit5 : QMCLeafB.RoundProgram.stX (rnd^[5] s0) = [10 / 81, 0, 0, 0] := by
  have h := step_of_fields (s := rnd^[4] s0) (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁)
    (a := 10 / 81) (b := 0) stN_4 stA_4 orbit4 stT_4 stMu_4 stD_4
    (by norm_num) (by norm_num) (by norm_num)
  show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round (rnd^[4] s0)) = _
  rw [h]
  have h3 : (3 : ℚ) * 0 = 0 := by norm_num
  rw [h3, nrmQ_10_81]
  norm_num [nrmQ_zero]

/-- The stall: from round `4` on, the primal code is `diag(10/81, 0)` for ever. -/
theorem stX_tail (T : ℕ) :
    QMCLeafB.RoundProgram.stX (rnd^[T] (rnd^[4] s0)) = [10 / 81, 0, 0, 0] := by
  induction T with
  | zero =>
      show QMCLeafB.RoundProgram.stX (rnd^[4] s0) = [10 / 81, 0, 0, 0]
      exact orbit4
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round (rnd^[k] (rnd^[4] s0))) = _
      have hNk : QMCLeafB.RoundProgram.stN (rnd^[k] (rnd^[4] s0)) = 2 := by
        rw [stN_iter, stN_4]
      have hAk : QMCLeafB.RoundProgram.stA (rnd^[k] (rnd^[4] s0))
          = QMCLeafB.RoundProgram.stA s0 := by
        rw [stA_iter, stA_4]
      have hTk : QMCLeafB.RoundProgram.stT (rnd^[k] (rnd^[4] s0)) = t₁ := by
        rw [stT_iter, stT_4]
      have hMk : QMCLeafB.RoundProgram.stMu (rnd^[k] (rnd^[4] s0)) = M₀ := by
        rw [stMu_iter, stMu_4]
      have hDk : QMCLeafB.RoundProgram.stD (rnd^[k] (rnd^[4] s0)) = 81 := by
        rw [stD_iter, stD_4]
      have h := step_of_fields (s := rnd^[k] (rnd^[4] s0))
        (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := 10 / 81) (b := 0)
        hNk hAk ih hTk hMk hDk (by norm_num) (by norm_num) (by norm_num)
      rw [h]
      have h3 : (3 : ℚ) * 0 = 0 := by norm_num
      rw [h3, nrmQ_10_81]
      norm_num [nrmQ_zero]

/-! ## 6.  No round of the campaign's run reads `ok` at the sliver -/

theorem cut_tail (T : ℕ) :
    (QMCLeafB.RoundProgram.oracleR (rnd^[T] (rnd^[4] s0))).1 = true := by
  have hNk : QMCLeafB.RoundProgram.stN (rnd^[T] (rnd^[4] s0)) = 2 := by
    rw [stN_iter, stN_4]
  have hAk : QMCLeafB.RoundProgram.stA (rnd^[T] (rnd^[4] s0)) = QMCLeafB.RoundProgram.stA s0 := by
    rw [stA_iter, stA_4]
  have hTk : QMCLeafB.RoundProgram.stT (rnd^[T] (rnd^[4] s0)) = t₁ := by
    rw [stT_iter, stT_4]
  have hMk : QMCLeafB.RoundProgram.stMu (rnd^[T] (rnd^[4] s0)) = M₀ := by
    rw [stMu_iter, stMu_4]
  have hDk : QMCLeafB.RoundProgram.stD (rnd^[T] (rnd^[4] s0)) = 81 := by
    rw [stD_iter, stD_4]
  exact cut_of_fields (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := 10 / 81) (b := 0)
    hNk hAk (stX_tail T) hTk hMk hDk (by norm_num) (by norm_num)

/-- **Every round of the campaign's run is a cut round at the sliver.** -/
theorem flag_cut (T : ℕ) : (QMCLeafB.RoundProgram.oracleR (rnd^[T] s0)).1 = true := by
  rcases Nat.lt_or_ge T 4 with h | h
  · interval_cases T
    · exact cut_of_fields (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := c₀) (b := c₀)
        stN_s0 rfl stX_s0 stT_s0 stMu_s0 stD_s0 (by norm_num [c₀]) (by norm_num [c₀])
    · exact cut_of_fields (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := 10 / 81) (b := 10 / 27)
        stN_1 stA_1 orbit1 stT_1 stMu_1 stD_1 (by norm_num) (by norm_num)
    · exact cut_of_fields (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := 10 / 81) (b := 10 / 9)
        stN_2 stA_2 orbit2 stT_2 stMu_2 stD_2 (by norm_num) (by norm_num)
    · exact cut_of_fields (A := QMCLeafB.RoundProgram.stA s0) (τ := t₁) (a := 10 / 81) (b := 10 / 3)
        stN_3 stA_3 orbit3 stT_3 stMu_3 stD_3 (by norm_num) (by norm_num)
  · obtain ⟨j, rfl⟩ : ∃ j, T = 4 + j := ⟨T - 4, by omega⟩
    rw [show 4 + j = j + 4 by omega, Function.iterate_add_apply]
    exact cut_tail j

/-! ## 7.  The verdict: `false`, at every horizon -/

theorem oks_replicate : ∀ T : ℕ,
    QMCLeafB.RoundProgram.stOks (rnd^[T] s0) = List.replicate T false := by
  intro T
  induction T with
  | zero =>
      show QMCLeafB.RoundProgram.stOks s0 = List.replicate 0 false
      rw [stOks_s0]
      rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      show QMCLeafB.RoundProgram.stOks (QMCLeafB.RoundProgram.round (rnd^[k] s0)) =
        List.replicate (k + 1) false
      rw [stOks_round_cut (flag_cut k), ih, List.replicate_succ']

theorem verdict_false (T : ℕ) : QMCLeafB.RoundProgram.verdict (rnd^[T] s0) = false := by
  have hoks := oks_replicate T
  have hnil : (List.replicate T false).filter id = [] := by
    induction T with
    | zero => rfl
    | succ k ih =>
        rw [List.replicate_succ]
        simp [ih]
  show decide (0 < ((QMCLeafB.RoundProgram.stOks (rnd^[T] s0)).filter id).length) = false
  rw [hoks, hnil]
  rfl

/-- The campaign's horizon `K·m` at the sliver. -/
def Tm : ℕ :=
  QMCLeafB.UnionShallow.Kbc2 (QMCLeafB.HalvePerG.mHalve (G₁.n * G₁.n)) G₁
    * QMCLeafB.HalvePerG.mHalve (G₁.n * G₁.n)

theorem campaignBit_eq : QMCLeafB.Audit2M5.campaignBit G₁ t₁
    = QMCLeafB.RoundProgram.verdict (rnd^[Tm] s0) := rfl

/-- **THE FALSIFICATION.**  The campaign's frozen program bit reads `false` at the sliver. -/
theorem campaignBit_sliver_false :
    QMCLeafB.Audit2M5.campaignBit G₁ t₁ = false := by
  rw [campaignBit_eq]
  exact verdict_false Tm

/-! ## 8.  The consequences: `ResidParts` and `Package` are uninhabited -/

/-- **The phase-25 residual is uninhabited at the campaign bit.**  `ResidParts` supplies a `RunParts`
at the sliver; the ball argument forces the bit `true` there; the frozen run reads `false`. -/
theorem not_residParts :
    ¬ Nonempty (QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
      QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  have htrue := QMCLeafB.BallM2.campaign_bit_true_at_sliver H
  rw [campaignBit_sliver_false] at htrue
  exact Bool.noConfusion htrue

/-- **THE FIFTH VACUITY: `Package` is uninhabited.** -/
theorem not_package : ¬ Nonempty QMCLeafB.Audit25M8.Package := by
  rintro ⟨P⟩
  exact not_residParts ⟨P.parts⟩

/-- The same, as a proof of `False` from a package. -/
theorem package_absurd (P : QMCLeafB.Audit25M8.Package) : False := not_package ⟨P⟩

/-- **The zip stroke `ZipM7.solution` is vacuous at the campaign bit** — its `ResidParts` slot
cannot be filled. -/
theorem zip_slot_empty :
    ¬ ∃ H : QMCLeafB.PartsM2.ResidParts QMCLeafB.Audit2M5.campaignBit
        QMCLeafB.UnionShallow.paramsKbc2, True := by
  rintro ⟨H, _⟩
  exact not_residParts ⟨H⟩

/-! ## 9.  What is *not* the obstruction: the un-pinched ok slot is non-vacuous

The kill is the program's frozen bit, not a certificate desert.  At the sliver an un-pinched
unit-diagonal member exists (`DichotM3.member_diag_one`), so any `ok` read at the leaf's own
tolerance is certifiable — the run simply never gets there. -/

theorem ok_slot_nonvacuous :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℚ,
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁) Q
        (t₁ - QMCLeafB.RundataCert.eps G₁)
        (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq ∧ ∀ i, Q i i = 1 :=
  QMCLeafB.DichotM3.member_diag_one

/-! ## 10.  Axiom receipts -/

#print axioms QMCLeafB.Falsify26M8.stepF_vec
#print axioms QMCLeafB.Falsify26M8.round_diag
#print axioms QMCLeafB.Falsify26M8.stX_s0
#print axioms QMCLeafB.Falsify26M8.orbit4
#print axioms QMCLeafB.Falsify26M8.stX_tail
#print axioms QMCLeafB.Falsify26M8.flag_cut
#print axioms QMCLeafB.Falsify26M8.verdict_false
#print axioms QMCLeafB.Falsify26M8.campaignBit_sliver_false
#print axioms QMCLeafB.Falsify26M8.not_residParts
#print axioms QMCLeafB.Falsify26M8.not_package
#print axioms QMCLeafB.Falsify26M8.ok_slot_nonvacuous

end QMCLeafB.Falsify26M8



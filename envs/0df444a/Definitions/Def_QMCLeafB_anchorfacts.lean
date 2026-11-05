-- Prove2me | Definitions.Def_QMCLeafB_anchorfacts
-- name    : QMCLeafB_anchorfacts
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T08:40:46.508719+00:00
-- url     : https://prove2.me/theorems/6b72e03c-e286-4a7a-90f2-5fea8012a6d6
-- title:
--   QMCLeafB anchorfacts
-- statement:
--   # Leaf B phase 23 — m2 / direction `concrete-anchor-fact-base`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_crater
import Definitions.Def_QMCLeafB_audit2
/-
# Leaf B phase 23 — m2 / direction `concrete-anchor-fact-base`

**The fact base at the sliver exemplar `(G₁, t₁)`, and the verdict it returns.**

`Check_crater_m2.not_coreDataG` kills the conduit shape `EndgameM2.CoreDataG` at
`(G₀, −99999/100000)` because the relaxed body there is **empty**, which forces `ok ≡ false`
below the horizon, which forces the whole-window trace budget to be read — and the engine's
λ-arithmetic (`CraterM2.per_round` / `sum_lb`) makes the cumulative trace exceed the pinched
ceiling `n(1 − dq/4)` after 20 rounds, while the campaign horizon is `K·m ≥ 279`.

`Check_audit2_m5` §5 believed that kill was *confined to the empty stratum* — that at the sliver
`(G₁, t₁)` (body nonempty, no pinched member) `CoreDataG` merely "owes" the drift pair.  This
file machine-checks that the kill is in fact **body-blind**: at `(G₁, t₁)` the em emptiness
hypothesis is not needed at all, because `no_pinched_member_G₁` already forces `ok ≡ false` below
the horizon (`Audit2M5.anchor3_gate`, first conjunct).  Everything else in the crater proof is
graph-independent once `n = 2`, `dq = 1/380000`, `rmax = 1/16`.

Consequences, all machine-checked below:

* `not_coreDataG_G₁ : ¬ Nonempty (CoreDataG o G₁ t₁ paramsKbc2)` — **for every verdict bit `o`**.
* `residSplit_forces_emptyBody` — `ResidSplit o paramsKbc2` *implies* the real relaxed body at
  `(G₁, t₁)` is empty; and since that body is in fact **nonempty** (`realBody_G₁`, an explicit
  real witness), `ResidSplit` is **uninhabited for every bit**
  (`residSplit_hypothesis_empty`).
* Hence the phase-22 "closure stroke" `Check_audit2_m5.solution_of_split` is **vacuous**: its
  hypothesis type is empty (`solution_of_split_is_vacuous`).  The residual of the leaf must be
  stated at `RunParts`/`RunData` level, exactly as `Audit2M5.audit_verdict` already demanded for
  the empty stratum.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
axiom audits at the end of every section.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.AnchorFactsM2

open QuantumMaxCutEnergy

/-! ## 1.  The exemplar and its campaign constants

The sliver input and threshold of `Check_emptybody_m5` §9 / `Check_audit2_m5` §5.  Every numeric
fact below is *graph-blind*: it depends on `G₁` only through `G₁.n = 2`, and on the campaign
family only through `rmax = rmaxOf 4 = 1/16` and `dq ≤ 1`, so the crater arithmetic transports
verbatim. -/

/-- The sliver input (two vertices, one edge of weight `1`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The campaign parameter family at `G₁`. -/
abbrev P₁ : QMCLeafB.FinalStroke.RunParams G₁ := QMCLeafB.UnionShallow.paramsKbc2 G₁

/-- The sliver threshold. -/
abbrev t₁ : ℚ := -(2 : ℚ) + 71 / 1520000

theorem hn₁ : 2 ≤ G₁.n := by
  show 2 ≤ 2
  norm_num

theorem n₁ : G₁.n = 2 := rfl

theorem hn4₁ : ((G₁.n * G₁.n : ℕ) : ℝ) = 4 := by
  rw [n₁]
  norm_num

theorem rmax₁ : (P₁.rmax : ℚ) = 1 / 16 := by
  show QMCLeafB.RundataHalving.rmaxOf (G₁.n * G₁.n) = 1 / 16
  unfold QMCLeafB.RundataHalving.rmaxOf
  rw [n₁]
  norm_num

theorem hrm1₁ : ((P₁.rmax : ℚ) : ℝ) ≤ 1 := by
  rw [rmax₁]
  norm_num

theorem hrmR₁ : ((P₁.rmax : ℚ) : ℝ) = 1 / 16 := by
  rw [rmax₁]
  norm_num

theorem qab₁ : QMCLeafB.CraterM2.qab G₁ P₁ hn₁ = 256 / 169 := by
  unfold QMCLeafB.CraterM2.qab
  rw [hrmR₁, n₁]
  unfold QMCLeafB.EngineIterates.alphaR QMCLeafB.EngineIterates.betaR
  norm_num

theorem UU₁ : ((QMCLeafB.CraterM2.uQ G₁ ⬝ᵥ QMCLeafB.CraterM2.uQ G₁ : ℚ) : ℝ) = 2 := by
  have h : (QMCLeafB.CraterM2.uQ G₁ ⬝ᵥ QMCLeafB.CraterM2.uQ G₁ : ℚ) = 2 := by
    have h1 := QMCLeafB.CraterM2.uQ_cast_dot (M := G₁.n) (QMCLeafB.CraterM2.uQ G₁)
    have h2 : QMCLeafB.RunPartsStream.dOne G₁.n ⬝ᵥ
        (fun i => ((QMCLeafB.CraterM2.uQ G₁ i : ℚ) : ℝ)) = QMCLeafB.RunPartsStream.dOne G₁.n ⬝ᵥ
        QMCLeafB.RunPartsStream.dOne G₁.n := rfl
    have h3 : QMCLeafB.RunPartsStream.dOne G₁.n ⬝ᵥ QMCLeafB.RunPartsStream.dOne G₁.n
        = QMCLeafB.DriftExact.diagSum (QMCLeafB.RunPartsStream.dOne G₁.n) :=
      QMCLeafB.DriftExact.dOne_dot _
    have h4 : QMCLeafB.DriftExact.diagSum (QMCLeafB.RunPartsStream.dOne G₁.n) = 2 := by
      rw [QMCLeafB.DriftExact.diagSum, n₁, Fin.sum_univ_two]
      rw [QMCLeafB.DriftExact.dOne_apply, QMCLeafB.DriftExact.dOne_apply]
      norm_num
    have h5 : ((QMCLeafB.CraterM2.uQ G₁ ⬝ᵥ QMCLeafB.CraterM2.uQ G₁ : ℚ) : ℝ) = 2 := by
      rw [h1, h2, h3, h4]
    exact_mod_cast h5
  rw [h]
  norm_num

theorem cap₁ : (8 : ℝ) ≤ ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ) := by
  unfold QMCLeafB.RundataArith.capOf
  rw [n₁]
  push_cast
  nlinarith [sq_nonneg ((P₁.dq : ℚ) : ℝ)]

/-- The engine's initial shape is `M⁻¹ • 1`, so the identity direction's form is at most `1/4`. -/
theorem UAU₁ (c : ℕ → Fin (G₁.n * G₁.n) → ℚ) (marg : ℕ → ℚ) :
    ((fun i => ((QMCLeafB.CraterM2.uQ G₁ i : ℚ) : ℝ)) ⬝ᵥ
      (QMCLeafB.EngineIterates.castM (QMCLeafB.CraterM2.Sh G₁ P₁ hn₁ c marg 0)
        *ᵥ fun i => ((QMCLeafB.CraterM2.uQ G₁ i : ℚ) : ℝ))) ≤ 1 / 4 := by
  have hA0 : QMCLeafB.EngineIterates.castM (QMCLeafB.CraterM2.Sh G₁ P₁ hn₁ c marg 0)
      = ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ)⁻¹ •
        (1 : Matrix (Fin (G₁.n * G₁.n)) (Fin (G₁.n * G₁.n)) ℝ) := by
    show QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G₁ P₁) = _
    rw [QMCLeafB.RunPartsDilate.A0P]
    exact QMCLeafB.Boundary.castM_initShapeOf (G₁.n * G₁.n) (QMCLeafB.RundataArith.capOf G₁ P₁.dq)
  rw [hA0, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hUU2 : ((fun i => ((QMCLeafB.CraterM2.uQ G₁ i : ℚ) : ℝ)) ⬝ᵥ
      (fun i => ((QMCLeafB.CraterM2.uQ G₁ i : ℚ) : ℝ))) = 2 := by
    rw [QMCLeafB.CraterM2.cast_dot]
    exact UU₁
  rw [hUU2]
  have hcap := cap₁
  have hpos : (0 : ℝ) < ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ) := by linarith
  have hcinv : ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ)⁻¹ ≤ 1 / 8 := by
    have h1 : ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ)⁻¹
        * ((QMCLeafB.RundataArith.capOf G₁ P₁.dq : ℚ) : ℝ) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hpos)
    nlinarith [hcap, hpos, h1]
  nlinarith

/-- **The κ decay at the campaign constants**, transported to `G₁`. -/
theorem kappa₁ (c : ℕ → Fin (G₁.n * G₁.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (16 : ℝ) * (169 / 256) ^ j ≤ ((QMCLeafB.CraterM2.kapQ G₁ P₁ hn₁ c marg j : ℚ) : ℝ) := by
  have h := QMCLeafB.CraterM2.kappa_lb G₁ P₁ hn₁ c marg j
  have hq : QMCLeafB.CraterM2.qab G₁ P₁ hn₁ = 256 / 169 := qab₁
  have hqq : (0 : ℝ) < (QMCLeafB.CraterM2.qab G₁ P₁ hn₁) ^ j := pow_pos (by rw [hq]; norm_num) j
  have hUU : ((QMCLeafB.CraterM2.uQ G₁ ⬝ᵥ QMCLeafB.CraterM2.uQ G₁ : ℚ) : ℝ) = 2 := UU₁
  rw [hUU] at h
  have hUAU := UAU₁ c marg
  have hκpos : (0 : ℝ) < ((QMCLeafB.CraterM2.kapQ G₁ P₁ hn₁ c marg j : ℚ) : ℝ) := by
    have := QMCLeafB.CraterM2.kappa_pos G₁ P₁ hn₁ c marg j
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ ((QMCLeafB.CraterM2.kapQ G₁ P₁ hn₁ c marg j : ℚ) : ℝ)
      * (QMCLeafB.CraterM2.qab G₁ P₁ hn₁) ^ j :=
    mul_nonneg hκpos.le hqq.le
  have h1 : (16 : ℝ) ≤ ((QMCLeafB.CraterM2.kapQ G₁ P₁ hn₁ c marg j : ℚ) : ℝ)
      * (QMCLeafB.CraterM2.qab G₁ P₁ hn₁) ^ j := by
    nlinarith [h, hUAU, hκpos, hqq, hnn]
  have h2 : ((QMCLeafB.CraterM2.kapQ G₁ P₁ hn₁ c marg j : ℚ) : ℝ)
      * (QMCLeafB.CraterM2.qab G₁ P₁ hn₁) ^ j * (169 / 256) ^ j
      ≥ 16 * (169 / 256) ^ j := by
    have h3 : (0 : ℝ) ≤ (169 / 256 : ℝ) ^ j := by positivity
    nlinarith [h1, h3]
  rw [hq, mul_assoc] at h2
  have hinv : (256 / 169 : ℝ) ^ j * (169 / 256) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hinv, mul_one] at h2
  linarith

/-- **The trace budget fails at `G₁` too**, at every normal and margin stream. -/
theorem budget_false₁ (c : ℕ → Fin (G₁.n * G₁.n) → ℚ) (marg : ℕ → ℚ) :
    ((1 - P₁.dq / 4 : ℚ) : ℝ) * (G₁.n : ℝ)
      < ∑ j ∈ Finset.range 20,
          QMCLeafB.DriftExact.engLam (G₁.n * G₁.n)
              (QMCLeafB.CraterM2.dcd G₁ P₁ hn₁ c marg) j
            * QMCLeafB.DriftExact.diagSum
                (QMCLeafB.EngineIterates.cutPR
                  (QMCLeafB.CraterM2.dcd G₁ P₁ hn₁ c marg) j) := by
  have hsum := QMCLeafB.CraterM2.sum_lb G₁ P₁ hn₁ c marg hrm1₁ hn4₁ hrmR₁ (kappa₁ c marg)
  have hceil : ((1 - P₁.dq / 4 : ℚ) : ℝ) * (G₁.n : ℝ) ≤ 2 := by
    have hq := QMCLeafB.RundataParams.dqShallow_pos G₁
    have hnn : (0 : ℝ) ≤ ((P₁.dq : ℚ) : ℝ) := by exact_mod_cast hq.le
    rw [n₁]
    push_cast
    nlinarith
  linarith

/-- **The horizon at `G₁` is far beyond the twenty rounds the trace needs.** -/
theorem Km₁ : 20 < P₁.K * P₁.m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
  unfold QMCLeafB.UnionShallow.Kbc2
  have hm := QMCLeafB.HalvePerG.one_le_mHalve (G₁.n * G₁.n)
  have hbc : 0 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G₁) := Nat.zero_le _
  have hn2 : G₁.n = 2 := n₁
  rw [hn2] at hm ⊢
  nlinarith [hm, hbc, Nat.mul_le_mul hm hm]

/-! ## 2.  The body-blindness of the `ok ≡ false` gate

`Check_audit2_m5.anchor3_gate` already observes that no `CoreDataG` at `(G₁, t₁)` can have a
`true` bit below the horizon: `recordsM2.cXst` pins the query centre's diagonal, and
`EmptyBodyM5.no_pinched_member_G₁` says no pinched matrix is a member.  That is the *entire*
input the crater argument needs — the emptiness of a body is only one way to make the gate fire.
Restated here as a standalone slot so the two lanes are visibly the same hypothesis. -/

/-- **`ok ≡ false` below the horizon at `(G₁, t₁)` — for every bit, from the pinch alone.** -/
theorem hok_false (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (D : QMCLeafB.EndgameM2.CoreDataG o G₁ t₁ P₁ hn₁) :
    ∀ k, k < P₁.K * P₁.m → D.ok k = false := by
  intro k hk
  cases h : D.ok k with
  | false => rfl
  | true =>
    exact absurd (D.hmem k hk h)
      (QMCLeafB.Audit2M5.anchor3_no_pinched_member
        (QMCLeafB.RecordsM2.cXst G₁.n D.X P₁.dq k)
        (fun i => QMCLeafB.RecordsM2.cXst_diag G₁.n D.X P₁.dq k i))

#print axioms QMCLeafB.AnchorFactsM2.hok_false

/-! ## 3.  The tally at `(G₁, t₁)`: the conduit shape is uninhabited

`Check_crater_m2.not_coreDataG`'s proof, with `hempty₀` replaced by §2 and the campaign constants
at `G₁` supplied by §1.  Nothing else changes: the engine's λ-arithmetic does not see the graph. -/

/-- **THE CRATER AT `(G₁, t₁)`, FOR EVERY BIT.**  The conduit shape `CoreDataG` is uninhabited at
the sliver exemplar — the point whose relaxed body is **nonempty** — for every verdict bit `o`.
The phase-22 reading (`audit2_m5` §5: "the whole drift pair is owed there") is therefore not an
obligation but an impossibility. -/
theorem not_coreDataG_G₁ (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG o G₁ t₁ P₁ hn₁) := by
  rintro ⟨D⟩
  have hok := hok_false o D
  have hdr := D.hdriftd 20 (hok 20 Km₁)
  rw [show QMCLeafB.RecordsM2.cXst G₁.n D.X P₁.dq 20
      = QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G₁.n (D.X 20)) P₁.dq from rfl]
    at hdr
  have hbudget := (QMCLeafB.RecordsM2.hdriftd_diagPinch_iff
    (cd := QMCLeafB.CraterM2.dcd G₁ P₁ hn₁ D.c D.marg)
    (Q := QMCLeafB.StateDiag.stMat G₁.n (D.X 20)) (k := 20)).1 hdr
  have hgt := budget_false₁ D.c D.marg
  linarith

#print axioms QMCLeafB.AnchorFactsM2.not_coreDataG_G₁

/-! ## 4.  The real relaxed body at `(G₁, t₁)` is NONEMPTY

`EmptyBodyM5.body_nonempty_G₁` gives a **rational** member of the analytic body
`RelaxMem (wMatrixQ G₁) Q₁ (t₁ − ε) dq`.  The `ResidSplit` stratum is keyed on the **real**
relaxed body at `t₁ − Rq/40000`, a *looser* threshold (`Rq/40000 < ε`), so `Q₁` cast to `ℝ` is a
member there too.  Proved directly over `ℝ` (no rational-to-real density bridge needed: the same
`nlinarith` certificate works in both fields). -/

theorem wMatrix_G₁_00 : QMCLeafB.wMatrix G₁ (0 : Fin 2) (0 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₁_11 : QMCLeafB.wMatrix G₁ (1 : Fin 2) (1 : Fin 2) = 0 :=
  QMCLeafB.wMatrix_apply_of_eq

theorem wMatrix_G₁_01 : QMCLeafB.wMatrix G₁ (0 : Fin 2) (1 : Fin 2) = 1 := by
  rw [QMCLeafB.wMatrix_apply_of_lt (show (0 : Fin 2) < 1 by decide)]
  norm_num [G₁]

theorem wMatrix_G₁_10 : QMCLeafB.wMatrix G₁ (1 : Fin 2) (0 : Fin 2) = 1 := by
  rw [QMCLeafB.wMatrix_apply_of_gt (show (0 : Fin 2) < 1 by decide)]
  norm_num [G₁]

/-- **A real member of the relaxed body at the sliver.** -/
theorem realBody_G₁ :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        (((t₁ : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
        (((P₁.dq : ℚ) : ℝ)) X := by
  have hRq : QMCLeafB.EngineRuntime.Rq G₁ = 2 := QMCLeafB.EmptyBodyM5.Rq_G₁
  have hdq : P₁.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq
  refine ⟨QMCLeafB.SepOracle.castMat QMCLeafB.EmptyBodyM5.Q₁, ?_, ?_, ?_⟩
  · -- the PSD margin, in `ℝ`, at `δ = 1/380000`
    intro x
    have hq : QMCLeafB.BallFloor.qfR (QMCLeafB.SepOracle.castMat QMCLeafB.EmptyBodyM5.Q₁) x
        = x 0 ^ 2 + x 1 ^ 2 + 2 * (-(1 + 3 / 3040000)) * (x 0 * x 1) := by
      rw [QMCLeafB.BallFloor.qfR_eq_sum]
      simp only [Fin.sum_univ_two, QMCLeafB.SepOracle.castMat_apply]
      simp only [QMCLeafB.EmptyBodyM5.Q₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Rat.cast_neg, Rat.cast_one,
        Rat.cast_add, Rat.cast_div, Rat.cast_ofNat]
      ring
    rw [hq, hdq]
    have hx : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by
      rw [Fin.sum_univ_two]
    rw [hx]
    nlinarith [sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]
  · -- unit diagonal
    intro i
    have hentries : ∀ j : Fin 2,
        QMCLeafB.SepOracle.castMat QMCLeafB.EmptyBodyM5.Q₁ j j
          = ((QMCLeafB.EmptyBodyM5.Q₁ j j : ℚ) : ℝ) := fun j =>
      QMCLeafB.SepOracle.castMat_apply _ _ _
    rw [hentries i, hdq]
    fin_cases i <;> norm_num [QMCLeafB.EmptyBodyM5.Q₁]
  · -- the objective, at the looser real threshold
    rw [hRq, hdq]
    have hentries : ∀ i j : Fin 2,
        QMCLeafB.SepOracle.castMat QMCLeafB.EmptyBodyM5.Q₁ i j
          = ((QMCLeafB.EmptyBodyM5.Q₁ i j : ℚ) : ℝ) := fun i j =>
      QMCLeafB.SepOracle.castMat_apply _ _ _
    rw [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
    simp only [hentries, QMCLeafB.EmptyBodyM5.Q₁, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, wMatrix_G₁_00, wMatrix_G₁_11, wMatrix_G₁_01, wMatrix_G₁_10,
      Rat.cast_neg, Rat.cast_one, Rat.cast_add, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
    norm_num

#print axioms QMCLeafB.AnchorFactsM2.realBody_G₁

/-! ## 5.  The verdict on the phase-22 split residual

`ResidSplit` demands `CoreDataG` at every interior point whose real body is **nonempty**.
`(G₁, t₁)` is such a point, so `ResidSplit` forces that body to be empty — and it is not.
Hence `ResidSplit` is uninhabited for every bit, and `solution_of_split` closes nothing. -/

/-- **`ResidSplit` forces the sliver body to be empty.** -/
theorem residSplit_forces_emptyBody (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (H : QMCLeafB.Audit2M5.ResidSplit o QMCLeafB.UnionShallow.paramsKbc2) :
    ¬ ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
          (((t₁ : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
          (((P₁.dq : ℚ) : ℝ)) X := by
  rintro ⟨X, hX⟩
  exact not_coreDataG_G₁ o ⟨H G₁ t₁ hn₁
    QMCLeafB.Audit2M5.anchor3_interior.1
    QMCLeafB.Audit2M5.anchor3_interior.2
    (fun hall => hall X hX)⟩

#print axioms QMCLeafB.AnchorFactsM2.residSplit_forces_emptyBody

/-- **`ResidSplit` is uninhabited, for every verdict bit.** -/
theorem residSplit_hypothesis_empty (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.Audit2M5.ResidSplit o QMCLeafB.UnionShallow.paramsKbc2) := by
  rintro ⟨H⟩
  exact residSplit_forces_emptyBody o H realBody_G₁

#print axioms QMCLeafB.AnchorFactsM2.residSplit_hypothesis_empty

/-- **The phase-22 closure stroke is vacuous**: `solution_of_split`'s hypothesis type is empty at
the campaign bit, so the stroke is true and closes nothing.  This is the third recurrence of the
vacuity defect (phase 20 `SolutionFinite`, phase 21 `ResidFinite`/`ResidG`, now phase 22
`ResidSplit`); the repair the earlier phases already identified stands: state the residual at the
leaf's own interface `FinalStroke.RunParts`/`RunData`, where the empty stratum and this sliver both
produce with no drift at all. -/
theorem solution_of_split_is_vacuous :
    ¬ Nonempty (QMCLeafB.Audit2M5.ResidSplit QMCLeafB.Audit2M5.campaignBit
        QMCLeafB.UnionShallow.paramsKbc2) :=
  residSplit_hypothesis_empty _

#print axioms QMCLeafB.AnchorFactsM2.solution_of_split_is_vacuous

end QMCLeafB.AnchorFactsM2



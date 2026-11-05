-- Prove2me | Definitions.Def_QMCLeafB_oklevel
-- name    : QMCLeafB_oklevel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T09:16:31.378475+00:00
-- url     : https://prove2.me/theorems/80485394-806e-4496-9d06-e153b5d1a1e4
-- title:
--   QMCLeafB oklevel
-- statement:
--   # Leaf B phase 24 — m5, direction d10: the ok-test level at the sliver
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_okprod2
/-
# Leaf B phase 24 — m5, direction d10: the ok-test level at the sliver

The `(G₁, t₁)` sliver (nonempty real body, no pinched member) is the one stratum of
`QMCLeafB.PartsM2.ResidParts` that still owes a `FinalStroke.RunParts`.  Two machine-checked facts in
the tree make it look like a certificate desert:

* `QMCLeafB.EmptyBodyM5.no_pinched_member_G₁` — no matrix with diagonal pinned to `1 - dq/4` is a
  `RelaxOracle.RelaxMem` at `(t₁ - ε)`, i.e. the engine's *pinched* stop test cannot fire there;
* `QMCLeafB.OkProd_M8.oracleV_not_ok_at_G₁` — consequently `OkLower.oracleV` answers `cut` at every
  state, so the campaign bit at `(G₁, t₁)` is forced `false` for the whole run.

This file shows that the obstruction is the *level* at which the stop test is read, and that it is not
a shortage of certificates.  `RunParts.hcert` asks for a unit-diagonal positive semidefinite `X` with
`tr(wMatrix G · X) ≤ t + ε` (i.e. at `t + Rq/40000`), while the engine reads its test at the *body*
level `t - ε + dq/2`.  The window between the two is `2ε - dq/2`, and the entire cost of the pinch
(`dq/4`, the loss `no_pinched_member_G₁` is made of) sits more than a hundred times inside it.  At
`(G₁, t₁)` the mint slot is *satisfied outright* by `!![1,-1;-1,1]`, whose objective is the exact
floor `-2`.

What this does and does not give: it does not build `RunParts` at the sliver (the remaining slot there
is `hcut`, genuine separation work), but it pins the residual: at the sliver the certificate slot is
free with 150× slack, so any ok-test read at the leaf's own tolerance `t + ε` is non-vacuous there.
`hcert_G₁` below is stated in the verbatim slot shape so that it plugs into `RunParts.hcert` directly.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.OkLevelM5

open QuantumMaxCutEnergy

/-! ## 1.  The two levels, and the window between them

`RundataCert.eps G = Rq G / 40000` is *both* the downward offset of the relaxed body
(`relaxBodyLE (wMatrix G) (t - Rq/40000) dq`) and the upward tolerance of the mint slot
(`RunParts.hcert`: `tr (wMatrix G · X) ≤ t + Rq/40000`).  The engine's stop test sits at the body
level `t - ε + dq/2`; the window from there to the mint tolerance is `2ε - dq/2`. -/

theorem eps_def (G : QuantumMaxCutEnergy.Input) :
    QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl

/-- The pinch loss at the sliver, in lowest terms: `dq/4 = 1/1520000`. -/
theorem pinch_loss_G₁ :
    (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4 = 1 / 1520000 := by
  rw [QMCLeafB.EmptyBodyM5.dq₁_eq]
  norm_num

/-- **The mint slack at the sliver**: the exact floor `-2` lies `147/1520000` below the leaf's own
tolerance `t₁ + ε`. -/
theorem mint_slack_G₁ :
    ((-(2 : ℚ) + 71 / 1520000 : ℚ)
        + QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000) - (-2) = 147 / 1520000 := by
  rw [QMCLeafB.EmptyBodyM5.Rq_G₁]
  norm_num

/-- **The finding in one equation**: the leaf's certificate allowance at the sliver is exactly `147`
times the pinch loss that makes the engine's stop test fail there. -/
theorem mint_slack_eq_147_pinch :
    ((-(2 : ℚ) + 71 / 1520000 : ℚ)
        + QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000) - (-2)
      = 147 * ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) := by
  rw [mint_slack_G₁, pinch_loss_G₁]
  norm_num

/-- **The window is positive at the campaign's constants.**  `2ε - dq/2 > 0` at `G₁`. -/
theorem window_pos :
    (0 : ℚ) < 2 * QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁
      - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 2 := by
  rw [QMCLeafB.EmptyBodyM5.eps_G₁, QMCLeafB.EmptyBodyM5.dq₁_eq]
  norm_num

/-- **The pinch cost sits a hundred times inside the window.**  The loss that
`no_pinched_member_G₁` is made of is `dq/4`; the window to the mint tolerance is `2ε - dq/2`. -/
theorem pinch_cost_well_inside :
    100 * ((QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4)
      < 2 * QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁
        - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 2 := by
  rw [QMCLeafB.EmptyBodyM5.eps_G₁, QMCLeafB.EmptyBodyM5.dq₁_eq]
  norm_num

/-- The same window at any input, in the engine's own terms: the engine's level
`t - ε + dq/2` is strictly below the leaf's mint tolerance `t + ε` as soon as `dq < 4ε`. -/
theorem engine_level_lt_mint {G : QuantumMaxCutEnergy.Input} {t dq : ℚ}
    (hdq : dq < 4 * QMCLeafB.RundataCert.eps G) :
    (t : ℝ) - (QMCLeafB.RundataCert.eps G : ℚ) + (dq : ℝ) / 2
      < (t : ℝ) + (QMCLeafB.RundataCert.eps G : ℚ) := by
  have h : (0 : ℚ) < 4 * QMCLeafB.RundataCert.eps G - dq := by linarith
  have h' : (0 : ℝ) < ((4 * QMCLeafB.RundataCert.eps G - dq : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- **Campaign-wide: the oracle tolerance is below `4ε`.**  `dq = dqShallow = ε/(9Rq+1)`. -/
theorem dq_lt_four_eps {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    (QMCLeafB.UnionShallow.paramsKbc2 G).dq < 4 * QMCLeafB.RundataCert.eps G := by
  have hpos : (0 : ℚ) < QMCLeafB.RundataCert.eps G := QMCLeafB.RundataCert.eps_pos G hRq
  have hRq' : (0 : ℚ) < QMCLeafB.EngineRuntime.Rq G := hRq
  rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg (ne_of_gt hRq')]
  unfold QMCLeafB.RundataParams.dqShallowCore
  have hden : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  have hle : QMCLeafB.RundataCert.eps G / (9 * QMCLeafB.EngineRuntime.Rq G + 1)
      ≤ QMCLeafB.RundataCert.eps G := by
    rw [div_le_iff₀ hden]
    nlinarith
  linarith

/-- **The level artefact is campaign-wide, not an exemplar accident.**  At every input with
`Rq G > 0` and every threshold, the engine's stop level `t - ε + dq/2` lies strictly below the
leaf's own mint tolerance `t + ε`. -/
theorem campaign_engine_level_lt_mint {G : QuantumMaxCutEnergy.Input}
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (t : ℚ) :
    (t : ℝ) - (QMCLeafB.RundataCert.eps G : ℚ)
        + ((QMCLeafB.UnionShallow.paramsKbc2 G).dq : ℝ) / 2
      < (t : ℝ) + (QMCLeafB.RundataCert.eps G : ℚ) :=
  engine_level_lt_mint (G := G) (t := t) (dq := (QMCLeafB.UnionShallow.paramsKbc2 G).dq)
    (dq_lt_four_eps hRq)

/-! ## 2.  The mint floor at `G₁`

`wMatrix G₁` is the adjacency matrix of a single edge of weight `1`, so
`tr (wMatrix G₁ · X) = X₀₁ + X₁₀`.  For any unit-diagonal positive semidefinite `X` this is `≥ -2`,
and `-2` is attained by `!![1,-1;-1,1]`.  So the leaf's certificate tolerance `t₁ + ε` clears the
floor by `2 + t₁ + ε = 71/1520000 + 1/20000 > 0`. -/

/-- `wMatrix G₁ = !![0,1;1,0]`. -/
theorem wMatrix_G₁ : QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ = !![(0 : ℝ), 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [QMCLeafB.wMatrix, QMCLeafB.EmptyBodyM5.G₁]

/-- The objective against the single edge: `tr (!![0,1;1,0] · X) = X₁₀ + X₀₁`. -/
theorem trace_edge_mul (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (!![(0 : ℝ), 1; 1, 0] * X).trace = X 1 0 + X 0 1 := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.of_apply, zero_mul, one_mul, zero_add, add_zero]

/-- The objective of `!![1,y;y,1]` against `wMatrix G₁` is `2y`. -/
theorem trace_wMatrix_G₁ (y : ℝ) :
    (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * !![(1 : ℝ), y; y, 1]).trace = 2 * y := by
  rw [wMatrix_G₁, trace_edge_mul]
  simp
  ring

/-- The quadratic form of a `2×2` real matrix at an explicit vector. -/
theorem qf_fin_two (X : Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) :
    (![a, b] : Fin 2 → ℝ) ⬝ᵥ (X *ᵥ ![a, b])
      = a * a * X 0 0 + a * b * X 0 1 + b * a * X 1 0 + b * b * X 1 1 := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

/-- On `Fin 2` the star of a real vector is the vector itself. -/
theorem star_fin_two_vec (a b : ℝ) :
    star (![a, b] : Fin 2 → ℝ) = ![a, b] := by
  funext i
  fin_cases i <;> simp

/-- **The 2×2 unit-diagonal bound**: a positive semidefinite matrix with unit diagonal has
`|X₀₁| ≤ 1`.  This is the whole content of the mint floor. -/
theorem offdiag_abs_le_one {X : Matrix (Fin 2) (Fin 2) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) : |X 0 1| ≤ 1 := by
  have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hX).2
  have hsymm : X 1 0 = X 0 1 := by
    have hh : X.IsHermitian := hX.1
    have := hh.apply 0 1
    simpa using this
  have hp : 0 ≤ 2 + 2 * X 0 1 := by
    have h1 := h (![1, 1] : Fin 2 → ℝ)
    rw [star_fin_two_vec, qf_fin_two, hdiag 0, hdiag 1, hsymm] at h1
    linarith
  have hq : 0 ≤ 2 - 2 * X 0 1 := by
    have h1 := h (![1, -1] : Fin 2 → ℝ)
    rw [star_fin_two_vec, qf_fin_two, hdiag 0, hdiag 1, hsymm] at h1
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **The mint floor at `G₁`**: every unit-diagonal positive semidefinite matrix has objective `≥ -2`. -/
theorem trace_floor_G₁ {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.AnswerProducer.IsUnitDiagPSD X) :
    -2 ≤ (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * X).trace := by
  obtain ⟨hpsd, hdiag⟩ := hX
  have hsymm : X 1 0 = X 0 1 := by
    have := hpsd.1.apply 0 1
    simpa using this
  have hb := offdiag_abs_le_one hpsd hdiag
  rw [wMatrix_G₁, trace_edge_mul]
  rw [abs_le] at hb
  linarith

/-- `!![1,-1;-1,1]` is positive semidefinite: it is `vecMulVec v v` at `v = ![1,-1]`. -/
theorem posSemidef_sliver :
    (!![(1 : ℝ), -1; -1, 1]).PosSemidef := by
  have h : (!![(1 : ℝ), -1; -1, 1])
      = Matrix.vecMulVec (fun i : Fin 2 => ![(-1 : ℝ), 1] i)
          (star (fun i : Fin 2 => ![(-1 : ℝ), 1] i)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star _

/-- The sliver's mint witness is unit-diagonal. -/
theorem isUnitDiagPSD_sliver :
    QMCLeafB.AnswerProducer.IsUnitDiagPSD (!![(1 : ℝ), -1; -1, 1]) := by
  refine ⟨posSemidef_sliver, ?_⟩
  intro i
  fin_cases i <;> simp

/-! ## 3.  The residual's `hcert` slot, satisfied verbatim at `(G₁, t₁)` -/

/-- **`RunParts.hcert`'s conclusion holds at `(G₁, t₁)`**, in the verbatim slot shape
(`IsUnitDiagPSD X` and `tr (wMatrix G₁ · X) ≤ t₁ + Rq G₁ / 40000`).  The slack is `71/1520000 +
1/20000`, i.e. the mint slot at the sliver is not a certificate shortage. -/
theorem hcert_G₁ :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * X).trace
          ≤ ((-(2 : ℚ) + 71 / 1520000 : ℚ) : ℝ)
            + ((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ) : ℝ) := by
  refine ⟨!![(1 : ℝ), -1; -1, 1], isUnitDiagPSD_sliver, ?_⟩
  rw [trace_wMatrix_G₁]
  rw [QMCLeafB.EmptyBodyM5.Rq_G₁]
  norm_num

/-- **The `hcert` slot of `RunParts` at `(G₁, t₁)`, discharged for every ok stream.**  This is the
slot in its verbatim binder shape (`P.K * P.m`, `ok k = true`), so it plugs straight into a
`FinalStroke.RunParts` term at `(G₁, t₁)` and leaves `hcut` as the only real obligation there. -/
theorem hcert_slot_G₁ (K m : ℕ) (ok : ℕ → Bool) :
    ∀ k, k < K * m → ok k = true →
      ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * X).trace
            ≤ ((-(2 : ℚ) + 71 / 1520000 : ℚ) : ℝ)
              + ((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ) : ℝ) :=
  fun _ _ _ => hcert_G₁

/-- The same for any threshold above the mint floor `-2`. -/
theorem hcert_G₁_of_threshold {t : ℚ}
    (ht : -(2 : ℚ) - QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 ≤ t) :
    ∃ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ) : ℝ) := by
  refine ⟨!![(1 : ℝ), -1; -1, 1], isUnitDiagPSD_sliver, ?_⟩
  rw [trace_wMatrix_G₁]
  have h : ((-(2 : ℚ) - QMCLeafB.EngineRuntime.Rq QMCLeafB.EmptyBodyM5.G₁ / 40000 : ℚ) : ℝ)
      ≤ (t : ℝ) := by exact_mod_cast ht
  push_cast at h ⊢
  linarith

/-! ## 4.  The contrast, at the tree's own statements

`no_pinched_member_G₁` says the engine's pinned stop test is unsatisfiable at `(G₁, t₁)`, while §3
exhibits a matrix meeting the *leaf's* mint tolerance with slack.  Together with
`oracleV_not_ok_at_G₁` (every run state there answers `cut`), this locates the sliver's difficulty
entirely in the cut slot `hcut` — the only `RunParts` slot that is not free at a false-bit point —
and shows that moving the stop test from the body level to the leaf's own tolerance is both sound
(`hcert` is exactly that existential) and non-vacuous (it is satisfiable at the sliver). -/

/-- **The sliver's separation is the only obstruction**: at `(G₁, t₁)` the mint slot is satisfiable
while the engine's pinned stop test is not.  Stated as the pair of facts, for use as a plug. -/
theorem sliver_mint_not_obstruction :
    (∃ X : Matrix (Fin 2) (Fin 2) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix QMCLeafB.EmptyBodyM5.G₁ * X).trace ≤ (0 : ℝ)) ∧
      (∀ Q : Matrix (Fin 2) (Fin 2) ℚ,
        (∀ i, Q i i = 1 - (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq / 4) →
        ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ QMCLeafB.EmptyBodyM5.G₁) Q
            ((-(2 : ℚ) + 71 / 1520000) - QMCLeafB.RundataCert.eps QMCLeafB.EmptyBodyM5.G₁)
            (QMCLeafB.UnionShallow.paramsKbc2 QMCLeafB.EmptyBodyM5.G₁).dq) := by
  refine ⟨⟨!![(1 : ℝ), -1; -1, 1], isUnitDiagPSD_sliver, ?_⟩,
    QMCLeafB.EmptyBodyM5.no_pinched_member_G₁⟩
  rw [trace_wMatrix_G₁]
  norm_num



/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.OkLevelM5.pinch_loss_G₁
#print axioms QMCLeafB.OkLevelM5.mint_slack_G₁
#print axioms QMCLeafB.OkLevelM5.mint_slack_eq_147_pinch
#print axioms QMCLeafB.OkLevelM5.eps_def
#print axioms QMCLeafB.OkLevelM5.window_pos
#print axioms QMCLeafB.OkLevelM5.pinch_cost_well_inside
#print axioms QMCLeafB.OkLevelM5.engine_level_lt_mint
#print axioms QMCLeafB.OkLevelM5.dq_lt_four_eps
#print axioms QMCLeafB.OkLevelM5.campaign_engine_level_lt_mint
#print axioms QMCLeafB.OkLevelM5.wMatrix_G₁
#print axioms QMCLeafB.OkLevelM5.trace_edge_mul
#print axioms QMCLeafB.OkLevelM5.trace_wMatrix_G₁
#print axioms QMCLeafB.OkLevelM5.qf_fin_two
#print axioms QMCLeafB.OkLevelM5.offdiag_abs_le_one
#print axioms QMCLeafB.OkLevelM5.trace_floor_G₁
#print axioms QMCLeafB.OkLevelM5.posSemidef_sliver
#print axioms QMCLeafB.OkLevelM5.isUnitDiagPSD_sliver
#print axioms QMCLeafB.OkLevelM5.hcert_G₁
#print axioms QMCLeafB.OkLevelM5.hcert_slot_G₁
#print axioms QMCLeafB.OkLevelM5.hcert_G₁_of_threshold
#print axioms QMCLeafB.OkLevelM5.sliver_mint_not_obstruction

end QMCLeafB.OkLevelM5



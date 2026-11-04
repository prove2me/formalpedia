-- Prove2me | Definitions.Def_QMCLeafB_crater
-- name    : QMCLeafB_crater
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:56:35.543106+00:00
-- url     : https://prove2.me/theorems/da706595-9096-44c5-9812-14fe7849c625
-- title:
--   QMCLeafB crater
-- statement:
--   # leaf B phase 22 — THE CRATER IS UNSATISFIABLE: no free normal stream saves the trace budget
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_endgame_m2
import Definitions.Def_QMCLeafB_emptybody
/-
# leaf B phase 22 — THE CRATER IS UNSATISFIABLE: no free normal stream saves the trace budget
(swarm `smw1ntur6`, member m2, direction d2 `crater-construction`)

## What this file checks

Phase 21 left one analytic crater: at a **refuted** interior point (empty relaxed body) the
horizon-bounded residual `EndgameM2.CoreDataG`/`CoreDataB` asks for the drift pair at the run's
own stream below the horizon `K·m`.  m8's `Check_cutbudget_m8` killed the *trace-direction drill*
at every multiplier `λ`, and phase 21 left route (a) open: **the stream is a free construction at
an empty body, so maybe some clever choice of normals satisfies the trace budget**
(`hdriftd`) after all.  Route (a) is what this file refutes.

## The mechanism

`EndgameM2.CoreDataG` supplies the cut records `C k`, their margins `marg k` and their normals
`c k`; the engine's normal at round `k` is however **not** free — it is the dilated stream

    cn k = c k + λ_k • 1       (`RecordM2.cnInd`),

`λ_k` being the sequential depth multiplier `RecordM2.lamInd`.  The trace budget is exactly

    ∑_{j<k} γ_j/√σ_j · tr(p_j) ≤ (1 − dq/4)·n ,     p_j = A_j⁻¹ cn_j ,

i.e. the trace of the engine's centre stays under the pinched centre's trace.  Two facts force
every single increment to be positive:

* `λ_k ≥ lamThr k / lamCoeff k`, and `lamThr k` contains the terms `2·a_k`, `T_k²` and the additive
  `+1` (`9marg²/(4rmax²)+1`), while `lamCoeff k = κ_k = ⟨1,1⟩_{A_k}` — so
  `λ_k κ_k ≥ 2|a_k| + T_k² + 1`;
* consequently the numerator `N_k = ⟨1, cn_k⟩_{A_k} = a_k + λ_kκ_k` obeys
  `N_k ≥ |a_k| + T_k² + 1 > 0`, and the elementary identity
  `(κ+4)·N² − 4κ·σ = κ·(N² − 4T²) + 4a² ≥ 0` (with `(a+b)² ≥ (T²+1)² ≥ 4T²`) gives

      √(4κ_k/(κ_k+4)) ≤ N_k/√σ_k ,     so   increment_k ≥ (1−rmax)/(N+1)·√(4κ_k/(κ_k+4)) .

  Dictatorship of the *direction* over the *scale*: this is exactly the `λ`-invariance m8 found,
  now with the sharp constant.
* `κ_k` cannot decay arbitrarily fast either: one step in the A-metric gives
  `vᵀA_{k+1}v ≤ α(1+β)·vᵀA_kv` with `α(1+β) = (N+1)²/(N+rmax)²`, so
  `κ_k ≥ κ_0·(169/256)^k` at `N = 4, rmax = 1/16`.

So the cumulative sum is bounded *below* by a geometric series that leaves `n(1−dq/4)` behind
after 20 rounds — while the campaign horizon is `K·m ≥ 279` at `n = 2`.  At an empty body every
round below the horizon is a cut round (`hmem` is unsatisfiable), so `hdriftd` is read at every
`k < K·m` and the contradiction is immediate.

## Consequences (machine-checked at the phase-19/20 refuting input `G₀`, threshold `t₀`)

* `CoreDataG`, `CoreDataB`, `CoreDataScalarB` are **uninhabited** at `(G₀, t₀)` — for every
  verdict bit, every normal stream, every margin stream.
* `ResidG`, `ResidB`, `ResidScalarB` are therefore **false**: route (a) does not exist, and the
  campaign must widen the ceiling (route (b)) or restate the drift obligation away from the
  pinched trace budget.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audits at the end of every section.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CraterM2

open QuantumMaxCutEnergy

/-! ## 1.  The scalar core

`(κ+4)·(a+b)² − 4κ·(T² + 2ab/κ + b²/κ) = κ·((a+b)² − 4T²) + 4a²`, and `b ≥ 2|a| + T² + 1`
forces `(a+b)² ≥ (|a| + T² + 1)² ≥ (T²+1)² ≥ 4T²`.  So the trace increment is bounded below by the
*sharp* direction-optimal constant `√(4κ/(κ+4))` — no Cauchy–Schwarz loss anywhere. -/

/-- **The scalar core of the refutation.**  With `b ≥ 2|a| + T² + 1` the trace increment
`N/√σ` (`N = a+b`, `σ = T² + 2ab/κ + b²/κ`) dominates `√(4κ/(κ+4))`. -/
theorem alg_core_b {κ T2 a b : ℝ} (hκ : 0 < κ) (hT2 : 0 ≤ T2) (hb : 2 * |a| + T2 + 1 ≤ b) :
    4 * κ * (T2 + 2 * a * b / κ + b ^ 2 / κ) ≤ (κ + 4) * (a + b) ^ 2 := by
  have h2 : |a| + T2 + 1 ≤ a + b := by
    have h3 : a + 2 * |a| + T2 + 1 ≤ a + b := by linarith
    have h4 : |a| ≤ a + 2 * |a| := by
      have := neg_abs_le a
      linarith
    linarith
  have h5 : (0 : ℝ) ≤ |a| + T2 + 1 := by positivity
  have h8 : (|a| + T2 + 1) ^ 2 ≤ (a + b) ^ 2 := by
    have hp : (0 : ℝ) ≤ (a + b - (|a| + T2 + 1)) * (a + b + (|a| + T2 + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hp]
  have h9 : (T2 + 1) ^ 2 ≤ (|a| + T2 + 1) ^ 2 := by
    have hp : (0 : ℝ) ≤ |a| * (|a| + 2 * (T2 + 1)) :=
      mul_nonneg (abs_nonneg a) (by linarith)
    nlinarith [hp]
  have h6 : 4 * T2 ≤ (a + b) ^ 2 := by
    nlinarith [h8, h9, sq_nonneg (T2 - 1)]
  have heq : (κ + 4) * (a + b) ^ 2 - 4 * κ * (T2 + 2 * a * b / κ + b ^ 2 / κ)
      = κ * ((a + b) ^ 2 - 4 * T2) + 4 * a ^ 2 := by
    field_simp
    ring
  have h7 : 0 ≤ κ * ((a + b) ^ 2 - 4 * T2) + 4 * a ^ 2 := by
    have := sq_nonneg a
    nlinarith
  linarith

/-- **The scalar core, in the multiplier form actually met at a round**: `b = λ·κ`. -/
theorem alg_core {κ T2 a lam : ℝ} (hκ : 0 < κ) (hT2 : 0 ≤ T2)
    (hb : 2 * |a| + T2 + 1 ≤ lam * κ) :
    4 * κ * (T2 + 2 * lam * a + lam ^ 2 * κ) ≤ (κ + 4) * (a + lam * κ) ^ 2 := by
  have hk : (κ : ℝ) ≠ 0 := ne_of_gt hκ
  have hmain := alg_core_b (κ := κ) (T2 := T2) (a := a) (b := lam * κ) hκ hT2 hb
  have hconv1 : 2 * a * (lam * κ) / κ = 2 * lam * a := by
    field_simp
  have hconv2 : (lam * κ) ^ 2 / κ = lam ^ 2 * κ := by
    field_simp
  rw [hconv1, hconv2] at hmain
  linarith [hmain]

#print axioms QMCLeafB.CraterM2.alg_core

 /-- `v ⬝ ((A+B) v) = v ⬝ (A v) + v ⬝ (B v)`. -/
theorem qf_add {M : ℕ} (A B : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    v ⬝ᵥ ((A + B) *ᵥ v) = v ⬝ᵥ (A *ᵥ v) + v ⬝ᵥ (B *ᵥ v) := by
  rw [Matrix.add_mulVec, dotProduct_add]

/-- `v ⬝ ((x • A) v) = x · v ⬝ (A v)`. -/
theorem qf_smul {M : ℕ} (x : ℝ) (A : Matrix (Fin M) (Fin M) ℝ) (v : Fin M → ℝ) :
    v ⬝ᵥ ((x • A) *ᵥ v) = x * (v ⬝ᵥ (A *ᵥ v)) := by
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- `v ⬝ ((c cᵀ) v) = (c ⬝ v)²`. -/
theorem qf_vmv {M : ℕ} (c v : Fin M → ℝ) :
    v ⬝ᵥ (Matrix.vecMulVec c c *ᵥ v) = (c ⬝ᵥ v) ^ 2 := by
  rw [Matrix.vecMulVec_mulVec]
  simp [dotProduct_comm v c, smul_eq_mul, sq]

/-! ## 2.  The abstract step bound at one round

The engine's data at round `k`: a positive-definite shape `A`, the dilated normal `C + λ·1`, its
witness `P` (`A P = C + λ·1`), the witness `PU` of the identity direction `1` and the witness `PC`
of the supplied normal `C`.  Everything the trace increment needs is read off these three witness
relations — no matrix inverse appears. -/

/-- `(A x) ⬝ y = x ⬝ (A y)` for a symmetric `A`. -/
theorem dot_mulVec_swap {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hsym : Aᵀ = A)
    (x y : Fin N → ℝ) : (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := by
  rw [dotProduct_comm (A *ᵥ x) y, dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym,
    dotProduct_comm]

/-- **The abstract per-round bound.**  If the dilated normal `C + λ·1` has witness `P` and the
multiplier dominates the depth threshold (`2|a| + T² + 1 ≤ λ κ`), then the round's trace increment
dominates `√(4κ/(κ+4))`, where `κ = ⟨1,1⟩_A`. -/
theorem step_abs {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {U C PU PC P : Fin N → ℝ} {lam : ℝ}
    (hPU : A *ᵥ PU = U) (hPC : A *ᵥ PC = C) (hP : A *ᵥ P = C + lam • U)
    (hcn : C + lam • U ≠ 0) (hU : U ≠ 0)
    (hthr : 2 * |C ⬝ᵥ PU| + (C ⬝ᵥ PC) + 1 ≤ lam * (U ⬝ᵥ PU)) :
    Real.sqrt (4 * (U ⬝ᵥ PU) / (U ⬝ᵥ PU + 4))
      ≤ (U ⬝ᵥ P) / Real.sqrt ((C + lam • U) ⬝ᵥ P) := by
  have hsym : Aᵀ = A := QMCLeafB.EngineIterates.transpose_of_posDef hA
  have hbil : ∀ x y : Fin N → ℝ, (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (A *ᵥ y) := dot_mulVec_swap hsym
  have hPU0 : PU ≠ 0 := by
    intro h
    apply hU
    rw [← hPU, h, Matrix.mulVec_zero]
  have hP0 : P ≠ 0 := by
    intro h
    apply hcn
    rw [← hP, h, Matrix.mulVec_zero]
  -- `κ > 0`, `T² ≥ 0`, `σ > 0`
  have hκ : (0 : ℝ) < U ⬝ᵥ PU := by
    have h1 : (0 : ℝ) < PU ⬝ᵥ (A *ᵥ PU) := hA.dotProduct_mulVec_pos hPU0
    rw [hPU, dotProduct_comm] at h1
    exact h1
  have hT2 : (0 : ℝ) ≤ C ⬝ᵥ PC := by
    have h1 : (0 : ℝ) ≤ PC ⬝ᵥ (A *ᵥ PC) := by
      simpa using hA.posSemidef.dotProduct_mulVec_nonneg PC
    rw [hPC, dotProduct_comm] at h1
    exact h1
  have hσ : (0 : ℝ) < (C + lam • U) ⬝ᵥ P := by
    have h1 : (0 : ℝ) < P ⬝ᵥ (A *ᵥ P) := hA.dotProduct_mulVec_pos hP0
    rw [hP, dotProduct_comm] at h1
    exact h1
  -- the two linear readings
  have e1 : U ⬝ᵥ P = PU ⬝ᵥ (C + lam • U) := by
    calc U ⬝ᵥ P = (A *ᵥ PU) ⬝ᵥ P := by rw [hPU]
      _ = PU ⬝ᵥ (A *ᵥ P) := hbil PU P
      _ = PU ⬝ᵥ (C + lam • U) := by rw [hP]
  have e2 : PU ⬝ᵥ (C + lam • U) = C ⬝ᵥ PU + lam * (U ⬝ᵥ PU) := by
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm PU C,
      dotProduct_comm PU U]
  have hUP : U ⬝ᵥ P = C ⬝ᵥ PU + lam * (U ⬝ᵥ PU) := by
    rw [e1, e2]
  have e3 : PC ⬝ᵥ U = (A *ᵥ PC) ⬝ᵥ PU := by
    calc PC ⬝ᵥ U = PC ⬝ᵥ (A *ᵥ PU) := by rw [hPU]
      _ = (A *ᵥ PC) ⬝ᵥ PU := (hbil PC PU).symm
  have e4 : PC ⬝ᵥ U = C ⬝ᵥ PU := by
    rw [e3, hPC]
  have e5 : C ⬝ᵥ P = PC ⬝ᵥ (C + lam • U) := by
    calc C ⬝ᵥ P = (A *ᵥ PC) ⬝ᵥ P := by rw [hPC]
      _ = PC ⬝ᵥ (A *ᵥ P) := hbil PC P
      _ = PC ⬝ᵥ (C + lam • U) := by rw [hP]
  have hCP : C ⬝ᵥ P = C ⬝ᵥ PC + lam * (C ⬝ᵥ PU) := by
    rw [e5, dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_comm PC C, e4]
  -- the dilation identity for `σ`
  have hσeq : (C + lam • U) ⬝ᵥ P
      = (C ⬝ᵥ PC) + 2 * lam * (C ⬝ᵥ PU) + lam ^ 2 * (U ⬝ᵥ PU) := by
    rw [add_dotProduct, smul_dotProduct, smul_eq_mul, hCP, hUP]
    ring
  have hcore := alg_core hκ hT2 hthr
  have hN : (0 : ℝ) < U ⬝ᵥ P := by
    rw [hUP]
    have h1 := neg_abs_le (C ⬝ᵥ PU)
    have h2 := abs_nonneg (C ⬝ᵥ PU)
    linarith
  have hkey : 4 * (U ⬝ᵥ PU) * ((C + lam • U) ⬝ᵥ P)
      ≤ (U ⬝ᵥ PU + 4) * (U ⬝ᵥ P) ^ 2 := by
    rw [hσeq, hUP]
    exact hcore
  have hκ4 : (0 : ℝ) < U ⬝ᵥ PU + 4 := by linarith
  have hgoal2 : 4 * (U ⬝ᵥ PU) / (U ⬝ᵥ PU + 4) * ((C + lam • U) ⬝ᵥ P)
      ≤ (U ⬝ᵥ P) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hκ4]
    linarith [hkey]
  rw [le_div_iff₀ (Real.sqrt_pos.2 hσ), mul_comm]
  calc Real.sqrt ((C + lam • U) ⬝ᵥ P) * Real.sqrt (4 * (U ⬝ᵥ PU) / (U ⬝ᵥ PU + 4))
      = Real.sqrt ((4 * (U ⬝ᵥ PU) / (U ⬝ᵥ PU + 4)) * ((C + lam • U) ⬝ᵥ P)) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]
    _ ≤ Real.sqrt ((U ⬝ᵥ P) ^ 2) := Real.sqrt_le_sqrt hgoal2
    _ = U ⬝ᵥ P := Real.sqrt_sq hN.le

#print axioms QMCLeafB.CraterM2.alg_core_b
#print axioms QMCLeafB.CraterM2.alg_core
#print axioms QMCLeafB.CraterM2.dot_mulVec_swap
#print axioms QMCLeafB.CraterM2.qf_add
#print axioms QMCLeafB.CraterM2.qf_smul
#print axioms QMCLeafB.CraterM2.qf_vmv
#print axioms QMCLeafB.CraterM2.step_abs



/-! ## 3.  The engine's chain at the dilated stream, and the decay of `κ`

The trace increment's lower bound degrades only as `√κ`, where `κ_j = ⟨1,1⟩_{A_j}`.  So the second
half of the refutation is the statement that `κ` cannot collapse: one GLS step gives
`vᵀA_{j+1}v ≤ α(1+β)·vᵀA_jv` with `α(1+β) = (N+1)²/(N+rmax)²`, hence
`vᵀA_jv ≤ q^j vᵀA_0v`, and then `κ_j ≥ (1⬝1)²/(1ᵀA_j1) ≥ (1⬝1)²/(q^j·1ᵀA_01)`. -/

section Engine

variable (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)

/-- The dilated normal stream of a supplied normal/margin pair. -/
abbrev dcn (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) : ℕ → Fin (G.n * G.n) → ℚ :=
  QMCLeafB.EndgameM2.gCn G P hn c marg

/-- The engine's recorded cut stream at that normal stream. -/
abbrev dcd (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  QMCLeafB.EndgameM2.gStream G P hn c marg

/-- The engine's shape at round `j`. -/
abbrev Sh (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.RunPartsDilate.runShape G P hn (dcn G P hn c marg)
    (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j

/-- The engine's witness at round `j` is the proof-free `witRel` of the shape. -/
theorem dcd_p_eq (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (dcd G P hn c marg j).p
      = QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (dcn G P hn c marg j) := by
  have h := QMCLeafB.RecordM2.witAt_eq_witRel G P hn (dcn G P hn c marg)
    (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) (dcn G P hn c marg j) j
  rw [← QMCLeafB.RecordM2.runShape_eq_shapeVal] at h
  rw [show (dcd G P hn c marg j).p
      = QMCLeafB.RunPartsDilate.witAt G P hn (dcn G P hn c marg)
        (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) (dcn G P hn c marg j) j from rfl, h]

theorem Sh_posDef (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)).PosDef :=
  (QMCLeafB.RunPartsDilate.runChain G P hn _ _ j).2

/-- The witness relation of round `j`, over `ℝ`. -/
theorem Sh_witR (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)
        *ᵥ (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ))
      = fun i => (((dcn G P hn c marg j) i : ℚ) : ℝ) := by
  have h := QMCLeafB.RunPartsDilate.runShape_mulVec_wit G P hn (dcn G P hn c marg)
    (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j
  show QMCLeafB.EngineIterates.castM
      (QMCLeafB.RunPartsDilate.runShape G P hn (dcn G P hn c marg)
        (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j)
      *ᵥ (fun i => ((QMCLeafB.RunPartsDilate.runWit G P hn (dcn G P hn c marg)
        (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j i : ℚ) : ℝ))
    = fun i => (((dcn G P hn c marg j) i : ℚ) : ℝ)
  rw [QMCLeafB.EngineIterates.cast_mulVec, h]

/-- The step recurrence of the shape, over `ℝ`. -/
theorem Sh_step (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.EngineIterates.castM (Sh G P hn c marg (j + 1))
      = QMCLeafB.EngineIterates.stepShape (G.n * G.n)
          (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j))
          (QMCLeafB.EngineIterates.cutCR (dcd G P hn c marg) j)
          (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j) ((P.rmax : ℚ) : ℝ) := by
  have h := QMCLeafB.EngineIterates.rStep_cast
    (n := G.n * G.n) (A := Sh G P hn c marg j) (c := (dcd G P hn c marg j).c)
    (p := (dcd G P hn c marg j).p) (ρ := P.rmax)
  rw [← h]
  rfl

/-- The dilated normal is nowhere zero, over `ℝ`. -/
theorem dcR_ne (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (fun i => (((dcn G P hn c marg j) i : ℚ) : ℝ)) ≠ 0 := by
  intro h
  have h' : dcn G P hn c marg j = 0 := QMCLeafB.EngineIterates.cast_fun_eq_zero h
  exact QMCLeafB.EndgameM2.gCn_ne G P hn c marg j h'

/-- **The log-concavity of the shape in the `A`-metric**: one step multiplies every quadratic form
by at most `α(1+β)`. -/
theorem form_step (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ)
    (v : Fin (G.n * G.n) → ℝ) :
    v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg (j + 1)) *ᵥ v)
      ≤ (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)))
        * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ v)) := by
  set A := QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) with hA
  set cR : Fin (G.n * G.n) → ℝ := QMCLeafB.EngineIterates.cutCR (dcd G P hn c marg) j with hcR
  set pR : Fin (G.n * G.n) → ℝ := QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j with hpR
  have hpos : A.PosDef := Sh_posDef G P hn c marg j
  have hwit : A *ᵥ pR = cR := Sh_witR G P hn c marg j
  have hcne : cR ≠ 0 := dcR_ne G P hn c marg j
  have hσ : 0 < QMCLeafB.EngineIterates.sigmaR cR pR :=
    QMCLeafB.EngineIterates.sigmaR_pos hpos hwit hcne
  have hβ : 0 ≤ QMCLeafB.EngineIterates.betaR (G.n * G.n) :=
    QMCLeafB.EngineIterates.betaR_nonneg (by
      have := Nat.mul_le_mul hn hn
      omega)
  have hα : 0 ≤ QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ) := by
    unfold QMCLeafB.EngineIterates.alphaR
    have h1 : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) ^ 2 - 1 := by
      have : (2 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by
        have hh := Nat.mul_le_mul hn hn
        exact_mod_cast (show 2 ≤ G.n * G.n by omega)
      nlinarith
    have h2 : (0 : ℝ) < (((G.n * G.n : ℕ) : ℝ) + ((P.rmax : ℚ) : ℝ)) ^ 2 := by
      have : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by positivity
      have := P.hrmax
      have h3 : (0 : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast this
      positivity
    exact div_nonneg h1 h2.le
  have hcs := QMCLeafB.EngineIterates.cauchy_sigmaR hpos hwit hcne v
  have hkey : v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg (j + 1)) *ᵥ v)
      = QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
        * (v ⬝ᵥ (A *ᵥ v)
          + (QMCLeafB.EngineIterates.betaR (G.n * G.n) / QMCLeafB.EngineIterates.sigmaR cR pR)
            * (cR ⬝ᵥ v) ^ 2) := by
    rw [Sh_step G P hn c marg j]
    rw [QMCLeafB.EngineIterates.stepShape]
    rw [QMCLeafB.CraterM2.qf_smul, QMCLeafB.CraterM2.qf_add, QMCLeafB.CraterM2.qf_smul,
      QMCLeafB.CraterM2.qf_vmv]
  rw [hkey]
  have h1 : (QMCLeafB.EngineIterates.betaR (G.n * G.n) / QMCLeafB.EngineIterates.sigmaR cR pR)
      * (cR ⬝ᵥ v) ^ 2 ≤ QMCLeafB.EngineIterates.betaR (G.n * G.n) * (v ⬝ᵥ (A *ᵥ v)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hσ]
    nlinarith [hcs, hβ]
  have h2 : v ⬝ᵥ (A *ᵥ v)
      + (QMCLeafB.EngineIterates.betaR (G.n * G.n) / QMCLeafB.EngineIterates.sigmaR cR pR)
        * (cR ⬝ᵥ v) ^ 2
      ≤ (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)) * (v ⬝ᵥ (A *ᵥ v)) := by
    nlinarith [h1]
  calc QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
        * (v ⬝ᵥ (A *ᵥ v)
          + (QMCLeafB.EngineIterates.betaR (G.n * G.n) / QMCLeafB.EngineIterates.sigmaR cR pR)
            * (cR ⬝ᵥ v) ^ 2)
      ≤ QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          * ((1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)) * (v ⬝ᵥ (A *ᵥ v))) := by
        exact mul_le_mul_of_nonneg_left h2 hα
    _ = (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)))
        * (v ⬝ᵥ (A *ᵥ v)) := by ring

/-- **The quadratic form at round `j` is at most `q^j` times the initial one.** -/
theorem form_bound (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ)
    (v : Fin (G.n * G.n) → ℝ) :
    v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ v)
      ≤ (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n))) ^ j
        * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0) *ᵥ v)) := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hq0 : (0 : ℝ) ≤ QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
          * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)) := by
        have hβ : 0 ≤ QMCLeafB.EngineIterates.betaR (G.n * G.n) :=
          QMCLeafB.EngineIterates.betaR_nonneg (by
            have := Nat.mul_le_mul hn hn
            omega)
        have hα : 0 ≤ QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ) := by
          unfold QMCLeafB.EngineIterates.alphaR
          have h1 : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) ^ 2 - 1 := by
            have h2 : (2 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by
              have hh := Nat.mul_le_mul hn hn
              exact_mod_cast (show 2 ≤ G.n * G.n by omega)
            nlinarith
          have h3 : (0 : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast P.hrmax
          have h4 : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by positivity
          exact div_nonneg h1 (by positivity)
        exact mul_nonneg hα (by linarith)
      calc v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg (j + 1)) *ᵥ v)
          ≤ (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
              * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)))
            * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ v)) :=
            form_step G P hn c marg j v
        _ ≤ (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
              * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n)))
            * ((QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
              * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n))) ^ j
              * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0) *ᵥ v))) :=
            mul_le_mul_of_nonneg_left ih hq0
        _ = (QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
              * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n))) ^ (j + 1)
            * (v ⬝ᵥ (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0) *ᵥ v)) := by
            rw [pow_succ']
            ring

end Engine

section Engine2

variable (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)

/-- `witRel` really is the witness. -/
theorem witRel_mulVec {M : ℕ} {S : Matrix (Fin M) (Fin M) ℚ}
    (h : QMCLeafB.EngineIterates.PosQ S) (v : Fin M → ℚ) :
    S *ᵥ QMCLeafB.RecordM2.witRel S v = v := by
  rw [QMCLeafB.RecordM2.witRel_of_posQ h]
  exact QMCLeafB.RunPartsShallow.witOf_spec h v

/-- The symmetric bilinear pairing `x ⪝ S⁻¹y` (over `ℚ`). -/
theorem witRel_symm {M : ℕ} {S : Matrix (Fin M) (Fin M) ℚ}
    (h : QMCLeafB.EngineIterates.PosQ S) (x y : Fin M → ℚ) :
    x ⬝ᵥ QMCLeafB.RecordM2.witRel S y = y ⬝ᵥ QMCLeafB.RecordM2.witRel S x := by
  have hsym : Sᵀ = S := h.1
  have hX : S *ᵥ QMCLeafB.RecordM2.witRel S x = x := witRel_mulVec h x
  have hY : S *ᵥ QMCLeafB.RecordM2.witRel S y = y := witRel_mulVec h y
  have hswap : ∀ a b : Fin M → ℚ, (S *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (S *ᵥ b) := by
    intro a b
    rw [dotProduct_comm (S *ᵥ a) b, dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym,
      dotProduct_comm]
  calc x ⬝ᵥ QMCLeafB.RecordM2.witRel S y
      = (S *ᵥ QMCLeafB.RecordM2.witRel S x) ⬝ᵥ QMCLeafB.RecordM2.witRel S y := by rw [hX]
    _ = QMCLeafB.RecordM2.witRel S x ⬝ᵥ (S *ᵥ QMCLeafB.RecordM2.witRel S y) :=
        hswap _ _
    _ = QMCLeafB.RecordM2.witRel S x ⬝ᵥ y := by rw [hY]
    _ = y ⬝ᵥ QMCLeafB.RecordM2.witRel S x := dotProduct_comm _ _

/-- The identity flat vector of the engine's space. -/
abbrev uQ : Fin (G.n * G.n) → ℚ := QMCLeafB.RecordM2.u0 G.n

/-- `κ_j`: the identity direction's `A_j`-pairing. -/
abbrev kapQ (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) : ℚ :=
  uQ G ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)

/-- The threshold `q = α(1+β)` of the shape recursion. -/
abbrev qab (_hn : 2 ≤ G.n) : ℝ :=
  QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ)
    * (1 + QMCLeafB.EngineIterates.betaR (G.n * G.n))

/-- `0 < q`. -/
theorem qab_pos : 0 < qab G P hn := by
  have hβ : 0 ≤ QMCLeafB.EngineIterates.betaR (G.n * G.n) :=
    QMCLeafB.EngineIterates.betaR_nonneg (n := G.n * G.n) (by
      have hh := Nat.mul_le_mul hn hn
      omega)
  have h1 : (0 : ℝ) < ((G.n * G.n : ℕ) : ℝ) ^ 2 - 1 := by
    have h2 : (4 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by
      have hh := Nat.mul_le_mul hn hn
      exact_mod_cast (show 4 ≤ G.n * G.n by omega)
    nlinarith
  have h2 : (0 : ℝ) < (((G.n * G.n : ℕ) : ℝ) + ((P.rmax : ℚ) : ℝ)) ^ 2 := by
    have h3 : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by positivity
    have h4 : (0 : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast P.hrmax
    positivity
  have hα : 0 < QMCLeafB.EngineIterates.alphaR (G.n * G.n) ((P.rmax : ℚ) : ℝ) := by
    unfold QMCLeafB.EngineIterates.alphaR
    exact div_pos h1 h2
  unfold qab
  exact mul_pos hα (by linarith)

/-- Casting commutes with the dot product (over `ℚ → ℝ`). -/
theorem cast_dot {M : ℕ} (x y : Fin M → ℚ) :
    (fun i => ((x i : ℚ) : ℝ)) ⬝ᵥ (fun i => ((y i : ℚ) : ℝ)) = ((x ⬝ᵥ y : ℚ) : ℝ) := by
  simp only [dotProduct, Rat.cast_sum, Rat.cast_mul]

/-- **`κ` cannot collapse faster than `q^{-j}`.** -/
theorem kappa_lb (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    ((kapQ G P hn c marg j : ℚ) : ℝ)
        * (qab G P hn ^ j
          * ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
              (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0)
                *ᵥ fun i => ((uQ G i : ℚ) : ℝ))))
      ≥ ((uQ G ⬝ᵥ uQ G : ℚ) : ℝ) ^ 2 := by
  have hpos : (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)).PosDef :=
    Sh_posDef G P hn c marg j
  have hwit : QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)
      *ᵥ (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) i : ℚ) : ℝ))
      = fun i => ((uQ G i : ℚ) : ℝ) := by
    have h := witRel_mulVec (QMCLeafB.RunPartsDilate.runShape_posQ G P hn (dcn G P hn c marg)
      (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j) (uQ G)
    rw [QMCLeafB.EngineIterates.cast_mulVec]
    exact congrArg (fun v : Fin (G.n * G.n) → ℚ => fun i => ((v i : ℚ) : ℝ)) h
  have hURne : (fun i => ((uQ G i : ℚ) : ℝ)) ≠ 0 := by
    intro hzero
    have h1 : uQ G = 0 := QMCLeafB.EngineIterates.cast_fun_eq_zero hzero
    have h2 : uQ G (QMCLeafB.RecordM2.d0idx G.n (by omega)) = 1 :=
      QMCLeafB.RecordM2.u0_d0idx G.n (by omega)
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have hcs := QMCLeafB.EngineIterates.cauchy_sigmaR hpos hwit hURne
    (fun i => ((uQ G i : ℚ) : ℝ))
  rw [cast_dot (uQ G) (uQ G)] at hcs
  simp only [QMCLeafB.EngineIterates.sigmaR] at hcs
  rw [cast_dot (uQ G) (QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G))] at hcs
  have hXpos : (0 : ℝ) < (fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
      (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ
        fun i => ((uQ G i : ℚ) : ℝ)) :=
    hpos.dotProduct_mulVec_pos hURne
  have hκpos : (0 : ℝ) < ((kapQ G P hn c marg j : ℚ) : ℝ) := by
    have h2 : (0 : ℝ) < QMCLeafB.EngineIterates.sigmaR (fun i => ((uQ G i : ℚ) : ℝ))
        (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) i : ℚ) : ℝ)) :=
      QMCLeafB.EngineIterates.sigmaR_pos hpos hwit hURne
    simp only [QMCLeafB.EngineIterates.sigmaR] at h2
    rwa [cast_dot] at h2
  have hform := form_bound G P hn c marg j (fun i => ((uQ G i : ℚ) : ℝ))
  have hXle : (fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
      (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ
        fun i => ((uQ G i : ℚ) : ℝ))
      ≤ qab G P hn ^ j * ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
        (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0) *ᵥ
          fun i => ((uQ G i : ℚ) : ℝ))) := hform
  calc ((uQ G ⬝ᵥ uQ G : ℚ) : ℝ) ^ 2
      ≤ ((kapQ G P hn c marg j : ℚ) : ℝ) * ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
          (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j) *ᵥ
            fun i => ((uQ G i : ℚ) : ℝ))) := hcs
    _ ≤ ((kapQ G P hn c marg j : ℚ) : ℝ) * (qab G P hn ^ j
          * ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
            (QMCLeafB.EngineIterates.castM (Sh G P hn c marg 0) *ᵥ
              fun i => ((uQ G i : ℚ) : ℝ)))) :=
        mul_le_mul_of_nonneg_left hXle hκpos.le

#print axioms QMCLeafB.CraterM2.cast_dot
#print axioms QMCLeafB.CraterM2.witRel_mulVec
#print axioms QMCLeafB.CraterM2.witRel_symm
#print axioms QMCLeafB.CraterM2.qab_pos
#print axioms QMCLeafB.CraterM2.kappa_lb

end Engine2



/-- **The sequential multiplier dominates its own depth threshold.**  This is the only content of
`lamInd` the trace budget needs. -/
theorem lamThr_le_ind {M : ℕ} (A0 : Matrix (Fin M) (Fin M) ℚ) (u : Fin M → ℚ) (d0 : Fin M)
    (c : ℕ → Fin M → ℚ) (marg : ℕ → ℚ) (rmax : ℚ) (k : ℕ)
    (hcoeff : 0 < QMCLeafB.RecordM2.lamCoeff A0 u d0 c marg rmax k
      (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)) :
    QMCLeafB.RecordM2.lamThr A0 u d0 c marg rmax k
        (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
      ≤ QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax k
        * QMCLeafB.RecordM2.lamCoeff A0 u d0 c marg rmax k
            (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m) := by
  have h1 : QMCLeafB.RecordM2.lamThr A0 u d0 c marg rmax k
        (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
        / QMCLeafB.RecordM2.lamCoeff A0 u d0 c marg rmax k
            (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
      ≤ QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax k := by
    rw [QMCLeafB.RecordM2.lamInd_eq]
    unfold QMCLeafB.RecordM2.lamStep
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have h2 : QMCLeafB.RecordM2.lamThr A0 u d0 c marg rmax k
        (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
      = QMCLeafB.RecordM2.lamThr A0 u d0 c marg rmax k
            (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
          / QMCLeafB.RecordM2.lamCoeff A0 u d0 c marg rmax k
              (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m)
          * QMCLeafB.RecordM2.lamCoeff A0 u d0 c marg rmax k
              (fun m _ => QMCLeafB.RecordM2.lamInd A0 u d0 c marg rmax m) := by
    field_simp
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 hcoeff.le

#print axioms QMCLeafB.CraterM2.lamThr_le_ind

section Engine3

variable (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)

/-- The identity flat vector, cast to `ℝ`, is `dOne`. -/
theorem uQ_cast_dot {M : ℕ} (p : Fin (M * M) → ℚ) :
    ((QMCLeafB.RecordM2.u0 M ⬝ᵥ p : ℚ) : ℝ)
      = QMCLeafB.RunPartsStream.dOne M ⬝ᵥ (fun i => ((p i : ℚ) : ℝ)) := by
  simp only [dotProduct, QMCLeafB.RunPartsStream.dOne, QMCLeafB.RecordM2.u0,
    Rat.cast_sum, Rat.cast_mul]

/-- **The threshold read-off at the run's own stream.**  `lamThr`'s three terms are exactly the
supplied normal's pairing `a`, the squared normal `T²` and the margin charge. -/
theorem shape_stream_eq (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.RecordM2.shapeVal (QMCLeafB.RunPartsDilate.A0P G P)
        (fun m => c m + (if h : m < j then QMCLeafB.EndgameM2.gLam G P hn c marg m
          else 1 - c m (QMCLeafB.RecordM2.d0idx G.n (by omega))) • uQ G)
        (fun _ => P.rmax) j
      = Sh G P hn c marg j := by
  rw [show Sh G P hn c marg j = QMCLeafB.RecordM2.shapeVal
      (QMCLeafB.RunPartsDilate.A0P G P) (dcn G P hn c marg) (fun _ => P.rmax) j from
    QMCLeafB.RecordM2.runShape_eq_shapeVal G P hn _ _ j]
  refine QMCLeafB.RecordM2.shapeVal_ext (QMCLeafB.RunPartsDilate.A0P G P)
    (fun _ => P.rmax) j (fun m hm => ?_)
  simp only [hm, dif_pos]
  rfl

/-- The threshold's value in the run's own terms. -/
theorem lamThr_ident (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.RecordM2.lamThr (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
        (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j
        (fun m _ => QMCLeafB.EndgameM2.gLam G P hn c marg m)
      = |c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)
          + uQ G ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j)|
        + |c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j)|
        + 9 * marg j ^ 2 / (4 * P.rmax ^ 2) + 1 := by
  simp only [QMCLeafB.RecordM2.lamThr]
  rw [shape_stream_eq G P hn c marg j]

/-- The coefficient's value in the run's own terms. -/
theorem lamCoeff_ident (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.RecordM2.lamCoeff (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
        (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j
        (fun m _ => QMCLeafB.EndgameM2.gLam G P hn c marg m)
      = kapQ G P hn c marg j := by
  simp only [QMCLeafB.RecordM2.lamCoeff, kapQ]
  rw [shape_stream_eq G P hn c marg j]

/-- `gLam` really is `lamInd`. -/
theorem gLam_eq (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    QMCLeafB.EndgameM2.gLam G P hn c marg j
      = QMCLeafB.RecordM2.lamInd (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
          (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j := rfl

/-- **`κ_j > 0`.** -/
theorem kappa_pos (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (0 : ℚ) < kapQ G P hn c marg j := by
  have hpos : (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)).PosDef :=
    Sh_posDef G P hn c marg j
  have hwit : QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)
      *ᵥ (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) i : ℚ) : ℝ))
      = fun i => ((uQ G i : ℚ) : ℝ) := by
    have h := witRel_mulVec (QMCLeafB.RunPartsDilate.runShape_posQ G P hn (dcn G P hn c marg)
      (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j) (uQ G)
    rw [QMCLeafB.EngineIterates.cast_mulVec]
    exact congrArg (fun v : Fin (G.n * G.n) → ℚ => fun i => ((v i : ℚ) : ℝ)) h
  have hURne : (fun i => ((uQ G i : ℚ) : ℝ)) ≠ 0 := by
    intro hzero
    have h1 : uQ G = 0 := QMCLeafB.EngineIterates.cast_fun_eq_zero hzero
    have h2 : uQ G (QMCLeafB.RecordM2.d0idx G.n (by omega)) = 1 :=
      QMCLeafB.RecordM2.u0_d0idx G.n (by omega)
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have h2 : (0 : ℝ) < QMCLeafB.EngineIterates.sigmaR (fun i => ((uQ G i : ℚ) : ℝ))
      (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) i : ℚ) : ℝ)) :=
    QMCLeafB.EngineIterates.sigmaR_pos hpos hwit hURne
  simp only [QMCLeafB.EngineIterates.sigmaR] at h2
  rw [cast_dot] at h2
  have h2' : (0 : ℝ) < ((kapQ G P hn c marg j : ℚ) : ℝ) := h2
  exact_mod_cast h2'

/-- **The threshold inequality at the run's stream.** -/
theorem threshQ (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    2 * |((c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) : ℚ) : ℝ)|
        + ((c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j) : ℚ) : ℝ) + 1
      ≤ ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ)
        * ((kapQ G P hn c marg j : ℚ) : ℝ) := by
  -- the rational threshold inequality
  have hcoeff : (0 : ℚ) < QMCLeafB.RecordM2.lamCoeff (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
      (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j
      (fun m _ => QMCLeafB.EndgameM2.gLam G P hn c marg m) := by
    rw [lamCoeff_ident]
    exact kappa_pos G P hn c marg j
  have hle := lamThr_le_ind (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
    (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j hcoeff
  rw [lamThr_ident G P hn c marg j, lamCoeff_ident G P hn c marg j] at hle
  have hsymm : uQ G ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j)
      = c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) :=
    witRel_symm (QMCLeafB.EngineIterates.posQ_of_cast (Sh_posDef G P hn c marg j)) (uQ G) (c j)
  rw [hsymm] at hle
  have h2a : |c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)
      + c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)|
      = 2 * |c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)| := by
    rw [← two_mul, abs_mul]
    norm_num
  rw [h2a] at hle
  have h9 : (0 : ℚ) ≤ 9 * marg j ^ 2 / (4 * P.rmax ^ 2) := by positivity
  have hmain : 2 * |c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)|
        + (c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j)) + 1
      ≤ QMCLeafB.EndgameM2.gLam G P hn c marg j * kapQ G P hn c marg j := by
    have h3 := le_abs_self (c j ⬝ᵥ QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j))
    linarith [hle, h3, h9]
  exact_mod_cast hmain

#print axioms QMCLeafB.CraterM2.uQ_cast_dot
#print axioms QMCLeafB.CraterM2.shape_stream_eq
#print axioms QMCLeafB.CraterM2.lamThr_ident
#print axioms QMCLeafB.CraterM2.lamCoeff_ident
#print axioms QMCLeafB.CraterM2.kappa_pos
#print axioms QMCLeafB.CraterM2.threshQ

end Engine3


section Engine4

variable (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)

/-- **The per-round trace increment is bounded below, at the run's own stream.** -/
theorem per_round (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ)
    (hrm1 : ((P.rmax : ℚ) : ℝ) ≤ 1) (j : ℕ) :
    ((1 - ((P.rmax : ℚ) : ℝ)) / (((G.n * G.n : ℕ) : ℝ) + 1))
        * Real.sqrt (4 * ((kapQ G P hn c marg j : ℚ) : ℝ)
            / (((kapQ G P hn c marg j : ℚ) : ℝ) + 4))
      ≤ QMCLeafB.DriftExact.engLam (G.n * G.n) (dcd G P hn c marg) j
        * QMCLeafB.DriftExact.diagSum (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j) := by
  have hA : (QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)).PosDef :=
    Sh_posDef G P hn c marg j
  have hwitR : ∀ v : Fin (G.n * G.n) → ℚ,
      QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)
        *ᵥ (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) v i : ℚ) : ℝ))
        = fun i => ((v i : ℚ) : ℝ) := by
    intro v
    have h := witRel_mulVec (QMCLeafB.RunPartsDilate.runShape_posQ G P hn (dcn G P hn c marg)
      (QMCLeafB.EndgameM2.gCn_ne G P hn c marg) j) v
    rw [QMCLeafB.EngineIterates.cast_mulVec]
    exact congrArg (fun w : Fin (G.n * G.n) → ℚ => fun i => ((w i : ℚ) : ℝ)) h
  have hURne : (fun i => ((uQ G i : ℚ) : ℝ)) ≠ 0 := by
    intro hzero
    have h1 : uQ G = 0 := QMCLeafB.EngineIterates.cast_fun_eq_zero hzero
    have h2 : uQ G (QMCLeafB.RecordM2.d0idx G.n (by omega)) = 1 :=
      QMCLeafB.RecordM2.u0_d0idx G.n (by omega)
    rw [h1] at h2
    exact absurd h2 (by norm_num)
  have hcn : (fun i => ((c j i : ℚ) : ℝ))
      + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) • (fun i => ((uQ G i : ℚ) : ℝ))
      ≠ 0 := by
    intro hzero
    have h1 : ((c j (QMCLeafB.RecordM2.d0idx G.n (by omega)) : ℚ) : ℝ)
        + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) = 0 := by
      have h2 := congrFun hzero (QMCLeafB.RecordM2.d0idx G.n (by omega))
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, QMCLeafB.RecordM2.u0_d0idx G.n (by omega)]
        using h2
    have h3 : (0 : ℚ) < c j (QMCLeafB.RecordM2.d0idx G.n (by omega))
        + QMCLeafB.EndgameM2.gLam G P hn c marg j := by
      have hg := QMCLeafB.RecordM2.lamInd_gt (QMCLeafB.RunPartsDilate.A0P G P) (uQ G)
        (QMCLeafB.RecordM2.d0idx G.n (by omega)) c marg P.rmax j
      linarith [hg]
    have h4 : ((0 : ℚ) : ℝ) < ((c j (QMCLeafB.RecordM2.d0idx G.n (by omega))
        + QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) := by exact_mod_cast h3
    push_cast at h4
    linarith
  -- the witness of the dilated normal
  have hP : QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)
      *ᵥ (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ))
      = (fun i => ((c j i : ℚ) : ℝ))
        + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) • (fun i => ((uQ G i : ℚ) : ℝ)) := by
    rw [Sh_witR G P hn c marg j]
    funext i
    simp [QMCLeafB.EndgameM2.gCn, QMCLeafB.RecordM2.cnInd, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  have hthrC := threshQ G P hn c marg j
  rw [← cast_dot (c j) (QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G)),
    ← cast_dot (c j) (QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (c j)),
    ← cast_dot (uQ G) (QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G))] at hthrC
  have hstep := step_abs (A := QMCLeafB.EngineIterates.castM (Sh G P hn c marg j)) hA
    (hwitR (uQ G)) (hwitR (c j)) hP hcn hURne hthrC
  -- rewrite `step_abs` into the engine's own vocabulary
  have hκeq : ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
        (fun i => ((QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G) i : ℚ) : ℝ)))
      = ((kapQ G P hn c marg j : ℚ) : ℝ) := cast_dot (uQ G)
        (QMCLeafB.RecordM2.witRel (Sh G P hn c marg j) (uQ G))
  have hUP : ((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
        (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ)))
      = ((uQ G ⬝ᵥ (dcd G P hn c marg j).p : ℚ) : ℝ) := cast_dot (uQ G) _
  have hcast : (fun i => ((c j i : ℚ) : ℝ))
        + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) • (fun i => ((uQ G i : ℚ) : ℝ))
      = fun i => (((dcn G P hn c marg j) i : ℚ) : ℝ) := by
    funext i
    simp [QMCLeafB.EndgameM2.gCn, QMCLeafB.RecordM2.cnInd, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
  have hσeq : QMCLeafB.EngineIterates.sigmaR (QMCLeafB.EngineIterates.cutCR (dcd G P hn c marg) j)
        (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j)
      = ((fun i => ((c j i : ℚ) : ℝ))
        + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) • (fun i => ((uQ G i : ℚ) : ℝ)))
        ⬝ᵥ (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ)) := by
    rw [QMCLeafB.EngineIterates.sigmaR, hcast,
      show QMCLeafB.EngineIterates.cutCR (dcd G P hn c marg) j
        = fun i => ((dcn G P hn c marg j i : ℚ) : ℝ) from rfl,
      show QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j
        = fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ) from rfl]
  have hdiag : QMCLeafB.DriftExact.diagSum
        (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j)
      = (fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
        (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ)) := by
    rw [← QMCLeafB.DriftExact.dOne_dot]
    rfl
  have hγpos : (0 : ℝ) ≤ (1 - ((P.rmax : ℚ) : ℝ)) / (((G.n * G.n : ℕ) : ℝ) + 1) := by
    have h1 : (0 : ℝ) ≤ ((P.rmax : ℚ) : ℝ) := by exact_mod_cast P.hrmax
    have h2 : (0 : ℝ) ≤ ((G.n * G.n : ℕ) : ℝ) := by positivity
    have h3 : (0 : ℝ) < ((G.n * G.n : ℕ) : ℝ) + 1 := by linarith
    exact div_nonneg (by linarith) h3.le
  have hstep2 : (1 - ((P.rmax : ℚ) : ℝ)) / (((G.n * G.n : ℕ) : ℝ) + 1)
        * Real.sqrt (4 * ((kapQ G P hn c marg j : ℚ) : ℝ)
            / (((kapQ G P hn c marg j : ℚ) : ℝ) + 4))
      ≤ (1 - ((P.rmax : ℚ) : ℝ)) / (((G.n * G.n : ℕ) : ℝ) + 1)
        * (((fun i => ((uQ G i : ℚ) : ℝ)) ⬝ᵥ
            (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ)))
          / Real.sqrt (((fun i => ((c j i : ℚ) : ℝ))
            + ((QMCLeafB.EndgameM2.gLam G P hn c marg j : ℚ) : ℝ) • (fun i => ((uQ G i : ℚ) : ℝ)))
            ⬝ᵥ (fun i => (((dcd G P hn c marg j).p i : ℚ) : ℝ)))) := by
    refine mul_le_mul_of_nonneg_left ?_ hγpos
    rw [← hκeq]
    exact hstep
  refine hstep2.trans (le_of_eq ?_)
  rw [hdiag]
  simp only [QMCLeafB.DriftExact.engLam, QMCLeafB.CentreTrack.lam,
    QMCLeafB.EngineIterates.sqrtSigmaR, QMCLeafB.EngineIterates.gammaR, hσeq,
    show (dcd G P hn c marg j).rho = P.rmax from rfl]
  ring_nf

#print axioms QMCLeafB.CraterM2.per_round

end Engine4


section Engine5

variable (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)

/-- `x ↦ 4x/(x+4)` is increasing on the positive axis. -/
theorem form_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    4 * x / (x + 4) ≤ 4 * y / (y + 4) := by
  have h1 : (0 : ℝ) < x + 4 := by linarith
  have h2 : (0 : ℝ) < y + 4 := by linarith
  have e : 4 * y / (y + 4) - 4 * x / (x + 4)
      = 16 * (y - x) / ((x + 4) * (y + 4)) := by
    field_simp
    ring
  rw [← sub_nonneg, e]
  positivity

/-- **The increment dominates `√(4κ/(κ+4))` at any positive lower bound of `κ`.** -/
theorem sqrt_sq_le {κ cst k0 : ℝ} (hc0 : 0 ≤ cst) (hk0 : 0 < k0) (hk : k0 ≤ κ)
    (hsq : cst ^ 2 ≤ 4 * k0 / (k0 + 4)) : cst ≤ Real.sqrt (4 * κ / (κ + 4)) := by
  have h1 : 4 * k0 / (k0 + 4) ≤ 4 * κ / (κ + 4) := form_mono hk0 hk
  exact Real.le_sqrt_of_sq_le (le_trans hsq h1)

/-- **The cumulative trace budget fails at the run's own stream, for every normal/margin stream.**
At `n² = 4`, `rmax = 1/16` and the campaign decay `q = 256/169`, the first `20` rounds already
carry more than `2.3` of trace, while the pinched ceiling is `n(1 − dq/4) < 2`. -/
theorem sum_lb (c : ℕ → Fin (G.n * G.n) → ℚ) (marg : ℕ → ℚ)
    (hrm1 : ((P.rmax : ℚ) : ℝ) ≤ 1)
    (h4 : ((G.n * G.n : ℕ) : ℝ) = 4)
    (hrm : ((P.rmax : ℚ) : ℝ) = 1 / 16)
    (hκ : ∀ j, (16 : ℝ) * (169 / 256) ^ j ≤ ((kapQ G P hn c marg j : ℚ) : ℝ)) :
    (2.3 : ℝ) ≤ ∑ j ∈ Finset.range 20,
      QMCLeafB.DriftExact.engLam (G.n * G.n) (dcd G P hn c marg) j
        * QMCLeafB.DriftExact.diagSum
            (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j) := by
  set inc : ℕ → ℝ := fun j =>
    QMCLeafB.DriftExact.engLam (G.n * G.n) (dcd G P hn c marg) j
      * QMCLeafB.DriftExact.diagSum
          (QMCLeafB.EngineIterates.cutPR (dcd G P hn c marg) j) with hinc
  have hpr : ∀ j, ((3 : ℝ) / 16) * Real.sqrt (4 * ((kapQ G P hn c marg j : ℚ) : ℝ)
      / (((kapQ G P hn c marg j : ℚ) : ℝ) + 4)) ≤ inc j := by
    intro j
    have h := per_round G P hn c marg hrm1 j
    rw [h4, hrm] at h
    have hfac : (1 - (1 : ℝ) / 16) / (4 + 1) = 3 / 16 := by norm_num
    rw [hfac] at h
    exact h
  have hb1 : ∀ j, j < 4 → ((3 : ℝ) / 16) * (29 / 20) ≤ inc j := by
    intro j hj
    have hk : (16 : ℝ) * (169 / 256) ^ 3 ≤ ((kapQ G P hn c marg j : ℚ) : ℝ) := by
      have h := hκ j
      have hmono : (169 / 256 : ℝ) ^ 3 ≤ (169 / 256) ^ j := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      nlinarith
    have hsq : ((29 : ℝ) / 20) ^ 2 ≤ 4 * ((16 : ℝ) * (169 / 256) ^ 3)
        / ((16 : ℝ) * (169 / 256) ^ 3 + 4) := by norm_num
    have hroot := sqrt_sq_le (κ := ((kapQ G P hn c marg j : ℚ) : ℝ))
      (by norm_num : (0:ℝ) ≤ 29 / 20) (by norm_num) hk hsq
    have h3 : (0 : ℝ) ≤ 3 / 16 := by norm_num
    calc ((3 : ℝ) / 16) * (29 / 20) = (3 / 16) * (29 / 20) := rfl
      _ ≤ (3 / 16) * Real.sqrt (4 * ((kapQ G P hn c marg j : ℚ) : ℝ)
            / (((kapQ G P hn c marg j : ℚ) : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left hroot h3
      _ ≤ inc j := hpr j
  have hb2 : ∀ j, 4 ≤ j → ((3 : ℝ) / 16) * (3 * (13 / 16 : ℝ) ^ j) ≤ inc j := by
    intro j hj
    have hk : (16 : ℝ) * (169 / 256) ^ j ≤ ((kapQ G P hn c marg j : ℚ) : ℝ) := hκ j
    have hσ4 : (169 / 256 : ℝ) ^ j ≤ (169 / 256) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    have hpow : ((13 / 16 : ℝ) ^ j) ^ 2 = (169 / 256) ^ j := by
      rw [pow_two, ← pow_add, show j + j = 2 * j by ring, pow_mul]
      norm_num
    have hsq : (3 * (13 / 16 : ℝ) ^ j) ^ 2
        ≤ 4 * ((16 : ℝ) * (169 / 256) ^ j) / ((16 : ℝ) * (169 / 256) ^ j + 4) := by
      have h16 : (0 : ℝ) < (16 : ℝ) * (169 / 256) ^ j := by
        have : (0 : ℝ) < (169 / 256 : ℝ) ^ j := by positivity
        linarith
      have hq1 : (169 / 256 : ℝ) ^ j ≤ 7 / 36 := le_trans hσ4 (by norm_num)
      have hstep : 9 * (169 / 256 : ℝ) ^ j
          ≤ 4 * ((16 : ℝ) * (169 / 256) ^ j) / ((16 : ℝ) * (169 / 256) ^ j + 4) := by
        have hb : (0 : ℝ) < (16 : ℝ) * (169 / 256) ^ j + 4 := by linarith
        rw [le_div_iff₀ hb]
        have hσ : (0 : ℝ) < (169 / 256 : ℝ) ^ j := by positivity
        nlinarith [hq1, hσ, mul_pos hσ hσ]
      have hsq' : (3 * (13 / 16 : ℝ) ^ j) ^ 2 = 9 * ((169 / 256 : ℝ) ^ j) := by
        rw [mul_pow, hpow]
        norm_num
      linarith [hstep, hsq']
    have hroot := sqrt_sq_le (κ := ((kapQ G P hn c marg j : ℚ) : ℝ))
      (by positivity) (by positivity) hk hsq
    have h3 : (0 : ℝ) ≤ 3 / 16 := by norm_num
    calc ((3 : ℝ) / 16) * (3 * (13 / 16 : ℝ) ^ j)
        ≤ (3 / 16) * Real.sqrt (4 * ((kapQ G P hn c marg j : ℚ) : ℝ)
            / (((kapQ G P hn c marg j : ℚ) : ℝ) + 4)) :=
          mul_le_mul_of_nonneg_left hroot h3
      _ ≤ inc j := hpr j
  have hs1 : ((87 : ℝ) / 80) ≤ ∑ j ∈ Finset.range 4, inc j := by
    have h1 : ∑ j ∈ Finset.range 4, ((3 : ℝ) / 16 * (29 / 20)) ≤ ∑ j ∈ Finset.range 4, inc j :=
      Finset.sum_le_sum (fun j hj => hb1 j (Finset.mem_range.1 hj))
    have h2 : (∑ j ∈ Finset.range 4, ((3 : ℝ) / 16 * (29 / 20))) = 87 / 80 := by
      norm_num [Finset.sum_range_succ]
    linarith
  have hs2 : ((63 : ℝ) / 50) ≤ ∑ j ∈ Finset.range 16, inc (j + 4) := by
    have h1 : ∑ j ∈ Finset.range 16, ((3 : ℝ) / 16 * (3 * (13 / 16 : ℝ) ^ (j + 4)))
        ≤ ∑ j ∈ Finset.range 16, inc (j + 4) :=
      Finset.sum_le_sum (fun j _ => hb2 (j + 4) (by omega))
    have h2 : (63 : ℝ) / 50
        ≤ ∑ j ∈ Finset.range 16, ((3 : ℝ) / 16 * (3 * (13 / 16 : ℝ) ^ (j + 4))) := by
      norm_num [Finset.sum_range_succ]
    linarith
  have hsplit : (∑ j ∈ Finset.range 20, inc j)
      = (∑ j ∈ Finset.range 4, inc j) + (∑ j ∈ Finset.range 16, inc (j + 4)) := by
    rw [show (20 : ℕ) = 4 + 16 from rfl, Finset.sum_range_add]
    simp [Nat.add_comm]
  rw [hsplit]
  linarith

#print axioms QMCLeafB.CraterM2.form_mono
#print axioms QMCLeafB.CraterM2.sqrt_sq_le
#print axioms QMCLeafB.CraterM2.sum_lb

end Engine5

/-! ## 6.  The campaign constants at the refuting input `G₀`, and the refutation of the residual -/

section Crash

/-- The refuting input (two vertices, one edge of weight `1/2`). -/
abbrev G₀ : QuantumMaxCutEnergy.Input := QMCLeafB.ResidRefute.G₀

/-- The campaign's parameter family at `G₀`. -/
abbrev P₀ : QMCLeafB.FinalStroke.RunParams G₀ := QMCLeafB.UnionShallow.paramsKbc2 G₀

/-- The refuted interior threshold. -/
abbrev t₀ : ℚ := -(99999 / 100000)

theorem hn₀ : 2 ≤ G₀.n := QMCLeafB.ResidKill.hnG₀

theorem n₀ : G₀.n = 2 := rfl

theorem hn4₀ : ((G₀.n * G₀.n : ℕ) : ℝ) = 4 := by
  rw [n₀]
  norm_num

theorem rmax₀ : (P₀.rmax : ℚ) = 1 / 16 := by
  show QMCLeafB.RundataHalving.rmaxOf (G₀.n * G₀.n) = 1 / 16
  unfold QMCLeafB.RundataHalving.rmaxOf
  rw [n₀]
  norm_num

theorem hrm1₀ : ((P₀.rmax : ℚ) : ℝ) ≤ 1 := by
  rw [rmax₀]
  norm_num

theorem hrmR₀ : ((P₀.rmax : ℚ) : ℝ) = 1 / 16 := by
  rw [rmax₀]
  norm_num

theorem qab₀ : qab G₀ P₀ hn₀ = 256 / 169 := by
  unfold qab
  rw [hrmR₀, n₀]
  unfold QMCLeafB.EngineIterates.alphaR QMCLeafB.EngineIterates.betaR
  norm_num

theorem UU₀ : ((uQ G₀ ⬝ᵥ uQ G₀ : ℚ) : ℝ) = 2 := by
  have h : (uQ G₀ ⬝ᵥ uQ G₀ : ℚ) = 2 := by
    have h1 := uQ_cast_dot (M := G₀.n) (uQ G₀)
    have h2 : QMCLeafB.RunPartsStream.dOne G₀.n ⬝ᵥ
        (fun i => ((uQ G₀ i : ℚ) : ℝ)) = QMCLeafB.RunPartsStream.dOne G₀.n ⬝ᵥ
        QMCLeafB.RunPartsStream.dOne G₀.n := rfl
    have h3 : QMCLeafB.RunPartsStream.dOne G₀.n ⬝ᵥ QMCLeafB.RunPartsStream.dOne G₀.n
        = QMCLeafB.DriftExact.diagSum (QMCLeafB.RunPartsStream.dOne G₀.n) :=
      QMCLeafB.DriftExact.dOne_dot _
    have h4 : QMCLeafB.DriftExact.diagSum (QMCLeafB.RunPartsStream.dOne G₀.n) = 2 := by
      rw [QMCLeafB.DriftExact.diagSum, n₀, Fin.sum_univ_two]
      rw [QMCLeafB.DriftExact.dOne_apply, QMCLeafB.DriftExact.dOne_apply]
      norm_num
    have h5 : ((uQ G₀ ⬝ᵥ uQ G₀ : ℚ) : ℝ) = 2 := by
      rw [h1, h2, h3, h4]
    exact_mod_cast h5
  rw [h]
  norm_num

theorem cap₀ : (8 : ℝ) ≤ ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ) := by
  unfold QMCLeafB.RundataArith.capOf
  rw [n₀]
  push_cast
  nlinarith [sq_nonneg ((P₀.dq : ℚ) : ℝ)]

/-- The engine's initial shape is `M⁻¹ • 1`, so the identity direction's form is at most `1/4`. -/
theorem UAU₀ (c : ℕ → Fin (G₀.n * G₀.n) → ℚ) (marg : ℕ → ℚ) :
    ((fun i => ((uQ G₀ i : ℚ) : ℝ)) ⬝ᵥ
      (QMCLeafB.EngineIterates.castM (Sh G₀ P₀ hn₀ c marg 0)
        *ᵥ fun i => ((uQ G₀ i : ℚ) : ℝ))) ≤ 1 / 4 := by
  have hA0 : QMCLeafB.EngineIterates.castM (Sh G₀ P₀ hn₀ c marg 0)
      = ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ)⁻¹ •
        (1 : Matrix (Fin (G₀.n * G₀.n)) (Fin (G₀.n * G₀.n)) ℝ) := by
    show QMCLeafB.EngineIterates.castM (QMCLeafB.RunPartsDilate.A0P G₀ P₀) = _
    rw [QMCLeafB.RunPartsDilate.A0P]
    exact QMCLeafB.Boundary.castM_initShapeOf (G₀.n * G₀.n) (QMCLeafB.RundataArith.capOf G₀ P₀.dq)
  rw [hA0, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hUU2 : ((fun i => ((uQ G₀ i : ℚ) : ℝ)) ⬝ᵥ (fun i => ((uQ G₀ i : ℚ) : ℝ))) = 2 := by
    rw [cast_dot]
    exact UU₀
  rw [hUU2]
  have hcap := cap₀
  have hpos : (0 : ℝ) < ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ) := by linarith
  have hcinv : ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ)⁻¹ ≤ 1 / 8 := by
    have h1 : ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ)⁻¹
        * ((QMCLeafB.RundataArith.capOf G₀ P₀.dq : ℚ) : ℝ) = 1 :=
      inv_mul_cancel₀ (ne_of_gt hpos)
    nlinarith [hcap, hpos, h1]
  nlinarith

/-- **The κ decay at the campaign constants.** -/
theorem kappa₀ (c : ℕ → Fin (G₀.n * G₀.n) → ℚ) (marg : ℕ → ℚ) (j : ℕ) :
    (16 : ℝ) * (169 / 256) ^ j ≤ ((kapQ G₀ P₀ hn₀ c marg j : ℚ) : ℝ) := by
  have h := kappa_lb G₀ P₀ hn₀ c marg j
  have hq : qab G₀ P₀ hn₀ = 256 / 169 := qab₀
  have hqq : (0 : ℝ) < (qab G₀ P₀ hn₀) ^ j := pow_pos (by rw [hq]; norm_num) j
  have hUU : ((uQ G₀ ⬝ᵥ uQ G₀ : ℚ) : ℝ) = 2 := UU₀
  rw [hUU] at h
  have hUAU := UAU₀ c marg
  have hκpos : (0 : ℝ) < ((kapQ G₀ P₀ hn₀ c marg j : ℚ) : ℝ) := by
    have := kappa_pos G₀ P₀ hn₀ c marg j
    exact_mod_cast this
  have hnn : (0 : ℝ) ≤ ((kapQ G₀ P₀ hn₀ c marg j : ℚ) : ℝ) * (qab G₀ P₀ hn₀) ^ j :=
    mul_nonneg hκpos.le hqq.le
  have h1 : (16 : ℝ) ≤ ((kapQ G₀ P₀ hn₀ c marg j : ℚ) : ℝ) * (qab G₀ P₀ hn₀) ^ j := by
    nlinarith [h, hUAU, hκpos, hqq, hnn]
  have h2 : ((kapQ G₀ P₀ hn₀ c marg j : ℚ) : ℝ) * (qab G₀ P₀ hn₀) ^ j * (169 / 256) ^ j
      ≥ 16 * (169 / 256) ^ j := by
    have h3 : (0 : ℝ) ≤ (169 / 256 : ℝ) ^ j := by positivity
    nlinarith [h1, h3]
  rw [hq, mul_assoc] at h2
  have hinv : (256 / 169 : ℝ) ^ j * (169 / 256) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hinv, mul_one] at h2
  linarith

/-- **The trace budget fails at `G₀`, at every normal and margin stream.** -/
theorem budget_false (c : ℕ → Fin (G₀.n * G₀.n) → ℚ) (marg : ℕ → ℚ) :
    ((1 - P₀.dq / 4 : ℚ) : ℝ) * (G₀.n : ℝ)
      < ∑ j ∈ Finset.range 20,
          QMCLeafB.DriftExact.engLam (G₀.n * G₀.n) (dcd G₀ P₀ hn₀ c marg) j
            * QMCLeafB.DriftExact.diagSum
                (QMCLeafB.EngineIterates.cutPR (dcd G₀ P₀ hn₀ c marg) j) := by
  have hsum := sum_lb G₀ P₀ hn₀ c marg hrm1₀ hn4₀ hrmR₀ (kappa₀ c marg)
  have hceil : ((1 - P₀.dq / 4 : ℚ) : ℝ) * (G₀.n : ℝ) ≤ 2 := by
    have hq := QMCLeafB.RundataParams.dqShallow_pos G₀
    have hnn : (0 : ℝ) ≤ ((P₀.dq : ℚ) : ℝ) := by exact_mod_cast hq.le
    rw [n₀]
    push_cast
    nlinarith
  linarith

end Crash

/-- **The horizon at `G₀` is far beyond the twenty rounds the trace needs.** -/
theorem Km₀ : 20 < P₀.K * P₀.m := by
  rw [QMCLeafB.UnionShallow.paramsKbc2_K_mul_m]
  unfold QMCLeafB.UnionShallow.Kbc2
  have hm := QMCLeafB.HalvePerG.one_le_mHalve (G₀.n * G₀.n)
  have hbc : 0 ≤ QMCLeafB.Hspec.bitCost (QMCLeafB.EngineRuntime.Rq G₀) := Nat.zero_le _
  have hn2 : G₀.n = 2 := n₀
  rw [hn2] at hm ⊢
  nlinarith [hm, hbc, Nat.mul_le_mul hm hm]

/-- **The relaxed body at `(G₀, t₀)` is empty.** -/
theorem hempty₀ :
    ∀ X : Matrix (Fin G₀.n) (Fin G₀.n) ℚ,
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) X
        (t₀ - QMCLeafB.RundataCert.eps G₀) P₀.dq :=
  QMCLeafB.EmptyBodyM5.not_relaxMem_G₀

/-- **THE CRATER IS UNSATISFIABLE.**  At the refuting input `G₀` and the refuted threshold `t₀`,
`CoreDataG` — the supplier-friendly horizon-bounded residual — is uninhabited, for **every** verdict
bit.  At an empty body every round below the horizon is a cut round, so the trace budget is read at
round 20, where `budget_false` says the cumulative trace already exceeds the pinched ceiling. -/
theorem not_coreDataG (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    ¬ Nonempty (QMCLeafB.EndgameM2.CoreDataG o G₀ t₀ P₀ hn₀) := by
  rintro ⟨D⟩
  have hok : ∀ k, k < P₀.K * P₀.m → D.ok k = false := by
    intro k hk
    by_contra hne
    have htrue : D.ok k = true := by
      cases h : D.ok k <;> simp_all
    exact hempty₀ _ (D.hmem k hk htrue)
  have hdr := D.hdriftd 20 (hok 20 Km₀)
  rw [show QMCLeafB.RecordsM2.cXst G₀.n D.X P₀.dq 20
      = QMCLeafB.CentreAdm.diagPinch (QMCLeafB.StateDiag.stMat G₀.n (D.X 20)) P₀.dq from rfl]
    at hdr
  have hbudget := (QMCLeafB.RecordsM2.hdriftd_diagPinch_iff
    (cd := dcd G₀ P₀ hn₀ D.c D.marg)
    (Q := QMCLeafB.StateDiag.stMat G₀.n (D.X 20)) (k := 20)).1 hdr
  have hgt := budget_false D.c D.marg
  linarith

/-- **The supplier-friendly residual `ResidG` is false at the campaign family.** -/
theorem not_residG (o : QuantumMaxCutEnergy.Input → ℚ → Bool) :
    QMCLeafB.EndgameM2.ResidG o QMCLeafB.UnionShallow.paramsKbc2 → False := by
  intro H
  exact not_coreDataG o ⟨H G₀ t₀ hn₀
    (by rw [QMCLeafB.ResidRefute.Rq_G₀]; unfold t₀; norm_num)
    (by rw [QMCLeafB.ResidRefute.Rq_G₀]; unfold t₀; norm_num)⟩

#print axioms QMCLeafB.CraterM2.n₀
#print axioms QMCLeafB.CraterM2.hn4₀
#print axioms QMCLeafB.CraterM2.rmax₀
#print axioms QMCLeafB.CraterM2.hrm1₀
#print axioms QMCLeafB.CraterM2.hrmR₀
#print axioms QMCLeafB.CraterM2.qab₀
#print axioms QMCLeafB.CraterM2.UU₀
#print axioms QMCLeafB.CraterM2.cap₀
#print axioms QMCLeafB.CraterM2.UAU₀
#print axioms QMCLeafB.CraterM2.kappa₀
#print axioms QMCLeafB.CraterM2.budget_false
#print axioms QMCLeafB.CraterM2.Km₀
#print axioms QMCLeafB.CraterM2.hempty₀
#print axioms QMCLeafB.CraterM2.not_coreDataG
#print axioms QMCLeafB.CraterM2.not_residG

end QMCLeafB.CraterM2



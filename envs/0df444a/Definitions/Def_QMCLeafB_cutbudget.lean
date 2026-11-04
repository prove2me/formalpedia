-- Prove2me | Definitions.Def_QMCLeafB_cutbudget
-- name    : QMCLeafB_cutbudget
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T05:31:11.671672+00:00
-- url     : https://prove2.me/theorems/bc83ef44-8d38-4b03-b4d8-c1745b5f993f
-- title:
--   QMCLeafB cutbudget
-- statement:
--   # leaf B phase 21 — brick `cut-budget-scalar` (swarm `smw1m5nkm`, member m8, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_records_m2
/-
# leaf B phase 21 — brick `cut-budget-scalar` (swarm `smw1m5nkm`, member m8, direction d3)

The phase-20 residual `RecordsM2.CoreDataScalar` asks for **one scalar** at the run's own
constructed stream:

    ∑_{j<k} engLam (n·n) cd j · diagSum (cutPR cd j) ≤ (1 − dq/4)·n      (∀ k at cut rounds)

(`hbud`), plus the cut normal's per-round budget (`hnorm`).  This brick attacks the scalar
*falsification-first*: it machine-checks what the scalar can and cannot be derived from, and it
machine-checks the phase-18 trivial-cut overflow that `smw1i2drp/m3`'s `RESULTS.md` §3b left as
"derived in exact rationals, not machine-checked".

**What is proved here (the receipt).**  Take the *pure dilation* normal stream — the cut normal is
the trace direction `f = flatQ 1` at every round, the witness is the engine's own `A_k⁻¹ f`, and the
depth is the campaign ceiling `rmax = rmaxOf (n·n) = 1/16` at shape dimension `N = n·n = 4`
(`n = 2`).  Along the engine's own recursion the shape stays in the two-dimensional algebra
`A_k = a_k•1 + b_k•f fᵀ`, and *everything closes exactly*:

* §2 `Aat_eq_Aex` — the induction `Aat 4 A₀ cd k = a_k•1 + b_k•f fᵀ` along `rStep`, with
  `A₀ = initShapeOf 4 M`, `M = 2n² + 2dq² = capOf` at `n = 2`, `a_k = M⁻¹·α^k`,
  `t_k = a_k + 2b_k = M⁻¹·(256/169)^k`;
* `Aex_wit` / `Aex_posQ` — the stream is *legitimate*: the witness is the exact one
  (`A_k *ᵥ p_k = f`), every shape is `PosQ`, the depth is in `[0,1]`, the normals are nonzero;
* §3 `drift_overflow` — the scalar **fails at round 4** for every `dq > 0`:
  `diagSum (Cat 4 0 cd 4) > 2·(1 − dq/4)` (the exact limit is `√(nM) = √(8+2dq²) > n`);
* `drift_overflow_ge` — it fails at **every** `k ≥ 4` (the drift is monotone), so
  *horizon-bounding alone does not repair the scalar*: below any horizon `≥ 5` it is still false;
* §4 `hdriftd_false_pinch` — at the record's own pinched centre `diagPinch Q dq`
  (`RecordsM2.hdriftd_diagPinch_iff`), the `hdriftd` slot of `CoreData`/`StreamCore` is **false**
  at round 4, for *every* base `Q`;
* `nonempty_relaxCut_of_emptyBody` — at a point whose relaxed body is empty, a cut record exists at
  **every** normal and every positive margin (the `separates` field is vacuous).  So nothing at a
  refuted point forbids the trace-direction stream above;
* §6 `drift_overflow_scaled` (and `_ge`) — **`λ` cancels**: any *positive* dilation multiplier
  stream `λ_k • f` (with its exact witness `λ_k • (t_k⁻¹ f)`) has exactly the same per-round
  increments (`incr_smul`), so it overflows the budget at round 4 and at every `k ≥ 4` too.  No
  choice of the multiplier that `hlam2` forces can repair the budget.

**What this means for the leaf.**  The scalar is not a consequence of the engine's structural
invariants (exact witness + `PosQ` shape chain + `0 ≤ ρ ≤ 1`); it is genuine analytic content about
the *directions* the oracle returns.  At a **refuted** point nothing prevents the dilation stream, so
the ∀k (and any horizon `≥ 5`) flag-conditioned budget shape
(`FlagsM5.StreamCore`/`RecordsM2.CoreData.hdriftd`) is uninhabitable there by this route as well,
independently of the phase-21 `hcutfin` argument (direction d1).  The positive route must therefore
index the budget to the *oracle's* directions with strict negative trace (never the dilation-only
stream) **and** state it with a constant that grows with the horizon, not `(1 − dq/4)·n`.

No `sorry`, no `admit`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
`#print axioms` audit at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.CutBudgetM8

open QMCLeafB.EngineIterates
open QMCLeafB.DriftExact

/-! ## 1.  The iso algebra of a two-term shape `a•1 + b•f fᵀ`

A shape built from the identity and one rank-one term `f fᵀ` stays inside that two-dimensional
algebra under `rStep`, because the trace direction `f` is an eigenvector of it.  These lemmas are the
entire algebraic content of the induction. -/

/-- The rank-one term acts by the scalar `f ⬝ᵥ v` on `f`. -/
theorem vecMulVec_mulVec' {N : ℕ} (u v w : Fin N → ℚ) :
    Matrix.vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]

/-- The two-term shape acts on any vector. -/
theorem iso_mulVec {N : ℕ} (f v : Fin N → ℚ) (a b : ℚ) :
    (a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f) *ᵥ v
      = a • v + (b * (f ⬝ᵥ v)) • f := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    vecMulVec_mulVec', smul_smul]

/-- A multiple of `f` is an eigenvector of the two-term shape: `A *ᵥ (x•f) = (x·t)•f` with
`t = a + b·(f ⪝ f)`. -/
theorem iso_mulVec_smul {N : ℕ} (f : Fin N → ℚ) (a b x : ℚ) (t : ℚ)
    (ht : t = a + b * (f ⬝ᵥ f)) :
    (a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f) *ᵥ (x • f)
      = (x * t) • f := by
  rw [iso_mulVec, dotProduct_smul, smul_eq_mul]
  have h : a • (x • f) + (b * (x * (f ⬝ᵥ f))) • f = (a * x) • f + (b * (x * (f ⬝ᵥ f))) • f := by
    rw [smul_smul]
  rw [h, ← add_smul, ht]
  congr 1
  ring

/-- The two-term shape is symmetric. -/
theorem iso_transpose {N : ℕ} (f : Fin N → ℚ) (a b : ℚ) :
    (a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f)ᵀ
      = a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f := by
  rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one,
    Matrix.transpose_vecMulVec]

/-- The quadratic form of the two-term shape: `x ⪝ A x = a·(x ⪝ x) + b·(f ⪝ x)²`. -/
theorem iso_qf {N : ℕ} (f x : Fin N → ℚ) (a b : ℚ) :
    x ⬝ᵥ ((a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f) *ᵥ x)
      = a * (x ⬝ᵥ x) + b * (f ⬝ᵥ x) ^ 2 := by
  rw [iso_mulVec, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_comm x f,
    smul_eq_mul, smul_eq_mul]
  ring

/-- **The two-term shape is `PosQ`** as soon as `a > 0` and `b ≥ 0`. -/
theorem iso_posQ {N : ℕ} (f : Fin N → ℚ) {a b : ℚ} (ha : 0 < a) (hb : 0 ≤ b) :
    PosQ (a • (1 : Matrix (Fin N) (Fin N) ℚ) + b • Matrix.vecMulVec f f) := by
  refine ⟨iso_transpose f a b, ?_⟩
  intro x hx
  rw [qf, iso_qf]
  have hxx : 0 < x ⬝ᵥ x := by
    rw [dotProduct]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    refine Finset.sum_pos' (fun j _ => mul_self_nonneg (x j)) ⟨i, Finset.mem_univ i, ?_⟩
    exact mul_self_pos.mpr hi
  have hsq : 0 ≤ (f ⬝ᵥ x) ^ 2 := sq_nonneg _
  nlinarith [mul_pos ha hxx, mul_nonneg hb hsq]

/-! ## 2.  The pure-dilation stream at `n = 2`

`f = flatQ 1` is the flattened identity — the *trace direction* the dilation brick
(`RecordM2.cnInd`) adds to every oracle normal, and the only direction a zero-normal (trivial) cut
carries.  Everything below is at shape dimension `N = n·n = 4`. -/

/-- The trace direction: the flattened identity at `n = 2`. -/
def fr : Fin (2 * 2) → ℚ := QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin 2) (Fin 2) ℚ)

theorem fr_apply (i j : Fin 2) : fr (finProdFinEquiv (i, j)) = if i = j then (1 : ℚ) else 0 := by
  have hs : finProdFinEquiv.symm (finProdFinEquiv (i, j)) = (i, j) :=
    Equiv.symm_apply_apply _ _
  show (1 : Matrix (Fin 2) (Fin 2) ℚ) (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = (if i = j then (1 : ℚ) else 0)
  rw [hs, Matrix.one_apply]

/-- `f ⪝ f = n = 2`. -/
theorem fr_dot : fr ⬝ᵥ fr = 2 := by
  rw [dotProduct, ← Equiv.sum_comp finProdFinEquiv (fun k => fr k * fr k), Fintype.sum_prod_type]
  have hinner : ∀ i : Fin 2,
      (∑ j : Fin 2, fr (finProdFinEquiv (i, j)) * fr (finProdFinEquiv (i, j))) = 1 := by
    intro i
    simp only [fr_apply]
    rw [Fin.sum_univ_two]
    fin_cases i <;> norm_num
  simp [hinner]

theorem fr_ne_zero : fr ≠ 0 := by
  intro h
  have h2 := fr_dot
  rw [h] at h2
  simp at h2

/-! ### 2.1  The campaign's scalars at `N = 4`

`ρ` is the campaign ceiling `rmaxOf (n·n) = 1/(4·4) = 1/16`; `M` is `capOf` at `n = 2`,
`2·n² + 2·dq² = 8 + 2·dq²`.  The shape recursion's constants at `N = 4, ρ = 1/16` are then
`α = 768/845`, `β = 2/3`, `γ = 3/16`, and the shape's own "trace scale" grows by
`q = (N+ρ)/(N+1)` per round, which is `(1 + β)·α = (5/3)·α = 256/169`. -/

/-- `capOf` at `n = 2`: `2·n² + 2·dq²`. -/
def Mpar (dq : ℚ) : ℚ := 8 + 2 * dq ^ 2

/-- The campaign ceiling `rmaxOf 4 = 1/16`. -/
def rhoQ : ℚ := 1 / 16

/-- `alphaQ 4 rhoQ`. -/
def alpQ : ℚ := 768 / 845

/-- `betaQ 4`. -/
def betQ : ℚ := 2 / 3

/-- `gammaR 4 rhoQ`. -/
def gamQ : ℚ := 3 / 16

/-- The shape's trace scale: `q = (N+ρ)/(N+1)`, squared `= 256/169`. -/
def geoQ : ℚ := 256 / 169

theorem Mpar_pos (dq : ℚ) : 0 < Mpar dq := by
  unfold Mpar
  nlinarith [sq_nonneg dq]

theorem alphaQ_val : alphaQ (2 * 2) rhoQ = alpQ := by
  unfold alphaQ rhoQ alpQ
  norm_num

theorem betaQ_val : betaQ (2 * 2) = betQ := by
  unfold betaQ betQ
  norm_num

theorem gammaR_val : gammaR (2 * 2) ((rhoQ : ℚ) : ℝ) = ((gamQ : ℚ) : ℝ) := by
  unfold gammaR rhoQ gamQ
  norm_num

theorem gamQ_pos : 0 < ((gamQ : ℚ) : ℝ) := by unfold gamQ; norm_num

theorem alpQ_pos : 0 < alpQ := by unfold alpQ; norm_num

theorem geoQ_pos : 0 < geoQ := by unfold geoQ; norm_num

/-- The step's trace scale is `(1 + β)·α`: `q = (5/3)·α`. -/
theorem geoQ_eq : geoQ = (5 / 3) * alpQ := by unfold geoQ alpQ; norm_num

theorem alpQ_le_geoQ : alpQ ≤ geoQ := by unfold geoQ alpQ; norm_num

/-! ### 2.2  The explicit shape and its trace scale

`a_k = M⁻¹·α^k`, `b_k = (t_k − a_k)/2` with `t_k = a_k + 2·b_k = M⁻¹·q^k` (so `t_k` *is*
`f ⪝ (A_k⁻¹ f)`). -/

/-- The shape's trace scale `t_k = M⁻¹·q^k = f ⪝ A_k⁻¹ f`. -/
def tsc (dq : ℚ) (k : ℕ) : ℚ := (Mpar dq)⁻¹ * geoQ ^ k

/-- The identity coefficient of the shape. -/
def asc (dq : ℚ) (k : ℕ) : ℚ := (Mpar dq)⁻¹ * alpQ ^ k

/-- The rank-one coefficient of the shape. -/
def bsc (dq : ℚ) (k : ℕ) : ℚ := (tsc dq k - asc dq k) / 2

/-- The explicit two-term shape. -/
def Aex (dq : ℚ) (k : ℕ) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ :=
  asc dq k • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ) + bsc dq k • Matrix.vecMulVec fr fr

/-- The starting shape, at the campaign cap `M = capOf` of `n = 2`. -/
def A0 (dq : ℚ) : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (2 * 2) (Mpar dq)

/-- The exact witness of the trace direction at round `k`: `t_k⁻¹ • f`. -/
def pvec (dq : ℚ) (k : ℕ) : Fin (2 * 2) → ℚ := (tsc dq k)⁻¹ • fr

/-- **The pure-dilation cut stream**: normal `f`, exact witness `t_k⁻¹•f`, depth `rmax`. -/
def cd (dq : ℚ) : ℕ → CutData (2 * 2) := fun k => ⟨fr, pvec dq k, rhoQ⟩

@[simp] theorem cd_c (dq : ℚ) (k : ℕ) : (cd dq k).c = fr := rfl
@[simp] theorem cd_p (dq : ℚ) (k : ℕ) : (cd dq k).p = pvec dq k := rfl
@[simp] theorem cd_rho (dq : ℚ) (k : ℕ) : (cd dq k).rho = rhoQ := rfl

theorem cd_cne (dq : ℚ) : ∀ k, (cd dq k).c ≠ 0 := fun _ => fr_ne_zero

theorem Mpar_inv_pos (dq : ℚ) : 0 < (Mpar dq)⁻¹ := inv_pos.mpr (Mpar_pos dq)

theorem tsc_pos (dq : ℚ) (k : ℕ) : 0 < tsc dq k :=
  mul_pos (Mpar_inv_pos dq) (pow_pos geoQ_pos k)

theorem tsc_ne (dq : ℚ) (k : ℕ) : tsc dq k ≠ 0 := ne_of_gt (tsc_pos dq k)

theorem asc_pos (dq : ℚ) (k : ℕ) : 0 < asc dq k :=
  mul_pos (Mpar_inv_pos dq) (pow_pos alpQ_pos k)

/-- `a_k ≤ t_k`: `α^k ≤ q^k` and `M⁻¹ > 0`. -/
theorem asc_le_tsc (dq : ℚ) (k : ℕ) : asc dq k ≤ tsc dq k :=
  mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (le_of_lt alpQ_pos) alpQ_le_geoQ k) (le_of_lt (Mpar_inv_pos dq))

theorem bsc_nonneg (dq : ℚ) (k : ℕ) : 0 ≤ bsc dq k := by
  unfold bsc
  have := asc_le_tsc dq k
  linarith

theorem tsc_succ (dq : ℚ) (k : ℕ) : tsc dq (k + 1) = geoQ * tsc dq k := by
  unfold tsc
  rw [pow_succ']
  ring

theorem asc_succ (dq : ℚ) (k : ℕ) : asc dq (k + 1) = alpQ * asc dq k := by
  unfold asc
  rw [pow_succ']
  ring

/-- The rank-one coefficient's step, which is `rStep`'s action on `b_k`. -/
theorem bsc_succ (dq : ℚ) (k : ℕ) (ht : tsc dq k ≠ 0) :
    bsc dq (k + 1) = alpQ * (bsc dq k + betQ / (2 / tsc dq k)) := by
  have hdiv : betQ / (2 / tsc dq k) = betQ * tsc dq k / 2 := by
    field_simp
  rw [bsc, bsc, tsc_succ, asc_succ, hdiv]
  unfold betQ alpQ geoQ
  field_simp
  ring

/-- The engine's `σ` at the pure-dilation stream: `c ⪝ p = t_k⁻¹·(f ⪝ f) = 2/t_k`. -/
theorem sigmaQ_fr_pvec (dq : ℚ) (k : ℕ) (ht : tsc dq k ≠ 0) :
    sigmaQ fr (pvec dq k) = 2 / tsc dq k := by
  unfold sigmaQ pvec
  rw [dotProduct_smul, fr_dot, smul_eq_mul]
  field_simp

theorem initShapeOf_eq (dq : ℚ) :
    QMCLeafB.Boundary.initShapeOf (2 * 2) (Mpar dq)
      = (Mpar dq)⁻¹ • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ) := rfl

/-- The scalar action of a two-term shape's update: `α•((x•1 + y•ffᵀ) + c•ffᵀ)` is the two-term
shape with coefficients `α·x` and `α·(y + c)`. -/
theorem iso_step {N : ℕ} (f0 : Fin N → ℚ) (x y c : ℚ) :
    alpQ • ((x • (1 : Matrix (Fin N) (Fin N) ℚ) + y • Matrix.vecMulVec f0 f0)
        + c • Matrix.vecMulVec f0 f0)
      = (alpQ * x) • (1 : Matrix (Fin N) (Fin N) ℚ)
        + (alpQ * (y + c)) • Matrix.vecMulVec f0 f0 := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> ring

theorem tsc_zero (dq : ℚ) : tsc dq 0 = (Mpar dq)⁻¹ := by
  unfold tsc
  simp

theorem asc_zero (dq : ℚ) : asc dq 0 = (Mpar dq)⁻¹ := by
  unfold asc
  simp

/-- One step of the two-term recursion: `rStep` acts on the coefficients exactly as
`a ↦ α·a`, `b ↦ α·(b + β/σ)`. -/
theorem Aex_succ (dq : ℚ) (k : ℕ) :
    rStep (2 * 2) (Aex dq k) fr (pvec dq k) rhoQ = Aex dq (k + 1) := by
  have h1 : rStep (2 * 2) (Aex dq k) fr (pvec dq k) rhoQ
      = alpQ • (Aex dq k + (betQ / (2 / tsc dq k)) • Matrix.vecMulVec fr fr) := by
    rw [rStep, alphaQ_val, betaQ_val, sigmaQ_fr_pvec dq k (tsc_ne dq k)]
  rw [h1,
    show Aex dq k = asc dq k • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ)
      + bsc dq k • Matrix.vecMulVec fr fr from rfl,
    iso_step, ← asc_succ dq k, ← bsc_succ dq k (tsc_ne dq k),
    show asc dq (k + 1) • (1 : Matrix (Fin (2 * 2)) (Fin (2 * 2)) ℚ)
      + bsc dq (k + 1) • Matrix.vecMulVec fr fr = Aex dq (k + 1) from rfl]

/-- **The shape induction**: along the engine's own recursion the shape stays in the two-term
algebra.  This is the missing Lean step of `smw1i2drp/m3`'s `RESULTS.md` §3b. -/
theorem Aat_eq_Aex (dq : ℚ) (k : ℕ) : Aat (2 * 2) (A0 dq) (cd dq) k = Aex dq k := by
  induction k with
  | zero =>
      show A0 dq = Aex dq 0
      rw [A0, initShapeOf_eq, Aex, bsc, tsc_zero, asc_zero]
      simp
  | succ k ih =>
      rw [show Aat (2 * 2) (A0 dq) (cd dq) (k + 1)
          = rStep (2 * 2) (Aat (2 * 2) (A0 dq) (cd dq) k) fr (pvec dq k) rhoQ from rfl, ih,
        Aex_succ dq k]

/-- **The stream is legitimate (exact witness).** -/
theorem Aex_wit (dq : ℚ) (k : ℕ) :
    Aat (2 * 2) (A0 dq) (cd dq) k *ᵥ pvec dq k = fr := by
  rw [Aat_eq_Aex]
  have hff : fr ⬝ᵥ fr = 2 := fr_dot
  rw [Aex, pvec]
  have hs : tsc dq k = asc dq k + bsc dq k * (fr ⬝ᵥ fr) := by
    rw [hff]; unfold bsc; ring
  rw [iso_mulVec_smul fr (asc dq k) (bsc dq k) (tsc dq k)⁻¹ (tsc dq k) hs]
  rw [inv_mul_cancel₀ (tsc_ne dq k), one_smul]

/-- **The stream is legitimate (positive definite shapes).** -/
theorem Aex_posQ (dq : ℚ) (k : ℕ) : PosQ (Aat (2 * 2) (A0 dq) (cd dq) k) := by
  rw [Aat_eq_Aex, Aex]
  exact iso_posQ fr (asc_pos dq k) (bsc_nonneg dq k)
/-! ## 3.  The drift at the pure-dilation stream overflows the trace budget

`engLam j = γ/√σ_j` and `diagSum (p_j) = σ_j = 2/t_j`, so round `j`'s increment is `γ·√σ_j` (one
`√σ` cancels), and `σ_j = 2M·(13/16)^{2j}`.  Hence

    diagSum (Cat 4 0 cd k) = √(nM)·∑_{j<k} (13/16)^j ,

whose limit `√(nM) = √(8 + 2dq²) > n = 2` is over the budget `(1 − dq/4)·n`; the explicit partial
sum at `k = 4` already is: `4·(1 + 13/16 + (13/16)² + (13/16)³) = 36975/16384 > 2`. -/

/-- The dilation scale `13/16`: `f ⪝ A_k⁻¹ f = 2M·(13/16)^{2k}`. -/
def sqQ : ℚ := 13 / 16

theorem sqQ_pos : 0 < sqQ := by unfold sqQ; norm_num

/-- `(q^j)⁻¹ = (13/16)^{2j}`: the trace scale's inverse is a perfect square. -/
theorem inv_geoQ_pow (j : ℕ) : ((geoQ : ℚ) ^ j)⁻¹ = ((sqQ : ℚ) ^ j) ^ 2 := by
  have h : (geoQ : ℚ) = ((sqQ : ℚ) ^ 2)⁻¹ := by unfold geoQ sqQ; norm_num
  rw [h, ← inv_pow, inv_inv, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The engine's `σ`-scale at round `j`: `σ_j = 2/t_j = 2M·(13/16)^{2j}`. -/
theorem sQ_eq (dq : ℚ) (j : ℕ) :
    2 / tsc dq j = 2 * Mpar dq * ((sqQ : ℚ) ^ j) ^ 2 := by
  rw [← inv_geoQ_pow]
  unfold tsc
  have hM : Mpar dq ≠ 0 := ne_of_gt (Mpar_pos dq)
  have hq : geoQ ^ j ≠ 0 := pow_ne_zero j (by unfold geoQ; norm_num)
  field_simp

/-- Casting a rational dot product. -/
theorem cast_dotQ {N : ℕ} (u v : Fin N → ℚ) :
    ((u ⬝ᵥ v : ℚ) : ℝ) = (fun i => ((u i : ℚ) : ℝ)) ⬝ᵥ (fun i => ((v i : ℚ) : ℝ)) := by
  simp only [dotProduct, Rat.cast_sum, Rat.cast_mul]

theorem cutCR_cd (dq : ℚ) (j : ℕ) : cutCR (cd dq) j = fun i => ((fr i : ℚ) : ℝ) := rfl

theorem cutPR_cd (dq : ℚ) (j : ℕ) : cutPR (cd dq) j = fun i => ((pvec dq j i : ℚ) : ℝ) := rfl

/-- The engine's real squared cut norm at the pure-dilation stream. -/
theorem sigmaR_cd (dq : ℚ) (j : ℕ) (ht : tsc dq j ≠ 0) :
    sigmaR (cutCR (cd dq) j) (cutPR (cd dq) j) = (((2 / tsc dq j : ℚ)) : ℝ) := by
  unfold sigmaR
  rw [cutCR_cd, cutPR_cd, ← cast_dotQ,
    show fr ⬝ᵥ pvec dq j = sigmaQ fr (pvec dq j) from rfl, sigmaQ_fr_pvec dq j ht]

/-- The engine's `√σ` at the pure-dilation stream. -/
theorem sqrtSigmaR_cd (dq : ℚ) (j : ℕ) (ht : tsc dq j ≠ 0) :
    sqrtSigmaR (cutCR (cd dq) j) (cutPR (cd dq) j)
      = Real.sqrt (((2 / tsc dq j : ℚ)) : ℝ) := by
  unfold sqrtSigmaR
  rw [sigmaR_cd dq j ht]

/-- **The engine's step coefficient** at the pure-dilation stream: `γ/√(2/t_j)`. -/
theorem engLam_val (dq : ℚ) (j : ℕ) (ht : tsc dq j ≠ 0) :
    engLam (2 * 2) (cd dq) j
      = ((gamQ : ℚ) : ℝ) / Real.sqrt (((2 / tsc dq j : ℚ)) : ℝ) := by
  rw [engLam, QMCLeafB.CentreTrack.lam, cd_rho, gammaR_val, sqrtSigmaR_cd dq j ht]

/-- **The diagonal read-out** at the pure-dilation stream: `diagSum (p_j) = 2/t_j = σ_j`. -/
theorem diagSum_cutPR (dq : ℚ) (j : ℕ) (ht : tsc dq j ≠ 0) :
    QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) = (((2 / tsc dq j : ℚ)) : ℝ) := by
  rw [← QMCLeafB.DriftExact.dOne_dot]
  have hfR : QMCLeafB.RunPartsStream.dOne 2 = fun i => ((fr i : ℚ) : ℝ) := rfl
  rw [hfR, cutPR_cd]
  have hsplit : (fun i => ((pvec dq j i : ℚ) : ℝ))
      = (((tsc dq j : ℚ) : ℝ))⁻¹ • (fun i => ((fr i : ℚ) : ℝ)) := by
    funext i
    simp [pvec, smul_eq_mul]
  rw [hsplit, dotProduct_smul, smul_eq_mul]
  have hff : (fun i => ((fr i : ℚ) : ℝ)) ⬝ᵥ (fun i => ((fr i : ℚ) : ℝ)) = 2 := by
    rw [← cast_dotQ, fr_dot]
    norm_num
  rw [hff]
  push_cast
  field_simp

/-- `√σ_j = √(2M)·(13/16)^j`. -/
theorem sqrt_s_val (dq : ℚ) (j : ℕ) :
    Real.sqrt (((2 / tsc dq j : ℚ)) : ℝ)
      = Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) * ((sqQ : ℚ) : ℝ) ^ j := by
  rw [sQ_eq dq j]
  have hcast : (((2 * Mpar dq * ((sqQ : ℚ) ^ j) ^ 2 : ℚ)) : ℝ)
      = (((2 * Mpar dq : ℚ)) : ℝ) * (((sqQ : ℚ) : ℝ) ^ j) ^ 2 := by push_cast; ring
  have hsq : (0 : ℝ) ≤ ((sqQ : ℚ) : ℝ) ^ j :=
    pow_nonneg (by exact_mod_cast le_of_lt sqQ_pos) j
  have h2M : (0 : ℝ) ≤ ((2 * Mpar dq : ℚ) : ℝ) := by
    have h : (0 : ℝ) < ((Mpar dq : ℚ) : ℝ) := by exact_mod_cast Mpar_pos dq
    have h2 : ((2 * Mpar dq : ℚ) : ℝ) = 2 * ((Mpar dq : ℚ) : ℝ) := by push_cast; ring
    rw [h2]; linarith
  rw [hcast, Real.sqrt_mul h2M, Real.sqrt_sq hsq]

theorem div_sqrt_mul_self {g S : ℝ} (hS : 0 < S) :
    (g / Real.sqrt S) * S = g * Real.sqrt S := by
  have h : Real.sqrt S ^ 2 = S := Real.sq_sqrt (le_of_lt hS)
  have hne : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hS)
  field_simp
  rw [h]

/-- **The round's increment** at the pure-dilation stream: `γ·√(2M)·(13/16)^j`. -/
theorem incr_val (dq : ℚ) (j : ℕ) (ht : tsc dq j ≠ 0) :
    engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j)
      = ((gamQ : ℚ) : ℝ) * (Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) * ((sqQ : ℚ) : ℝ) ^ j) := by
  have hs : (0 : ℝ) < (((2 / tsc dq j : ℚ)) : ℝ) := by
    have hq : (0 : ℚ) < 2 / tsc dq j := div_pos (by norm_num) (tsc_pos dq j)
    exact_mod_cast hq
  rw [engLam_val dq j ht, diagSum_cutPR dq j ht,
    div_sqrt_mul_self (g := ((gamQ : ℚ) : ℝ)) hs, sqrt_s_val dq j]

theorem incr_nonneg (dq : ℚ) (j : ℕ) :
    0 ≤ engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) := by
  rw [incr_val dq j (tsc_ne dq j)]
  have h1 : (0 : ℝ) ≤ Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ ((sqQ : ℚ) : ℝ) ^ j :=
    pow_nonneg (by exact_mod_cast le_of_lt sqQ_pos) j
  have h3 : (0 : ℝ) ≤ ((gamQ : ℚ) : ℝ) := le_of_lt gamQ_pos
  exact mul_nonneg h3 (mul_nonneg h1 h2)

/-- `√(2M) ≥ 4` — because `2M = 16 + 4dq²`. -/
theorem sqrt_two_M_ge (dq : ℚ) : 4 ≤ Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) := by
  have h2M : (16 : ℝ) ≤ (((2 * Mpar dq : ℚ)) : ℝ) := by
    have hq : (16 : ℚ) ≤ 2 * Mpar dq := by unfold Mpar; nlinarith [sq_nonneg dq]
    exact_mod_cast hq
  calc (4 : ℝ) = Real.sqrt 16 := by norm_num
    _ ≤ Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) := Real.sqrt_le_sqrt h2M

/-- The finite geometric sum. -/
theorem sqQ_sum_four : (∑ j ∈ Finset.range 4, ((sqQ : ℚ) : ℝ) ^ j) = ((12325 / 4096 : ℚ) : ℝ) := by
  have h1 : (∑ j ∈ Finset.range 4, ((sqQ : ℚ) : ℝ) ^ j)
      = (((∑ j ∈ Finset.range 4, (sqQ : ℚ) ^ j : ℚ)) : ℝ) := by
    rw [Rat.cast_sum]
    exact Finset.sum_congr rfl (fun j _ => (Rat.cast_pow ..).symm)
  rw [h1]
  norm_num [Finset.sum_range_succ, sqQ]

/-- **The trace-budget scalar fails at round 4.**  At the pure-dilation stream the accumulated
drift after four rounds already exceeds `(1 − dq/4)·n` for *every* `dq > 0`. -/
theorem drift_overflow (dq : ℚ) (hdq : 0 < dq) :
    ((1 - dq / 4 : ℚ) : ℝ) * 2
      < ∑ j ∈ Finset.range 4,
          engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) := by
  rw [Finset.sum_congr rfl (fun j (_ : j ∈ Finset.range 4) => incr_val dq j (tsc_ne dq j))]
  have hsum : (∑ j ∈ Finset.range 4,
        ((gamQ : ℚ) : ℝ) * (Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) * ((sqQ : ℚ) : ℝ) ^ j))
      = ((gamQ : ℚ) : ℝ) * Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ)
        * (∑ j ∈ Finset.range 4, ((sqQ : ℚ) : ℝ) ^ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hsum, sqQ_sum_four]
  have hS : 4 ≤ Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) := sqrt_two_M_ge dq
  have hg : (0 : ℝ) ≤ ((gamQ : ℚ) : ℝ) := le_of_lt gamQ_pos
  have hstep : ((gamQ : ℚ) : ℝ) * 4 * ((12325 / 4096 : ℚ) : ℝ)
      ≤ ((gamQ : ℚ) : ℝ) * Real.sqrt (((2 * Mpar dq : ℚ)) : ℝ) * ((12325 / 4096 : ℚ) : ℝ) := by
    have hQ : (0 : ℝ) ≤ ((12325 / 4096 : ℚ) : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left hS hg
    nlinarith [this, hQ]
  have hval : (2 : ℝ) < ((gamQ : ℚ) : ℝ) * 4 * ((12325 / 4096 : ℚ) : ℝ) := by
    norm_num [gamQ]
  have hbound : ((1 - dq / 4 : ℚ) : ℝ) * 2 ≤ 2 := by
    have h1 : ((1 - dq / 4 : ℚ) : ℝ) ≤ 1 := by
      have hq : (1 - dq / 4 : ℚ) ≤ 1 := by
        have := le_of_lt hdq
        linarith
      exact_mod_cast hq
    nlinarith
  linarith

/-- **The budget fails at every round `k ≥ 4`** (the drift is monotone in the round count), so
horizon-bounding the scalar does not repair it. -/
theorem drift_overflow_ge (dq : ℚ) (hdq : 0 < dq) {k : ℕ} (hk : 4 ≤ k) :
    ((1 - dq / 4 : ℚ) : ℝ) * 2
      < QMCLeafB.DriftExact.diagSum (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ) (cd dq) k) := by
  rw [QMCLeafB.DriftExact.diagSum_cat]
  have hmono : (∑ j ∈ Finset.range 4,
        engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j))
      ≤ ∑ j ∈ Finset.range k,
        engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk) ?_
    intro j _ _
    exact incr_nonneg dq j
  linarith [drift_overflow dq hdq]

/-! ## 4.  The record-level consequences

`RecordsM2.hdriftd_diagPinch_iff` identifies the `hdriftd` slot of `CoreData`/`StreamCore` at the
record's own pinched centre with exactly the scalar above.  So at the pure-dilation stream the slot
is **false** at round 4 — and, by §3, at every later round. -/

/-- **`hdriftd` is false at the pinched centre, round 4, at the pure-dilation stream** — for every
base matrix `Q` (the pinched centre's trace is `n(1 − dq/4)` unconditionally). -/
theorem hdriftd_false_pinch (dq : ℚ) (hdq : 0 < dq) (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ (QMCLeafB.RunPartsStream.dOne 2 ⬝ᵥ
        (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ) (cd dq) 4
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))) ≤ 0) := by
  intro h
  have h2 := (QMCLeafB.RecordsM2.hdriftd_diagPinch_iff (cd dq) Q 4).1 h
  have h3 : (∑ j ∈ Finset.range 4,
      engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j))
      ≤ ((1 - dq / 4 : ℚ) : ℝ) * 2 := by
    simpa using h2
  linarith [drift_overflow dq hdq]

/-- **At an empty relaxed body every normal is a legal cut.**  The `separates` field of
`RelaxOracle.RelaxCut` is vacuous, so a refuted point has no constraint at all on the cut stream —
in particular the trace-direction stream of §2 is admissible there. -/
theorem nonempty_relaxCut_of_emptyBody {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (hempty : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      ¬ QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X)
    (normal : Matrix (Fin n) (Fin n) ℚ) (margin : ℚ) (hm : 0 < margin) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut A cX u δ) :=
  ⟨{ normal := normal
     margin := margin
     margin_pos := hm
     separates := fun X hX => absurd hX (hempty X) }⟩

/-! ## 5.  The campaign's own constants

`rmaxOf 4 = 1/16`, and at `G.n = 2` the campaign cap is `capOf G dq = 8 + 2dq² = M`; so the stream
of §2 is literally the engine's chain at the campaign's own starting shape `A0P` and its own ceiling
depth `rmaxOf (n·n)`. -/

theorem capOf_n_two (G : QuantumMaxCutEnergy.Input) (hG : G.n = 2) (dq : ℚ) :
    QMCLeafB.RundataArith.capOf G dq = Mpar dq := by
  unfold QMCLeafB.RundataArith.capOf Mpar
  rw [hG]
  norm_num

theorem rmaxOf_four_eq : QMCLeafB.RundataHalving.rmaxOf (2 * 2) = rhoQ := by
  unfold QMCLeafB.RundataHalving.rmaxOf rhoQ
  norm_num

/-- The starting shape of §2 *is* the campaign's initial shape `initShapeOf (2n² + 2dq²)` (i.e.
`A0P G P` at `G.n = 2`, definitionally). -/
theorem A0_eq_campaign (G : QuantumMaxCutEnergy.Input) (hG : G.n = 2) (dq : ℚ) :
    A0 dq = QMCLeafB.Boundary.initShapeOf (2 * 2) (QMCLeafB.RundataArith.capOf G dq) := by
  rw [A0, capOf_n_two G hG dq]

/-- At the pure-dilation stream the cut normal *is* the trace direction, so the normal budget
(`hnorm`) and the trace budget (`hbud`) have the *same* left-hand side there — only their
right-hand sides differ (the normal one carries the extra `marg_k/2`). -/
theorem normal_budget_eq_trace (dq : ℚ) (j : ℕ) :
    (fun i => ((fr i : ℚ) : ℝ)) ⬝ᵥ cutPR (cd dq) j
      = QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) := by
  rw [show (fun i => ((fr i : ℚ) : ℝ)) = QMCLeafB.RunPartsStream.dOne 2 from rfl,
    QMCLeafB.DriftExact.dOne_dot]

/-! ## 6.  `λ` cancels: the drift is invariant under positive rescaling of (normal, witness)

The dilation brick (`RecordM2.cnInd`) adds `λ_k • f` to every oracle normal, and `hlam2` forces
`λ_k` large.  This section machine-checks the phase-18 claim that `λ` *cancels identically*: a
positive rescaling of the normal–witness pair leaves `rStep` — hence the whole shape chain — and
each round's increment unchanged.  So no choice of dilation multiplier can repair the trace budget
of §3, and the refutation applies to the dilation-only stream at *any* multiplier. -/

theorem vecMulVec_smul_self {N : ℕ} (s : ℚ) (f0 : Fin N → ℚ) :
    Matrix.vecMulVec (s • f0) (s • f0) = (s * s) • Matrix.vecMulVec f0 f0 := by
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem sigmaQ_smul {N : ℕ} (s : ℚ) (c p : Fin N → ℚ) :
    sigmaQ (s • c) (s • p) = (s * s) * sigmaQ c p := by
  unfold sigmaQ
  rw [dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  ring

theorem rStep_smul {N : ℕ} (s : ℚ) (hs : s ≠ 0) (A : Matrix (Fin N) (Fin N) ℚ)
    (c p : Fin N → ℚ) (ρ : ℚ) :
    rStep N A (s • c) (s • p) ρ = rStep N A c p ρ := by
  unfold rStep
  rw [sigmaQ_smul, vecMulVec_smul_self]
  have hinner : A + (betaQ N / ((s * s) * sigmaQ c p)) • ((s * s) • Matrix.vecMulVec c c)
      = A + (betaQ N / sigmaQ c p) • Matrix.vecMulVec c c := by
    rw [smul_smul]
    congr 2
    by_cases hσ : sigmaQ c p = 0
    · simp [hσ]
    · field_simp
  rw [hinner]

/-- **Positive rescaling leaves the whole shape chain unchanged.** -/
theorem Aat_smul {N : ℕ} (A0 : Matrix (Fin N) (Fin N) ℚ) (cd : ℕ → CutData N)
    (s : ℕ → ℚ) (hs : ∀ k, s k ≠ 0) (k : ℕ) :
    Aat N A0 (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) k = Aat N A0 cd k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      show rStep N (Aat N A0 (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) k)
          (s k • (cd k).c) (s k • (cd k).p) ((cd k).rho) = Aat N A0 cd (k + 1)
      rw [ih, rStep_smul (s k) (hs k),
        show Aat N A0 cd (k + 1) = rStep N (Aat N A0 cd k) (cd k).c (cd k).p (cd k).rho from rfl]

theorem cutCR_smul {N : ℕ} (cd : ℕ → CutData N) (s : ℕ → ℚ) (j : ℕ) :
    cutCR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
      = (((s j : ℚ) : ℝ)) • cutCR cd j := by
  funext i
  simp [cutCR, smul_eq_mul]

theorem cutPR_smul {N : ℕ} (cd : ℕ → CutData N) (s : ℕ → ℚ) (j : ℕ) :
    cutPR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
      = (((s j : ℚ) : ℝ)) • cutPR cd j := by
  funext i
  simp [cutPR, smul_eq_mul]

theorem sigmaR_smul {N : ℕ} (cd : ℕ → CutData N) (s : ℕ → ℚ) (j : ℕ) :
    sigmaR (cutCR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j)
        (cutPR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j)
      = ((((s j : ℚ) : ℝ))) ^ 2 * sigmaR (cutCR cd j) (cutPR cd j) := by
  unfold sigmaR
  rw [cutCR_smul, cutPR_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The step coefficient scales by `1/s`.** -/
theorem lam_smul {N : ℕ} (cd : ℕ → CutData N) (s : ℕ → ℚ) (hpos : ∀ k, 0 < s k) (j : ℕ) :
    QMCLeafB.CentreTrack.lam N (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
      = (1 / (((s j : ℚ) : ℝ))) * QMCLeafB.CentreTrack.lam N cd j := by
  have hsR : (0 : ℝ) < (((s j : ℚ) : ℝ)) := by exact_mod_cast hpos j
  have hsq : Real.sqrt (((((s j : ℚ) : ℝ))) ^ 2 * sigmaR (cutCR cd j) (cutPR cd j))
      = (((s j : ℚ) : ℝ)) * Real.sqrt (sigmaR (cutCR cd j) (cutPR cd j)) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hsR)]
  unfold QMCLeafB.CentreTrack.lam QMCLeafB.EngineIterates.sqrtSigmaR
  rw [sigmaR_smul, hsq]
  field_simp

/-- **The round increment is invariant under positive rescaling.** -/
theorem incr_smul {m : ℕ} (cd : ℕ → CutData (m * m)) (s : ℕ → ℚ) (hpos : ∀ k, 0 < s k)
    (j : ℕ) :
    engLam (m * m) (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
        * QMCLeafB.DriftExact.diagSum
          (cutPR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j)
      = engLam (m * m) cd j * QMCLeafB.DriftExact.diagSum (cutPR cd j) := by
  have hsR : (((s j : ℚ) : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < (((s j : ℚ) : ℝ)) := by exact_mod_cast hpos j
    linarith
  rw [show engLam (m * m) (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
        = QMCLeafB.CentreTrack.lam (m * m)
            (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j from rfl,
    lam_smul cd s hpos j, cutPR_smul cd s j, QMCLeafB.DriftExact.diagSum_smul]
  field_simp
  rw [show engLam (m * m) cd j = QMCLeafB.CentreTrack.lam (m * m) cd j from rfl]
  ring

/-- **The accumulated drift is invariant under positive rescaling.** -/
theorem drift_smul {m : ℕ} (cd : ℕ → CutData (m * m)) (s : ℕ → ℚ) (hpos : ∀ k, 0 < s k)
    (k : ℕ) :
    (∑ j ∈ Finset.range k,
        engLam (m * m) (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j
          * QMCLeafB.DriftExact.diagSum
              (cutPR (fun j => ⟨s j • (cd j).c, s j • (cd j).p, (cd j).rho⟩) j))
      = ∑ j ∈ Finset.range k,
          engLam (m * m) cd j * QMCLeafB.DriftExact.diagSum (cutPR cd j) :=
  Finset.sum_congr rfl (fun j _ => incr_smul cd s hpos j)

/-- The concrete-dilation form of `drift_smul` (the multiplier stream written out). -/
theorem drift_smul_cd (dq : ℚ) (lam : ℕ → ℚ) (hlam : ∀ k, 0 < lam k) (k : ℕ) :
    (∑ j ∈ Finset.range k,
        engLam (2 * 2) (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) j
          * QMCLeafB.DriftExact.diagSum
              (cutPR (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) j))
      = ∑ j ∈ Finset.range k,
          engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) :=
  drift_smul (m := 2) (cd dq) lam hlam k

/-- **`λ` cannot repair the trace budget.**  Any positive dilation multiplier stream of the
trace direction (`λ_k • f` with its exact witness `λ_k • (t_k⁻¹ f)`) overflows the budget at
round 4, exactly as the multiplier-free stream does. -/
theorem drift_overflow_scaled (dq : ℚ) (hdq : 0 < dq) (lam : ℕ → ℚ) (hlam : ∀ k, 0 < lam k) :
    ((1 - dq / 4 : ℚ) : ℝ) * 2
      < QMCLeafB.DriftExact.diagSum (n := 2)
          (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ)
            (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) 4) := by
  rw [QMCLeafB.DriftExact.diagSum_cat]
  rw [drift_smul_cd dq lam hlam 4]
  exact drift_overflow dq hdq

/-- The scaled overflow persists at every later round (the per-round increments are the *same*
numbers, §3's `incr_nonneg`). -/
theorem drift_overflow_scaled_ge (dq : ℚ) (hdq : 0 < dq) (lam : ℕ → ℚ) (hlam : ∀ k, 0 < lam k)
    {k : ℕ} (hk : 4 ≤ k) :
    ((1 - dq / 4 : ℚ) : ℝ) * 2
      < QMCLeafB.DriftExact.diagSum (n := 2)
          (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ)
            (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) k) := by
  rw [QMCLeafB.DriftExact.diagSum_cat, drift_smul_cd dq lam hlam k]
  have hmono : (∑ j ∈ Finset.range 4,
        engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j))
      ≤ ∑ j ∈ Finset.range k,
        engLam (2 * 2) (cd dq) j * QMCLeafB.DriftExact.diagSum (cutPR (cd dq) j) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk) ?_
    intro j _ _
    exact incr_nonneg dq j
  linarith [drift_overflow dq hdq]

/-- The same at the record's pinched centre, at any positive dilation multiplier. -/
theorem hdriftd_false_pinch_scaled (dq : ℚ) (hdq : 0 < dq) (lam : ℕ → ℚ) (hlam : ∀ k, 0 < lam k)
    (Q : Matrix (Fin 2) (Fin 2) ℚ) :
    ¬ (QMCLeafB.RunPartsStream.dOne 2 ⬝ᵥ
        (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ)
            (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) 4
          - QMCLeafB.AnswerProducer.flat
              (QMCLeafB.SepOracle.castMat (QMCLeafB.CentreAdm.diagPinch Q dq))) ≤ 0) := by
  intro h
  have h2 := (QMCLeafB.RecordsM2.hdriftd_diagPinch_iff
    (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) Q 4).1 h
  have h3 : QMCLeafB.DriftExact.diagSum (n := 2)
      (Cat (2 * 2) (0 : Fin (2 * 2) → ℝ)
        (fun j => ⟨lam j • fr, lam j • pvec dq j, rhoQ⟩) 4) ≤ ((1 - dq / 4 : ℚ) : ℝ) * 2 := by
    rw [QMCLeafB.DriftExact.diagSum_cat]
    simpa using h2
  linarith [drift_overflow_scaled dq hdq lam hlam]

end QMCLeafB.CutBudgetM8

/-! ## 5.  Axiom audit -/

#print axioms QMCLeafB.CutBudgetM8.iso_mulVec
#print axioms QMCLeafB.CutBudgetM8.iso_posQ
#print axioms QMCLeafB.CutBudgetM8.fr_dot
#print axioms QMCLeafB.CutBudgetM8.sQ_eq
#print axioms QMCLeafB.CutBudgetM8.inv_geoQ_pow
#print axioms QMCLeafB.CutBudgetM8.Aat_eq_Aex
#print axioms QMCLeafB.CutBudgetM8.Aex_wit
#print axioms QMCLeafB.CutBudgetM8.Aex_posQ
#print axioms QMCLeafB.CutBudgetM8.engLam_val
#print axioms QMCLeafB.CutBudgetM8.diagSum_cutPR
#print axioms QMCLeafB.CutBudgetM8.sqrt_s_val
#print axioms QMCLeafB.CutBudgetM8.incr_val
#print axioms QMCLeafB.CutBudgetM8.incr_nonneg
#print axioms QMCLeafB.CutBudgetM8.sqrt_two_M_ge
#print axioms QMCLeafB.CutBudgetM8.sqQ_sum_four
#print axioms QMCLeafB.CutBudgetM8.drift_overflow
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_ge
#print axioms QMCLeafB.CutBudgetM8.hdriftd_false_pinch
#print axioms QMCLeafB.CutBudgetM8.nonempty_relaxCut_of_emptyBody
#print axioms QMCLeafB.CutBudgetM8.capOf_n_two
#print axioms QMCLeafB.CutBudgetM8.rmaxOf_four_eq
#print axioms QMCLeafB.CutBudgetM8.A0_eq_campaign
#print axioms QMCLeafB.CutBudgetM8.normal_budget_eq_trace
#print axioms QMCLeafB.CutBudgetM8.rStep_smul
#print axioms QMCLeafB.CutBudgetM8.Aat_smul
#print axioms QMCLeafB.CutBudgetM8.lam_smul
#print axioms QMCLeafB.CutBudgetM8.drift_smul
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_scaled
#print axioms QMCLeafB.CutBudgetM8.hdriftd_false_pinch_scaled
#print axioms QMCLeafB.CutBudgetM8.incr_smul
#print axioms QMCLeafB.CutBudgetM8.drift_overflow_scaled_ge



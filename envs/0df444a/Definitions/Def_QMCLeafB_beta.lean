-- Prove2me | Definitions.Def_QMCLeafB_beta
-- name    : QMCLeafB_beta
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:28:57.653351+00:00
-- url     : https://prove2.me/theorems/0fa49163-c31b-43cf-89b7-9fabab41ccac
-- title:
--   QMCLeafB beta
-- statement:
--   # leaf B phase 24 — m6, direction `beta-pricing`: the exact price of the `dM = −1` / β lane,
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_orient
import Definitions.Def_QMCLeafB_parts_m2
/-
# leaf B phase 24 — m6, direction `beta-pricing`: the exact price of the `dM = −1` / β lane,
and the one-sided reading that makes the price zero

## What the direction asked

At the sliver exemplar `(G₁, t₁)` (body nonempty, no pinched member, verdict bit forced `false`)
`Check_orient_m1` refuted the reversed orientation `dM = −1` at `β = 0` and left exactly one
escape: `RelaxCut.dilate`'s full form with a body margin `β > 0`, "priced through the `λβ` margin".
This file prices that lane in exact arithmetic, and then shows the price is being paid on the wrong
object.

## 1.  The one-sided reading of `RunParts.hcut` (§1–§2)

`RunParts.hcut` reads `−del ≤ cutCR k ⬝ (z − Cat k)` for every `z` of the relaxed ball.  It is
**one-sided**: nothing forces the body to lie *behind* the cut.  If the body lies in the positive
half-space of the hyperplane through the engine's centre, then `del ≡ 0` is legal
(`hdel0 : 0 ≤ 0`, `hcheck : 0² ≤ rho²σ`, `hle` untouched).  `runParts_of_posSide` (§2) is the
resulting producer: it eliminates `del` from the interface, so **no depth ledger is owed**.

That is the whole "depth obstruction" of the falsification bank: at round `0` the sliver body sits
at relative depth `‖Q₁‖/√cap = 2/√8 ≈ 0.707 ≈ 11·rmax` from the engine's centre — but only in the
radial direction, and only if one insists on cutting *behind* the body.  The two-sided form belongs
to the `runParts_of_relaxRun` / `runParts_of_dilated` producer route (whose `happr`/`hbody`/
`hdriftd` slots are drift bookkeeping), not to the residual object.  §5 machine-checks the
positive-side cut at `(G₁, t₁)` round `0` with the explicit data (`del = 0`, `rho = rmax = 1/16`,
normal `flatQ Q₁`), and §6 assembles the round-0 slots verbatim.

## 2.  The price of the β lane, exactly (§3–§4)

* `beta_floor_sliver`: at `(G₁, t₁)` the `dM = −1` body slot at round `0` (where `Cat 0 = 0`)
  forces `β ≥ n + δ/2 = 2 + 1/760000`.  The witness is the body point `X*` of trace `n + δ/2`
  (`X* = !![1+δ/4, −(1+3δ/4); ·, 1+δ/4]`, lower eigenvalue exactly `−δ/2`), and the `hdriftd` gate
  `tr q ≤ tr (Cat 0) = 0` caps the query centre's trace from above.
* `dilated_drift_cap`: `hdriftc` + `hdriftd` give `⟨cn k, Cat k − q_k⟩ ≤ m₀k/2` — the recorded
  (dilated) normal's pairing is bounded by **half the original margin**, never the dilated one.
  `λ` cannot buy drift slack, at any `λ`.
* `beta_price_chain`: the depth ledger must pay for the recorded margin `m₀ + λβ`, so it needs
  `√σ' ≥ 24 (m₀ + λβ) ≥ 24 λ (n + δ/2)` — i.e. `σ' ≥ (24·(n+δ/2))²` unconditionally.  The only free
  lever is inflating the oracle normal, which `dilated_drift_cap` then pairs against the engine's
  centre at half the *original* margin.  Combined with §1, the β lane is strictly harder than the
  direct route: the price is never worth paying.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.BetaM6

open QuantumMaxCutEnergy

/-! ## 1.  The one-sided reading: `del = 0` is legal -/

/-- **The one-sided `hcut` at zero margin.**  If the whole relaxed ball lies in the positive closed
half-space of the hyperplane through the engine's centre, the recorded margin `del = 0` discharges
`RunParts.hcut` verbatim. -/
theorem hcut_zero_of_posSide {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ M : ℝ}
    {c a : Fin (n * n) → ℝ}
    (h : ∀ z : Fin (n * n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall A u δ M → 0 ≤ c ⬝ᵥ (z - a)) :
    ∀ z : Fin (n * n) → ℝ, z ∈ QMCLeafB.Boundary.relaxBall A u δ M →
      -(((0 : ℚ) : ℝ)) ≤ c ⬝ᵥ (z - a) := by
  intro z hz
  simpa using h z hz

#print axioms QMCLeafB.BetaM6.hcut_zero_of_posSide

/-- **The one-sided depth slot at zero margin**: `0² ≤ rho²σ` is `0 ≤ rho²σ`, no ledger. -/
theorem check_zero_of_nonneg {rho σ : ℚ} (hσ : 0 ≤ σ) :
    ((0 : ℚ)) ^ 2 ≤ rho ^ 2 * σ := by
  have h0 : ((0 : ℚ)) ^ 2 = 0 := by norm_num
  rw [h0]
  exact mul_nonneg (sq_nonneg rho) hσ

#print axioms QMCLeafB.BetaM6.check_zero_of_nonneg

/-! ## 2.  The producer: `RunParts` from positive-side cuts, with `del ≡ 0`

`FinalStroke.RunParts`' eleven non-`del` slots with `del` eliminated: the interface owes
`0 ≤ sigmaQ (cd k).c (cd k).p` per cut round (automatic from `A p = c` on a positive-definite
shape) and the positive-side cut.  No margin stream, no depth ledger, no drift pair. -/

/-- **`RunParts` from positive-side cuts.** -/
def runParts_of_posSide (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n))
    (hcert : ∀ k, k < P.K * P.m → ok k = true →
      ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
        QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
          (QMCLeafB.wMatrix G * X).trace
            ≤ (t : ℝ) + ((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
    (hwit : ∀ k, k < P.K * P.m → ok k = false →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
            (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) cd k *ᵥ (cd k).p = (cd k).c)
    (hrho : ∀ k, k < P.K * P.m → ok k = false → 0 ≤ (cd k).rho)
    (hcne : ∀ k, k < P.K * P.m → ok k = false → (cd k).c ≠ 0)
    (hσ0 : ∀ k, k < P.K * P.m → ok k = false →
      0 ≤ QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < P.K * P.m → ok k = false → (cd k).rho ≤ P.rmax)
    (hcut : ∀ k, k < P.K * P.m → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (P.dq : ℝ)
          ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ) →
        0 ≤ QMCLeafB.EngineIterates.cutCR cd k
            ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
              (0 : Fin (G.n * G.n) → ℝ) cd k))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P where
  ok := ok
  cd := cd
  del := fun _ => 0
  hcert := hcert
  hwit := hwit
  hrho := hrho
  hcne := hcne
  hdel0 := fun _ _ _ => le_refl 0
  hcheck := fun k hk hok => check_zero_of_nonneg (hσ0 k hk hok)
  hle := hle
  hcut := fun k hk hok z hz => by
    simpa using hcut k hk hok z hz
  hverdict := hverdict

#print axioms QMCLeafB.BetaM6.runParts_of_posSide

/-! ## 3.  The β floor at the sliver: `dM = −1` needs `β ≥ n + δ/2 = 2 + 1/760000` -/

/-- The sliver input (two vertices, one edge of weight `1`, `Rq = 2`). -/
abbrev G1 : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- The sliver threshold. -/
abbrev t1 : ℚ := -(2 : ℚ) + 71 / 1520000

/-- The campaign parameter family at `G₁`. -/
abbrev P1 : QMCLeafB.FinalStroke.RunParams G1 := QMCLeafB.UnionShallow.paramsKbc2 G1

theorem eps1 : QMCLeafB.RundataCert.eps G1 = 1 / 20000 := QMCLeafB.EmptyBodyM5.eps_G₁

theorem dq1 : P1.dq = 1 / 380000 := QMCLeafB.EmptyBodyM5.dq₁_eq

theorem dq1' : QMCLeafB.RundataParams.dqShallow G1 = 1 / 380000 :=
  QMCLeafB.EmptyBodyM5.dqShallow_G₁

theorem rmax1 : P1.rmax = 1 / 16 := QMCLeafB.AnchorFactsM2.rmax₁

/-- **`−1`'s `frob` reading is the trace difference**: `⟪−1, X − q⟫ = tr q − tr X`. -/
theorem frob_neg_one {n : ℕ} (X q : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ))
        (X - q)
      = (∑ i, q i i) - (∑ i, X i i) := by
  have hval : ∀ i j : Fin n,
      QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ) i j
        = if i = j then (-1 : ℝ) else 0 := by
    intro i j
    rw [QMCLeafB.SepOracle.castMat_apply, Matrix.neg_apply, Matrix.one_apply]
    by_cases h : i = j <;> simp [h]
  have hrow : ∀ i, (∑ j, QMCLeafB.SepOracle.castMat
        (-1 : Matrix (Fin n) (Fin n) ℚ) i j * (X - q) i j) = -((X - q) i i) := by
    intro i
    have h1 : QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ) i i = -1 := by
      rw [hval i i, if_pos rfl]
    rw [Finset.sum_eq_single i]
    · rw [h1]; ring
    · intro j _ hj
      have h0 : QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin n) (Fin n) ℚ) i j = 0 := by
        rw [hval i j, if_neg (Ne.symm hj)]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [QMCLeafB.SepOracle.frob, hrow]
  rw [Finset.sum_neg_distrib]
  simp only [Matrix.sub_apply]
  rw [Finset.sum_sub_distrib]
  ring

#print axioms QMCLeafB.BetaM6.frob_neg_one

/-- The witness of the trace ceiling: diagonal `1 + δ/4`, off-diagonal `−(1 + 3δ/4)`, lower
eigenvalue exactly `−δ/2` (`δ = 1/380000`). -/
def Xstar : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + (1:ℝ)/380000/4, -((1:ℝ) + 3*(1:ℝ)/380000/4);
     -((1:ℝ) + 3*(1:ℝ)/380000/4), 1 + (1:ℝ)/380000/4]

theorem trace_Xstar : (∑ i, Xstar i i) = 2 + 1/760000 := by
  simp [Xstar, Fin.sum_univ_two]
  ring

/-- `X*` is a real member of the sliver body. -/
theorem Xstar_mem :
    QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G1)
      (((t1 : ℝ) - ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ))) ((P1.dq : ℚ) : ℝ) Xstar := by
  have heps : ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ) = 1 / 20000 := by rw [eps1]; norm_num
  have hdqS : ((QMCLeafB.RundataParams.dqShallow G1 : ℚ) : ℝ) = 1 / 380000 := by
    rw [dq1']; norm_num
  have hdqR : ((P1.dq : ℚ) : ℝ) = 1 / 380000 := by rw [dq1]; norm_num
  have ht : (t1 : ℝ) = -2 + 71 / 1520000 := by norm_num [t1]
  have hw : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G1) Xstar = Xstar 0 1 + Xstar 1 0 := by
    simp [QMCLeafB.BallFloor.frob, QMCLeafB.wMatrix, G1, Fin.sum_univ_two, Matrix.of_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rw [QMCLeafB.BallFloor.qfR_eq_sum]
    simp only [Xstar, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [hdqS, hdqR, sq_nonneg (x 0 - x 1), sq_nonneg (x 0 + x 1)]
  · intro i
    have hdi : Xstar i i = 1 + (1:ℝ)/380000/4 := by
      fin_cases i <;> norm_num [Xstar, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hdi, abs_le]
    constructor <;> nlinarith [hdqS, hdqR]
  · rw [hw]
    simp only [Xstar, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    nlinarith [hdqS, hdqR, heps, ht]

#print axioms QMCLeafB.BetaM6.Xstar_mem

/-- **THE β FLOOR AT THE SLIVER.**  Any `dM = −1` body margin at `(G₁, t₁)` at round `0` (engine
centre `Cat 0 = 0`) satisfies `β ≥ n + δ/2 = 2 + 1/760000`.  Compare
`Check_orient_m1.neg_one_dead` (the `β = 0` case, where this is already a contradiction). -/
theorem beta_floor_sliver {q : Matrix (Fin 2) (Fin 2) ℝ} {β : ℝ}
    (hbody : ∀ X : Matrix (Fin 2) (Fin 2) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G1)
        (((t1 : ℝ) - ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ))) ((P1.dq : ℚ) : ℝ) X →
      -β ≤ QMCLeafB.SepOracle.frob
        (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin 2) (Fin 2) ℚ)) (X - q))
    (hdriftd : QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (-1 : Matrix (Fin 2) (Fin 2) ℚ))
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) - q) ≤ 0) :
    2 + 1 / 760000 ≤ β := by
  have hq : (∑ i, q i i) ≤ 0 := by
    have h := hdriftd
    rw [frob_neg_one] at h
    simpa using h
  have hXs := hbody Xstar Xstar_mem
  rw [frob_neg_one] at hXs
  have htr := trace_Xstar
  linarith

#print axioms QMCLeafB.BetaM6.beta_floor_sliver

/-! ## 4.  `λ` cannot buy drift slack, and the ledger price of β -/

/-- **The dilation is drift-neutral.**  If the recorded normal is the dilated `cn = c + λ•d`, the
oracle normal's pairing with the centre mismatch is at most `m₀/2`, and the dilation direction's
pairing is at most `0`, then the recorded normal's pairing is at most `m₀/2` — for every `λ ≥ 0`.
A dilated cut never gains drift room: the ledger must pay `m₀ + λβ` against `√σ'`. -/
theorem dilated_drift_cap {N : ℕ} (c d cn : Fin N → ℝ) (a q : Fin N → ℝ) (m0 lam : ℝ)
    (hcn : cn = c + lam • d) (hlam : 0 ≤ lam)
    (hdriftc : c ⬝ᵥ (a - q) ≤ m0 / 2) (hdriftd : d ⬝ᵥ (a - q) ≤ 0) :
    cn ⬝ᵥ (a - q) ≤ m0 / 2 := by
  have h : (lam • d) ⬝ᵥ (a - q) ≤ 0 := by
    rw [smul_dotProduct, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hlam hdriftd
  rw [hcn, add_dotProduct]
  linarith

#print axioms QMCLeafB.BetaM6.dilated_drift_cap

/-- **The β price chain.**  With the depth ledger `(3m'/2)² ≤ rmax²σ'` at `rmax = 1/16`, the β
floor and `λ ≥ 1`, the recorded squared norm must reach `(24·(n+δ/2))²` no matter what the oracle
margin is — and `dilated_drift_cap` shows that same normal is paired against the engine's centre at
half the *original* margin. -/
theorem beta_price_chain {m0 lam β sig' : ℚ}
    (hlam : 1 ≤ lam) (hβ : 2 + 1/760000 ≤ β) (h0 : 0 < m0)
    (hledger : (3 * (m0 + lam * β) / 2) ^ 2 ≤ (1/16 : ℚ) ^ 2 * sig') :
    (24 * (2 + 1/760000)) ^ 2 ≤ sig' := by
  have hβ0 : (0:ℚ) < β := by linarith
  have hx : (2:ℚ) + 1/760000 ≤ m0 + lam * β := by
    have h1 : β ≤ lam * β := by nlinarith
    linarith
  have hx0 : (0:ℚ) < m0 + lam * β := by linarith
  have h2' : 576 * (m0 + lam * β) ^ 2 ≤ sig' := by nlinarith [hledger]
  have hy : (0:ℚ) ≤ 2 + 1/760000 := by norm_num
  have hmono : (2 + 1/760000) * (2 + 1/760000) ≤ (m0 + lam * β) * (m0 + lam * β) :=
    mul_le_mul hx hx hy (le_of_lt hx0)
  nlinarith [h2', hmono]

#print axioms QMCLeafB.BetaM6.beta_price_chain

/-! ## 5.  The sliver's round-0 cut is one-sided: `Q₁`'s flat puts the whole body in the positive
half-space through the engine's origin, so `del = 0` and the depth ledger is vacuous -/

/-- The sliver's un-pinched member (`Check_emptybody_m5.body_nonempty_G₁`), over `ℚ`. -/
abbrev Q1 : Matrix (Fin 2) (Fin 2) ℚ := QMCLeafB.EmptyBodyM5.Q₁

/-- The two `frob`s of the library have the same body (`∑ᵢ ∑ⱼ`), so they are interchangeable. -/
theorem frob_bridge {n : ℕ} (N M : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob N M = QMCLeafB.SepOracle.frob N M := rfl

#print axioms QMCLeafB.BetaM6.frob_bridge

/-- **The flat dot product is `frob` against the un-flattening.** -/
theorem flat_dot_unflat {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℚ) (z : Fin (n * n) → ℝ) :
    (fun i => ((QMCLeafB.RelaxOracle.flatQ Q i : ℚ) : ℝ)) ⬝ᵥ z
      = QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Q)
          (QMCLeafB.Boundary.unflat z) := by
  rw [frob_bridge, QMCLeafB.RelaxOracle.frob_eq_flat_dot,
    QMCLeafB.OrientM1.flat_castMat_cast, QMCLeafB.Boundary.flat_unflat]
  simp [dotProduct]

#print axioms QMCLeafB.BetaM6.flat_dot_unflat

/-- **`Q₁` is a supporting normal of the WHOLE sliver body, strictly positive.**  Every real point of
the body has `⟪Q₁, X⟫ ≥ (2 − δ/2) + (1+3δ/8)(2+3δ/4) > 2`.  So the body sits in the positive open
half-space of the hyperplane through the origin with this normal: the round-0 cut needs no margin
at all, and the "relative depth `≈ 0.707 ≈ 11·rmax`" arithmetic of the falsification bank is a
statement about the *radial* direction, not an obstruction. -/
theorem frob_Q1_pos {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.wMatrix G1)
      (((t1 : ℝ) - ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ))) ((P1.dq : ℚ) : ℝ) X) :
    0 < QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Q1) X := by
  have heps : ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ) = 1 / 20000 := by rw [eps1]; norm_num
  have hdqS : ((QMCLeafB.RundataParams.dqShallow G1 : ℚ) : ℝ) = 1 / 380000 := by
    rw [dq1']; norm_num
  have hdqR : ((P1.dq : ℚ) : ℝ) = 1 / 380000 := by rw [dq1]; norm_num
  have ht : (t1 : ℝ) = -2 + 71 / 1520000 := by norm_num [t1]
  obtain ⟨hpsd, hdiag, hobj⟩ := hX
  have hw : QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G1) X = X 0 1 + X 1 0 := by
    simp [QMCLeafB.BallFloor.frob, QMCLeafB.wMatrix, G1, Fin.sum_univ_two, Matrix.of_apply]
  have hobj' : X 0 1 + X 1 0 ≤ -(2:ℝ) - 3 / 1520000 := by
    rw [hw] at hobj
    nlinarith [hobj, hdqS, hdqR, heps, ht]
  have h00 : 1 - 1 / 1520000 ≤ X 0 0 := by
    have := (abs_le.mp (hdiag 0)).1
    nlinarith [this, hdqS, hdqR]
  have h11 : 1 - 1 / 1520000 ≤ X 1 1 := by
    have := (abs_le.mp (hdiag 1)).1
    nlinarith [this, hdqS, hdqR]
  have hfr : QMCLeafB.BallFloor.frob (QMCLeafB.SepOracle.castMat Q1) X
      = X 0 0 + X 1 1 - (1 + 3 / 3040000) * (X 0 1 + X 1 0) := by
    simp only [QMCLeafB.BallFloor.frob, QMCLeafB.SepOracle.castMat_apply,
      QMCLeafB.EmptyBodyM5.Q₁, Q1, Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
    ring
  rw [hfr]
  have hpos : (0:ℝ) < 1 + 3 / 3040000 := by norm_num
  have hmul := mul_le_mul_of_nonneg_left hobj' (le_of_lt hpos)
  nlinarith [hmul, h00, h11, hpos]

#print axioms QMCLeafB.BetaM6.frob_Q1_pos

/-- **THE ROUND-0 POSITIVE-SIDE CUT AT THE SLIVER**, in exactly `RunParts.hcut`'s shape at `k = 0`
(engine centre `Cat 0 = 0`): the whole relaxed ball is in the positive closed half-space of the
hyperplane with normal `flatQ Q₁`, so the recorded margin `0` is legal. -/
theorem sliver_round0_posSide :
    ∀ z : Fin (G1.n * G1.n) → ℝ,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G1)
        ((t1 : ℝ) - ((QMCLeafB.RundataCert.eps G1 : ℚ) : ℝ)) ((P1.dq : ℚ) : ℝ)
        ((2 * (G1.n : ℚ) ^ 2 + 2 * P1.dq ^ 2 : ℚ) : ℝ) →
      0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ Q1 i : ℚ) : ℝ)) ⬝ᵥ (z - 0) := by
  intro z hz
  rw [sub_zero, flat_dot_unflat]
  exact (frob_Q1_pos hz.1).le

#print axioms QMCLeafB.BetaM6.sliver_round0_posSide

/-! ## 6.  The round-0 record: the explicit `CutData`, its witness, and its arithmetic slots -/

/-- The initial shape's radius cap at the sliver (`2n² + 2dq²`). -/
def capQ : ℚ := 2 * (G1.n : ℚ) ^ 2 + 2 * P1.dq ^ 2

theorem capQ_pos : 0 < capQ := by
  have hdqR : ((P1.dq : ℚ) : ℝ) = 1 / 380000 := by rw [dq1]; norm_num
  have h2 : P1.dq = 1 / 380000 := dq1
  rw [capQ, h2]
  norm_num

/-- **The round-0 record at the sliver**: normal `flatQ Q₁`, witness `cap • flatQ Q₁`, ceiling depth
`rho = rmax = 1/16`.  Filled to exhibit the slots, not to claim they are forced. -/
def cd0 : QMCLeafB.EngineIterates.CutData (G1.n * G1.n) where
  c := QMCLeafB.RelaxOracle.flatQ Q1
  p := capQ • QMCLeafB.RelaxOracle.flatQ Q1
  rho := 1 / 16

theorem cd0_c_ne : cd0.c ≠ 0 := by
  intro h
  have h0 := congrFun h (finProdFinEquiv (0, 0))
  simp [cd0, QMCLeafB.RelaxOracle.flatQ, QMCLeafB.EmptyBodyM5.Q₁, Q1] at h0

#print axioms QMCLeafB.BetaM6.cd0_c_ne

/-- **`hwit` at round `0`**: the recorded witness inverts the initial shape. -/
theorem cd0_wit :
    QMCLeafB.EngineIterates.Aat (G1.n * G1.n)
        (QMCLeafB.Boundary.initShapeOf (G1.n * G1.n)
          (2 * (G1.n : ℚ) ^ 2 + 2 * P1.dq ^ 2)) (fun _ => cd0) 0 *ᵥ cd0.p = cd0.c := by
  have hcap : capQ ≠ 0 := ne_of_gt capQ_pos
  show QMCLeafB.Boundary.initShapeOf (G1.n * G1.n) capQ
      *ᵥ (capQ • QMCLeafB.RelaxOracle.flatQ Q1) = QMCLeafB.RelaxOracle.flatQ Q1
  rw [QMCLeafB.Boundary.initShapeOf, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul,
    inv_mul_cancel₀ hcap, one_smul]

#print axioms QMCLeafB.BetaM6.cd0_wit

/-- **`hcheck`'s positivity side at round `0`**: `σ = cap·‖flatQ Q₁‖² ≥ 0`. -/
theorem cd0_sigma_nonneg : 0 ≤ QMCLeafB.EngineIterates.sigmaQ cd0.c cd0.p := by
  have hcap : (0:ℚ) ≤ capQ := le_of_lt capQ_pos
  have hnn : (0:ℚ) ≤ ∑ i, cd0.c i * cd0.c i :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  show 0 ≤ QMCLeafB.EngineIterates.sigmaQ (QMCLeafB.RelaxOracle.flatQ Q1)
    (capQ • QMCLeafB.RelaxOracle.flatQ Q1)
  simp only [QMCLeafB.EngineIterates.sigmaQ, dotProduct_smul, smul_eq_mul]
  exact mul_nonneg hcap hnn

#print axioms QMCLeafB.BetaM6.cd0_sigma_nonneg

/-! ## 7.  Uniform round-0 positive-side cut: at EVERY point of the stratum the trace normal with
`del = 0` discharges `hcut` at round `0` -/

theorem frob_one (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob (1 : Matrix (Fin n) (Fin n) ℝ) X = ∑ i, X i i := by
  have hrow : ∀ i, (∑ j, (1 : Matrix (Fin n) (Fin n) ℝ) i j * X i j) = X i i := by
    intro i
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have h0 : (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
        rw [Matrix.one_apply, if_neg (Ne.symm hj)]
      rw [h0, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  simp only [QMCLeafB.BallFloor.frob, hrow]

#print axioms QMCLeafB.BetaM6.frob_one

theorem castMat_one (n : ℕ) :
    QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ)
      = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  rw [QMCLeafB.SepOracle.castMat_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

#print axioms QMCLeafB.BetaM6.castMat_one

/-- **The round-0 cut is never an obstruction on the stratum.**  At *any* point whose relaxed body
is nonempty (over `ℝ`, `1 ≤ n`, `δ < 4`), the trace normal `flatQ 1` puts the whole relaxed ball in
the positive half-space through the engine's origin: every body point has trace at least
`n(1 − δ/4) > 0`.  So `del = 0` discharges `RunParts.hcut` at round `0`, and no depth ledger is
read.  What remains of the stratum is the *dynamics* (`k ≥ 1`, keeping the engine's centre out of
the body), not round `0` and not the ledger. -/
theorem round0_posSide_uniform {n : ℕ} (hn : 1 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} {u δ M : ℝ}
    (hδ : δ < 4) :
    ∀ z : Fin (n * n) → ℝ, z ∈ QMCLeafB.Boundary.relaxBall A u δ M →
      0 ≤ (fun i => ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ))
            ⬝ᵥ (z - 0) := by
  intro z hz
  have htr := QMCLeafB.OrientM1.trace_lower_of_body hz.1
  have hpos := QMCLeafB.OrientM1.trace_floor_pos hn hδ
  rw [sub_zero, flat_dot_unflat, castMat_one, frob_one]
  linarith

#print axioms QMCLeafB.BetaM6.round0_posSide_uniform

end QMCLeafB.BetaM6



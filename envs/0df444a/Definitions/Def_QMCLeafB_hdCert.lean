-- Prove2me | Definitions.Def_QMCLeafB_hdCert
-- name    : QMCLeafB_hdCert
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T23:26:57.437244+00:00
-- url     : https://prove2.me/theorems/34972c28-aedf-40c8-a0c1-1260bafdedfd
-- title:
--   QMCLeafB hdCert — the RunData content fields from relax-oracle rounds
-- statement:
--   The relax-oracle route to the RunData content fields of the QMC ellipsoid SDP engine: `dqShallow` (the forced oracle tolerance $\varepsilon/(9c_A+1)$), its rounding budget, `hcert` from `RelaxMem` (the ok-branch witness), `hcut` from `RelaxCut` via centre-approximation with recorded margin $\mathrm{del}=3\cdot\mathrm{margin}/2$, and `rundata_of_relaxRun` assembling a full RunData. Replaces the deprecated `QMCLeafB_brick_hd_cert_m5` (stale import of the merged shim; identical content with `Check_relax_oracle_m4` rooted at `QMCLeafB_Core`).

import Mathlib
import Definitions.Def_QMCLeafB_brick_rundata_arith_m5
import Definitions.Def_QMCLeafB_relax_oracle_m4
import Definitions.Def_QMCLeafB_finalization
/-
# leaf B phase 13 — brick `hd-cert` (swarm `smw17fqzz`, member m5, direction d8)

`rundata-arith` (my first brick) reduced `hd : ∀ G t, … → RunData o G t` to a run
(`ok cd del`) plus its analytic facts, with every *scalar* slot discharged at explicit constants —
but it left two free parameters of the arithmetic: the oracle tolerance `dq` and the ledger
constant `cAq`.  This brick closes them and both *content* fields:

* §1 the slacks: `eps G = Rq G / 40000` (the leaf's own `εw = εr`) and
  **`dq G = eps G / (9 · cAq G + 1)`**.  `cAq G = n²·Rq G` is my first brick's ledger constant.
* §2 `∑ᵢⱼ |wMatrixQ G i j| = Rq G` (the exact rational ledger is the total weight; `wMatrixQ` is
  `Check_finalization`'s rational weight matrix, whose cast is `wMatrix G`).
* §3 `roundCost (wMatrixQ G) ν ≤ 6ν · cAq G` for `0 ≤ ν ≤ 1` (the diagonal of the weight matrix
  vanishes, so the rounding cost is the coefficient times `∑ᵢⱼ|Aᵢⱼ|` alone).
* §4 **the ok-branch budget, proved**: at `ν = 3·dq/4` the rounding cost plus the shift fits in the
  leaf's slack — `roundCost A (3·dq/4) + dq/2 - εr ≤ εw` at `εw = εr = eps G`.  This is the
  side condition of the shelf's `RelaxOracle.hcert_of_relaxMem`, and it is why `dq` may not be
  chosen freely: `dq` has to be tied to `eps` and to `cAq`.
* §5 `hcert_of_relaxMem` — `RunData.hcert` (the feasible-round witness at `t + εw`) from one
  `RelaxMem` at the round's centre, at the campaign's rational weight matrix.
* §6 `hcut_of_relaxCuts` — `RunData.hcut` (the separation contract of the cut rounds) from one
  `RelaxCut` per cut round, at `wMatrix G`, in the loop's flat `cutCR`/`Cat` shape.
* §7 `rundata_of_relaxRun` — **the whole `RunData`**: the relax-oracle's two verdicts per round
  (`RelaxMem` / `RelaxCut`) plus the three stream identifications and the ledger facts supply it.
  No scalar, no tolerance, no ledger constant and no rounding budget is left to the caller.
* §8 axiom audit.

## Build note (important)

This file imports `Solutions.Check_relax_oracle_merged_m5`, **not** `Check_relax_oracle_m4`:
`MergeAll3_m8` and `Check_CastBridge` both declare `QMCLeafB.CastBridge.castM`, and the closing
chain (`Check_brick_verdict_sound` … → `Check_ThresholdDriver` → `MergeAll3_m8`) cannot avoid the
merged module, so `Check_relax_oracle_m4` and `RunData` cannot be imported together.  The `_merged_`
copy is `Check_relax_oracle_m4` verbatim with `import Solutions.Check_CastBridge` replaced by
`import Solutions.MergeAll3_m8`; it compiles clean and its audits are the usual three.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; no edits to existing files.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false

namespace QMCLeafB.RundataCert

open QuantumMaxCutEnergy

/-! ## 1.  The two slacks and the oracle tolerance -/

/-- The leaf's own additive slack `Rq G / 40000`; both `εw` and `εr` of `RunData` are this. -/
noncomputable def eps (G : Input) : ℚ := QMCLeafB.EngineRuntime.Rq G / 40000

/-- The ledger constant of my first brick: `n² · Rq G`. -/
noncomputable def cAq (G : Input) : ℚ := QMCLeafB.RundataArith.cAqOf G

/-- **The oracle tolerance.**  Not free: §4 shows that the ok-branch rounding budget holds exactly
at this value, and no value much larger can work. -/
noncomputable def dq (G : Input) : ℚ := eps G / (9 * cAq G + 1)

theorem eps_nonneg (G : Input) : 0 ≤ eps G := by
  unfold eps
  have h := QMCLeafB.RundataArith.Rq_nonneg G
  linarith

theorem eps_pos (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) : 0 < eps G := by
  unfold eps; linarith

theorem cAq_nonneg (G : Input) : 0 ≤ cAq G := QMCLeafB.RundataArith.cAqOf_nonneg G

/-- `Rq ≤ cAq` as soon as the order is positive: `cAq = n²·Rq` and `n² ≥ 1`. -/
theorem Rq_le_cAq (G : Input) (hn : 1 ≤ G.n) : QMCLeafB.EngineRuntime.Rq G ≤ cAq G := by
  unfold cAq QMCLeafB.RundataArith.cAqOf
  have h1 : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by
    have := Nat.mul_le_mul hn hn
    exact_mod_cast this
  have h2 := QMCLeafB.RundataArith.Rq_nonneg G
  calc QMCLeafB.EngineRuntime.Rq G = 1 * QMCLeafB.EngineRuntime.Rq G := by ring
    _ ≤ ((G.n * G.n : ℕ) : ℚ) * QMCLeafB.EngineRuntime.Rq G :=
        mul_le_mul_of_nonneg_right h1 h2

/-- The `cAqOf` form used by `rundata_of_run`'s `hAsum` slot is a `n*n` cast, not a product. -/
theorem cAq_eq (G : Input) : cAq G = ((G.n * G.n : ℕ) : ℚ) * QMCLeafB.EngineRuntime.Rq G := rfl

theorem Rq_le_cAq' (G : Input) (hn : 1 ≤ G.n) : QMCLeafB.EngineRuntime.Rq G ≤ cAq G := Rq_le_cAq G hn

theorem dq_pos (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) : 0 < dq G := by
  unfold dq
  have h1 : 0 < eps G := eps_pos G hRq
  have h2 : 0 ≤ cAq G := cAq_nonneg G
  positivity

/-! ## 2.  The rational ledger is the total weight -/

/-- `∑ᵢⱼ |wMatrixQ G i j| = Rq G` over `ℚ`: every entry is a weight, all weights are nonnegative,
and the matrix has each edge exactly twice. -/
theorem sum_abs_wMatrixQ (G : Input) :
    ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j| = QMCLeafB.EngineRuntime.Rq G := by
  have hnonneg : ∀ i j : Fin G.n, (0 : ℚ) ≤ QMCLeafB.Finalization.wMatrixQ G i j :=
    QMCLeafB.Finalization.IsQMCWeight.nonneg (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G)
  have h1 : ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|
      = ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    exact abs_of_nonneg (hnonneg i j)
  have h2 : ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j = QMCLeafB.EngineRuntime.Rq G :=
    QMCLeafB.Finalization.Vq_wMatrixQ G
  rw [h1, h2]

theorem sum_abs_wMatrixQ_le (G : Input) (hn : 1 ≤ G.n) :
    ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j| ≤ cAq G := by
  rw [sum_abs_wMatrixQ]
  exact Rq_le_cAq G hn

/-! ## 3.  The rounding cost at the weight matrix -/

/-- The weight matrix has zero diagonal, so `roundCost` is the coefficient times `∑ᵢⱼ|Aᵢⱼ|`. -/
theorem roundCost_wMatrixQ (G : Input) (ν : ℚ) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) ν
      = (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|) := by
  unfold QMCLeafB.RoundingOut.roundCost
  have hdiag : (∑ i, |QMCLeafB.Finalization.wMatrixQ G i i|) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [QMCLeafB.Finalization.wMatrixQ_apply_of_eq, abs_zero]
  rw [hdiag, mul_zero, add_zero]

/-- **The rounding cost is at most `6ν·cAq`** for a shallow depth `ν ≤ 1`. -/
theorem roundCost_wMatrixQ_le (G : Input) (hn : 1 ≤ G.n) {ν : ℚ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) ν ≤ 6 * ν * cAq G := by
  rw [roundCost_wMatrixQ]
  have hcoef : (1 + ν) * (2 * ν + ν ^ 2) ≤ 6 * ν := by
    nlinarith [hν0, hν1, mul_nonneg hν0 (sub_nonneg.mpr hν1),
      mul_nonneg (sq_nonneg ν) (sub_nonneg.mpr hν1)]
  have hSnn : (0 : ℚ) ≤ ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hSR : ∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j| ≤ cAq G :=
    sum_abs_wMatrixQ_le G hn
  calc (1 + ν) * (2 * ν + ν ^ 2) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|)
      ≤ (6 * ν) * (∑ i, ∑ j, |QMCLeafB.Finalization.wMatrixQ G i j|) :=
        mul_le_mul_of_nonneg_right hcoef hSnn
    _ ≤ (6 * ν) * cAq G := by
        refine mul_le_mul_of_nonneg_left hSR ?_
        nlinarith [hν0]

/-! ## 4.  The ok-branch budget, at the chosen tolerance

`RelaxOracle.hcert_of_relaxMem` asks for `roundCost A (3δ/4) + δ/2 - εr ≤ εw`.  At
`δ = dq G`, `εw = εr = eps G` that is a theorem: `dq` is defined as `eps/(9·cAq + 1)`, so

    roundCost ≤ 6·(3dq/4)·cAq = (9/2)·dq·cAq ≤ eps/2,   dq/2 ≤ eps/2.

The estimate is deliberately crude; what matters is that the tolerance is *explicit* and positive. -/

theorem dq_budget (G : Input) (hn : 1 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * dq G / 4)
        + dq G / 2 - eps G ≤ eps G := by
  set S := cAq G with hS
  set e := eps G with he
  have hS0 : 0 ≤ S := cAq_nonneg G
  have he0 : 0 < e := eps_pos G hRq
  have heS : e ≤ S := by
    have h := Rq_le_cAq G hn
    rw [he, hS]
    unfold eps
    have h2 := QMCLeafB.RundataArith.Rq_nonneg G
    rw [div_le_iff₀ (by norm_num : (0:ℚ) < 40000)]
    nlinarith
  have hden : (0 : ℚ) < 9 * S + 1 := by linarith
  have hdvd : dq G = e / (9 * S + 1) := rfl
  have hdpos : 0 < dq G := dq_pos G hRq
  have hle1 : e / (9 * S + 1) ≤ 1 := by
    rw [div_le_iff₀ hden]
    nlinarith [he0.le, hS0]
  have hd1 : 3 * dq G / 4 ≤ 1 := by
    rw [hdvd]
    nlinarith
  have hcost := roundCost_wMatrixQ_le G hn (ν := 3 * dq G / 4) (by positivity) hd1
  have hhalf : dq G / 2 ≤ e / 2 := by
    rw [hdvd]
    have h1 : e / (9 * S + 1) ≤ e := by
      rw [div_le_iff₀ hden]
      nlinarith [he0.le, hS0]
    linarith
  have hkey : 6 * (3 * dq G / 4) * cAq G ≤ e / 2 := by
    rw [hdvd, hS]
    have hstep : 6 * (3 * (e / (9 * S + 1)) / 4) * S = 9 * e * S / (2 * (9 * S + 1)) := by
      field_simp
      ring
    rw [hstep, div_le_iff₀ (by positivity : (0:ℚ) < 2 * (9 * S + 1))]
    nlinarith [he0.le]
  linarith

/-! ## 5.  `RunData.hcert`: the feasible round's witness -/

/-- **The ok round's witness at the campaign's weight matrix.**  One `RelaxMem` at the round's
centre, at the tolerance `dq G`, gives the unit-diagonal real point with
`tr (wMatrix G · X) ≤ t + eps G` that `RunData.hcert` asks for. -/
theorem hcert_of_relaxMem (G : Input) (t : ℚ) (cX : Matrix (Fin G.n) (Fin G.n) ℚ)
    (hn : 1 ≤ G.n) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX (t - eps G) (dq G))
    (hCsym : cXᵀ = cX) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace ≤ (t : ℝ) + ((eps G : ℚ) : ℝ) := by
  obtain ⟨X, hX, htr⟩ :=
    QMCLeafB.RelaxOracle.hcert_of_relaxMem (A := QMCLeafB.Finalization.wMatrixQ G) (cX := cX)
      (t := t) (εr := eps G) (δ := dq G) (εw := eps G) h
      (QMCLeafB.Finalization.IsQMCWeight.symm (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G))
      hCsym (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq)
      (dq_budget G hn hRq)
  refine ⟨X, hX, ?_⟩
  rw [← QMCLeafB.Finalization.wMatrix_castM G]
  exact htr

/-! ## 6.  `RunData.hcut`: the cut rounds' separation contract -/

/-- **The cut round's separation contract at `wMatrix G`.**  A `RelaxCut` per cut round, plus the
identifications that tie the recorded stream `cd` (its normal `c`, its centre `Cat`) to the
oracle's data, gives `RunData.hcut` verbatim.  The `M` of the ball is arbitrary. -/
theorem hcut_of_relaxCuts (G : Input) (t : ℚ) {M : ℝ} (T : ℕ) (ok : ℕ → Bool)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (mg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k) (t - eps G) (dq G))
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), mg k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - ((eps G : ℚ) : ℝ)) ((dq G : ℚ) : ℝ) M →
        -(((mg k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk hok z hz
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat
      (QMCLeafB.Finalization.wMatrixQ G)) ((t : ℝ) - ((eps G : ℚ) : ℝ)) ((dq G : ℚ) : ℝ) M := by
    rwa [← QMCLeafB.Finalization.wMatrix_castM G] at hz
  exact QMCLeafB.RelaxOracle.hcutδ_of_relaxCuts (A := QMCLeafB.Finalization.wMatrixQ G)
    (t := t) (εr := eps G) (δq := dq G) (M := M) ok T cX C cd mg hnorm hmg hctr k hk hok z hz'

/-! ## 7.  The whole `RunData` from the relax-oracle's per-round verdicts -/

/-- **`RunData` from a run of the relaxed oracle.**  The caller supplies, per round, the oracle's
verdict at the round's centre (`RelaxMem` on the `ok` rounds, `RelaxCut` on the cut rounds), the
three identifications between the recorded stream and the oracle's data, the ledger facts `hwit`,
`ρ ≥ 0`, `c ≠ 0`, `δ ≥ 0`, `δ² ≤ ρ²σ`, the shallow-regime ceiling `ρ ≤ rmax`, and the verdict
equation.  Everything else — the tolerance `dq G`, the ledger constant `cAq G`, the rounding budget,
the budget inequality `hbudget` and the witness/separation content of the two branches — is proved
here. -/
noncomputable def rundata_of_relaxRun
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (rmax : ℚ) (hrmax : 0 ≤ rmax) (m : ℕ) (hm1 : 1 ≤ m)
    (hhalve : (Real.sqrt (QMCLeafB.EngineIterates.rho0R (G.n * G.n) (rmax : ℝ)))⁻¹ ^ m ≤ 1 / 2)
    (k0 : ℕ)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k) (t - eps G) (dq G))
    (hmem : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k) (t - eps G) (dq G))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), del k = (C k hok).margin)
    (hctr : ∀ k, QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
    (hwit : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      QMCLeafB.EngineIterates.Aat (G.n * G.n)
          (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (QMCLeafB.RundataArith.capOf G (dq G))) cd k *ᵥ
        (cd k).p = (cd k).c)
    (hrho : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      0 ≤ (cd k).rho)
    (hcne : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      (cd k).c ≠ 0)
    (hdel0 : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      0 ≤ del k)
    (hcheck : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      (del k) ^ 2 ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hle : ∀ k, k < QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m → ok k = false →
      (cd k).rho ≤ rmax)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m)) :
    QMCLeafB.VerdictSound.RunData o G t := by
  refine QMCLeafB.RundataArith.rundata_of_run o G t (dq G) (dq_pos G hRq) (cAq G) (cAq_nonneg G)
    (QMCLeafB.RundataArith.sum_abs_wMatrix_le G) rmax hrmax m hm1 hhalve k0 ok cd del ?_ hwit hrho
    hcne hdel0 hcheck ?_ hle hverdict
  · -- `hcert`, from the ok rounds' `RelaxMem`
    intro k hk hok
    exact hcert_of_relaxMem G t (cX k) (by omega) hRq (hmem k hk hok) (hCsym k)
  · -- `hcut`, from the cut rounds' `RelaxCut`
    intro k hk hok
    exact hcut_of_relaxCuts G t (M := ((QMCLeafB.RundataArith.capOf G (dq G) : ℚ) : ℝ))
      (QMCLeafB.RundataArith.runK G (dq G) (cAq G) m k0 * m) ok cd del cX C hnorm hmg hctr k hk hok

/-! ## 8.  The `rmax = 0` obstruction (a warning for the run's assembly)

The shelf's halving inequality is proved at `rmax = 0` (`runData_hhalve_close`), and the natural
choice for a run's contraction ceiling is therefore `rmax = 0`.  That choice is **not** compatible
with a genuine cut round: `hle` gives `ρ ≤ 0` and `hrho` gives `0 ≤ ρ`, so `ρ = 0`, and then
`hcheck` (`δ² ≤ ρ²σ`) gives `δ = 0`.  A zero margin cannot separate a relaxation of positive
thickness — the ball of radius `δq/(8(c_A+1))` around a feasible point must stay on the correct side.
The two lemmas below are the machine-checked first half of that statement. -/

theorem del_eq_zero_of_rmax_zero {o : Input → ℚ → Bool} {G : Input} {t : ℚ}
    (d : QMCLeafB.VerdictSound.RunData o G t) (hrmax : d.rmax = 0)
    {k : ℕ} (hk : k < d.K * d.m) (hok : d.ok k = false) : d.del k = 0 := by
  have hle := d.hle k hk hok
  rw [hrmax] at hle
  have hρ := d.hrho k hk hok
  have hρ0 : (d.cd k).rho = 0 := le_antisymm hle hρ
  have hsq : (d.del k) ^ 2 ≤ 0 := by
    have hchk := d.hcheck k hk hok
    rw [hρ0] at hchk
    simpa using hchk
  have := sq_nonneg (d.del k)
  have : (d.del k) ^ 2 = 0 := le_antisymm hsq this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- With `rmax = 0` a cut round's `hcut` degenerates to a **margin-free** halfspace:
`0 ≤ c ⬝ (z - centre)` for every `z` of the ball.  `RelaxOracle.RelaxCut` supplies only margins
`> 0`, so a run at `rmax = 0` must have no cut round with a nonempty ball. -/
theorem hcut_zero_of_rmax_zero {o : Input → ℚ → Bool} {G : Input} {t : ℚ}
    (d : QMCLeafB.VerdictSound.RunData o G t) (hrmax : d.rmax = 0) {k : ℕ}
    (hk : k < d.K * d.m) (hok : d.ok k = false) {z : Fin (G.n * G.n) → ℝ}
    (hz : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
      ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ)) (d.dq : ℝ)
      ((2 * (G.n : ℚ) ^ 2 + 2 * d.dq ^ 2 : ℚ) : ℝ)) :
    0 ≤ QMCLeafB.EngineIterates.cutCR d.cd k
          ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) d.cd k) := by
  have h := d.hcut k hk hok z hz
  rw [del_eq_zero_of_rmax_zero d hrmax hk hok] at h
  simpa using h

/-! ## 8b.  An approximate centre

`hcut_of_relaxCuts` needs the engine's centre `Cat` to be the cast of the *rational* matrix at which
the oracle was queried.  `Cat` moves by `(γ/√σ) • p` every round, which is irrational in general, so
a design that queries the oracle at a rational approximation must pay for the mismatch.  This lemma
is the exact bookkeeping: if the query centre is within `margin/2` of the engine's centre in the
cut's own normal direction, then recording the *halved-then-some* margin `3·margin/2` still gives
`RunData.hcut`. -/

theorem hcut_of_approx (G : Input) (t : ℚ) {M : ℝ} (T : ℕ) (ok : ℕ → Bool)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (mg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k) (t - eps G) (dq G))
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmg : ∀ k (hok : ok k = false), mg k = 3 * (C k hok).margin / 2)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR cd k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - ((eps G : ℚ) : ℝ)) ((dq G : ℚ) : ℝ) M →
        -(((mg k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k hk hok z hz
  have hcf : QMCLeafB.EngineIterates.cutCR cd k
      = fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ) := by
    funext i
    simp [QMCLeafB.EngineIterates.cutCR, hnorm k hok]
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat
      (QMCLeafB.Finalization.wMatrixQ G)) (((t - eps G : ℚ)) : ℝ) ((dq G : ℚ) : ℝ) M := by
    rw [show (((t - eps G : ℚ)) : ℝ) = (t : ℝ) - ((eps G : ℚ) : ℝ) by push_cast; ring]
    rwa [← QMCLeafB.Finalization.wMatrix_castM G] at hz
  have hsep := (C k hok).separates_ball M z hz'
  have happr' := happr k hok
  rw [hcf] at happr'
  rw [hcf]
  have hsplit : z - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
      = (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
          - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) := by
    abel
  rw [hsplit, dotProduct_add]
  have h2 : -((((C k hok).margin : ℚ) : ℝ)) / 2
      ≤ (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ))
          ⬝ᵥ (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
            - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k) := by
    have hneg : (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ))
        ⬝ᵥ (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
          - QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k)
        = - ((fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ))
            ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
              - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))) := by
      rw [← dotProduct_neg]
      congr 1
      abel
    rw [hneg]
    linarith
  have hmg' : -(((mg k : ℚ)) : ℝ) = -(3 * (((C k hok).margin : ℚ) : ℝ) / 2) := by
    rw [hmg k hok]
    push_cast
    ring
  rw [hmg']
  have hsep' : -(((C k hok).margin : ℚ) : ℝ)
      ≤ (fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ))
        ⬝ᵥ (z - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := hsep
  linarith

#print axioms QMCLeafB.RundataCert.hcut_of_approx

/-! ## 9.  Axiom audit -/

#print axioms QMCLeafB.RundataCert.eps_nonneg
#print axioms QMCLeafB.RundataCert.eps_pos
#print axioms QMCLeafB.RundataCert.cAq_nonneg
#print axioms QMCLeafB.RundataCert.Rq_le_cAq
#print axioms QMCLeafB.RundataCert.dq_pos
#print axioms QMCLeafB.RundataCert.sum_abs_wMatrixQ
#print axioms QMCLeafB.RundataCert.roundCost_wMatrixQ
#print axioms QMCLeafB.RundataCert.roundCost_wMatrixQ_le
#print axioms QMCLeafB.RundataCert.dq_budget
#print axioms QMCLeafB.RundataCert.hcert_of_relaxMem
#print axioms QMCLeafB.RundataCert.hcut_of_relaxCuts
#print axioms QMCLeafB.RundataCert.rundata_of_relaxRun
#print axioms QMCLeafB.RundataCert.del_eq_zero_of_rmax_zero
#print axioms QMCLeafB.RundataCert.hcut_zero_of_rmax_zero

end QMCLeafB.RundataCert



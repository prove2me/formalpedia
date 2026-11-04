-- Prove2me | Definitions.Def_QMCLeafB_runparts_m5
-- name    : QMCLeafB_runparts_m5
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:14:28.729017+00:00
-- url     : https://prove2.me/theorems/4a44c390-ca7e-4fb8-8518-21c00de52ad6
-- title:
--   QMCLeafB runparts_m5
-- statement:
--   # leaf B phase 14 — brick `runparts` (swarm `smw1a99tp`, member m5, direction d1)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_hdCert
/-
# leaf B phase 14 — brick `runparts` (swarm `smw1a99tp`, member m5, direction d1)

`QMCLeafB.FinalStroke.RunParts o G t P` is the *run half* of `RunData` (m7's split of the 21
fields): the ok bits, the recorded cut stream `cd`, the recorded margins `del`, and twelve fields.
The leaf's remaining content item is to inhabit it for every bracketed `(G, t)` at the shallow
numeric parameters `P = QMCLeafB.RundataParams.runParamsShallow G hn`.

This brick does that **modulo the oracle's per-round verdicts**, and it pins exactly which residual
each side of the split carries.

## What is discharged here (nothing of the following is assumed)

* §2 `σ > 0` at every cut round — `σ = c ⬝ p` is the engine's exact squared cut norm; the engine's
  iterates stay `PosQ` (`Aat_posQ` from `hwit` + `ρ ≥ 0` + `c ≠ 0`), and a nonzero normal's witness
  is nonzero, so `σ = qf (Aat k) p > 0` (`sigmaQ_eq_qf`, `sigmaQ_pos_of_wit`).
* §3 `hcert` — the ok round's primal witness at `t + εw`.  `RelaxOracle.hcert_of_relaxMem`
  (`Check_brick_hd_cert_m5`'s `hcert_of_relaxMem`) with the tolerance kept general (`δ = P.dq`) and
  the ok-branch rounding budget as its only side condition; at `P = runParamsShallow` that budget is
  m5's `dqShallow_budget` (`QMCLeafB.RundataParams.dqShallow_budget`), discharged in §6.
* §4 `hcut` — the cut rounds' separation contract.  The engine's centre `Cat …` moves by
  `(γ/√σ) • p`, which is irrational, so the oracle can only ever be queried at a rational surrogate
  `cX k`.  If the query error in the cut's *own* normal direction is at most half the oracle's
  margin `m`, then recording the *tripled-and-halved* margin `3m/2` separates the relaxation about
  the engine's centre (`hcut_of_approx_gen`; m5's `RundataCert.hcut_of_approx` with the tolerance
  and the recorded margin generalised).
* §5 the assembly: `ok`, `cd`, `del` (`del k = 3·marg k/2`) and all twelve fields.

## The one numeric residual, in its sharp form

`RunData.hcheck` is `del² ≤ ρ²σ` and `hle` is `ρ ≤ rmax`.  Combined with `hcut` — which at the
engine's own centre is only derivable from an *approximate* query centre, at margin `3m/2` — the run
needs

    (3·m_k/2)² ≤ ρ_k² · σ_k   and   ρ_k ≤ rmax,   i.e.   (3/2)·m_k / √σ_k ≤ rmax = 1/(4·N).

`hcheck` is a *lower* bound on the recorded margin (a larger recorded halfspace contains more), so
the oracle's margin cannot be shrunk away: `del` must be at least `m_k + θ_k`, where
`θ_k = cutCR ⬝ (Cat k − q_k) ≤ m_k/2` is the centre mismatch.  The bound is therefore a genuine
condition on the oracle's *output* — the shallow-cut regime — and §1 converts its usual real form
(a dyadic enclosure of `√σ`, so that no irrational enters the recorded state) into the rational
squared form `hcheck` speaks (`sq_le_of_sqrt_le`), the exact converse of the shelf's
`EngineIterates.margin_le_of_sq_check`.

## Final theorem and its residual hypothesis list

`QMCLeafB.RunPartsShallow.runParts_shallow_bracket` (§9): for every `G` with `2 ≤ G.n` and every `t`
in the leaf's bracket `-Rq G ≤ t < -Rq G/40000`,

    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.RundataParams.runParamsShallow G hn)

for **arbitrary** `o : Input → ℚ → Bool`, with the recorded run *constructed* end to end
(`shallowCut`: the engine's own iterate stream at the oracle's normals and the ceiling depth
`rmax`, §7).  `RunParts` has twelve fields; the caller owes eight hypotheses, all of them on the
oracle/program side and none of them arithmetic:

1. `C` — the cut verdict `RelaxCut (wMatrixQ G) (cX k) (t − eps) (dqShallow G)` at the rational query
   centre `cX k`, for every round with `ok k = false`;
2. `hmem` — the `ok` verdict `RelaxMem` at the same centre, for every `ok k = true` with `k < K·m`;
3. `hCsym` — the query centres are symmetric;
4. `hnorm` — the recorded normal is the oracle's: `c k = flatQ (C k hok).normal` on cut rounds
   (`c` may be any nonzero stream that takes these values; on `ok` rounds the run's cut data is
   irrelevant, so fill it with anything nonzero);
5. `hc` — that normal stream is nonzero;
6. `happr` — the centre approximation:
   `cutCR ⬝ (Cat k − flat (castMat (cX k))) ≤ margin/2`;
7. `hdepthR` — the shallow-depth ledger in its real form
   `(3·marg k/2) ≤ rmax·√σ_k` (`§1` converts it to the rational squared form `RunData.hcheck`);
8. `hverdict` — the loop's verdict bit is the run's `anyOk` over `K·m` rounds.

**Why (8) cannot be dropped.**  `RunParts.hcert` *is* the ok-branch feasibility statement: on a round
with `ok k = true` it produces a unit-diagonal semidefinite point at `t + εw`.  So no producer of
`RunParts o G t P` can exist for an arbitrary `o`; the ok bits must be tied to the program's own run,
and `hverdict` is the minimal such tie.  The eight items above are therefore the *sharp* interface
between this brick and the round program, not an artefact of the proof.

§10 supplies one machine-checked enabler for item 7 (`RelaxCut.dilate`): `RelaxCut` is an existential
over `(normal, margin)`, so a cut may be re-presented on a diluted normal `c + λ·d` with margin
`m + λβ`, where `β` bounds the body's extent in the direction `d`.  The margin grows only linearly in
`λ` while `σ` grows quadratically, so the normalised depth can be pushed down to `β/√(dᵀA⁻¹d)`; the
relaxed body is *thin* in the diagonal-ones direction (`|Xᵢᵢ − 1| ≤ δ/4`), which is what makes that
limit small.  Item 7 is thus an instruction to the oracle design, not a hope about its output.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
no edits to existing files.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace QMCLeafB.RunPartsShallow

open QuantumMaxCutEnergy

/-! ## 1.  The depth ledger, in the rational squared form `hcheck` speaks -/

/-- **The normalised shallow-depth bound, real form → rational squared form.**  The algorithmic side
naturally proves `(3m/2) ≤ ρ·√σ` (through a dyadic enclosure of `√σ`, so that no irrational enters
the recorded state); `hcheck` wants the exact rational comparison `(3m/2)² ≤ ρ²σ`.  This is the
converse of the shelf's `EngineIterates.margin_le_of_sq_check`. -/
theorem sq_le_of_sqrt_le {δ ρ σ : ℚ} (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : (δ : ℝ) ≤ (ρ : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) : δ ^ 2 ≤ ρ ^ 2 * σ := by
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hσR : (0 : ℝ) ≤ ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  have hsq : (δ : ℝ) ^ 2 ≤ ((ρ : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 := by
    nlinarith [h, hδR, Real.sqrt_nonneg ((σ : ℚ) : ℝ)]
  have hrhs : ((ρ : ℝ) * Real.sqrt ((σ : ℚ) : ℝ)) ^ 2 = (ρ : ℝ) ^ 2 * ((σ : ℚ) : ℝ) := by
    rw [mul_pow, Real.sq_sqrt hσR]
  have hcast : ((δ ^ 2 : ℚ) : ℝ) ≤ ((ρ ^ 2 * σ : ℚ) : ℝ) := by
    push_cast
    rw [← hrhs]
    exact hsq
  exact_mod_cast hcast

/-! ## 2.  `σ > 0`: the witness relation plus the engine's positivity -/

/-- On the witness relation, `σ = c ⬝ p` is the quadratic form of `p`. -/
theorem sigmaQ_eq_qf {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ} {c p : Fin N → ℚ}
    (h : A *ᵥ p = c) :
    QMCLeafB.EngineIterates.sigmaQ c p = QMCLeafB.EngineIterates.qf A p := by
  rw [QMCLeafB.EngineIterates.sigmaQ, QMCLeafB.EngineIterates.qf, ← h, dotProduct_comm]

/-- **`σ > 0` at every cut round.**  The engine's iterates stay `PosQ` (`Aat_posQ`), and a nonzero
normal's witness is nonzero (`A p = c ≠ 0`), so the exact rational `σ` that the depth check speaks
about is positive. -/
theorem sigmaQ_pos_of_wit {N : ℕ} (hN : 2 ≤ N) {A0 : Matrix (Fin N) (Fin N) ℚ}
    {cd : ℕ → QMCLeafB.EngineIterates.CutData N}
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef)
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat N A0 cd k *ᵥ (cd k).p = (cd k).c)
    (hρ : ∀ k, 0 ≤ (cd k).rho) (hcne : ∀ k, (cd k).c ≠ 0) :
    ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p := by
  intro k
  have hpos : QMCLeafB.EngineIterates.PosQ (QMCLeafB.EngineIterates.Aat N A0 cd k) :=
    QMCLeafB.EngineIterates.Aat_posQ hN hA0 hwit hρ hcne k
  have hpne : (cd k).p ≠ 0 := by
    intro hp
    exact hcne k (by rw [← hwit k, hp, Matrix.mulVec_zero])
  rw [sigmaQ_eq_qf (hwit k)]
  exact hpos.qform hpne

/-! ## 3.  The ok branch's witness, at an arbitrary tolerance -/

/-- **`RelaxMem` at any tolerance gives the `ok` round's witness.**  `Check_brick_hd_cert_m5`'s
`hcert_of_relaxMem` is the `δ = dq G` case; the run's own tolerance is `P.dq`, so the rounding
budget hypothesis is kept general here. -/
theorem hcert_of_relaxMem_gen (G : Input) (t δ : ℚ) (cX : Matrix (Fin G.n) (Fin G.n) ℚ)
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
      (t - QMCLeafB.RundataCert.eps G) δ)
    (hCsym : cXᵀ = cX)
    (hbudget : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * δ / 4)
      + δ / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G) :
    ∃ X : Matrix (Fin G.n) (Fin G.n) ℝ,
      QMCLeafB.AnswerProducer.IsUnitDiagPSD X ∧
        (QMCLeafB.wMatrix G * X).trace
          ≤ (t : ℝ) + ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ) := by
  obtain ⟨X, hX, htr⟩ :=
    QMCLeafB.RelaxOracle.hcert_of_relaxMem (A := QMCLeafB.Finalization.wMatrixQ G) (cX := cX)
      (t := t) (εr := QMCLeafB.RundataCert.eps G) (δ := δ)
      (εw := QMCLeafB.RundataCert.eps G) h
      (QMCLeafB.Finalization.IsQMCWeight.symm (QMCLeafB.Finalization.isQMCWeight_wMatrixQ G))
      hCsym (fun i => QMCLeafB.Finalization.wMatrixQ_apply_of_eq) hbudget
  refine ⟨X, hX, ?_⟩
  rw [← QMCLeafB.Finalization.wMatrix_castM G]
  exact htr

/-! ## 4.  The cut branch's separation contract at an approximate centre -/

/-- **`hcut` from one `RelaxCut` per cut round, at an approximate centre.**  The oracle is queried at
the rational surrogate `cX k`; the engine's centre is `Cat …`; if their mismatch in the cut's own
normal direction is at most half the oracle's margin `m`, then recording *any* margin at least
`3m/2` separates the relaxation about the engine's centre.  (This is
`QMCLeafB.RundataCert.hcut_of_approx` with the tolerance generalised from `dq G` to `δ` and the
recorded margin generalised from `3m/2` to any larger rational stream.) -/
theorem hcut_of_approx_gen (G : Input) (t δ : ℚ) {M : ℝ} (T : ℕ) (ok : ℕ → Bool)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (del : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) δ)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hdel : ∀ k (hok : ok k = false), 3 * (C k hok).margin / 2 ≤ del k)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR cd k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2) :
    ∀ k, k < T → ok k = false → ∀ z,
      z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.wMatrix G)
          ((t : ℝ) - ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ)) ((δ : ℚ) : ℝ) M →
        -(((del k : ℚ)) : ℝ)
          ≤ QMCLeafB.EngineIterates.cutCR cd k
              ⬝ᵥ (z - QMCLeafB.EngineIterates.Cat (G.n * G.n)
                (0 : Fin (G.n * G.n) → ℝ) cd k) := by
  intro k _ hok z hz
  have hcf : QMCLeafB.EngineIterates.cutCR cd k
      = fun i => (((QMCLeafB.RelaxOracle.flatQ (C k hok).normal) i : ℚ) : ℝ) := by
    funext i
    simp [QMCLeafB.EngineIterates.cutCR, hnorm k hok]
  have hz' : z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat
      (QMCLeafB.Finalization.wMatrixQ G)) (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
      ((δ : ℚ) : ℝ) M := by
    rw [show (((t - QMCLeafB.RundataCert.eps G : ℚ)) : ℝ)
      = (t : ℝ) - ((QMCLeafB.RundataCert.eps G : ℚ) : ℝ) by push_cast; ring]
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
  have hcast : (((3 * (C k hok).margin / 2 : ℚ)) : ℝ)
      = 3 * (((C k hok).margin : ℚ) : ℝ) / 2 := by push_cast; ring
  have hdelq : -(del k) ≤ -(3 * (C k hok).margin / 2) := by
    have h := hdel k hok
    linarith
  have hdel' : -(((del k : ℚ)) : ℝ)
      ≤ -(3 * (((C k hok).margin : ℚ) : ℝ) / 2) := by
    rw [← hcast]
    exact_mod_cast hdelq
  nlinarith [hsep, h2, hdel']

/-! ## 5.  The assembly: `RunParts` at an arbitrary `P : RunParams G`

The recorded margin stream is `del k = 3 · marg k / 2`, where `marg` is the oracle's margin
(`hmarg` ties it to the cut verdict).  `hcert`, `hcut`, `hrho`, `hdel0`, `hcheck` are then
constructed; the hypotheses are exactly the six items of the module's header. -/

/-- **`RunParts o G t P` from one run of the relaxed oracle.**  `ok`/`cd` are the recorded stream,
`cX k` the rational query centres, `marg` the oracle's margins; the cut-side contract is §4 and the
feasible-side witness §3. -/
noncomputable def runParts_of_relaxRun
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hbud : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n))
    (marg : ℕ → ℚ) (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < P.K * P.m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) P.dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR cd k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2)
    (hdepth : ∀ k (hok : ok k = false),
      (3 * marg k / 2) ^ 2
        ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n) (QMCLeafB.RundataArith.capOf G P.dq)) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hρ0 : ∀ k, 0 ≤ (cd k).rho) (hρmax : ∀ k, (cd k).rho ≤ P.rmax)
    (hcne : ∀ k, (cd k).c ≠ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok (P.K * P.m)) :
    QMCLeafB.FinalStroke.RunParts o G t P := by
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hcap : (0 : ℚ) < QMCLeafB.RundataArith.capOf G P.dq :=
    QMCLeafB.RundataArith.capOf_pos G P.dq P.hdq
  have hA0 : (QMCLeafB.EngineIterates.castM
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (QMCLeafB.RundataArith.capOf G P.dq))).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hcap
  have hσ : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p :=
    sigmaQ_pos_of_wit hN hA0 hwit hρ0 hcne
  refine
    { ok := ok
      cd := cd
      del := fun k => 3 * marg k / 2
      hcert := ?_
      hwit := ?_
      hrho := ?_
      hcne := ?_
      hdel0 := ?_
      hcheck := ?_
      hcut := ?_
      hle := ?_
      hverdict := hverdict }
  · intro k hk hok
    exact hcert_of_relaxMem_gen G t P.dq (cX k) (hmem k hk hok) (hCsym k) hbud
  · intro k _ _
    exact hwit k
  · intro k _ _
    exact hρ0 k
  · intro k _ _
    exact hcne k
  · intro k _ hok
    have hm : 0 < marg k := by rw [hmarg k hok]; exact (C k hok).margin_pos
    linarith
  · intro k _ hok
    exact hdepth k hok
  · intro k _ _
    exact hρmax k
  · intro k hk hok
    refine hcut_of_approx_gen G t P.dq (T := P.K * P.m)
      (M := ((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ) : ℝ))
      ok cd (fun j => 3 * marg j / 2) cX C hnorm ?_ happr k hk hok
    intro j hj
    rw [hmarg j hj]

/-! ## 6.  The shallow parameters: the rounding budget is `dqShallow_budget` -/

/-- `runParamsShallow`'s tolerance really is `dqShallow G`. -/
theorem runParamsShallow_dq (G : Input) (hn : 2 ≤ G.n) :
    (QMCLeafB.RundataParams.runParamsShallow G hn).dq = QMCLeafB.RundataParams.dqShallow G := rfl

/-- At positive total weight the guarded tolerance is the core formula. -/
theorem dqShallow_eq_core (G : Input) (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G = QMCLeafB.RundataParams.dqShallowCore G := by
  unfold QMCLeafB.RundataParams.dqShallow
  rw [if_neg (ne_of_gt hRq)]

/-- **The ok-branch rounding budget at the shallow parameters** — m5's `dqShallow_budget`. -/
theorem runParamsShallow_budget (G : Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
        (3 * (QMCLeafB.RundataParams.runParamsShallow G hn).dq / 4)
      + (QMCLeafB.RundataParams.runParamsShallow G hn).dq / 2
      - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G := by
  rw [runParamsShallow_dq, dqShallow_eq_core G hRq]
  exact QMCLeafB.RundataParams.dqShallow_budget G hn hRq

/-- **`RunParts` at the shallow parameters, per bracketed `(G, t)`.**  The rounding budget of §5 is
discharged by `dqShallow_budget`; what remains is exactly the oracle side (its per-round verdicts,
the stream identifications, the shallow-depth ledger, the witness relation and the ok-bit
agreement). -/
noncomputable def runParts_shallow
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool)
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hnorm : ∀ k (hok : ok k = false),
      (cd k).c = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR cd k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2)
    (hdepth : ∀ k (hok : ok k = false),
      (3 * marg k / 2) ^ 2
        ≤ ((cd k).rho) ^ 2 * QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hwit : ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n)
      (QMCLeafB.Boundary.initShapeOf (G.n * G.n)
        (QMCLeafB.RundataArith.capOf G (QMCLeafB.RundataParams.dqShallow G))) cd k
        *ᵥ (cd k).p = (cd k).c)
    (hρ0 : ∀ k, 0 ≤ (cd k).rho)
    (hρmax : ∀ k, (cd k).rho ≤ (QMCLeafB.RundataParams.runParamsShallow G hn).rmax)
    (hcne : ∀ k, (cd k).c ≠ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.RundataParams.runParamsShallow G hn) :=
  runParts_of_relaxRun o G t (QMCLeafB.RundataParams.runParamsShallow G hn) hn
    (runParamsShallow_budget G hn hRq) ok cd marg cX C hmarg hmem hCsym hnorm happr hdepth
    hwit hρ0 hρmax hcne hverdict

/-! ## 7.  `hwit` by construction: the witness stream of a normal/depth stream

`RunParts.hwit` asks `Aat k *ᵥ p_k = c_k`, where `Aat` is the engine's *own* recursion from the very
stream `cd` that `p_k` belongs to.  That is not an obligation: `PosQ` rational matrices are
surjective (§7.1, m6's `SlotConf.exists_mulVec_eq_of_posQ`, reproved here so the brick does not
import the slot-conformance module), so we can carry the shape *and* its positivity along a
`Nat.rec` and read each round's witness off the current shape (§7.2).  The resulting stream
`cdStream` is the engine's own iterates, so `hwit` holds by `rfl` (§7.3). -/

/-- **A `PosQ` rational matrix is surjective over `ℚ`**: injectivity from positive-definiteness and
finite dimension. -/
theorem exists_mulVec_eq_of_posQ {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (h : QMCLeafB.EngineIterates.PosQ A) (c : Fin N → ℚ) :
    ∃ p : Fin N → ℚ, A *ᵥ p = c := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    by_contra hxne
    have hAx : A *ᵥ x = 0 := by
      rw [LinearMap.mem_ker, Matrix.toLin'_apply] at hx
      exact hx
    have hq0 : QMCLeafB.EngineIterates.qf A x = 0 := by
      show x ⬝ᵥ (A *ᵥ x) = 0
      rw [hAx]
      simp
    exact absurd hq0 (ne_of_gt (h.2 x hxne))
  have hsurj : Function.Surjective (Matrix.toLin' A) :=
    LinearMap.injective_iff_surjective.mp hinj
  obtain ⟨p, hp⟩ := hsurj c
  exact ⟨p, by rwa [Matrix.toLin'_apply] at hp⟩

/-- The witness of `A p = c`, chosen from the positivity test. -/
noncomputable def witOf {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) (v : Fin N → ℚ) : Fin N → ℚ :=
  Classical.choose (exists_mulVec_eq_of_posQ hA v)

theorem witOf_spec {N : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    (hA : QMCLeafB.EngineIterates.PosQ A) (v : Fin N → ℚ) :
    A *ᵥ witOf hA v = v :=
  Classical.choose_spec (exists_mulVec_eq_of_posQ hA v)

/-- **The engine's shape sequence, carrying its positivity.**  One `Nat.rec`: from the current
positive-definite shape we choose the witness of the next normal and take the exact rational step at
the next recorded depth.  Every round of the run is therefore taken at *any* rational depth stream
`ρ ≥ 0` — in particular at the constant shallow ceiling. -/
noncomputable def shapeChain {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) :
    ℕ → { A : Matrix (Fin N) (Fin N) ℚ // (QMCLeafB.EngineIterates.castM A).PosDef } :=
  Nat.rec ⟨A0, hA0⟩ (fun k ih =>
    ⟨QMCLeafB.EngineIterates.rStep N ih.1 (c k)
        (witOf (QMCLeafB.EngineIterates.posQ_of_cast ih.2) (c k)) (ρ k), by
      rw [QMCLeafB.EngineIterates.rStep_cast]
      exact QMCLeafB.EngineIterates.stepShape_posDef hN ih.2
        (fun h => hc k (QMCLeafB.EngineIterates.cast_fun_eq_zero h))
        (by rw [QMCLeafB.EngineIterates.cast_mulVec, witOf_spec])
        (by exact_mod_cast hρ k)⟩)

/-- **The recorded cut stream of a normal/depth stream**: normal `c k`, the chosen witness of
`Aat k p = c k`, and depth `ρ k`. -/
noncomputable def cdStream {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) :
    ℕ → QMCLeafB.EngineIterates.CutData N :=
  fun k => ⟨c k,
    witOf (QMCLeafB.EngineIterates.posQ_of_cast (shapeChain hN A0 hA0 c hc ρ hρ k).2) (c k),
    ρ k⟩

/-- `cdStream` *is* the engine's own iterate stream. -/
theorem Aat_cdStream {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    QMCLeafB.EngineIterates.Aat N A0 (cdStream hN A0 hA0 c hc ρ hρ) k
      = (shapeChain hN A0 hA0 c hc ρ hρ k).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [QMCLeafB.EngineIterates.Aat_unfold, ih]
      rfl

/-- **`hwit` for the constructed stream.** -/
theorem hwit_cdStream {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) :
    ∀ k, QMCLeafB.EngineIterates.Aat N A0 (cdStream hN A0 hA0 c hc ρ hρ) k
        *ᵥ (cdStream hN A0 hA0 c hc ρ hρ k).p
      = (cdStream hN A0 hA0 c hc ρ hρ k).c := by
  intro k
  rw [Aat_cdStream hN A0 hA0 c hc ρ hρ k]
  exact witOf_spec (A := (shapeChain hN A0 hA0 c hc ρ hρ k).1)
    (QMCLeafB.EngineIterates.posQ_of_cast (shapeChain hN A0 hA0 c hc ρ hρ k).2) (c k)

/-- **The normals and depths of `cdStream`.** -/
theorem cdStream_c {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    (cdStream hN A0 hA0 c hc ρ hρ k).c = c k := rfl

theorem cdStream_rho {N : ℕ} (hN : 2 ≤ N) (A0 : Matrix (Fin N) (Fin N) ℚ)
    (hA0 : (QMCLeafB.EngineIterates.castM A0).PosDef) (c : ℕ → Fin N → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    (cdStream hN A0 hA0 c hc ρ hρ k).rho = ρ k := rfl

/-! ## 10.  Making the shallow-depth ledger achievable: diluting a cut's normal

§5–§9 leave one ledger that is a condition on the oracle's *output*: the normalised depth
`(3m/2)/√σ` must fit under the ceiling `rmax` (§5's `hdepth`).  That is not a property the oracle
has to *happen* to have: `RelaxCut` is an existential over `(normal, margin)`, so a cut may be
re-presented on a *diluted* normal `c + λ·d`.  The margin then grows only linearly in `λ`
(`m + λβ`, `β` the body's extent in the direction `d`) while `σ` grows quadratically, so the
normalised depth tends to `β/√(dᵀA⁻¹d)` — and the relaxed body is *thin* in the diagonal-ones
direction (`|Xᵢᵢ − 1| ≤ δ/4`), which is what makes that limit small.  This section proves the
separation half of that mechanism; the quantitative depth half is the remaining instruction to the
algorithmic side. -/

/-- `frob` is additive in its first argument. -/
theorem frob_add_left {n : ℕ} (C D X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (C + D) X
      = QMCLeafB.SepOracle.frob C X + QMCLeafB.SepOracle.frob D X := by
  simp [QMCLeafB.SepOracle.frob, Finset.sum_add_distrib, add_mul]

/-- `frob` is homogeneous in its first argument. -/
theorem frob_smul_left' {n : ℕ} (l : ℝ) (C X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (l • C) X = l * QMCLeafB.SepOracle.frob C X := by
  simp [QMCLeafB.SepOracle.frob, Finset.mul_sum, mul_assoc, smul_eq_mul]

/-- **Normal dilation.**  If the whole relaxed body lies at distance at most `β` below the centre in
the direction `d`, then the cut with normal `c + λ·d` and margin `m + λβ` is still a `RelaxCut` of the
relaxation (for `λ, β ≥ 0`): the margin grows only linearly in `λ`, while `σ = c ⬝ A⁻¹c` grows
quadratically, so the normalised depth can be pushed down to `β/√(dᵀA⁻¹d)`. -/
noncomputable def RelaxCut.dilate {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ)
    (d : Matrix (Fin n) (Fin n) ℚ) (lam β : ℚ) (hβ0 : 0 ≤ β) (hlam : 0 ≤ lam)
    (hβ : ∀ X : Matrix (Fin n) (Fin n) ℝ,
      QMCLeafB.BallFloor.relaxBodyLE (QMCLeafB.SepOracle.castMat A) ((u : ℚ) : ℝ)
        ((δ : ℚ) : ℝ) X →
      -((β : ℚ) : ℝ)
        ≤ QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat d)
            (X - QMCLeafB.SepOracle.castMat cX)) :
    QMCLeafB.RelaxOracle.RelaxCut A cX u δ where
  normal := C.normal + lam • d
  margin := C.margin + lam * β
  margin_pos := by
    have h1 := C.margin_pos
    have h2 : 0 ≤ lam * β := mul_nonneg hlam hβ0
    linarith
  separates := by
    intro X hX
    have h1 := C.separates X hX
    have h2 := hβ X hX
    have hcast : QMCLeafB.SepOracle.castMat (C.normal + lam • d)
        = QMCLeafB.SepOracle.castMat C.normal
          + (((lam : ℚ) : ℝ)) • QMCLeafB.SepOracle.castMat d := by
      ext i j
      simp [QMCLeafB.SepOracle.castMat_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul]
    have hfrob : QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat (C.normal + lam • d))
          (X - QMCLeafB.SepOracle.castMat cX)
        = QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat C.normal)
            (X - QMCLeafB.SepOracle.castMat cX)
          + ((lam : ℚ) : ℝ)
            * QMCLeafB.SepOracle.frob (QMCLeafB.SepOracle.castMat d)
                (X - QMCLeafB.SepOracle.castMat cX) := by
      rw [hcast, frob_add_left, frob_smul_left']
    have hmargin : (((C.margin + lam * β : ℚ)) : ℝ)
        = ((C.margin : ℚ) : ℝ) + ((lam : ℚ) : ℝ) * ((β : ℚ) : ℝ) := by push_cast; ring
    rw [hfrob, hmargin]
    have hlamR : (0 : ℝ) ≤ ((lam : ℚ) : ℝ) := by exact_mod_cast hlam
    nlinarith [h1, h2, hlamR]

#print axioms QMCLeafB.RunPartsShallow.frob_add_left
#print axioms QMCLeafB.RunPartsShallow.RelaxCut.dilate


/-! ## 8.  The composed statement: `RunParts` at the shallow parameters from the oracle alone -/

/-- The initial shape of the shallow run (`RunParts`' own `initShapeOf (2n² + 2dq²)`). -/
noncomputable def A0Of (G : Input) : Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (G.n * G.n)
    (QMCLeafB.RundataArith.capOf G (QMCLeafB.RundataParams.dqShallow G))

theorem A0Of_posDef (G : Input) : (QMCLeafB.EngineIterates.castM (A0Of G)).PosDef :=
  QMCLeafB.Boundary.initShapeOf_cast_posDef
    (QMCLeafB.RundataArith.capOf_pos G _ (QMCLeafB.RundataParams.dqShallow_pos G))

/-- The recorded cut stream of the shallow run at a normal stream `c` and a depth stream `ρ`: the
engine's own iterates, so every field of the run that is about `cd` is a theorem. -/
noncomputable def cutStream (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) :
    ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  cdStream (N := G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn
    omega) (A0Of G) (A0Of_posDef G) c hc ρ hρ

theorem cutStream_c (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    (cutStream G hn c hc ρ hρ k).c = c k := rfl

theorem cutStream_rho (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) (k : ℕ) :
    (cutStream G hn c hc ρ hρ k).rho = ρ k := rfl

theorem cutStream_wit (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) (ρ : ℕ → ℚ) (hρ : ∀ k, 0 ≤ ρ k) :
    ∀ k, QMCLeafB.EngineIterates.Aat (G.n * G.n) (A0Of G) (cutStream G hn c hc ρ hρ) k
        *ᵥ (cutStream G hn c hc ρ hρ k).p
      = (cutStream G hn c hc ρ hρ k).c :=
  hwit_cdStream (N := G.n * G.n) (by
    have h := Nat.mul_le_mul hn hn
    omega) (A0Of G) (A0Of_posDef G) c hc ρ hρ

/-- **`RunParts` at the shallow parameters from the oracle's verdicts alone.**  The recorded cut
stream is *constructed* (the engine's own iterates at the oracle's normals and the program's depths),
so `hwit`, the stream identification, `c ≠ 0`, `ρ ≥ 0` and `ρ ≤ rmax` are all disposed of.  What is
left is exactly the oracle side:

* `C` — the cut verdict at the query centre `cX k` (every `ok k = false` round);
* `hmem` — the `ok` verdict at the same centre (every `ok k = true` round, `k < K·m`);
* `hCne`, `hnorm` — the oracle's normal is nonzero and *is* the recorded normal;
* `happr` — the centre approximation: the engine's centre and the rational query centre differ by at
  most half the oracle's margin in the cut's own direction;
* `hdepth` — the shallow-depth ledger, in the rational squared form of `RunData.hcheck`
  (prove it from the real form `(3m/2) ≤ ρ√σ` with `sq_le_of_sqrt_le`);
* `hverdict` — the loop's verdict bit is the run's `anyOk` over `K·m` rounds. -/
noncomputable def runParts_shallow_of_oracle
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ) (ρ : ℕ → ℚ)
    (hc : ∀ k, c k ≠ 0) (hρ0 : ∀ k, 0 ≤ ρ k)
    (hρmax : ∀ k, ρ k ≤ (QMCLeafB.RundataParams.runParamsShallow G hn).rmax)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hnorm : ∀ k (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmem : ∀ k, k < (QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR (cutStream G hn c hc ρ hρ0) k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (cutStream G hn c hc ρ hρ0) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2)
    (hdepth : ∀ k (hok : ok k = false),
      (3 * marg k / 2) ^ 2
        ≤ ((cutStream G hn c hc ρ hρ0 k).rho) ^ 2
          * QMCLeafB.EngineIterates.sigmaQ (cutStream G hn c hc ρ hρ0 k).c
              (cutStream G hn c hc ρ hρ0 k).p)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.RundataParams.runParamsShallow G hn) :=
  runParts_shallow o G t hn hRq ok (cutStream G hn c hc ρ hρ0) marg cX C hmarg hmem hCsym
    (fun k hok => (cutStream_c G hn c hc ρ hρ0 k).trans (hnorm k hok))
    happr hdepth
    (cutStream_wit G hn c hc ρ hρ0)
    hρ0
    (fun k => (cutStream_rho G hn c hc ρ hρ0 k).le.trans (hρmax k))
    (fun k => by rw [cutStream_c G hn c hc ρ hρ0 k]; exact hc k)
    hverdict

#print axioms QMCLeafB.RunPartsShallow.A0Of_posDef
#print axioms QMCLeafB.RunPartsShallow.cutStream_wit
#print axioms QMCLeafB.RunPartsShallow.runParts_shallow_of_oracle

/-! ## 9.  The bracketed form: `RunParts` for every `(G, t)` of the bracket

The bracket `-Rq G ≤ t < -Rq G/40000` forces `Rq G > 0` (`Rq_pos_of_bracket`), which is exactly what
the ok-branch rounding budget needs — so the shallow run's parameters are total on the bracket.

The depth stream is pinned to the ceiling `ρ ≡ P.rmax`: the shallow-cut method takes *every* cut at
the largest depth the halving inequality allows.  That leaves only the oracle side and the ok bits. -/

/-- The shallow run's recorded cut stream: every cut at the depth ceiling `rmax`. -/
noncomputable def shallowCut (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n) :=
  cutStream G hn c hc (fun _ => (QMCLeafB.RundataParams.runParamsShallow G hn).rmax)
    (fun _ => (QMCLeafB.RundataParams.runParamsShallow G hn).hrmax)

theorem shallowCut_sigma_pos (G : Input) (hn : 2 ≤ G.n) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ k, c k ≠ 0) :
    ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (shallowCut G hn c hc k).c
      (shallowCut G hn c hc k).p := by
  have hN : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hrm : 0 ≤ (QMCLeafB.RundataParams.runParamsShallow G hn).rmax :=
    (QMCLeafB.RundataParams.runParamsShallow G hn).hrmax
  refine sigmaQ_pos_of_wit (N := G.n * G.n) (A0 := A0Of G)
    (cd := shallowCut G hn c hc) hN (A0Of_posDef G) ?_ (fun _ => hrm) ?_
  · exact cutStream_wit G hn c hc
      (fun _ => (QMCLeafB.RundataParams.runParamsShallow G hn).rmax) (fun _ => hrm)
  · intro k
    rw [show (shallowCut G hn c hc k).c = c k from rfl]
    exact hc k

/-- **The bracket forces positive total weight.**  `-Rq G ≤ t < -Rq G/40000` is nonempty exactly when
`Rq G > 0`; this is the hypothesis the shallow rounding budget needs. -/
theorem Rq_pos_of_bracket (G : Input) {t : ℚ}
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : t < -(QMCLeafB.EngineRuntime.Rq G / 40000)) :
    0 < QMCLeafB.EngineRuntime.Rq G := by
  have hlt : -QMCLeafB.EngineRuntime.Rq G < -(QMCLeafB.EngineRuntime.Rq G / 40000) :=
    lt_of_le_of_lt hlo hhi
  by_contra h
  push Not at h
  linarith

/-- **`RunParts` for every bracketed `(G, t)`, from the oracle's verdicts.**  The recorded run is
constructed end to end (`shallowCut`: the engine's own iterates at the oracle's normals and the
ceiling depth `rmax`), so of the twelve fields of `RunParts` the caller owes only

* the oracle's two verdicts at the rational query centres `cX k` (`C` on the cut rounds, `hmem` on
  the ok rounds) and the identification of the recorded normal with the oracle's (`hnorm`),
* the centre approximation `happr`,
* the shallow-depth ledger `hdepthR`, in the *real* form `(3m/2) ≤ rmax·√σ` (use
  `sq_le_of_sqrt_le`'s converse if a rational form is more convenient),
* the ok bits' agreement `hverdict`. -/
noncomputable def runParts_shallow_bracket
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hlo : -QMCLeafB.EngineRuntime.Rq G ≤ t)
    (hhi : t < -(QMCLeafB.EngineRuntime.Rq G / 40000))
    (ok : ℕ → Bool) (marg : ℕ → ℚ) (c : ℕ → Fin (G.n * G.n) → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (hc : ∀ k, c k ≠ 0)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hnorm : ∀ k (hok : ok k = false),
      c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hmem : ∀ k, k < (QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (happr : ∀ k (hok : ok k = false),
      QMCLeafB.EngineIterates.cutCR (shallowCut G hn c hc) k
          ⬝ᵥ (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
              (shallowCut G hn c hc) k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ (((C k hok).margin : ℚ) : ℝ) / 2)
    (hdepthR : ∀ k (hok : ok k = false),
      (3 * marg k / 2 : ℝ)
        ≤ ((QMCLeafB.RundataParams.runParamsShallow G hn).rmax : ℝ)
          * Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (shallowCut G hn c hc k).c
              (shallowCut G hn c hc k).p : ℚ)) : ℝ))
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t (QMCLeafB.RundataParams.runParamsShallow G hn) :=
  runParts_shallow_of_oracle o G t hn (Rq_pos_of_bracket G hlo hhi) ok marg c cX
    (fun _ => (QMCLeafB.RundataParams.runParamsShallow G hn).rmax) hc
    (fun _ => (QMCLeafB.RundataParams.runParamsShallow G hn).hrmax)
    (fun _ => le_refl _) C hmarg hnorm hmem hCsym happr
    (fun k hok => sq_le_of_sqrt_le
      (δ := 3 * marg k / 2)
      (ρ := (QMCLeafB.RundataParams.runParamsShallow G hn).rmax)
      (σ := QMCLeafB.EngineIterates.sigmaQ (shallowCut G hn c hc k).c
        (shallowCut G hn c hc k).p)
      (by
        have hm : 0 < marg k := by
          rw [hmarg k hok]
          exact (C k hok).margin_pos
        linarith)
      (QMCLeafB.RundataParams.runParamsShallow G hn).hrmax
      (le_of_lt (shallowCut_sigma_pos G hn c hc k))
      (by
        have hcast : ((3 * marg k / 2 : ℚ) : ℝ) = 3 * ((marg k : ℚ) : ℝ) / 2 := by
          push_cast
          ring
        rw [hcast]
        exact hdepthR k hok))
    hverdict

#print axioms QMCLeafB.RunPartsShallow.shallowCut_sigma_pos
#print axioms QMCLeafB.RunPartsShallow.Rq_pos_of_bracket
#print axioms QMCLeafB.RunPartsShallow.runParts_shallow_bracket





#print axioms QMCLeafB.RunPartsShallow.shapeChain
#print axioms QMCLeafB.RunPartsShallow.Aat_cdStream
#print axioms QMCLeafB.RunPartsShallow.hwit_cdStream

#print axioms QMCLeafB.RunPartsShallow.sq_le_of_sqrt_le
#print axioms QMCLeafB.RunPartsShallow.sigmaQ_eq_qf
#print axioms QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit
#print axioms QMCLeafB.RunPartsShallow.hcert_of_relaxMem_gen
#print axioms QMCLeafB.RunPartsShallow.hcut_of_approx_gen
#print axioms QMCLeafB.RunPartsShallow.runParts_of_relaxRun
#print axioms QMCLeafB.RunPartsShallow.dqShallow_eq_core
#print axioms QMCLeafB.RunPartsShallow.runParamsShallow_budget
#print axioms QMCLeafB.RunPartsShallow.runParts_shallow

end QMCLeafB.RunPartsShallow



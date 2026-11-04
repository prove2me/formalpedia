-- Prove2me | Definitions.Def_QMCLeafB_runparts_stream_m4
-- name    : QMCLeafB_runparts_stream_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T02:24:36.389081+00:00
-- url     : https://prove2.me/theorems/5940e233-ec59-4dfd-bf29-31580f1f40dd
-- title:
--   QMCLeafB runparts_stream_m4
-- statement:
--   # leaf B phase 16 — brick `runparts-assembly` (swarm `smw1ez4a9`, member m4, direction `d5`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_centre_m5
import Definitions.Def_QMCLeafB_halve_perG_m2
/-
# leaf B phase 16 — brick `runparts-assembly` (swarm `smw1ez4a9`, member m4, direction `d5`)

Stream-level assembly of the interior run bundle `QMCLeafB.FinalStroke.RunParts o G t P` for the
campaign's dqShallow family.  The conduit inherited from the previous swarms is

    QMCLeafB.RunPartsDilate.runParts_of_dilated / runParts_shallow_dilated

from fourteen stream-side hypotheses.  This file removes the geometric ones by explicit
construction and pins the rest, ending at

* `runParts_of_stream_data` — `RunParts o G t P` for an **arbitrary** `P : RunParams G` from
  `0 < P.rmax`, `P.rmax ≤ 1`, the ok-branch rounding budget `hbudP`, the program's records and four
  rational conditions on the centre stream (§5);
* `runParts_shallow_dyadic` — the same with the surrogate and the dilation parameter instantiated at
  the *dyadic* data the program actually computes (`muUp`, `deltaUp`, `dOne`, §6), so the residual is
  the precision choice `grid`/`hgrid1` plus the four centre conditions;
* `runParts_shallow_concrete` — the phase-14 endpoint at `QMCLeafB.RundataParams.runParamsShallow`
  (§7);
* `paramsK_side_conditions` (§8) — the three scalar hypotheses at `HalvePerG.paramsK G
  (dqShallow G) … Kf hK`, which is *definitionally* brick 5's `UnionShallow.paramsShallowKf Kf hK`
  (checked by defeq against `Check_union_shallow_m5`), so instantiating §5 at the campaign family is
  one term;
* `lower_surrogate_breaks_hdriftd` (§9) — a machine-checked counterexample showing that the lower
  `invSqrtLe` surrogate makes `hdriftd` *strictly false* while still being admissible, so the bracket
  switch below is mandatory rather than cosmetic.

## What is no longer a hypothesis

`dM`, `hdM`, `hbody`, `hdriftc`, `hdriftd`, `hρ ≤ 1`, `σ > 0` are all discharged.

* **`hbody` at `dM = 1`** (§1 `hbody_of_diag`).  With the identity direction the body-above-centre
  condition is `tr X ≥ tr (cX k)` for every point of the relaxed body, and `relaxBodyLE` gives
  `|Xᵢᵢ − 1| ≤ dq/4`; so the *centre's* diagonal being `≤ 1 − dq/4` (a rational per-entry
  condition) suffices.  Note the strength of this: at `dM = 1` the condition `hdiagc` is essentially
  *equivalent* to `hbody` (the body's diagonal clause admits `Xᵢᵢ = 1 − dq/4` entrywise), so the
  identity direction is available exactly for a centre that sits **below the body in trace**.  The
  campaign's query centre is m3's state `stX`, whose diagonal at `init0` is `(2n² + 2dq²)⁻¹` (m1's
  `identVia` packing) — comfortably `≤ 1 − dq/4` — so at the campaign's program `hdiagc` is the run
  invariant *"the iterate's diagonal stays below the unit-diagonal body"* (the round's
  `α⁻¹ = (n+1)/(n−1)` scaling grows it, the rank-one subtraction pulls it down), while a centre with
  `diag = 1` (the `dvR = 0` branch's assumption) would violate it for every diagonal direction.
* **`hdriftd`** (§2 `drift_nonpos_of_upper`).  `Cat k − q_k = ∑_{j<k}(λ_j − μ_j)·p_j` with
  `λ_j = γ_j/√σ_j` the engine's increment and `μ_j` the program's rational surrogate, so
  `d ⪝ (Cat k − q_k) = ∑_{j<k}(λ_j − μ_j)(d ⪝ p_j)`.  The pairings `d ⪝ p_j` have **no fixed sign**
  (`d ⪝ p_j = flat ones ⪝ A_j⁻¹·cn_j` for a positive-definite flat-space `A_j` with no structural
  relation to the matrix world; it takes both signs on admissible data), so the choice of bracket
  decides which sign is needed:

  - LOWER bracket `μ_j = γ_j·invSqrtLe` (the choice the phase-14/15 notes describe): all
    `λ_j − μ_j ≥ 0`, so `hdriftd` needs `d ⪝ p_j ≤ 0` for **every** round.  That sign cannot be
    enforced: `d ⪝ p_j = d ⪝ A_j⁻¹c_j + λ_j·(d ⪝ A_j⁻¹d)` and the coefficient of the *dilation*
    parameter `λ_j` is `d ⪝ A_j⁻¹d > 0` (`dir_wit_pos`), so increasing `λ_j` pushes the pairing the
    wrong way.  With the lower bracket the dilated `hdriftd` is therefore dead.
  - UPPER bracket `μ_j = γ_j·invSqrtGe`: all `λ_j − μ_j ≤ 0`, so `hdriftd` follows from
    `0 ≤ d ⪝ p_j` — and *that* is exactly what a large `λ_j` buys (`hlam3` below).

  One-line switch in the surrogate, and the reason the dilated route closes at `dM = 1`.
* **`hdriftc`** (§3 `drift_bound_upper`): with the upper bracket the drift is charged only on the
  rounds where the cut direction pairs *negatively* with the increment, by the rational widths
  `δ_j = γ_j·(invSqrtGe − invSqrtLe)` — the mirrored twin of `CentreTrack.drift_bound`.
* **`hρ ≤ 1`, `σ > 0`** (§6): `rmaxOf = 1/(4N)` and `sigmaQ_pos_of_wit`.
* **`hpos` is NOT automatic but IS enforceable** (§4b).  `p_j = A_j⁻¹(c_j + λ_j·d)` and the term
  `d ⬝ A_j⁻¹c_j` has no sign (`d ⬝ A⁻¹c` is negative for plenty of positive-definite `A` built from
  PSD rank ones).  But the witness is affine in the normal (`witAt_add_lam`), so
  `d ⬝ p_j = d ⬝ A_j⁻¹c_j + λ_j·(d ⬝ A_j⁻¹d)` and the coefficient of `λ_j` is strictly positive
  (`dir_wit_pos`): taking `λ_j` at least `|d ⬝ A_j⁻¹c_j| / (d ⬝ A_j⁻¹d)` makes it nonnegative.  That
  is `hlam3`, the same "λ large enough" shape as the depth ledger's own `hlam2`; the two are jointly
  satisfiable (`exists_lam_of_pos`) and `hcne` costs nothing extra (`exists_lam_avoid`).

## The residual list of the endpoint

`runParts_shallow_dyadic` leaves exactly: the oracle's records `C`/`hmarg`/`hmem`/`hcEq`, the centre
symmetry `hCsym`, the recorded-normal identity `hcn` (`cn k = c k + λ_k·flat ones`),
`hcne`, `λ`-bounds `hlam0`/`hlam1`/`hlam2`/`hlam3`, the precision choice `grid`/`hgrid1`, and
**four rational conditions on the centre stream**:

    hdiagc  : diag (cX k) ≤ 1 − dq/4                 (hbody, via the trace)
    hqSurr  : qSurr k = ∑_{j<k} μ_j p_j              (the rational surrogate)
    hstatec : c_k ⪝ (qSurr k − flat (cX k))
                + ∑_{j<k} δ_j·max 0(−(c_k ⬝ p_j)) ≤ marg_k/2     (hdriftc: state + budget)
    hstated : flat ones ⬝ (qSurr k − flat (cX k)) ≤ 0             (hdriftd: state)
    hverdict : o G t = anyOk ok (K·m)

The **state mismatch is a separate term on purpose**: m3's `RoundProgram.oracleR` queries at the
program's own *state* `stX` (kept symmetric by the Sherman–Morrison update and the entrywise snap),
not at the surrogate, so `hstatec`/`hstated` carry `qSurr k − flat (cX k)`.  Taking
`qSurr := flat ∘ cX` recovers the exact-surrogate interface (`hstatec`'s first term and `hstated`
vanish).  In the campaign `tr (cX k) ≈ n` while the surrogate's trace is small, so `hstated` is the
easy side; `hstatec` is the real bookkeeping (the GLS state against the dual centre).

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RunPartsStream

open QuantumMaxCutEnergy

/-! ## 1.  The identity dilation direction -/

/-- The rational identity casts to the real identity. -/
theorem castMat_one {n : ℕ} :
    QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ) = 1 := by
  ext i j
  rw [QMCLeafB.SepOracle.castMat_apply]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- **The Frobenius pairing against the identity is the trace.** -/
theorem frob_one_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.SepOracle.frob (1 : Matrix (Fin n) (Fin n) ℝ) X = ∑ i, X i i := by
  rw [QMCLeafB.SepOracle.frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    rw [Matrix.one_apply_ne (Ne.symm hj), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **`hbody` at the identity direction, from the centre's diagonal.**  If every diagonal entry of
the query centre is `≤ 1 − δ/4` then every point of the relaxed body is above the centre in the
identity direction, because the body's diagonal entries are `≥ 1 − δ/4`. -/
theorem hbody_of_diag {n : ℕ} {δ : ℝ} {Q : Matrix (Fin n) (Fin n) ℚ}
    (hdiag : ∀ i, ((Q i i : ℚ) : ℝ) ≤ 1 - δ / 4)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : ∀ i, |X i i - 1| ≤ δ / 4) :
    -(0 : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q) := by
  have h1 : ∀ i, (1 : ℝ) - δ / 4 ≤ X i i := by
    intro i
    have h := (abs_le.mp (hX i)).1
    linarith
  rw [show -(0 : ℝ) = 0 by ring, castMat_one, QMCLeafB.SepOracle.frob_sub,
    frob_one_eq_trace, frob_one_eq_trace, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun i _ => ?_
  have h2 : (QMCLeafB.SepOracle.castMat Q) i i = ((Q i i : ℚ) : ℝ) := rfl
  rw [h2]
  linarith [h1 i, hdiag i]

/-- The same on the campaign's relaxed body predicate. -/
theorem hbody_of_diag_body {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {Q : Matrix (Fin n) (Fin n) ℚ}
    (hdiag : ∀ i, ((Q i i : ℚ) : ℝ) ≤ 1 - δ / 4)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : QMCLeafB.BallFloor.relaxBodyLE A u δ X) :
    -(0 : ℝ) ≤ QMCLeafB.SepOracle.frob
      (QMCLeafB.SepOracle.castMat (1 : Matrix (Fin n) (Fin n) ℚ))
      (X - QMCLeafB.SepOracle.castMat Q) :=
  hbody_of_diag hdiag hX.2.1

#print axioms QMCLeafB.RunPartsStream.castMat_one
#print axioms QMCLeafB.RunPartsStream.frob_one_eq_trace
#print axioms QMCLeafB.RunPartsStream.hbody_of_diag
#print axioms QMCLeafB.RunPartsStream.hbody_of_diag_body

/-! ## 2.  The sign of the centre surrogate: `hdriftd` -/

/-- The centre is the sum of its increments, in the shape the drift estimates use. -/
theorem cat_sub_surrogate (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (k : ℕ)
    (mu : ℕ → ℝ) :
    QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
        - ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j
      = ∑ j ∈ Finset.range k,
          (QMCLeafB.CentreTrack.lam N cd j - mu j) • QMCLeafB.EngineIterates.cutPR cd j := by
  rw [QMCLeafB.CentreTrack.Cat_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sub_smul]

/-- **`hdriftd` is free for an UPPER surrogate.**  If the surrogate coefficient dominates the
engine's increment (`λ_j ≤ μ_j`, which is what the `invSqrtGe` bracket gives) and the dilation
direction pairs nonnegatively with every recorded witness (`0 ≤ d ⬝ p_j`), then the centre's
displacement from the surrogate has nonpositive component in direction `d`. -/
theorem drift_nonpos_of_upper (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N)
    (d : Fin N → ℝ) (k : ℕ) (q : Fin N → ℝ) (mu : ℕ → ℝ)
    (hq : q = ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j)
    (hhi : ∀ j, j < k → QMCLeafB.CentreTrack.lam N cd j ≤ mu j)
    (hpos : ∀ j, j < k → 0 ≤ d ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j) :
    d ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k - q) ≤ 0 := by
  rw [hq, cat_sub_surrogate, QMCLeafB.CentreTrack.dot_sum_smul]
  refine Finset.sum_nonpos fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : QMCLeafB.CentreTrack.lam N cd j - mu j ≤ 0 := by linarith [hhi j hjk]
  exact mul_nonpos_of_nonpos_of_nonneg h1 (hpos j hjk)

/-! ## 3.  The cut-direction drift `hdriftc` with an upper surrogate -/

/-- **The drift bound with an upper bracket.**  Mirror of
`QMCLeafB.CentreTrack.drift_bound`: with `μ_j − δ_j ≤ λ_j ≤ μ_j` the mismatch is charged only on
the rounds where the cut direction pairs *negatively* with the increment, and the charge is the
rational interval width.  (The lower bracket's version is `drift_bound`.) -/
theorem drift_bound_upper (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (c : Fin N → ℝ)
    (k : ℕ) (mu delta : ℕ → ℝ)
    (hlo : ∀ j, j < k → mu j - delta j ≤ QMCLeafB.CentreTrack.lam N cd j)
    (hhi : ∀ j, j < k → QMCLeafB.CentreTrack.lam N cd j ≤ mu j) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.Cat N (0 : Fin N → ℝ) cd k
        - ∑ j ∈ Finset.range k, mu j • QMCLeafB.EngineIterates.cutPR cd j)
      ≤ ∑ j ∈ Finset.range k,
          delta j * max 0 (-(c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j)) := by
  rw [cat_sub_surrogate, QMCLeafB.CentreTrack.dot_sum_smul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  have h1 : mu j - delta j ≤ QMCLeafB.CentreTrack.lam N cd j := hlo j hjk
  have h2 : QMCLeafB.CentreTrack.lam N cd j ≤ mu j := hhi j hjk
  set a : ℝ := QMCLeafB.CentreTrack.lam N cd j - mu j with ha
  set b : ℝ := c ⬝ᵥ QMCLeafB.EngineIterates.cutPR cd j with hb
  have ha0 : a ≤ 0 := by linarith
  have haneg : -delta j ≤ a := by linarith
  rcases le_total 0 b with hb0 | hb0
  · have hle : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha0 hb0
    have hz : max 0 (-b) = 0 := max_eq_left (by linarith)
    rw [hz, mul_zero]
    exact hle
  · have hle : a * b ≤ (-delta j) * b := mul_le_mul_of_nonpos_right haneg hb0
    have hz : max 0 (-b) = -b := max_eq_right (by linarith)
    rw [hz]
    have hr : (-delta j) * b = delta j * (-b) := by ring
    linarith [hle, hr]

#print axioms QMCLeafB.RunPartsStream.cat_sub_surrogate
#print axioms QMCLeafB.RunPartsStream.drift_nonpos_of_upper
#print axioms QMCLeafB.RunPartsStream.drift_bound_upper

/-! ## 4.  The dyadic upper bracket as a surrogate -/

/-- **The upper dyadic bracket dominates the engine's increment** (this is the second half of
`QMCLeafB.CentreTrack.lam_bracket`, in the shape `drift_nonpos_of_upper` wants). -/
theorem upper_bracket (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j k : ℕ)
    (hρ1 : (cd j).rho ≤ 1)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
    (hk : 1 ≤ QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p * 4 ^ k) :
    QMCLeafB.CentreTrack.lam N cd j
      ≤ ((QMCLeafB.CentreTrack.gamQ N cd j
          * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ) :=
  (QMCLeafB.CentreTrack.lam_bracket N cd j k hρ1 hσ hk).2

/-- **The upper bracket's lower end is the lower bracket** (the width identity that makes
`drift_bound_upper`'s `hlo` hold for the dyadic brackets). -/
theorem upper_bracket_lo (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (j k : ℕ)
    (hρ1 : (cd j).rho ≤ 1)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p)
    (hk : 1 ≤ QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p * 4 ^ k) :
    ((QMCLeafB.CentreTrack.gamQ N cd j
        * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ)
      - ((QMCLeafB.CentreTrack.gamQ N cd j
          * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k
            - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k) : ℚ) : ℝ)
      ≤ QMCLeafB.CentreTrack.lam N cd j := by
  have h := (QMCLeafB.CentreTrack.lam_bracket N cd j k hρ1 hσ hk).1
  have hcast : ((QMCLeafB.CentreTrack.gamQ N cd j
        * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ)
      - ((QMCLeafB.CentreTrack.gamQ N cd j
          * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k
            - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k) : ℚ) : ℝ)
      = ((QMCLeafB.CentreTrack.gamQ N cd j
          * DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) k : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  exact h

#print axioms QMCLeafB.RunPartsStream.upper_bracket
#print axioms QMCLeafB.RunPartsStream.upper_bracket_lo

/-! ## 4b.  The direction's sign is not a residual: it follows from `λ` being large

`hpos` (`0 ≤ flat ones ⬝ p_j`) is *not* automatic: `p_j = A_j⁻¹(c_j + λ_j·d)` and the first term
`A_j⁻¹ c_j` has no sign (`d ⬝ A⁻¹c` is negative for plenty of positive-definite `A` built from PSD
rank ones).  But it *is* enforceable: the recorded witness is affine in the normal
(`witAt_add_lam`), so

    d ⬝ p_j = d ⬝ (A_j⁻¹c_j) + λ_j · (d ⬝ A_j⁻¹d),

and the second coefficient `δ_j = d ⬝ A_j⁻¹d` is strictly positive.  Choosing `λ_j` at least
`|d ⬝ A_j⁻¹c_j| / δ_j` therefore makes the pairing nonnegative — the same "λ large enough" shape as
the depth ledger's own condition. -/

/-- Cast linearity of the normal stream. -/
theorem cast_add_smul {N : ℕ} (c d : Fin N → ℚ) (lam : ℚ) :
    (fun i => (((c + lam • d) i : ℚ) : ℝ))
      = (fun i => ((c i : ℚ) : ℝ)) + ((lam : ℚ) : ℝ) • (fun i => ((d i : ℚ) : ℝ)) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Rat.cast_add, Rat.cast_mul, smul_eq_mul]

/-- **The recorded witness is affine in the normal.** -/
theorem witAt_add_lam (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (j : ℕ) (c : Fin (G.n * G.n) → ℚ) (lam : ℚ) :
    QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
        (c + lam • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j
      = QMCLeafB.RunPartsDilate.witAt G P hn cn hcne c j
        + lam • QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j := by
  refine QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ
    (QMCLeafB.RunPartsDilate.runShape_posQ G P hn cn hcne j) ?_
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, QMCLeafB.RunPartsDilate.witAt_spec,
    QMCLeafB.RunPartsDilate.witAt_spec, QMCLeafB.RunPartsDilate.witAt_spec]

/-- **The identity direction pairs nonnegatively with the recorded witness, once `λ` is large.** -/
theorem dir_pairing_nonneg (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (j : ℕ) (c : Fin (G.n * G.n) → ℚ) (lam : ℚ) (hlam0 : 0 ≤ lam)
    (hbig : |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne c j i : ℚ) : ℝ))|
        ≤ ((lam : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)))) :
    0 ≤ (fun i => (((QMCLeafB.RelaxOracle.flatQ
          (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
        ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (c + lam • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)) := by
  rw [witAt_add_lam, cast_add_smul, dotProduct_add, dotProduct_smul, smul_eq_mul]
  set x : ℝ := (fun i => (((QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
    ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne c j i : ℚ) : ℝ)) with hx
  set y : ℝ := (fun i => (((QMCLeafB.RelaxOracle.flatQ
      (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
    ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
        (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)) with hy
  have hbig' : |x| ≤ ((lam : ℚ) : ℝ) * y := hbig
  have h1 : -|x| ≤ x := neg_abs_le x
  linarith [hbig', h1]

#print axioms QMCLeafB.RunPartsStream.cast_add_smul
#print axioms QMCLeafB.RunPartsStream.witAt_add_lam
#print axioms QMCLeafB.RunPartsStream.dir_pairing_nonneg

/-! ## 4c.  The ledger denominator is positive, and the `λ`-slots are jointly satisfiable

`hlam2` and `hlam3` are both of the shape `bound ≤ λ·δ_j` with the *same*
`δ_j = flat ones ⬝ witAt (flat ones) j`, so they are not contradictory: `δ_j > 0`
(`dir_wit_pos`) and a single large `λ` satisfies both.  `hcne` is the only condition that can
exclude one particular `λ` (the unique scalar making `c + λ·d` vanish), and it is avoided by
shifting `λ` by one. -/

theorem flatQ_one_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) ≠ 0 := by
  intro h
  have hidx : 0 < n := hn
  have h1 := congrFun h (finProdFinEquiv (⟨0, hidx⟩, ⟨0, hidx⟩))
  simp only [QMCLeafB.RelaxOracle.flatQ, Pi.zero_apply] at h1
  rw [show finProdFinEquiv.symm (finProdFinEquiv (⟨0, hidx⟩, ⟨0, hidx⟩))
      = (⟨0, hidx⟩, ⟨0, hidx⟩) from Equiv.symm_apply_apply _ _] at h1
  simp at h1

/-- **The ledger denominator is strictly positive**: `flat ones ⬝ A⁻¹(flat ones) > 0`. -/
theorem dir_wit_pos (G : Input) (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (j : ℕ) :
    0 < (fun i => (((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
      ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
          (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)) := by
  have hP := QMCLeafB.RunPartsDilate.runShape_posQ G P hn cn hcne j
  have hspec := QMCLeafB.RunPartsDilate.witAt_spec G P hn cn hcne
    (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j
  have hwne : QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
      (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j ≠ 0 := by
    intro hzero
    rw [hzero, Matrix.mulVec_zero] at hspec
    exact flatQ_one_ne_zero (by omega) hspec.symm
  have hqf : 0 < QMCLeafB.EngineIterates.qf
      (QMCLeafB.RunPartsDilate.runShape G P hn cn hcne j)
      (QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
        (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j) :=
    hP.2 _ hwne
  have hcast : (fun i => (((QMCLeafB.RelaxOracle.flatQ
        (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
      ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
          (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))
      = ((QMCLeafB.EngineIterates.qf
          (QMCLeafB.RunPartsDilate.runShape G P hn cn hcne j)
          (QMCLeafB.RunPartsDilate.witAt G P hn cn hcne
            (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j) : ℚ) : ℝ) := by
    rw [dotProduct_comm]
    simp only [QMCLeafB.EngineIterates.qf, dotProduct, Rat.cast_sum, Rat.cast_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [congrFun hspec i]
  rw [hcast]
  exact_mod_cast hqf

/-- **A single large `λ` meets a `λ·δ` bound.** -/
theorem exists_lam_of_pos {δ b : ℚ} (hδ : 0 < δ) (hb : 0 ≤ b) :
    ∃ lam : ℚ, 1 ≤ lam ∧ b ≤ lam * δ := by
  refine ⟨max 1 (b / δ + 1), le_max_left _ _, ?_⟩
  have h1 : b / δ ≤ max 1 (b / δ + 1) := le_trans (le_add_of_nonneg_right zero_le_one)
    (le_max_right _ _)
  have h2 : b / δ * δ = b := by
    field_simp
  have := mul_le_mul_of_nonneg_right h1 hδ.le
  linarith [this, h2]

/-- **`hcne` can be bought for free.**  Among `lam` and `lam + 1` at most one makes `c + lam • d`
vanish, so a `λ` satisfying the bound can always be chosen nonzero-preserving when `d ≠ 0`. -/
theorem exists_lam_avoid {N : ℕ} {δ b : ℚ} {c d : Fin N → ℚ}
    (hδ : 0 < δ) (hb : 0 ≤ b) (hd : d ≠ 0) :
    ∃ lam : ℚ, 1 ≤ lam ∧ b ≤ lam * δ ∧ c + lam • d ≠ 0 := by
  obtain ⟨lam, h1, h2⟩ := exists_lam_of_pos hδ hb
  by_cases hgood : c + lam • d ≠ 0
  · exact ⟨lam, h1, h2, hgood⟩
  · push Not at hgood
    refine ⟨lam + 1, by linarith, ?_, ?_⟩
    · have : lam * δ ≤ (lam + 1) * δ := by nlinarith
      linarith
    · have hzero : c + lam • d = 0 := hgood
      have : c + (lam + 1) • d = d := by
        rw [add_smul, one_smul, ← add_assoc, hzero, zero_add]
      rw [this]
      exact hd

#print axioms QMCLeafB.RunPartsStream.flatQ_one_ne_zero
#print axioms QMCLeafB.RunPartsStream.dir_wit_pos
#print axioms QMCLeafB.RunPartsStream.exists_lam_of_pos
#print axioms QMCLeafB.RunPartsStream.exists_lam_avoid

/-- **The campaign's cut ceiling is at most one** (`rmaxOf N = 1/(4N)`), so `hrmax1` of §5 is
automatic at every order `1 ≤ N`. -/
theorem rmaxOf_le_one {N : ℕ} (hN : 1 ≤ N) : QMCLeafB.RundataHalving.rmaxOf N ≤ 1 := by
  unfold QMCLeafB.RundataHalving.rmaxOf
  rw [div_le_one (by positivity)]
  have h : (1 : ℚ) ≤ (N : ℚ) := by exact_mod_cast hN
  linarith

#print axioms QMCLeafB.RunPartsStream.rmaxOf_le_one


/-! ## 5.  The stream assembly at the shallow parameters

`QMCLeafB.RunPartsDilate.runParts_shallow_dilated` with the dilation direction pinned to the
identity: `dM`, `hdM`, `hbody` are gone, and the two drift hypotheses are replaced by the
program's own rational data (surrogate identification `hq`, bracket ordering `hmu_up`/`hmu_lo`,
direction signs `hpos`, and the budget `hbud`). -/

/-- **`RunParts` at `runParamsShallow` from the program's stream data.** -/
noncomputable def runParts_of_stream_data
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K
        * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (P) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (P) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((P).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - P.dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  have hpos : ∀ j, 0 ≤ dvec ⬝ᵥ QMCLeafB.EngineIterates.cutPR
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j := by
    intro j
    have h := dir_pairing_nonneg G (P) hn cn hcne j
      (c j) (lam j) (hlam0 j) (hlam3 j)
    have heq : QMCLeafB.EngineIterates.cutPR
        (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j
        = (fun i => ((QMCLeafB.RunPartsDilate.witAt G
            (P) hn cn hcne
            (c j + lam j • QMCLeafB.RelaxOracle.flatQ
              (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ)) := by
      funext i
      show ((QMCLeafB.RunPartsShallow.witOf
          (QMCLeafB.RunPartsDilate.runShape_posQ G
            (P) hn cn hcne j) (cn j)) i : ℝ) = _
      rw [hcn j]
      rfl
    rw [hdvec, heq]
    exact h
  refine QMCLeafB.RunPartsDilate.runParts_of_dilated o G t P hn hrmaxPos hbudP ok marg cX
    (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ?_ lam c cn C hmarg hmem hCsym hcEq (fun k _ => hcn k)
    hcne hlam0 ?_ ?_ ?_ hlam1 hlam2 hverdict
  · -- the identity matrix is not zero at `1 ≤ n`
    intro hzero
    have hidx : 0 < G.n := by omega
    have h1 := congrFun (congrFun hzero ⟨0, hidx⟩) ⟨0, hidx⟩
    simp at h1
  · -- `hbody` from the centre's diagonal
    intro k _hok X hX
    have hd' : ∀ i, ((cX k i i : ℚ) : ℝ)
        ≤ 1 - ((P.dq : ℚ) : ℝ) / 4 := by
      intro i
      have h := hdiagc k i
      have h2 : ((1 - P.dq / 4 : ℚ) : ℝ)
          = 1 - ((P.dq : ℚ) : ℝ) / 4 := by
        push_cast
        ring
      calc ((cX k i i : ℚ) : ℝ)
          ≤ ((1 - P.dq / 4 : ℚ) : ℝ) := by exact_mod_cast h
        _ = 1 - ((P.dq : ℚ) : ℝ) / 4 := h2
    simpa using hbody_of_diag_body hd' X hX
  · -- `hdriftc`: the surrogate's budget plus the state's mismatch
    intro k hok
    have hsplit : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k - qSurr k)
          + (qSurr k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hsplit, dotProduct_add]
    have hb := drift_bound_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      (fun i => ((c k i : ℚ) : ℝ)) k mu delta (fun j _ => hmu_lo j)
      (fun j _ => hmu_up j)
    rw [← hqSurr k] at hb
    linarith [hb, hstatec k hok]
  · -- `hdriftd`: the direction's sign, plus the state's mismatch
    intro k hok
    rw [← hdvec]
    have hsplit : QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
          (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k
          - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))
        = (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
            (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) k - qSurr k)
          + (qSurr k
            - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) := by
      abel
    rw [hsplit, dotProduct_add]
    have hb := drift_nonpos_of_upper (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne)
      dvec k (qSurr k) mu (hqSurr k) (fun j _ => hmu_up j) (fun j _ => hpos j)
    linarith [hb, hstated k hok]

#print axioms QMCLeafB.RunPartsStream.runParts_of_stream_data

/-! ## 6.  The dyadic instantiation

`mu`, `delta`, `dvec` are now the actual dyadic quantities the program computes
(`gamQ · invSqrtGe`, its width against `invSqrtLe`, and the identity direction), and the three
bracket hypotheses of §5 are discharged from `CentreTrack.lam_bracket`.  The two remaining checks of
§5 (`hρ ≤ 1`, `σ > 0`) are discharged from `rmaxOf = 1/(4N)` and the engine's own positivity. -/

/-- The dyadic upper surrogate coefficient (the program's rational centre coefficient). -/
noncomputable def muUp (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (grid : ℕ → ℕ)
    (j : ℕ) : ℝ :=
  ((QMCLeafB.CentreTrack.gamQ N cd j
    * DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j) : ℚ) : ℝ)

/-- The width of the dyadic upper bracket (the rational charge of `drift_bound_upper`). -/
noncomputable def deltaUp (N : ℕ) (cd : ℕ → QMCLeafB.EngineIterates.CutData N) (grid : ℕ → ℕ)
    (j : ℕ) : ℝ :=
  ((QMCLeafB.CentreTrack.gamQ N cd j
    * (DQ.invSqrtGe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)
      - DQ.invSqrtLe (QMCLeafB.EngineIterates.sigmaQ (cd j).c (cd j).p) (grid j)) : ℚ) : ℝ)

/-- The identity direction in the engine's flat coordinates (`flat (diagonal ones)`). -/
noncomputable def dOne (n : ℕ) : Fin (n * n) → ℝ :=
  fun i => ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin n) (Fin n) ℚ) i : ℚ) : ℝ)

/-- **`RunParts` at `runParamsShallow` from the concrete dyadic stream data.**  The residual
hypotheses are the program's own records (`C`, `hmarg`, `hmem`, `hcEq`, `hcn`, `hlam1`, `hlam2`,
`hverdict`), the symmetry of its query centres (`hCsym`), the precision choice (`grid`, `hgrid1`),
and the four conditions on the *rational* centre stream that replace `hbody`/`hdriftc`/`hdriftd`:
`hdiagc` (`diag ≤ 1 − dq/4`), `hq` (`flat (centre) = ∑ μ_j p_j`), `hpos`
(`0 ≤ flat ones ⬝ p_j`) and `hbud` (the mirrored rational budget). -/
noncomputable def runParts_shallow_dyadic
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (P : QMCLeafB.FinalStroke.RunParams G)
    (hn : 2 ≤ G.n)
    (hrmaxPos : 0 < P.rmax) (hrmax1 : P.rmax ≤ 1)
    (hbudP : QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G) (3 * P.dq / 4)
      + P.dq / 2 - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (P).K
        * (P).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G) (P.dq))
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (P) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (P) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((P).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (P) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (grid : ℕ → ℕ)
    (hgrid1 : ∀ j, 1 ≤ QMCLeafB.EngineIterates.sigmaQ
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).c
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).p
      * 4 ^ (grid j))
    (hdiagc : ∀ k, ∀ i, (cX k) i i ≤ 1 - P.dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k,
          muUp (G.n * G.n)
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) grid j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (P)
              hn cn hcne) j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (P) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k,
            deltaUp (G.n * G.n)
              (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) grid j
            * max 0
              (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
                (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dOne G.n ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((P).K
        * (P).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (P) := by
  have hN2 : 2 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  have hρ1 : ∀ j, (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne j).rho ≤ 1 := by
    intro j
    rw [QMCLeafB.RunPartsDilate.runCut_rho]
    exact hrmax1
  have hρ0 : ∀ j, (0 : ℚ) ≤ (QMCLeafB.RunPartsDilate.runCut G P hn cn hcne j).rho := by
    intro j
    rw [QMCLeafB.RunPartsDilate.runCut_rho]
    exact P.hrmax
  have hσ : ∀ j, 0 < QMCLeafB.EngineIterates.sigmaQ
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).c
      (QMCLeafB.RunPartsDilate.runCut G (P) hn cn hcne j).p :=
    QMCLeafB.RunPartsShallow.sigmaQ_pos_of_wit hN2
      (QMCLeafB.RunPartsDilate.A0P_posDef G
        (P))
      (QMCLeafB.RunPartsDilate.runCut_wit G
        (P) hn cn hcne)
      hρ0 hcne
  refine runParts_of_stream_data o G t P hn hrmaxPos hrmax1 hbudP ok marg cX lam c cn
    (muUp (G.n * G.n) _ grid) (deltaUp (G.n * G.n) _ grid) (dOne G.n) rfl
    C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2 hdiagc qSurr hqSurr ?_ ?_ hlam3 hstatec hstated hverdict
  · intro j
    exact upper_bracket (G.n * G.n) _ j (grid j) (hρ1 j) (hσ j) (hgrid1 j)
  · intro j
    exact upper_bracket_lo (G.n * G.n) _ j (grid j) (hρ1 j) (hσ j) (hgrid1 j)

#print axioms QMCLeafB.RunPartsStream.runParts_shallow_dyadic

/-! ## 7.  The endgame endpoint at the campaign's own family

The generic assembly instantiated at `QMCLeafB.RundataParams.runParamsShallow`: `K` is the
campaign's `runK`, so this is brick 4's slot at the phase-14 family.  For brick 5's
`paramsShallowKf`/`paramsK` families the same theorem applies directly — they carry
`dq = dqShallow G`, `rmax = rmaxOf (n·n)` by `rfl`, and their own budget. -/

/-- **`RunParts` at `runParamsShallow` (brick 4's slot).** -/
noncomputable def runParts_shallow_concrete
    (o : Input → ℚ → Bool) (G : Input) (t : ℚ) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G)
    (ok : ℕ → Bool) (marg : ℕ → ℚ)
    (cX : ℕ → Matrix (Fin G.n) (Fin G.n) ℚ)
    (lam : ℕ → ℚ) (c cn : ℕ → Fin (G.n * G.n) → ℚ)
    (mu delta : ℕ → ℝ) (dvec : Fin (G.n * G.n) → ℝ)
    (hdvec : dvec = fun i =>
      ((QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) i : ℚ) : ℝ))
    (C : ∀ k, ok k = false →
      QMCLeafB.RelaxOracle.RelaxCut (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G)
        (QMCLeafB.RundataParams.runParamsShallow G hn).dq)
    (hmarg : ∀ k (hok : ok k = false), marg k = (C k hok).margin)
    (hmem : ∀ k, k < (QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m → ok k = true →
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) (cX k)
        (t - QMCLeafB.RundataCert.eps G)
        (QMCLeafB.RundataParams.runParamsShallow G hn).dq)
    (hCsym : ∀ k, (cX k)ᵀ = cX k)
    (hcEq : ∀ k (hok : ok k = false), c k = QMCLeafB.RelaxOracle.flatQ (C k hok).normal)
    (hcn : ∀ k, cn k = c k + lam k • QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ))
    (hcne : ∀ k, cn k ≠ 0)
    (hlam0 : ∀ k, 0 ≤ lam k)
    (hlam1 : ∀ k, ok k = false → 1 ≤ lam k)
    (hlam2 : ∀ k, ok k = false →
      |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k
          + QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
            QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn
              cn hcne (c k) k|
        + |c k ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G
            (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne (c k) k|
        + 9 * marg k ^ 2
            / (4 * ((QMCLeafB.RundataParams.runParamsShallow G hn).rmax) ^ 2) + 1
      ≤ lam k * (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ) ⬝ᵥ
          QMCLeafB.RunPartsDilate.witAt G (QMCLeafB.RundataParams.runParamsShallow G hn) hn
            cn hcne (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) k))
    (hdiagc : ∀ k, ∀ i, (cX k) i i
      ≤ 1 - (QMCLeafB.RundataParams.runParamsShallow G hn).dq / 4)
    (qSurr : ℕ → Fin (G.n * G.n) → ℝ)
    (hqSurr : ∀ k, qSurr k = ∑ j ∈ Finset.range k, mu j •
          QMCLeafB.EngineIterates.cutPR
            (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.RundataParams.runParamsShallow G hn)
              hn cn hcne) j)
    (hmu_up : ∀ j, QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne)
      j ≤ mu j)
    (hmu_lo : ∀ j, mu j - delta j ≤ QMCLeafB.CentreTrack.lam (G.n * G.n)
      (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne)
      j)
    (hlam3 : ∀ j,
      |(fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne (c j) j i : ℚ) : ℝ))|
        ≤ ((lam j : ℚ) : ℝ) * ((fun i => (((QMCLeafB.RelaxOracle.flatQ
            (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) i : ℚ) : ℝ))
          ⬝ᵥ (fun i => ((QMCLeafB.RunPartsDilate.witAt G
              (QMCLeafB.RundataParams.runParamsShallow G hn) hn cn hcne
              (QMCLeafB.RelaxOracle.flatQ (1 : Matrix (Fin G.n) (Fin G.n) ℚ)) j i : ℚ) : ℝ))))
    (hstatec : ∀ k, ok k = false →
      (fun i => ((c k i : ℚ) : ℝ))
          ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k)))
        + ∑ j ∈ Finset.range k, delta j * max 0
            (-((fun i => ((c k i : ℚ) : ℝ)) ⬝ᵥ QMCLeafB.EngineIterates.cutPR
              (QMCLeafB.RunPartsDilate.runCut G (QMCLeafB.RundataParams.runParamsShallow G hn)
                hn cn hcne) j))
          ≤ ((marg k : ℚ) : ℝ) / 2)
    (hstated : ∀ k, ok k = false →
      dvec ⬝ᵥ (qSurr k - QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat (cX k))) ≤ 0)
    (hverdict : o G t = QMCLeafB.SimLoop.anyOk ok
      ((QMCLeafB.RundataParams.runParamsShallow G hn).K
        * (QMCLeafB.RundataParams.runParamsShallow G hn).m)) :
    QMCLeafB.FinalStroke.RunParts o G t
      (QMCLeafB.RundataParams.runParamsShallow G hn) := by
  have hrmax1 : (QMCLeafB.RundataParams.runParamsShallow G hn).rmax ≤ 1 := by
    show QMCLeafB.RundataHalving.rmaxOf (G.n * G.n) ≤ 1
    unfold QMCLeafB.RundataHalving.rmaxOf
    rw [div_le_one (by positivity)]
    have h : (1 : ℚ) ≤ ((G.n * G.n : ℕ) : ℚ) := by
      have h1 : 1 ≤ G.n * G.n := by nlinarith
      exact_mod_cast h1
    linarith
  exact runParts_of_stream_data o G t (QMCLeafB.RundataParams.runParamsShallow G hn) hn
    (QMCLeafB.RunPartsDilate.runParamsShallow_rmax_pos G hn) hrmax1
    (QMCLeafB.RunPartsShallow.runParamsShallow_budget G hn hRq)
    ok marg cX lam c cn mu delta dvec hdvec C hmarg hmem hCsym hcEq hcn hcne hlam0 hlam1 hlam2
    hdiagc qSurr hqSurr hmu_up hmu_lo hlam3 hstatec hstated hverdict

#print axioms QMCLeafB.RunPartsStream.runParts_shallow_concrete

/-! ## 8.  The side conditions at the phase-16 campaign family `paramsK`

Brick 5's family is `HalvePerG.paramsK G (dqShallow G) … Kf hK` (m5's `paramsShallowKf`).  The three
scalar hypotheses of §5 are discharged there in one place, so that instantiating §5 at the campaign
family is the `exact` of one term. -/

/-- **`0 < rmax`, `rmax ≤ 1`, `dq = dqShallow`, and the ok-branch rounding budget, at `paramsK`.** -/
theorem paramsK_side_conditions (G : Input) (hn : 2 ≤ G.n)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) (Kf : ℕ)
    (hKf : QMCLeafB.FinalStroke.budgetRounds G (QMCLeafB.RundataParams.dqShallow G)
      (QMCLeafB.HalvePerG.mHalve (G.n * G.n)) ≤ Kf) :
    0 < (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).rmax
      ∧ (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).rmax ≤ 1
      ∧ (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).dq
          = QMCLeafB.RundataParams.dqShallow G
      ∧ (QMCLeafB.RoundingOut.roundCost (QMCLeafB.Finalization.wMatrixQ G)
          (3 * (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
            (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).dq / 4)
        + (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
            (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).dq / 2
        - QMCLeafB.RundataCert.eps G ≤ QMCLeafB.RundataCert.eps G) := by
  have hN : 1 ≤ G.n * G.n := by
    have h := Nat.mul_le_mul hn hn
    omega
  refine ⟨?_, ?_, rfl, ?_⟩
  · exact QMCLeafB.RundataHalving.rmaxOf_pos (G.n * G.n) hN
  · exact rmaxOf_le_one hN
  · have hdq' : (QMCLeafB.HalvePerG.paramsK G (QMCLeafB.RundataParams.dqShallow G)
        (QMCLeafB.RundataParams.dqShallow_pos G) Kf hKf).dq
        = QMCLeafB.RundataParams.dqShallowCore G :=
      QMCLeafB.RunPartsShallow.dqShallow_eq_core G hRq
    rw [hdq']
    exact QMCLeafB.RundataParams.dqShallow_budget G hn hRq

#print axioms QMCLeafB.RunPartsStream.paramsK_side_conditions

/-! ## 9.  The lower dyadic surrogate really does break `hdriftd` (machine-checked counterexample)

`hdriftd` asks `d ⪝ (Cat k − q_k) ≤ 0`.  With the **lower** bracket
`μ_j = γ_j·invSqrtLe (σ_j) k` every `λ_j − μ_j ≥ 0`, and the surrogate is *admissible* in the sense
of `CentreTrack.drift_bound` (`μ_j ≤ λ_j`).  The one-dimensional instance below shows that the
conclusion nevertheless **fails strictly**: one round with normal `c = 1`, witness `p = 4`, `ρ = 0`
gives `σ = 4`, `λ_0 = 1/4`, `μ_0 < 1/4`, and the drift in the direction `flat ones = 1` is
`1 − 4·μ_0 > 0`.  So the lower bracket is not merely "hard to sign": it makes `hdriftd` false, and
the upper bracket (`γ·invSqrtGe`) is the one that works.
-/


noncomputable def cd1 : ℕ → QMCLeafB.EngineIterates.CutData 1 :=
  fun _ => ⟨fun _ => 1, fun _ => 4, 0⟩

theorem hσ : ∀ j, QMCLeafB.EngineIterates.sigmaQ (cd1 j).c (cd1 j).p = 4 := by
  intro j
  norm_num [cd1, QMCLeafB.EngineIterates.sigmaQ, dotProduct, Fin.sum_univ_one]

theorem hγ : ∀ j, QMCLeafB.CentreTrack.gamQ 1 cd1 j = 1 / 2 := by
  intro j
  norm_num [cd1, QMCLeafB.CentreTrack.gamQ]

theorem hsqrt4 : Real.sqrt 4 = 2 := by
  rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
  norm_num

theorem hinv_lt : ((DQ.invSqrtLe 4 0 : ℚ) : ℝ) < 1 / 2 := by
  have hlt : Real.sqrt 4 < ((DQ.sqrtGe 4 0 : ℚ) : ℝ) := DQ.sqrt_lt_sqrtGe 4 0 (by norm_num)
  rw [hsqrt4] at hlt
  have hpos : (0 : ℝ) < ((DQ.sqrtGe 4 0 : ℚ) : ℝ) := by linarith
  have hinv : ((DQ.invSqrtLe 4 0 : ℚ) : ℝ) = 1 / ((DQ.sqrtGe 4 0 : ℚ) : ℝ) := by
    norm_num [DQ.invSqrtLe]
  rw [hinv, div_lt_iff₀ hpos]
  linarith

theorem hlam : QMCLeafB.CentreTrack.lam 1 cd1 0
    = ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 : ℚ) : ℝ) * (1 / 2) := by
  rw [QMCLeafB.CentreTrack.lam, QMCLeafB.CentreTrack.gammaR_eq_gamQ,
    QMCLeafB.CentreTrack.sqrtSigmaR_eq, hσ 0]
  have h4 : (((4 : ℚ)) : ℝ) = 4 := by norm_num
  rw [h4, hsqrt4]
  ring

theorem hmu_lt : ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe
    (QMCLeafB.EngineIterates.sigmaQ (cd1 0).c (cd1 0).p) 0 : ℚ) : ℝ) < 1 / 4 := by
  rw [hσ 0]
  have hcast : ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe 4 0 : ℚ) : ℝ)
      = ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 : ℚ) : ℝ) * ((DQ.invSqrtLe 4 0 : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hγR : ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 : ℚ) : ℝ) = 1 / 2 := by
    rw [hγ 0]; norm_num
  rw [hγR]
  nlinarith [hinv_lt]

/-- The lower-bracket surrogate coefficient is admissible: it sits below the engine increment. -/
theorem lower_le_lam : ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe
    (QMCLeafB.EngineIterates.sigmaQ (cd1 0).c (cd1 0).p) 0 : ℚ) : ℝ)
    < QMCLeafB.CentreTrack.lam 1 cd1 0 := by
  rw [hlam, hσ 0]
  have hcast : ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe 4 0 : ℚ) : ℝ)
      = ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 : ℚ) : ℝ) * ((DQ.invSqrtLe 4 0 : ℚ) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  have hγ0 : (0 : ℝ) < ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 : ℚ) : ℝ) := by
    rw [hγ 0]; norm_num
  exact mul_lt_mul_of_pos_left hinv_lt hγ0

theorem hCat : QMCLeafB.EngineIterates.Cat 1 (0 : Fin 1 → ℝ) cd1 1 = fun _ => 1 := by
  funext i
  show (0 : Fin 1 → ℝ) i
      + (QMCLeafB.EngineIterates.gammaR 1 ((cd1 0).rho : ℝ)
        / QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd1 0)
          (QMCLeafB.EngineIterates.cutPR cd1 0)) * (QMCLeafB.EngineIterates.cutPR cd1 0) i = 1
  have hs : QMCLeafB.EngineIterates.sqrtSigmaR (QMCLeafB.EngineIterates.cutCR cd1 0)
      (QMCLeafB.EngineIterates.cutPR cd1 0) = 2 := by
    rw [QMCLeafB.CentreTrack.sqrtSigmaR_eq, hσ 0]
    have h4 : (((4 : ℚ)) : ℝ) = 4 := by norm_num
    rw [h4, hsqrt4]
  rw [hs]
  norm_num [QMCLeafB.EngineIterates.gammaR, QMCLeafB.EngineIterates.cutPR, cd1]

/-- With the lower bracket the drift is **strictly positive**: `hdriftd`'s conclusion fails. -/
theorem lower_drift_pos :
    0 < (fun _ => (1 : ℝ)) ⬝ᵥ
      (QMCLeafB.EngineIterates.Cat 1 (0 : Fin 1 → ℝ) cd1 1
        - ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe
            (QMCLeafB.EngineIterates.sigmaQ (cd1 0).c (cd1 0).p) 0 : ℚ) : ℝ)
          • QMCLeafB.EngineIterates.cutPR cd1 0) := by
  have hmu := hmu_lt
  rw [hCat]
  have hp : QMCLeafB.EngineIterates.cutPR cd1 0 = fun _ => (4 : ℝ) := by
    funext i
    norm_num [QMCLeafB.EngineIterates.cutPR, cd1]
  rw [hp]
  simp only [dotProduct, Fin.sum_univ_one, Pi.sub_apply, Pi.smul_apply,
    one_mul, smul_eq_mul]
  linarith


#print axioms QMCLeafB.RunPartsStream.lower_le_lam
#print axioms QMCLeafB.RunPartsStream.lower_drift_pos

/-- **The headline of §9.**  The lower dyadic surrogate coefficient is *admissible*
(`μ_0 < λ_0`, so `CentreTrack.drift_bound`'s ordering holds) and yet `hdriftd`'s conclusion is
strictly false at the same state. -/
theorem lower_surrogate_breaks_hdriftd :
    ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe
        (QMCLeafB.EngineIterates.sigmaQ (cd1 0).c (cd1 0).p) 0 : ℚ) : ℝ)
        < QMCLeafB.CentreTrack.lam 1 cd1 0
      ∧ 0 < (fun _ => (1 : ℝ)) ⬝ᵥ
          (QMCLeafB.EngineIterates.Cat 1 (0 : Fin 1 → ℝ) cd1 1
            - ((QMCLeafB.CentreTrack.gamQ 1 cd1 0 * DQ.invSqrtLe
                (QMCLeafB.EngineIterates.sigmaQ (cd1 0).c (cd1 0).p) 0 : ℚ) : ℝ)
              • QMCLeafB.EngineIterates.cutPR cd1 0) :=
  ⟨lower_le_lam, lower_drift_pos⟩

#print axioms QMCLeafB.RunPartsStream.lower_surrogate_breaks_hdriftd

end QMCLeafB.RunPartsStream



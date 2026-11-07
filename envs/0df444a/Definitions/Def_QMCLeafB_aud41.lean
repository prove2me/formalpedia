-- Prove2me | Definitions.Def_QMCLeafB_aud41
-- name    : QMCLeafB_aud41
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:58:35.897763+00:00
-- url     : https://prove2.me/theorems/e9a033a3-c258-4dbf-942f-8f4b9680ffc7
-- title:
--   QMCLeafB aud41
-- statement:
--   # `Check_aud41_m7` — phase 41, member m7, direction d3 (`audit41`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_rn40
import Definitions.Def_QMCLeafB_fa39
import Definitions.Def_QMCLeafB_ss40
/-
# `Check_aud41_m7` — phase 41, member m7, direction d3 (`audit41`)

**Task.** Recompile and receipt-check the four loaded bundles the (B) route rests on
(`Check_aud36_m6`, `Check_rn40_m4`, `Check_fa39_m4`, `Check_ss40_m3`), and then state, machine-check
and lock the exact interface the surviving route needs.  No reconstruction of the programme.

**What this file adds (all machine-checked; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`).**

* **§1 the ball in `Thin` is a ball in `hcut`'s OWN body.**  `BallM2.runBall`, `relaxBallP` and the
  set `RunParts.hcut` quantifies over are the same term, by `rfl`.  So the `¬Thin` witness of
  `no_runParts_of_ball_gen` really is a witness for the record's own `hcut` body: coordinator step 3
  is not a scope slip.
* **§2 `¬Thin` unpacked** into exactly `no_runParts_of_ball_gen`'s hypotheses.
* **§3 THE (B) REDUCTION.**  `bit_true_off_thin_of_record`: if the bit is `false` only at points that
  admit a record, then the bit is `true` at every non-`Thin` body (`2 ≤ G.n`).  This is verbatim the
  `(B)` binder of `Fa39M4.selfRecG_of_thin_sep` — so (B) is *exactly* "no bit-false body admits a
  record", nothing more, and the whole content of (B) is in the construction of that record.
* **§4 (B) from `SelfRecG`'s own object.**  `ThinRec34M4.BodyRec` at a bit-false point *is*
  `Nonempty (RunParts o G t P)` (`runParts_false_iff_bodyRec`), so the hypothesis of §3 is a
  restriction of `SelfRecG` — no `hverdict` and no programme is needed for the implication.
* **§5 step 2's verdict field is FREE.**  `SimLoop.anyOk (fun _ => false) N = false` for every `N`,
  so a constant-false all-cut stream satisfies `RunParts.hverdict` against `fun _ _ => false` with no
  side condition.  `hwit`/`hcheck`/`hcut` are then the ONLY live fields.
* **§6 THE PRICE BRIDGE.**  A cut supplied by a support at the round's own STATE `x k`, with price
  `c k ⬝ (Cat k − x k) ≤ del k`, *is* a `hcut` field.  This names the exact inequality the
  programme must produce: nothing else is missing.
* **§7 round 0 is free**: `Cat k` starts at `0`, so at `k = 0` the price is `c 0 ⬝ (0 − x 0)`, and it
  vanishes exactly when the round-0 state is `0`.  The price obstruction is a `k ≥ 1` phenomenon.
* **§8 the price ratio is scale-invariant.**  `(c, p) ↦ (λ c, λ p)` (`λ > 0`) keeps `A p = c` *and*
  keeps `c ⬝ (a − x) ≤ ρ √σ` true, since `σ ↦ λ²σ`.  So the normalisation of the support normal is a
  free parameter and cannot be used to buy the price.
* **§9 THE LEDGER DOES NOT FORCE `del ≡ 0`.**  Correction to the phase-40 map: `hcheck` + `hdel0`
  admit `del = ρ√σ > 0` (`hcheck_at_slack`, `del_pos_admissible`); what `Ss40M3.slack_no_reuse` kills
  is the *reuse of the same normal*, not positive slack.  `del = 0` is forced only by `ρ = 0`.
-/

set_option autoImplicit false

namespace QMCLeafB.Aud41M7

open QMCLeafB

/-! ## §1 The `Thin` ball is a ball in `hcut`'s own body -/

/-- `BallM2.runBall` and `ThinRec34M4.relaxBallP` are the same set (both are `rfl` to the relaxation
that `RunParts.hcut` quantifies over). -/
theorem runBall_eq_relaxBallP (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : FinalStroke.RunParams G) :
    BallM2.runBall G t P = ThinRec34M4.relaxBallP G t P := rfl

/-- The set `RunParts.hcut` quantifies over, spelled exactly as `RunParts.hcut` spells it. -/
theorem runBall_eq_hcutBody (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : FinalStroke.RunParams G) :
    BallM2.runBall G t P
      = Boundary.relaxBall (wMatrix G) ((t : ℝ) - ((EngineRuntime.Rq G / 40000 : ℚ) : ℝ))
          (P.dq : ℝ) (((2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 : ℚ)) : ℝ) := rfl

/-! ## §2 `¬Thin` unpacked into the ball obstruction's own hypotheses -/

/-- The negation of `Fa39M4.Thin` **is** the hypothesis pair of `Aud36M6.bit_true_of_ball_gen`. -/
theorem exists_ball_of_notThin {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : FinalStroke.RunParams G} (h : ¬ Fa39M4.Thin G t P) :
    ∃ (X₀ : Matrix (Fin G.n) (Fin G.n) ℝ) (r : ℝ),
      0 < r ∧ Boundary.eucBallF (AnswerProducer.flat X₀) r ⊆ BallM2.runBall G t P ∧
        EngineIterates.volPot (G.n * G.n)
            (Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)) *
            (1 / 2) ^ P.K
          < r ^ (G.n * G.n) := by
  simp only [Fa39M4.Thin, not_forall, not_le] at h
  obtain ⟨X₀, r, hr, hsub, hvol⟩ := h
  exact ⟨X₀, r, hr, hsub, hvol⟩

/-! ## §3 THE (B) REDUCTION

If the bit is `false` only at points which admit a record, then the bit is `true` at every non-`Thin`
body.  The conclusion is verbatim the `(B)` binder of `Fa39M4.selfRecG_of_thin_sep`. -/

theorem bit_true_off_thin_of_record
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (hrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      Nonempty (FinalStroke.RunParts o G t (P G))) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ Fa39M4.Thin G t (P G) →
      o G t = true := by
  intro G t hn hthin
  obtain ⟨X₀, r, hr, hsub, hvol⟩ := exists_ball_of_notThin hthin
  refine Aud36M6.bit_true_of_ball_gen hn hr hsub hvol ?_
  intro hofalse
  exact hrec G t hofalse

/-! ## §4 (B) from the record object `SelfRecG` already asks for

`ThinRec34M4.BodyRec G t P` is `Nonempty (RunParts falseBit G t P)`, and at a bit-false point that is
`Nonempty (RunParts o G t P)` for the *programme's own* bit — so the hypothesis of §3 is precisely a
record at the bit-false point.  No `hverdict`, no programme: this is a pure implication. -/

/-- A record at a bit-false point, in the programme's own bit. -/
theorem nonempty_runParts_of_bodyRec {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : FinalStroke.RunParams G}
    (ho : o G t = false) (h : ThinRec34M4.BodyRec G t P) :
    Nonempty (FinalStroke.RunParts o G t P) :=
  (ThinRec34M4.runParts_false_iff_bodyRec ho).mpr h

/-- **(B) from `SelfRecG`'s own body-record demand.**  At a bit-false point a `BodyRec` exists (or
the point is not in the bracket), hence the contract of `bit_true_off_thin_of_record` is met. -/
theorem bit_true_off_thin_of_bodyRecAtFalse
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (h : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      ThinRec34M4.BodyRec G t (P G)) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ Fa39M4.Thin G t (P G) →
      o G t = true :=
  bit_true_off_thin_of_record o P fun G t ho => nonempty_runParts_of_bodyRec ho (h G t ho)

/-! ## §5 Step 2's `hverdict` field is free for a constant-false all-cut stream -/

theorem anyOk_false (N : ℕ) : SimLoop.anyOk (fun _ : ℕ => false) N = false := by
  induction N with
  | zero => rfl
  | succ k ih => rw [SimLoop.anyOk_succ]; simp [ih]

/-- The `RunParts.hverdict` field at `o := fun _ _ => false` and `ok := fun _ => false`. -/
theorem hverdict_allcut (G : QuantumMaxCutEnergy.Input) (t : ℚ)
    (P : FinalStroke.RunParams G) :
    (fun _ _ => false : QuantumMaxCutEnergy.Input → ℚ → Bool) G t
      = SimLoop.anyOk (fun _ : ℕ => false) (P.K * P.m) := by
  rw [anyOk_false]

/-! ## §6 THE PRICE BRIDGE

`RunParts.hcut` is stated at the record's accumulated point `Cat k`, while a support supplied by
`Rn40M4.exists_rat_support` at the round's own STATE `x k` reads `0 ≤ c k ⬝ (z − x k)`.  The two differ
by exactly the **price** `c k ⬝ (Cat k − x k)`: a support at the state plus `price ≤ del k` *is* the
`hcut` field.  This is the only inequality separating "the programme's cut" from "`RunParts.hcut`". -/

theorem hcut_of_state_support {n : ℕ} {cd : ℕ → EngineIterates.CutData n}
    {x : ℕ → (Fin n → ℝ)} {del : ℕ → ℝ} {S : Set (Fin n → ℝ)}
    (hsup : ∀ k, ∀ z ∈ S, 0 ≤ EngineIterates.cutCR cd k ⬝ᵥ (z - x k))
    (hprice : ∀ k,
      EngineIterates.cutCR cd k ⬝ᵥ (EngineIterates.Cat n 0 cd k - x k) ≤ del k) :
    ∀ k, ∀ z ∈ S,
      -del k ≤ EngineIterates.cutCR cd k ⬝ᵥ (z - EngineIterates.Cat n 0 cd k) := by
  intro k z hz
  have hz_eq : z - EngineIterates.Cat n 0 cd k
      = (z - x k) + (x k - EngineIterates.Cat n 0 cd k) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have hneg_eq : x k - EngineIterates.Cat n 0 cd k
      = -(EngineIterates.Cat n 0 cd k - x k) := by
    ext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hz_eq, dotProduct_add, hneg_eq, dotProduct_neg]
  linarith [hsup k z hz, hprice k]

/-! ## §7 Round 0 carries no price -/

/-- The accumulated centre starts at the engine's own origin. -/
theorem Cat_zero (n : ℕ) (cd : ℕ → EngineIterates.CutData n) :
    EngineIterates.Cat n (0 : Fin n → ℝ) cd 0 = 0 := rfl

/-- At `k = 0` the price is exactly `c 0 ⬝ (0 − x 0)`; a round-0 state at the origin pays nothing. -/
theorem price_zero_at_origin_state {n : ℕ} {cd : ℕ → EngineIterates.CutData n}
    {x : ℕ → (Fin n → ℝ)} (hx : x 0 = 0) :
    EngineIterates.cutCR cd 0 ⬝ᵥ (EngineIterates.Cat n 0 cd 0 - x 0) = 0 := by
  rw [Cat_zero, hx, sub_self, dotProduct_zero]

/-! ## §8 The price ratio is invariant under rescaling the normal

`hwit` is `A p = c` and `hcheck` is `del² ≤ ρ² (c ⬝ p)`.  Replacing `(c, p)` by `(λ c, λ p)` keeps
`A p = c`, multiplies `σ = c ⬝ p` by `λ²`, hence multiplies both sides of the price condition
`c ⬝ (a − x) ≤ ρ √σ` by `λ > 0`.  So the normalisation of a support normal is free and cannot be
used to buy the price. -/

theorem sigmaR_smul {n : ℕ} (lam : ℝ) (c p : Fin n → ℝ) :
    EngineIterates.sigmaR (lam • c) (lam • p) = lam ^ 2 * EngineIterates.sigmaR c p := by
  simp only [EngineIterates.sigmaR, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sqrtSigmaR_smul {n : ℕ} {lam : ℝ} (hlam : 0 ≤ lam) (c p : Fin n → ℝ) :
    EngineIterates.sqrtSigmaR (lam • c) (lam • p) = lam * EngineIterates.sqrtSigmaR c p := by
  simp only [EngineIterates.sqrtSigmaR, sigmaR_smul]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg hlam]

theorem dot_smul_left {n : ℕ} (lam : ℝ) (c v : Fin n → ℝ) :
    (lam • c) ⬝ᵥ v = lam * (c ⬝ᵥ v) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The price bound is scale-invariant**: rescaling `(c, p)` by `λ > 0` does not change whether the
support normal can pay the price. -/
theorem price_bound_smul_iff {n : ℕ} {c p a x : Fin n → ℝ} {rho lam : ℝ} (hlam : 0 < lam) :
    (c ⬝ᵥ (a - x) ≤ rho * EngineIterates.sqrtSigmaR c p) ↔
      ((lam • c) ⬝ᵥ (a - x) ≤ rho * EngineIterates.sqrtSigmaR (lam • c) (lam • p)) := by
  rw [sqrtSigmaR_smul (le_of_lt hlam), dot_smul_left,
    show rho * (lam * EngineIterates.sqrtSigmaR c p)
      = lam * (rho * EngineIterates.sqrtSigmaR c p) from by ring]
  exact mul_le_mul_iff_of_pos_left hlam |>.symm

/-- And the witness relation survives the rescaling. -/
theorem witness_smul_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {c p : Fin n → ℝ}
    {lam : ℝ} (hlam : lam ≠ 0) :
    A.mulVec (lam • p) = lam • c ↔ A.mulVec p = c := by
  rw [Matrix.mulVec_smul]
  constructor
  · intro h
    have h' := congrArg (fun v => lam⁻¹ • v) h
    simpa [smul_smul, inv_mul_cancel₀ hlam] using h'
  · intro h
    rw [h]

/-! ## §9 THE LEDGER DOES NOT FORCE `del ≡ 0`

Phase 40's map records "`del ≡ 0` IS FORCED for any iterated record".  Read literally against the
`RunParts` ledger that is false: `hdel0` and `hcheck` admit `del = ρ√σ`, which is positive whenever
`ρ > 0` and `σ > 0`.  What `Ss40M3.del_zero_of_rho_zero` forces is `del = 0` at `ρ = 0` (restated
here), and what `Ss40M3.slack_no_reuse` kills is *reuse of the same normal* after spending slack —
not positive slack on a fresh normal.  So a positive price is ledger-legal, and the price gate is
exactly `c k ⬝ (Cat k − x k) ≤ ρ k √σ k` with `ρ k ≤ P.rmax`. -/

/-- The ledger's own slack is admissible: `del = ρ√σ` satisfies `hdel0` and `hcheck` with equality. -/
theorem hcheck_at_slack {sigma rho : ℝ} (hsigma : 0 ≤ sigma) (hrho : 0 ≤ rho) :
    0 ≤ rho * Real.sqrt sigma ∧ (rho * Real.sqrt sigma) ^ 2 ≤ rho ^ 2 * sigma := by
  refine ⟨mul_nonneg hrho (Real.sqrt_nonneg sigma), ?_⟩
  rw [mul_pow, Real.sq_sqrt hsigma]

/-- Positive slack is genuinely available to a legal round: `ρ > 0` and `σ > 0` admit `del > 0`. -/
theorem del_pos_admissible {sigma rho : ℝ} (hsigma : 0 < sigma) (hrho : 0 < rho) :
    ∃ del : ℝ, 0 < del ∧ del ^ 2 ≤ rho ^ 2 * sigma := by
  refine ⟨rho * Real.sqrt sigma / 2, ?_, ?_⟩
  · have := Real.sqrt_pos.mpr hsigma
    positivity
  · have hsq : (rho * Real.sqrt sigma / 2) ^ 2 = rho ^ 2 * sigma / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (le_of_lt hsigma)]; ring
    rw [hsq]
    have := mul_pos (mul_pos hrho hrho) hsigma
    linarith

/-! ## §10 The price budget, exactly

`hcheck` + `hle` bound the ledger's own slack by `rmax·√σ`, and `hcut` charges the price against it.
So the price gate on the programme is the single inequality

  `c k ⬝ (Cat k − x k)  ≤  P.rmax * √(c k ⬝ p k)`,

with `σ k = c k ⬝ p k`, `Aat k p k = c k`.  By §8 the left-to-`√σ` ratio is invariant under rescaling
`(c, p)`, so this is a genuine geometric condition, not an artefact of normalisation. -/

theorem del_le_rmax_sqrtSigma {del rho rmax sigma : ℝ}
    (hchk : del ^ 2 ≤ rho ^ 2 * sigma) (hrho : 0 ≤ rho) (hle : rho ≤ rmax)
    (hsigma : 0 ≤ sigma) :
    del ≤ rmax * Real.sqrt sigma := by
  have hX : 0 ≤ rho * Real.sqrt sigma := mul_nonneg hrho (Real.sqrt_nonneg sigma)
  have hsq : (rho * Real.sqrt sigma) ^ 2 = rho ^ 2 * sigma := by
    rw [mul_pow, Real.sq_sqrt hsigma]
  have h1 : del ≤ rho * Real.sqrt sigma := by nlinarith [hchk, hsq, hX]
  have h2 : rho * Real.sqrt sigma ≤ rmax * Real.sqrt sigma :=
    mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg sigma)
  linarith

/-! ## §11 Assembly: (B) + the Thin separation close `SelfRecG`

The two things the swarm is building now compose.  `record_at_false` here is the *only* input that is
not already banked, and by §3–§4 it is precisely what (B) is equivalent to. -/

theorem selfRecG_of_record_and_thinSep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), o G t = false →
      Nonempty (FinalStroke.RunParts o G t (P G)))
    (hsep : Fa39M4.ThinSep P c hc) :
    Asm36M8.SelfRecG o P :=
  Fa39M4.selfRecG_of_thin_sep o P c hc (bit_true_off_thin_of_record o P hrec) hsep

/-- The same assembly with the record supplied in `BodyRec` form at the bracket, which is the shape
`SelfRecG` itself asks for. -/
theorem selfRecG_of_bodyRec_and_thinSep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → o G t = false →
      ThinRec34M4.BodyRec G t (P G))
    (hsep : Fa39M4.ThinSep P c hc) :
    Asm36M8.SelfRecG o P := by
  refine Fa39M4.selfRecG_of_thin_sep o P c hc ?_ hsep
  intro G t hn hthin
  obtain ⟨X₀, r, hr, hsub, hvol⟩ := exists_ball_of_notThin hthin
  refine Aud36M6.bit_true_of_ball_gen hn hr hsub hvol ?_
  intro ho
  exact nonempty_runParts_of_bodyRec ho (hrec G t hn ho)

/-! ## §12 Locks

* `hcut_runs_on_runBall`: the body `RunParts.hcut` quantifies over is `BallM2.runBall` — the very set
  whose balls make a body non-`Thin`.  So `¬Thin` is a statement about the record's OWN constraint
  set, and coordinator step 3 is not a scope slip.
* `thinSlot_iff`: the (B) predicate, locked. -/

theorem hcut_runs_on_runBall {o : QuantumMaxCutEnergy.Input → ℚ → Bool}
    {G : QuantumMaxCutEnergy.Input} {t : ℚ} {P : FinalStroke.RunParams G}
    (B : FinalStroke.RunParts o G t P) (k : ℕ) (hk : k < P.K * P.m) (hok : B.ok k = false) :
    ∀ z, z ∈ BallM2.runBall G t P →
      -(((B.del k : ℚ)) : ℝ)
        ≤ EngineIterates.cutCR B.cd k
            ⬝ᵥ (z - EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) B.cd k) :=
  fun z hz => B.hcut k hk hok z hz

/-- The `(B)` predicate in the exact shape `Fa39M4.selfRecG_of_thin_sep` consumes. -/
def ThinSlot (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ Fa39M4.Thin G t (P G) → o G t = true

theorem thinSlot_iff (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G) :
    ThinSlot o P ↔
      ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → ¬ Fa39M4.Thin G t (P G) →
        o G t = true :=
  Iff.rfl

/-- **Statement lock on the surviving route**: `ThinSlot` is exactly the `(B)` binder of
`selfRecG_of_thin_sep`, so (B) plus `ThinSep` is `SelfRecG` — nothing else. -/
theorem selfRecG_of_thinSlot_and_thinSep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hB : ThinSlot o P) (hsep : Fa39M4.ThinSep P c hc) :
    Asm36M8.SelfRecG o P :=
  Fa39M4.selfRecG_of_thin_sep o P c hc ((thinSlot_iff o P).mp hB) hsep

/-! ## §14 The bracket-restricted route

`Fa39M4.selfRecG_of_thin_sep` asks for `(B)` and `ThinSep` at **every** `t : ℚ`, while `SelfRecG` —
the only thing the leaf consumes — asks only at the leaf's bracket
`-Rq G ≤ t < -Rq G / 40000`.  Since the banked proof is pointwise, both binders restrict to the
bracket at no cost.  This matters: the phase-39 refutation of `SepStream` was precisely the UNBOUNDED
`t`-quantifier (`witness_not_in_bracket`), so a concrete programme must not be asked for a global
`t`-statement it cannot have.  A global `(B)` at `t > 0` or `t < -Rq G` is not needed and not
plausibly available. -/

/-- `(B)` restricted to the leaf's own bracket. -/
def ThinSlotBracket (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → -EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → ¬ Fa39M4.Thin G t (P G) →
      o G t = true

/-- `ThinSep` restricted to the leaf's own bracket. -/
def ThinSepBracket (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0) : Prop :=
  ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n), -EngineRuntime.Rq G ≤ t →
    (t : ℝ) < -(((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → Fa39M4.Thin G t (P G) →
      ∀ k < (P G).K * (P G).m, ∀ z ∈ ThinRec34M4.relaxBallP G t (P G),
        (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ
            EngineIterates.Cat (G.n * G.n) 0
              (ThinRec34M4.NormalCut G (P G) hn (c G t) (hc G t)) k
          ≤ (fun i => (((c G t k) i : ℚ) : ℝ)) ⬝ᵥ z

/-- The global binders of the banked route imply the bracket-restricted ones. -/
theorem thinSlotBracket_of_thinSlot (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (h : ThinSlot o P) : ThinSlotBracket o P :=
  fun G t hn _ _ => h G t hn

theorem thinSepBracket_of_thinSep (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (h : Fa39M4.ThinSep P c hc) : ThinSepBracket P c hc :=
  fun G t hn _ _ => h G t hn

/-- **The leaf's route on bracket-restricted hypotheses only.**  `(B)` and `(S')` are asked for exactly
where `SelfRecG` consumes them and nowhere else. -/
theorem selfRecG_of_bracket_thinSlot_and_thinSep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hB : ThinSlotBracket o P) (hsep : ThinSepBracket P c hc) :
    Asm36M8.SelfRecG o P := by
  intro G t hn hlo hlt hb
  by_cases ht : Fa39M4.Thin G t (P G)
  · exact Fa39M4.bodyRec_of_sep hn (c G t) (hc G t) (hsep G t hn hlo hlt ht)
  · exact absurd (hB G t hn hlo hlt ht) (by rw [hb]; simp)

/-- The (B) reduction, bracket-restricted: a record at the bracket's bit-`false` points already forces
the bit `true` at the bracket's non-`Thin` bodies.  (The global §3 statement needs the record
everywhere; the leaf only ever uses it at the point under test, so the bracket form is what a
programme can supply.) -/
theorem bit_true_off_thin_of_record_bracket
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (hrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → -EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → o G t = false →
        Nonempty (FinalStroke.RunParts o G t (P G))) :
    ThinSlotBracket o P := by
  intro G t hn hlo hlt hthin
  obtain ⟨X₀, r, hr, hsub, hvol⟩ := exists_ball_of_notThin hthin
  refine Aud36M6.bit_true_of_ball_gen hn hr hsub hvol ?_
  intro hofalse
  exact hrec G t hn hlo hlt hofalse

/-- **THE END-TO-END INTERFACE.**  `SelfRecG` — hence, through `Asm36M8.solution_of_two_slots_selfRec`,
the leaf — follows from exactly two bracket-restricted hypotheses:

* a `RunParts` record at every BIT-`FALSE` bracket point (`hrec`), and
* the Thin separation at the bracket (`hsep`).

`hrec` is what the all-cut/price direction must produce (by §6 the only missing field is the price
`c k ⬝ (Cat k − x k) ≤ ρ k √σ k`, and by §7 round 0 pays nothing).  `hsep` is the (S') slot.  No
global-`t` statement is needed anywhere. -/
theorem selfRecG_of_bracket_record_and_thinSep
    (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (P : (G : QuantumMaxCutEnergy.Input) → FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hrec : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → -EngineRuntime.Rq G ≤ t →
      (t : ℝ) < -(((EngineRuntime.Rq G / 40000 : ℚ)) : ℝ) → o G t = false →
        Nonempty (FinalStroke.RunParts o G t (P G)))
    (hsep : ThinSepBracket P c hc) :
    Asm36M8.SelfRecG o P :=
  selfRecG_of_bracket_thinSlot_and_thinSep o P c hc
    (bit_true_off_thin_of_record_bracket o P hrec) hsep

/-- **THE PROGRAMME ⟹ LEDGER PACKAGE.**  A cut that is a support at the round's own state `x k` and
whose price is inside the round's depth budget `ρ k·√σ k` yields `RunParts.hdel0`, `RunParts.hcheck`
and `RunParts.hcut` simultaneously — with `del k := max (price k) 0`, so a *negative* price is free and
only the excess over `ρ k·√σ k` obstructs.  (Combined with `hverdict_allcut` (§5) this leaves `hwit`
as the only other live field of step 2.) -/
theorem exists_del_of_state_support
    {n : ℕ} {cd : ℕ → EngineIterates.CutData n} {x : ℕ → (Fin n → ℝ)}
    {S : Set (Fin n → ℝ)} {rho : ℕ → ℝ} {sigma : ℕ → ℝ}
    (hsup : ∀ k, ∀ z ∈ S, 0 ≤ EngineIterates.cutCR cd k ⬝ᵥ (z - x k))
    (hprice : ∀ k,
      EngineIterates.cutCR cd k ⬝ᵥ (EngineIterates.Cat n 0 cd k - x k)
        ≤ rho k * Real.sqrt (sigma k))
    (hrho : ∀ k, 0 ≤ rho k) (hsigma : ∀ k, 0 ≤ sigma k) :
    ∃ del : ℕ → ℝ, (∀ k, 0 ≤ del k) ∧
      (∀ k, del k ^ 2 ≤ rho k ^ 2 * sigma k) ∧
      ∀ k, ∀ z ∈ S,
        -del k ≤ EngineIterates.cutCR cd k ⬝ᵥ (z - EngineIterates.Cat n 0 cd k) := by
  refine ⟨fun k => max (EngineIterates.cutCR cd k
      ⬝ᵥ (EngineIterates.Cat n 0 cd k - x k)) 0, fun k => le_max_right _ _,
    fun k => ?_, fun k z hz => ?_⟩
  · have hb : 0 ≤ rho k * Real.sqrt (sigma k) := mul_nonneg (hrho k) (Real.sqrt_nonneg _)
    have h1 : max (EngineIterates.cutCR cd k
        ⬝ᵥ (EngineIterates.Cat n 0 cd k - x k)) 0 ≤ rho k * Real.sqrt (sigma k) :=
      max_le (hprice k) hb
    have hsq : (rho k * Real.sqrt (sigma k)) ^ 2 = rho k ^ 2 * sigma k := by
      rw [mul_pow, Real.sq_sqrt (hsigma k)]
    nlinarith [le_max_right (EngineIterates.cutCR cd k
      ⬝ᵥ (EngineIterates.Cat n 0 cd k - x k)) 0, h1, hsq]
  · exact hcut_of_state_support hsup (fun k => le_max_left _ _) k z hz

end QMCLeafB.Aud41M7

/-! ## §13 Receipts -/

#print axioms QMCLeafB.Aud41M7.runBall_eq_relaxBallP
#print axioms QMCLeafB.Aud41M7.runBall_eq_hcutBody
#print axioms QMCLeafB.Aud41M7.exists_ball_of_notThin
#print axioms QMCLeafB.Aud41M7.bit_true_off_thin_of_record
#print axioms QMCLeafB.Aud41M7.nonempty_runParts_of_bodyRec
#print axioms QMCLeafB.Aud41M7.bit_true_off_thin_of_bodyRecAtFalse
#print axioms QMCLeafB.Aud41M7.anyOk_false
#print axioms QMCLeafB.Aud41M7.hverdict_allcut
#print axioms QMCLeafB.Aud41M7.hcut_of_state_support
#print axioms QMCLeafB.Aud41M7.Cat_zero
#print axioms QMCLeafB.Aud41M7.price_zero_at_origin_state
#print axioms QMCLeafB.Aud41M7.sigmaR_smul
#print axioms QMCLeafB.Aud41M7.sqrtSigmaR_smul
#print axioms QMCLeafB.Aud41M7.dot_smul_left
#print axioms QMCLeafB.Aud41M7.price_bound_smul_iff
#print axioms QMCLeafB.Aud41M7.witness_smul_iff
#print axioms QMCLeafB.Aud41M7.hcheck_at_slack
#print axioms QMCLeafB.Aud41M7.del_pos_admissible
#print axioms QMCLeafB.Aud41M7.del_le_rmax_sqrtSigma
#print axioms QMCLeafB.Aud41M7.selfRecG_of_record_and_thinSep
#print axioms QMCLeafB.Aud41M7.selfRecG_of_bodyRec_and_thinSep
#print axioms QMCLeafB.Aud41M7.hcut_runs_on_runBall
#print axioms QMCLeafB.Aud41M7.thinSlot_iff
#print axioms QMCLeafB.Aud41M7.selfRecG_of_thinSlot_and_thinSep
#print axioms QMCLeafB.Aud41M7.thinSlotBracket_of_thinSlot
#print axioms QMCLeafB.Aud41M7.thinSepBracket_of_thinSep
#print axioms QMCLeafB.Aud41M7.selfRecG_of_bracket_thinSlot_and_thinSep
#print axioms QMCLeafB.Aud41M7.bit_true_off_thin_of_record_bracket
#print axioms QMCLeafB.Aud41M7.selfRecG_of_bracket_record_and_thinSep
#print axioms QMCLeafB.Aud41M7.exists_del_of_state_support



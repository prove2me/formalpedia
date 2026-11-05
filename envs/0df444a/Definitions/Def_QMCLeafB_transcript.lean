-- Prove2me | Definitions.Def_QMCLeafB_transcript
-- name    : QMCLeafB_transcript
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T13:59:11.878785+00:00
-- url     : https://prove2.me/theorems/25a37060-e591-488c-9ebd-cfec340be273
-- title:
--   QMCLeafB transcript
-- statement:
--   # leaf B phase 30 — the transcript pairing (swarm `smw239r00`, member m3, direction d4)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_EngineIterates
import Definitions.Def_QMCLeafB_final_stroke_m7
/-
# leaf B phase 30 — the transcript pairing (swarm `smw239r00`, member m3, direction d4)

The question the whole `hd` lane keys on: can a record class (a stream of `CutData` plus `ok` flags)
satisfy `RunParts.hcut`'s pairing against the **accumulated transcript centre** `Cat k`?  This file
answers it with four machine-checked receipts and states the exact residual.

## The answer (short)

`Cat k` advances by `(γ/√σ) • p` with `γ = (1−ρ)/(n+1)` rational, `σ = c ⠂ p` rational and `√σ`
irrational in general (§1: `Cat_succ`, definitional).  So:

* **the frozen escape is empty** — `p ≡ 0` freezes `Cat` at its start (§2 `stepCentre_zero`,
  `Cat_eq_zero_of_p_zero`), but `hwit` (`Aat · p = c`) plus `hcne` (`c ≠ 0`) force `p ≠ 0` at every
  cut round (§2 `p_ne_zero_of_hwit`), and then the centre really moves (§2 `Cat_succ_moves`);
* **a rational transcript must be square-class** — if two consecutive transcript centres are casts
  of rational points (`flat (castMat cX)` is exactly such a point), then `σ = c ⬂ p` is the square of
  a rational (§3 `sigma_square_of_rat_transcript`).  Since `σ = (A p) ⬂ p` under `hwit` and scaling
  `p` by a rational does not change the square class, this is a genuine arithmetic constraint on the
  recorded eigendata, not a free choice;
* **the universal route costs the drift** — a cut certified at a *surrogate* real point `q`
  (typically the cast of a rational, i.e. the oracle's own centre) yields `hcut`'s inequality at the
  true `Cat k` with the recorded margin raised by `(∑ᵢ |cᵢ|) · supᵢ |Cat k ᵢ − qᵢ|` (§4
  `hcut_of_surrogate`).  `RunParts.hcheck` (`del² ≤ ρ² σ`) then bounds the admissible drift.

**Verdict**: the pairing composes through the surrogate route at *every* body (empty or not — the
pairing is a property of the record, not of the body); it composes *at the transcript's own rational
centre* only under the square-class condition; and the degenerate frozen transcript that would make
it free is uninhabitable.  §5 turns §4 into `RunParts.hcut`'s own quantifier skeleton
(`hcut_field_of_surrogates`) and exhibits the record that shows the square-class condition bites at
the very first round (`sigma_one_one_not_square`, `hwit_one_one_legit`).  §6 gives the closed-form
necessary budget `mg + (∑ᵢ|cᵢ|)·ε ≤ ρ√(c ⬂ p)` (`drift_budget_necessary`,
`drift_budget_of_record`), which is the exact feasibility condition for the surrogate route.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` receipts at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.TranscriptM3

open QMCLeafB.EngineIterates

/-! ## 1.  The step is the definitional one -/

/-- The transcript centre's increment, definitionally: `Cat (k+1) = Cat k + (γ/√σ) • p`. -/
theorem Cat_succ (n : ℕ) (a0 : Fin n → ℝ) (cd : ℕ → CutData n) (k : ℕ) :
    Cat n a0 cd (k + 1) = stepCentre n (Cat n a0 cd k)
      (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)) ((cd k).rho : ℝ) := rfl

/-! ## 2.  The frozen transcript, and why it is uninhabitable -/

/-- A cut whose witness `p` is zero does not move the centre (the step is `· • 0`). -/
theorem stepCentre_zero (n : ℕ) (a c : Fin n → ℝ) (ρ : ℝ) :
    stepCentre n a c (0 : Fin n → ℝ) ρ = a := by
  simp [stepCentre]

/-- **The frozen transcript.**  If every recorded cut has `p = 0` then the transcript never leaves
its starting point. -/
theorem Cat_eq_zero_of_p_zero (n : ℕ) (cd : ℕ → CutData n) (hp : ∀ k, (cd k).p = 0) :
    ∀ k, Cat n (0 : Fin n → ℝ) cd k = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have hpk : (fun i => ((cd k).p i : ℝ)) = 0 := by
        funext i
        rw [hp k]
        simp
      rw [Cat_succ, stepCentre, hpk]
      simp [ih]

/-- **`hwit` + `hcne` forbid the frozen step.**  The engine records `p` as a witness of `A p = c`
(`RunParts.hwit`); a nonzero normal therefore forces a nonzero witness.  So the frozen transcript of
§2 is not a record class at all: the one trajectory on which the transcript pairing is free is
exactly the one the record forbids. -/
theorem p_ne_zero_of_hwit {n : ℕ} (A0 : Matrix (Fin n) (Fin n) ℚ) (cd : ℕ → CutData n) (k : ℕ)
    (hwit : Aat n A0 cd k *ᵥ (cd k).p = (cd k).c) (hcne : (cd k).c ≠ 0) :
    (cd k).p ≠ 0 := by
  intro hp
  apply hcne
  rw [← hwit, hp, Matrix.mulVec_zero]

/-- **The centre really moves at a cut round.**  With `p ≠ 0`, `ρ ≠ 1` and `σ > 0` the step
`(γ/√σ) • p` is nonzero, so `Cat (k+1) ≠ Cat k`.  (Together with `p_ne_zero_of_hwit` this kills every
"frozen centre" route: a cut round with a nonzero normal always moves the transcript.) -/
theorem Cat_succ_moves (n : ℕ) (a0 : Fin n → ℝ) (cd : ℕ → CutData n) (k : ℕ)
    (hp : (fun i => ((cd k).p i : ℝ)) ≠ 0)
    (hrho : ((cd k).rho : ℝ) ≠ 1)
    (hσ : 0 < sigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ))) :
    Cat n a0 cd (k + 1) ≠ Cat n a0 cd k := by
  intro h
  have hv : (gammaR n ((cd k).rho : ℝ)
      / sqrtSigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)))
      • (fun i => ((cd k).p i : ℝ)) = 0 := by
    have h2 : Cat n a0 cd k
        = Cat n a0 cd k + (gammaR n ((cd k).rho : ℝ)
          / sqrtSigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)))
          • (fun i => ((cd k).p i : ℝ)) := by
      have h0 : Cat n a0 cd k = stepCentre n (Cat n a0 cd k)
          (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)) ((cd k).rho : ℝ) := by
        rw [← Cat_succ]
        exact h.symm
      simpa [stepCentre] using h0
    have h3 : Cat n a0 cd k + (gammaR n ((cd k).rho : ℝ)
        / sqrtSigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)))
        • (fun i => ((cd k).p i : ℝ)) = Cat n a0 cd k + 0 := by
      rw [add_zero]
      exact h2.symm
    exact add_left_cancel h3
  have hγ : gammaR n ((cd k).rho : ℝ) ≠ 0 := by
    unfold gammaR
    have h1 : ((cd k).rho : ℝ) ≠ 1 := hrho
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : (1 - ((cd k).rho : ℝ)) ≠ 0 := by
      intro h0
      exact h1 (by linarith)
    exact div_ne_zero h3 h2
  have hσ0 : sqrtSigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)) ≠ 0 := by
    unfold sqrtSigmaR
    exact Real.sqrt_ne_zero'.mpr hσ
  have hcoef : gammaR n ((cd k).rho : ℝ)
      / sqrtSigmaR (fun i => ((cd k).c i : ℝ)) (fun i => ((cd k).p i : ℝ)) ≠ 0 :=
    div_ne_zero hγ hσ0
  rcases (smul_eq_zero.mp hv) with h1 | h1
  · exact hcoef h1
  · exact hp h1

/-! ## 3.  A rational transcript is square-class

The rational-centre route to `RunParts.hcut` (the `RundataCert.hcut_of_relaxCuts` shape) needs the
transcript centre to be the cast of a rational point, i.e. `Cat k = flat (castMat (cX k))`.  The
next two lemmas say what that costs arithmetically. -/

/-- **The step coefficient is rational whenever both centres are rational points.**  If `B = A + λ•p`
with `A`, `B` casts of rational vectors and `p` a nonzero rational vector, then `λ` is the cast of a
rational (its `j`-th component ratio). -/
theorem lambda_rat_of_rat_centres {n : ℕ} {A B : Fin n → ℝ} {vA vB : Fin n → ℚ}
    (hA : A = fun i => ((vA i : ℚ) : ℝ)) (hB : B = fun i => ((vB i : ℚ) : ℝ))
    {p : Fin n → ℚ} {lam : ℝ} (h : B = A + lam • (fun i => ((p i : ℚ) : ℝ)))
    (hp : p ≠ 0) :
    ∃ q : ℚ, lam = ((q : ℚ) : ℝ) := by
  obtain ⟨j, hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hp (funext hc)
  refine ⟨(vB j - vA j) / p j, ?_⟩
  have hcomp := congrFun h j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hA, hB] at hcomp
  have hpj : ((p j : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hj
  push_cast
  field_simp
  linarith

/-- **The `γ` of the step is a cast.** -/
theorem gammaR_cast (n : ℕ) (r : ℚ) :
    gammaR n ((r : ℚ) : ℝ) = (((1 - r) / ((n : ℚ) + 1) : ℚ) : ℝ) := by
  unfold gammaR
  push_cast
  ring

/-- **A rational transcript forces `σ` to be a rational square.**  If the two transcript centres are
casts of rational points and the step is the engine's `(γ/√σ) • p` with `p ≠ 0`, `ρ ≠ 1` and
`σ = c ⬂ p > 0`, then `σ` is the square of a *nonzero rational*.

Under `hwit` (`Aat · p = c`) one has `σ = (Aat p) ⬂ p`, a rational quadratic form; scaling `p` by a
rational multiplies `σ` by a square, so the condition is a genuine square-class constraint on the
recorded eigendata — it is not something the producer can arrange by rescaling. -/
theorem sigma_square_of_rat_transcript {n : ℕ} {A B : Fin n → ℝ} {vA vB : Fin n → ℚ}
    {p c : Fin n → ℚ} {rq : ℚ}
    (hA : A = fun i => ((vA i : ℚ) : ℝ)) (hB : B = fun i => ((vB i : ℚ) : ℝ))
    (h : B = A + (gammaR n ((rq : ℚ) : ℝ)
        / sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ)))
        • (fun i => ((p i : ℚ) : ℝ)))
    (hp : p ≠ 0) (hrq : rq ≠ 1)
    (hσ : 0 < sigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ))) :
    ∃ q : ℚ, q ≠ 0 ∧ ((q : ℚ) : ℝ) ^ 2
      = sigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ)) := by
  obtain ⟨qlam, hqlam⟩ := lambda_rat_of_rat_centres hA hB h hp
  have hsq : sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ)) ≠ 0 := by
    unfold sqrtSigmaR
    exact Real.sqrt_ne_zero'.mpr hσ
  have hgq : (1 - rq) / ((n : ℚ) + 1) ≠ 0 := by
    have hnum : (1 - rq) ≠ 0 := by
      intro h0
      exact hrq (by linarith)
    exact div_ne_zero hnum (by positivity)
  have hγ : gammaR n ((rq : ℚ) : ℝ) ≠ 0 := by
    rw [gammaR_cast]
    intro h0
    exact hgq (by exact_mod_cast h0)
  have hlam : qlam ≠ 0 := by
    intro h0
    apply hγ
    have h1 : gammaR n ((rq : ℚ) : ℝ)
        / sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ)) = 0 := by
      rw [hqlam, h0]
      norm_num
    have h2 : gammaR n ((rq : ℚ) : ℝ) = 0 * sqrtSigmaR (fun i => ((c i : ℚ) : ℝ))
        (fun i => ((p i : ℚ) : ℝ)) := (div_eq_iff hsq).mp h1
    simpa using h2
  have hγeq : gammaR n ((rq : ℚ) : ℝ) = ((qlam : ℚ) : ℝ)
      * sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ)) :=
    (div_eq_iff hsq).mp hqlam
  have hsqrt : sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ))
      = (((1 - rq) / ((n : ℚ) + 1)) / qlam : ℚ) := by
    have hl : ((qlam : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hlam
    have h1 : sqrtSigmaR (fun i => ((c i : ℚ) : ℝ)) (fun i => ((p i : ℚ) : ℝ))
        = gammaR n ((rq : ℚ) : ℝ) / ((qlam : ℚ) : ℝ) := by
      rw [hγeq]
      field_simp
    rw [h1, gammaR_cast]
    push_cast
    ring
  refine ⟨((1 - rq) / ((n : ℚ) + 1)) / qlam, div_ne_zero hgq hlam, ?_⟩
  rw [← hsqrt]
  simpa [sqrtSigmaR, pow_two] using Real.sq_sqrt hσ.le

/-! ## 4.  The surrogate route: the drift is paid in `del`

The constructive half.  A cut certified at a *surrogate* point `q` (in the campaign: `q = flat
(castMat cX)`, the oracle's own rational centre — necessarily *not* `Cat k`, by §3) gives `hcut`'s
inequality at the true transcript centre `a = Cat k` once the recorded margin `del` absorbs the drift:

    del k = margin + (∑ᵢ |cᵢ|) · supᵢ |Cat k ᵢ − qᵢ|.

`RunParts.hcheck` (`del² ≤ ρ²σ`) then caps the admissible drift from above, and `RunParts.hdel0`
(`0 ≤ del`) is automatic because the right-hand side is a sum of a positive margin and a
nonnegative penalty.  This is the route that works at *every* body — empty or not — because the
pairing is a property of the record, not of the body. -/

/-- **The surrogate penalty.**  A cut separating at the surrogate `q` separates at the true centre
`a`, with the margin raised by the `ℓ¹`-norm of the normal times the sup-norm drift. -/
theorem hcut_of_surrogate {N : ℕ} (c z a q : Fin N → ℝ) {m ε : ℝ}
    (hε : ∀ i, |a i - q i| ≤ ε)
    (hm : -m ≤ c ⬝ᵥ (z - q)) :
    -(m + (∑ i, |c i|) * ε) ≤ c ⬝ᵥ (z - a) := by
  have hsplit : c ⬝ᵥ (z - a) = c ⬝ᵥ (z - q) + c ⬝ᵥ (q - a) := by
    rw [← dotProduct_add]
    congr 1
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hb : |c ⬝ᵥ (q - a)| ≤ (∑ i, |c i|) * ε := by
    have hunf : c ⬝ᵥ (q - a) = ∑ i, c i * (q - a) i := rfl
    rw [hunf]
    calc |∑ i, c i * (q - a) i| ≤ ∑ i, |c i * (q - a) i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |c i| * ε := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          have h := hε i
          rw [abs_sub_comm] at h
          exact h
      _ = (∑ i, |c i|) * ε := (Finset.sum_mul Finset.univ (fun i => |c i|) ε).symm
  have h2 : -(∑ i, |c i|) * ε ≤ c ⬝ᵥ (q - a) := by
    have h3 := neg_abs_le (c ⬝ᵥ (q - a))
    nlinarith [h3, hb]
  rw [hsplit]
  nlinarith [hm, h2]

/-- **`RunParts.hcut`'s inequality at the transcript centre, from a cut at the surrogate.**  This is
the exact shape the record needs: `c` is `cutCR cd k`, `a` is `Cat k`, `del` is `del k`, and the
hypothesis `hdel` is the drift budget that `hcheck` then bounds above. -/
theorem hcut_at_centre_of_surrogate {N : ℕ} (c z a q : Fin N → ℝ) {m del ε : ℝ}
    (hdel : m + (∑ i, |c i|) * ε ≤ del)
    (hε : ∀ i, |a i - q i| ≤ ε)
    (hm : -m ≤ c ⬝ᵥ (z - q)) :
    -del ≤ c ⬝ᵥ (z - a) := by
  have h := hcut_of_surrogate c z a q hε hm
  linarith

/-! ## 5.  The `hcut` field from surrogate certificates, and a witness that the square-class
condition bites

`hcut_field_of_surrogates` is `RunParts.hcut`'s quantifier skeleton with the surrogate hypothesis in
place of the (unattainable, by §3) rational-centre one.  `sigma_one_one_not_square` then exhibits the
most natural record of all — identity shape, `c = p = 1` — whose `σ = 2` is *not* a rational square,
so the rational-transcript route is genuinely blocked there and the drift must be paid. -/

/-- **`RunParts.hcut` from surrogate certificates.**  `S` is the ball predicate, `q k` the surrogate
centre, `mg k` the certified margin there and `del k` the recorded margin at the true transcript
centre.  The only arithmetic obligation is the drift budget `mg k + ℓ¹(c_k)·ε k ≤ del k`. -/
theorem hcut_field_of_surrogates (N : ℕ) (T : ℕ) (cd : ℕ → CutData N) (ok : ℕ → Bool)
    (S : (Fin N → ℝ) → Prop) (q : ℕ → Fin N → ℝ) (ε mg del : ℕ → ℝ)
    (hε : ∀ k, ok k = false → ∀ i, |Cat N (0 : Fin N → ℝ) cd k i - q k i| ≤ ε k)
    (hdel : ∀ k, ok k = false →
      mg k + (∑ i, |cutCR cd k i|) * ε k ≤ del k)
    (hm : ∀ k, ok k = false → ∀ z : Fin N → ℝ,
      S z → -mg k ≤ cutCR cd k ⬝ᵥ (z - q k)) :
    ∀ k, k < T → ok k = false → ∀ z : Fin N → ℝ,
      S z → -del k ≤ cutCR cd k ⬝ᵥ (z - Cat N (0 : Fin N → ℝ) cd k) := by
  intro k _ hok z hz
  exact hcut_at_centre_of_surrogate (cutCR cd k) z (Cat N (0 : Fin N → ℝ) cd k) (q k)
    (hdel k hok) (hε k hok) (hm k hok z hz)

/-- `2` is not the square of a rational. -/
theorem two_not_rat_square : ¬ ∃ q : ℚ, ((q : ℚ) : ℝ) ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  have habs : Real.sqrt 2 = ((|q| : ℚ) : ℝ) := by
    rw [← hq, Real.sqrt_sq_eq_abs, Rat.cast_abs]
  exact irrational_sqrt_two ⟨|q|, habs.symm⟩

/-- `σ` of the all-ones certificate at the identity shape: `c = p = 1` gives `σ = n`; at `n = 2` this
is `2`. -/
theorem sigma_one_one_two :
    sigmaR (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) = 2 := by
  simp [sigmaR, dotProduct]

/-- **The square-class condition bites at the first round.**  Identity shape, `p = c = 1`: this is a
legitimate record (`hwit` holds — `Aat 2 1 cd 0 = 1` — and `c ≠ 0`), yet its `σ = 2` is not a
rational square, so by `sigma_square_of_rat_transcript` the transcript cannot have both `Cat 0 = 0`
and `Cat 1` rational.  The all-ones direction is exactly the direction a rational solver would return
first, so this is not a corner case. -/
theorem sigma_one_one_not_square :
    ¬ ∃ q : ℚ, ((q : ℚ) : ℝ) ^ 2
      = sigmaR (fun _ : Fin 2 => (1 : ℝ)) (fun _ : Fin 2 => (1 : ℝ)) := by
  rw [sigma_one_one_two]
  exact two_not_rat_square

/-- The record of the previous theorem is `hwit`-legitimate: the identity shape sends `p = 1` to
`c = 1`. -/
theorem hwit_one_one_legit :
    Aat 2 (1 : Matrix (Fin 2) (Fin 2) ℚ)
        (fun _ => (⟨fun _ => 1, fun _ => 1, 0⟩ : CutData 2)) 0
      *ᵥ (fun _ => (1 : ℚ)) = fun _ => (1 : ℚ) := by
  show (1 : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ (fun _ => (1 : ℚ)) = fun _ => (1 : ℚ)
  simp

/-! ## 6.  The drift budget is a *necessary* condition, in closed form

`RunParts` gives `hcheck : del² ≤ ρ²σ` and `hdel0 : 0 ≤ del`; the surrogate route (§4) needs
`mg + C·ε ≤ del`.  Combining the two: **the drift plus the certified margin can never exceed `ρ√σ`**.
So the surrogate route is feasible exactly when

    mg + (∑ᵢ|cᵢ|)·ε ≤ ρ·√(c ⬂ p),

which is the campaign's centre-approximation budget in closed form.  (§3 says that when the
square-class condition holds the penalty `C·ε` is *zero* — the centres coincide — so the same
inequality then reduces to `mg ≤ ρ√σ`, which is `hcheck` read as a margin bound.) -/

/-- **The necessary drift budget.**  A record satisfying both `hcheck` (`del² ≤ ρ²σ`) and the
surrogate lower bound `mg + Cε ≤ del` can exist only if `mg + Cε ≤ ρ√σ`. -/
theorem drift_budget_necessary {mg Cε del ρ σ : ℝ}
    (hCε : 0 ≤ mg + Cε) (hlow : mg + Cε ≤ del) (hcheck : del ^ 2 ≤ ρ ^ 2 * σ)
    (hσ : 0 ≤ σ) (hρ : 0 ≤ ρ) :
    mg + Cε ≤ ρ * Real.sqrt σ := by
  have h1 : (mg + Cε) ^ 2 ≤ ρ ^ 2 * σ := by
    have h2 : (mg + Cε) ^ 2 ≤ del ^ 2 := by nlinarith
    linarith
  have h3 : Real.sqrt ((mg + Cε) ^ 2) ≤ Real.sqrt (ρ ^ 2 * σ) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq hCε, Real.sqrt_mul (by positivity), Real.sqrt_sq hρ] at h3
  exact h3

/-- The same, at the engine's own rational epoch data: `σ = c ⬂ p` and `ρ = (cd k).rho`. -/
theorem drift_budget_of_record (N : ℕ) (cd : ℕ → CutData N) (k : ℕ) {mg Cε del : ℝ}
    (hCε : 0 ≤ mg + Cε) (hlow : mg + Cε ≤ del)
    (hcheck : del ^ 2 ≤ ((cd k).rho : ℝ) ^ 2
      * ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ))
    (hσ : 0 ≤ ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)) (hρ : 0 ≤ ((cd k).rho : ℝ)) :
    mg + Cε ≤ ((cd k).rho : ℝ) * Real.sqrt ((sigmaQ (cd k).c (cd k).p : ℚ) : ℝ) :=
  drift_budget_necessary hCε hlow hcheck hσ hρ

end QMCLeafB.TranscriptM3

/-! ## Axiom audit -/
#print axioms QMCLeafB.TranscriptM3.Cat_succ
#print axioms QMCLeafB.TranscriptM3.stepCentre_zero
#print axioms QMCLeafB.TranscriptM3.Cat_eq_zero_of_p_zero
#print axioms QMCLeafB.TranscriptM3.p_ne_zero_of_hwit
#print axioms QMCLeafB.TranscriptM3.Cat_succ_moves
#print axioms QMCLeafB.TranscriptM3.lambda_rat_of_rat_centres
#print axioms QMCLeafB.TranscriptM3.gammaR_cast
#print axioms QMCLeafB.TranscriptM3.sigma_square_of_rat_transcript
#print axioms QMCLeafB.TranscriptM3.hcut_of_surrogate
#print axioms QMCLeafB.TranscriptM3.hcut_at_centre_of_surrogate
#print axioms QMCLeafB.TranscriptM3.hcut_field_of_surrogates
#print axioms QMCLeafB.TranscriptM3.two_not_rat_square
#print axioms QMCLeafB.TranscriptM3.sigma_one_one_two
#print axioms QMCLeafB.TranscriptM3.sigma_one_one_not_square
#print axioms QMCLeafB.TranscriptM3.hwit_one_one_legit
#print axioms QMCLeafB.TranscriptM3.drift_budget_necessary
#print axioms QMCLeafB.TranscriptM3.drift_budget_of_record



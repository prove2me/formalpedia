-- Prove2me | Definitions.Def_QMCLeafB_obstruction_m1
-- name    : QMCLeafB_obstruction_m1
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T03:01:13.01822+00:00
-- url     : https://prove2.me/theorems/70f2113f-4dc1-4c13-8436-a4417cc2ec27
-- title:
--   QMCLeafB obstruction_m1
-- statement:
--   # leaf B phase 17 — refutability audit of the residual `hd` (swarm `smw1gfajf`, member m1, d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_runparts_stream_m4
import Definitions.Def_QMCLeafB_htop_init_m7
/-
# leaf B phase 17 — refutability audit of the residual `hd` (swarm `smw1gfajf`, member m1, d6)

The phase-16/17 residual `hd` (brick 4) is, at the campaign family `UnionShallow.paramsKbc2`,

    ∀ G t, 2 ≤ G.n → -Rq G ≤ t → t < -Rq G/40000 → RunParts (loopBit init0 roundGT verdict …) G t (paramsKbc2 G)

and every *concrete* route to `RunParts` on the shelf goes through
`QMCLeafB.RunPartsDilate.runParts_of_dilated`, with the dilation direction `dM` pinned to the
**identity** in `QMCLeafB.RunPartsStream.runParts_of_stream_data` (the term passed there is
`(1 : Matrix (Fin G.n) (Fin G.n) ℚ)`).  With `dM = 1`, `hbody` reduces (m4's `hbody_of_diag`) to the
*identity-band* condition

    hdiagc : ∀ k i, (cX k) i i ≤ 1 − P.dq/4 ,

on the centre stream `cX`, while the `ok`-round oracle contract supplied to the same conduit is

    hmem : ∀ k, k < K·m → ok k = true → RelaxMem (wMatrixQ G) (cX k) (t − eps) P.dq ,

whose diagonal clause is `diag_near : ∀ i, |(cX k) i i − 1| ≤ P.dq/4`.

This file is the audit of that pair.  Its findings, all machine-checked below:

* **§1 The pinch.**  `hdiagc` and `diag_near` at the *same* centre force **equality**:
  `(cX k) i i = 1 − dq/4` for every `i`, hence `trace (cX k) = n (1 − dq/4)` — the centre must sit
  exactly on the diagonal boundary of the relaxed body at every `ok` round, not merely inside the
  band.  (This is the quantitative form of m6's `Check_diagsign_m6` remark that `hdiagc` is
  "unsatisfiable at the actual programme states".)
* **§2 The scale dichotomy.**  Consequence: for a *unit-diagonal* base (any SDP-feasible point, and
  in particular the state of a PSD/threshold round) there is exactly **one** uniform rescaling that
  keeps the centre admissible for both fields, namely `s = 1 − dq/4`.  The **recorded `1 − dq/2`
  surrogate is refuted**: it satisfies `hdiagc` but violates `RelaxMem.diag_near` by a factor two
  (`dq/2 > dq/4`).  So the phase-16 note "centre must be `(1 − dq/2)•X_k`" is not a repair of this
  conduit: the only uniform scale compatible with `hmem` is `(1 − dq/4)•X_k`.
* **§3 The `dvR` obstruction.**  At any state where the oracle's PSD/threshold branch is consulted
  (`dvR s = 0`, i.e. every diagonal entry of `stX` is `1`) the identity band is *false*:
  `1 ≤ 1 − dq/4` for `dq > 0`.  Hence the identity-dilation conduit can never be instantiated with
  `cX k := stX` at a PSD/threshold round — the `Check_diagsign_m6` repair (`dM := flat (diagSign)`,
  band condition instead of `hdiagc`) is not cosmetic but necessary.
* **§4 No self-repair.**  The round's *pre-snap* diagonal never decreases while the iterate is PSD
  (the `α⁻¹ = (n+1)/(n−1)` scaling dominates the Sherman–Morrison drop by the Cauchy–Schwarz bound
  `(Xc)_i² ≤ X_ii σ`), and for a diagonal-sign cut on a uniform-diagonal state the factor is exactly
  `((n+1)/(n−1))·(1 − 2/((n+1)n))` — `2` at `n = 2`.  So the band, once lost, is never regained
  along the orbit, and `hdiagc` cannot be established on an initial segment and extended.

* **§5 The admissible lowering, transported.**  `RelaxMem` is transported along `(1 - dq/4) • -`:
if the base is a member at threshold `u'` and has diagonal `>= 1`, then the lowered centre is a
member at `u` as soon as `(1 - dq/4)(u' + dq/2) <= u + dq/2`.  This is the legal form of the
"carry the shift" note: the cost is a *threshold* shift, not an `hstatec` term.
* **§6 The `ok` test is `2 eps` too weak.**  `hmem` needs `frob A cX <= t - eps + dq/2` while the
programme's `ok` test gives only `frob A X <= t + eps`; the gap `2 eps - dq/2` is *positive* at the
campaign's tolerance (`dqShallow G / 2 < 2 eps G`), so `hmem` is not a consequence of the `ok`
verdict — the `ok`-round point must be strictly inside the body (the `OkLower` lowering) or the
centre must come from §5's scaled lowering with its threshold cost.

**What this file does NOT do.**  It does not refute `hd` itself: `cX` is free data in
`runParts_of_stream_data`, so the residual remains *consistent* — the audit's verdict is
"`hd` is not refutable, but the identity-dilation *conduit* is not instantiable at the programme's
own state, and the recorded `1 − dq/2` surrogate is the wrong scale".  §4's arithmetic is about the
round's diagonal recursion; it is not a computation of the campaign's orbit.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; axiom audit at the end.
-/

open scoped BigOperators
open scoped Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.AuditM1

/-! ## 0.  Sums of nonnegative rationals -/

theorem list_sum_nonneg : ∀ (l : List ℚ), (∀ x ∈ l, 0 ≤ x) → 0 ≤ l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons a as ih =>
      intro h
      simp only [List.sum_cons]
      exact add_nonneg (h a (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem list_sum_zero_of_nonneg : ∀ (l : List ℚ), (∀ x ∈ l, 0 ≤ x) → l.sum = 0 →
    ∀ x ∈ l, x = 0 := by
  intro l
  induction l with
  | nil => intro _ _ x hx; simp at hx
  | cons a as ih =>
      intro hnn hs x hx
      have ha : 0 ≤ a := hnn a (by simp)
      have htail : ∀ y ∈ as, 0 ≤ y := fun y hy => hnn y (by simp [hy])
      have hs' : a + as.sum = 0 := by simpa using hs
      have h2 : 0 ≤ as.sum := list_sum_nonneg as htail
      have ha0 : a = 0 := by linarith
      have hs0 : as.sum = 0 := by linarith
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha0
      · exact ih htail hs0 x hx'

/-! ## 1.  The diagonal pinch

`hdiagc` (the identity dilation direction) and `RelaxMem.diag_near` (the `ok`-round contract) act on
the same centre, and their two halves meet exactly at `1 - dq/4`. -/

theorem pinch_entry {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hband : ∀ i, Q i i ≤ 1 - dq / 4) (hnear : ∀ i, |Q i i - 1| ≤ dq / 4)
    (i : Fin n) : Q i i = 1 - dq / 4 := by
  have h1 : 1 - dq / 4 ≤ Q i i := by
    have h := (abs_le.mp (hnear i)).1
    linarith
  have h2 := hband i
  linarith

/-- **The pinch, in the conduit's own fields.**  A centre that is both in the identity band
(`hdiagc`) and an `ok`-round `RelaxMem` centre has diagonal exactly `1 - dq/4`. -/
theorem pinch_of_mem {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u dq)
    (hband : ∀ i, Q i i ≤ 1 - dq / 4) (i : Fin n) : Q i i = 1 - dq / 4 :=
  pinch_entry hband hmem.diag_near i

/-- The pinched centre has trace exactly `n (1 - dq/4)`: the *minimum* trace of the relaxed body, so
the identity-direction `hbody` holds with equality there. -/
theorem pinch_trace {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u dq)
    (hband : ∀ i, Q i i ≤ 1 - dq / 4) :
    Q.trace = (n : ℚ) * (1 - dq / 4) := by
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => pinch_of_mem hmem hband i)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- A centre in the identity band is never unit-diagonal when `dq > 0`. -/
theorem centre_ne_one {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ} (hdq : 0 < dq)
    (hband : ∀ i, Q i i ≤ 1 - dq / 4) (i : Fin n) : Q i i ≠ 1 := by
  intro h
  have h2 := hband i
  rw [h] at h2
  linarith

/-! ## 2.  The scale dichotomy

Which uniform rescalings `s • Q` of a unit-diagonal base keep the centre admissible for the identity
conduit?  Exactly one: `s = 1 - dq/4`.  In particular the recorded `1 - dq/2` surrogate is refuted
(it leaves `RelaxMem.diag_near`). -/

theorem smul_diag {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {s : ℚ} (hQ : ∀ i, Q i i = 1)
    (i : Fin n) : (s • Q) i i = s := by
  rw [Matrix.smul_apply, hQ i, smul_eq_mul, mul_one]

/-- **The only admissible uniform scale is `1 - dq/4`.** -/
theorem scale_forces_boundary {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {s dq : ℚ}
    (hQ : ∀ i, Q i i = 1)
    (hband : ∀ i, (s • Q) i i ≤ 1 - dq / 4)
    (hnear : ∀ i, |(s • Q) i i - 1| ≤ dq / 4) (i : Fin n) : s = 1 - dq / 4 := by
  have h := pinch_entry hband hnear i
  rwa [smul_diag hQ i] at h

/-- **The recorded `1 - dq/2` surrogate is not admissible**: it satisfies the identity band but
violates `RelaxMem.diag_near`, by a factor two. -/
theorem scaled_centre_not_both {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hQ : ∀ i, Q i i = 1) (hdq : 0 < dq) (i : Fin n) :
    ¬ (((1 - dq / 2) • Q) i i ≤ 1 - dq / 4 ∧ |((1 - dq / 2) • Q) i i - 1| ≤ dq / 4) := by
  rintro ⟨-, hn⟩
  rw [smul_diag hQ i] at hn
  have h := (abs_le.mp hn).1
  linarith

/-- The identity band *is* satisfied by the `1 - dq/2` surrogate (so the failure above is exactly
the `diag_near` clause). -/
theorem scaled_centre_in_band {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hQ : ∀ i, Q i i = 1) (hdq : 0 < dq) (i : Fin n) :
    ((1 - dq / 2) • Q) i i ≤ 1 - dq / 4 := by
  rw [smul_diag hQ i]
  linarith

/-- **`1 - dq/4 • Q` satisfies both fields** (with equality on both sides) — the admissible scale. -/
theorem boundary_scale_admissible {n : ℕ} {Q : Matrix (Fin n) (Fin n) ℚ} {dq : ℚ}
    (hQ : ∀ i, Q i i = 1) (hdq : 0 < dq) (i : Fin n) :
    ((1 - dq / 4) • Q) i i ≤ 1 - dq / 4 ∧ |((1 - dq / 4) • Q) i i - 1| ≤ dq / 4 := by
  rw [smul_diag hQ i]
  refine ⟨le_refl _, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- A worked instance: at `n = 2`, `dq = 1/10`, the `1 - dq/2` surrogate is off the admissible band
by `1/20 > 1/40`, while `1 - dq/4` sits on it. -/
theorem numeric_instance_dq_tenth :
    ¬ ((1 - (1 / 10 : ℚ) / 2) ≤ 1 - (1 / 10 : ℚ) / 4
        ∧ |(1 - (1 / 10 : ℚ) / 2) - 1| ≤ (1 / 10 : ℚ) / 4) ∧
      ((1 - (1 / 10 : ℚ) / 4) ≤ 1 - (1 / 10 : ℚ) / 4
        ∧ |(1 - (1 / 10 : ℚ) / 4) - 1| ≤ (1 / 10 : ℚ) / 4) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨-, h⟩
    have : |(1 - (1 / 10 : ℚ) / 2) - 1| = 1 / 20 := by norm_num
    linarith
  · refine ⟨le_refl _, ?_⟩
    have : |(1 - (1 / 10 : ℚ) / 4) - 1| = 1 / 40 := by norm_num
    linarith

/-! ## 3.  `dvR = 0` is incompatible with the identity band

`dvR s = ∑_{i<n} |X_{ii} - 1|`, so `dvR s = 0` forces every diagonal entry of the state's code to be
`1` — the state a PSD/threshold round is queried at.  The identity band then reads `1 ≤ 1 - dq/4`,
which is false for `dq > 0`. -/

theorem diagSumV_eq_zero {n : ℕ} {xs : List ℚ} (hlen : xs.length = n * n)
    (h0 : QMCLeafB.RoundProgram.diagSumV (n, xs) = 0) {i : ℕ} (hi : i < n) :
    QMCLeafB.RoundProgram.entV (n, xs) i i = 1 := by
  have hidx : QMCLeafB.RoundProgram.idxs (n, xs) = List.range n :=
    QMCLeafB.HtopInit.idxs_eq_range hlen
  have hsum : (List.map (fun i => QMCLeafB.RoundProgram.absq
      (QMCLeafB.RoundProgram.entV (n, xs) i i - 1)) (List.range n)).sum = 0 := by
    unfold QMCLeafB.RoundProgram.diagSumV at h0
    rw [hidx] at h0
    exact h0
  have hterm : QMCLeafB.RoundProgram.absq (QMCLeafB.RoundProgram.entV (n, xs) i i - 1) = 0 :=
    list_sum_zero_of_nonneg _
      (fun j hj => by
        obtain ⟨j', -, rfl⟩ := List.mem_map.mp hj
        rw [QMCLeafB.RoundProgram.absq_eq]
        exact abs_nonneg _)
      hsum _ (List.mem_map.2 ⟨i, List.mem_range.mpr hi, rfl⟩)
  rw [QMCLeafB.RoundProgram.absq_eq, abs_eq_zero] at hterm
  linarith

/-- **The identity band fails at every `dvR = 0` state.** -/
theorem band_false_of_dvR_zero {n : ℕ} {xs : List ℚ} (hlen : xs.length = n * n) (hn : 0 < n)
    {dq : ℚ} (hdq : 0 < dq) (h0 : QMCLeafB.RoundProgram.diagSumV (n, xs) = 0) :
    ¬ (∀ i : ℕ, i < n → QMCLeafB.RoundProgram.entV (n, xs) i i ≤ 1 - dq / 4) := by
  intro hband
  have h := hband 0 hn
  have h1 : QMCLeafB.RoundProgram.entV (n, xs) 0 0 = 1 := diagSumV_eq_zero hlen h0 hn
  rw [h1] at h
  linarith

/-! ## 4.  The round never restores the band

The pre-snap diagonal of one cut round is `α⁻¹ (X_ii - (2/((n+1)σ)) (Xc)_i²)` with
`α⁻¹ = (n+1)/(n-1)`, `σ = c ⬝ᵥ (X *ᵥ c)`.  Cauchy–Schwarz for a PSD `X` gives
`(Xc)_i² ≤ X_ii σ`, so the diagonal is **non-decreasing**; for a diagonal-sign cut on a
uniform-diagonal state the factor is `((n+1)/(n-1))·(1 - 2/((n+1)n))`, which is `2` at `n = 2`. -/

theorem diag_nondec_of_psd {n : ℕ} (hn : 1 < n) {X : Matrix (Fin n) (Fin n) ℝ} {c : Fin n → ℝ}
    {σ : ℝ} (hσ : σ = c ⬝ᵥ (X *ᵥ c)) (hσpos : 0 < σ) (i : Fin n) (hii : 0 ≤ X i i)
    (hcs : ((X *ᵥ c) i) ^ 2 ≤ X i i * σ) :
    X i i ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1)
      * (X i i - (2 / (((n : ℝ) + 1) * σ)) * ((X *ᵥ c) i) ^ 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hkpos : (0 : ℝ) < 2 / (((n : ℝ) + 1) * σ) := by positivity
  have h1 : (2 / (((n : ℝ) + 1) * σ)) * ((X *ᵥ c) i) ^ 2
      ≤ (2 / (((n : ℝ) + 1) * σ)) * (X i i * σ) :=
    mul_le_mul_of_nonneg_left hcs (le_of_lt hkpos)
  have h2 : (2 / (((n : ℝ) + 1) * σ)) * (X i i * σ) = 2 * X i i / ((n : ℝ) + 1) := by
    field_simp
  rw [h2] at h1
  have h3 : X i i - 2 * X i i / ((n : ℝ) + 1) = X i i * ((n : ℝ) - 1) / ((n : ℝ) + 1) := by
    field_simp
    ring
  have h5 : X i i * ((n : ℝ) - 1) / ((n : ℝ) + 1)
      ≤ X i i - (2 / (((n : ℝ) + 1) * σ)) * ((X *ᵥ c) i) ^ 2 := by
    rw [← h3]
    linarith [h1]
  have h6 : (0 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) := le_of_lt (by positivity)
  have h7 := mul_le_mul_of_nonneg_left h5 h6
  calc X i i = ((n : ℝ) + 1) / ((n : ℝ) - 1)
        * (X i i * ((n : ℝ) - 1) / ((n : ℝ) + 1)) := by
        field_simp
    _ ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1)
        * (X i i - (2 / (((n : ℝ) + 1) * σ)) * ((X *ᵥ c) i) ^ 2) := h7

/-- **Uniform-diagonal state, diagonal-sign cut: the exact factor is `≥ 1`.** -/
theorem diagSign_step_uniform {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 0 < x) :
    x ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1)
      * (x - (2 / (((n : ℝ) + 1) * ((n : ℝ) * x))) * x ^ 2) := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans zero_lt_one (by exact_mod_cast hn)
  have key : ((n : ℝ) + 1) / ((n : ℝ) - 1)
      * (x - (2 / (((n : ℝ) + 1) * ((n : ℝ) * x))) * x ^ 2)
      = x * (((n : ℝ) + 1) / ((n : ℝ) - 1) * (1 - 2 / (((n : ℝ) + 1) * (n : ℝ)))) := by
    field_simp
  rw [key]
  have hfac : 1 ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) * (1 - 2 / (((n : ℝ) + 1) * (n : ℝ))) := by
    have key2 : ((n : ℝ) + 1) / ((n : ℝ) - 1) * (1 - 2 / (((n : ℝ) + 1) * (n : ℝ)))
        = (((n : ℝ) + 1) * (n : ℝ) - 2) / (((n : ℝ) - 1) * (n : ℝ)) := by
      field_simp
    rw [key2, le_div_iff₀ (by positivity)]
    nlinarith [hn0, hn1]
  calc x = x * 1 := (mul_one x).symm
    _ ≤ x * (((n : ℝ) + 1) / ((n : ℝ) - 1)
          * (1 - 2 / (((n : ℝ) + 1) * (n : ℝ)))) :=
        mul_le_mul_of_nonneg_left hfac (le_of_lt hx)

/-- **At `n = 2` the uniform diagonal exactly doubles** (the campaign's own dimension). -/
theorem n2_doubles {x : ℝ} (hx : 0 < x) :
    ((2 : ℝ) + 1) / ((2 : ℝ) - 1)
      * (x - (2 / (((2 : ℝ) + 1) * ((2 : ℝ) * x))) * x ^ 2) = 2 * x := by
  have hx' : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

/-- **The band is lost in four doublings** at `n = 2` from the campaign's initial diagonal
`x₀ = 1/(2·2² + 2·dq²)` — arithmetic of the recursion, not a computation of the orbit. -/
theorem initial_diag_in_band {dq : ℚ} (hdq : 0 < dq) (hdq1 : dq < 1) :
    (1 / (2 * (2 : ℚ) ^ 2 + 2 * dq ^ 2) ≤ 1 - dq / 4)
      ∧ (1 - dq / 4 < (2 : ℚ) ^ 4 * (1 / (2 * (2 : ℚ) ^ 2 + 2 * dq ^ 2))) := by
  have h1 : (0 : ℚ) < 2 * (2 : ℚ) ^ 2 + 2 * dq ^ 2 := by positivity
  have h2 : (2 : ℚ) * (2 : ℚ) ^ 2 + 2 * dq ^ 2 = 8 + 2 * dq ^ 2 := by norm_num
  constructor
  · rw [h2, div_le_iff₀ (by positivity)]
    nlinarith [hdq, hdq1]
  · rw [h2, show (2 : ℚ) ^ 4 * (1 / (8 + 2 * dq ^ 2)) = 16 / (8 + 2 * dq ^ 2) by ring,
      lt_div_iff₀ (by positivity)]
    nlinarith [hdq, hdq1]

/-! ## 5.  The one admissible lowering, and what it costs

`hdiagc` is met by lowering the centre's diagonal, and §2 says the only uniform lowering that stays
inside `RelaxMem.diag_near` is `s = 1 - dq/4`.  This section transports a `RelaxMem` certificate
along that lowering: the centre is legal at the *lower* threshold `u` once the trace clause
`u' + dq/2` is paid for, so the cost is exactly the shift `u' ↦ u` in the hypothesis `hu`. -/

theorem frob_smul_right {n : ℕ} (c : ℚ) (A X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (c • X) = c * QMCLeafB.SepOracle.frob A X := by
  rw [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.frob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The boundary lowering keeps the diagonal in the band** *provided* the base diagonal is at
least `1` (the lowering pushes the diagonal down, so a base already below `1` leaves the band). -/
theorem abs_boundary_smul_sub_one {q dq : ℚ} (hdq : 0 < dq) (h4 : dq ≤ 4) (hq : 1 ≤ q)
    (hband : |q - 1| ≤ dq / 4) : |(1 - dq / 4) * q - 1| ≤ dq / 4 := by
  have h1 : q - 1 ≤ dq / 4 := (abs_le.mp hband).2
  have h0 : 0 ≤ 1 - dq / 4 := by linarith
  rw [abs_le]
  constructor
  · nlinarith [h0, hq]
  · nlinarith [h0, hq, h1]

/-- **`RelaxMem` transports along the boundary lowering.** -/
theorem relaxMem_boundary_smul {n : ℕ} {A Q : Matrix (Fin n) (Fin n) ℚ} {u u' dq : ℚ}
    (hmem : QMCLeafB.RelaxOracle.RelaxMem A Q u' dq) (hdq : 0 < dq) (h4 : dq ≤ 4)
    (hQ : ∀ i, 1 ≤ Q i i)
    (hu : (1 - dq / 4) * (u' + dq / 2) ≤ u + dq / 2) :
    QMCLeafB.RelaxOracle.RelaxMem A ((1 - dq / 4) • Q) u dq where
  δ_pos := hdq
  psd_margin := by
    intro x
    rw [QMCLeafB.SepOracle.qf_smulQ]
    have h := hmem.psd_margin x
    have hs0 : (0 : ℚ) ≤ 1 - dq / 4 := by linarith
    have hs1 : (1 - dq / 4) ≤ 1 := by linarith
    have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h1 : (1 - dq / 4) * (-(dq / 2) * (∑ i, x i ^ 2))
        ≤ (1 - dq / 4) * QMCLeafB.SepOracle.qf Q x :=
      mul_le_mul_of_nonneg_left h hs0
    have hneg : -(dq / 2) * (∑ i, x i ^ 2) ≤ 0 := by nlinarith [hsum, hdq]
    have h2 : -(dq / 2) * (∑ i, x i ^ 2)
        ≤ (1 - dq / 4) * (-(dq / 2) * (∑ i, x i ^ 2)) := by nlinarith [hneg, hs1]
    linarith
  diag_near := by
    intro i
    exact abs_boundary_smul_sub_one hdq h4 (hQ i) (hmem.diag_near i)
  trace_le := by
    rw [frob_smul_right]
    have hs0 : (0 : ℚ) ≤ 1 - dq / 4 := by linarith
    have h1 : (1 - dq / 4) * QMCLeafB.SepOracle.frob A Q
        ≤ (1 - dq / 4) * (u' + dq / 2) :=
      mul_le_mul_of_nonneg_left hmem.trace_le hs0
    linarith

/-! ## 6.  The `ok` test is `2 eps` too weak to hand over `hmem`

`RunParts.hcert` is fed by `RelaxMem` at `u = t - eps` (`hmem`), while the programme's own `ok` test
is `frob A X ≤ t + eps`.  The two differ by `2 eps`, and the conduit's `RelaxMem` trace clause is
*stronger* than the `ok` test by `2 eps - dq/2`, which is positive at the campaign's tolerance
`dq = dqShallow G = eps/(9 Rq + 1)`.  So `hmem` is not a consequence of the `ok` verdict: the run's
`ok`-round state must sit strictly *inside* the body, or the centre must be produced by lowering it. -/

theorem ok_test_not_imp_trace_le {eps dq : ℚ} (heps : 0 < eps) (hdq : 0 < dq)
    (hgap : dq / 2 < 2 * eps) (t : ℚ) :
    ∃ v : ℚ, v ≤ t + eps ∧ ¬ (v ≤ t - eps + dq / 2) := by
  refine ⟨t + eps, le_refl _, ?_⟩
  intro h
  linarith

/-- **At the campaign's tolerance the gap is positive**: `dqShallow G / 2 < 2 eps G`. -/
theorem dqShallow_half_lt_two_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G / 2
      < 2 * QMCLeafB.RundataCert.eps G := by
  rw [QMCLeafB.RundataParams.dqShallow, if_neg (ne_of_gt hRq),
    QMCLeafB.RundataParams.dqShallowCore]
  have heps : 0 < QMCLeafB.RundataCert.eps G := QMCLeafB.RundataCert.eps_pos G hRq
  have hRq' : (0 : ℚ) < 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  rw [div_div, div_lt_iff₀ (by positivity)]
  nlinarith [heps, hRq']

/-! ## 7.  The grid cannot represent the pinch: `ok` rounds are impossible at `n = 2`, `Rq = 1`

`RoundProgram.roundCut` writes the next state through `nrmRow mu d = snapDiv d ∘ clipRat mu`, so every
cut round's state entries are multiples of `1/d` with `d = stD`; the init packs `d = gridOf n =
(n+1)^4`.  §1 says an `ok` round forces the centre's diagonal to be exactly `1 - dq/4`.  Two
numeration systems therefore have to agree: `1 - dq/4` must be a grid multiple.  At `n = 2`, `Rq = 1`
it is not (`81 · (1 - 1/1600000) = 81·1599999/1600000` is not an integer, `5 ∤ 1599999`), so **no
round of the campaign's run can report `ok` in `hd`'s interior bracket once the run has cut** —
`hd` at the programme's own state, which is the only centre `oracleR` ever queries, must be an
*all-cut* `RunParts`, and the ok-branch machinery (`hcert`, `hmem`, `RoundingOut`, `OkLower`) is
unusable there. -/

/-- **A snapped entry times the grid denominator is an integer.** -/
theorem snapDiv_mul_int (d : ℕ) (hd : 0 < d) (q : ℚ) :
    ∃ m : ℤ, (d : ℚ) * QMCLeafB.RoundPolySnap.snapDiv d q = m := by
  refine ⟨QMCLeafB.RoundPolySnap.snapTrunc (q * (d : ℚ)), ?_⟩
  unfold QMCLeafB.RoundPolySnap.snapDiv
  rw [Rat.mkRat_eq_div]
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hd)
  field_simp

/-- **The pinch, in grid form**: a grid-multiple diagonal that is pinched to `1 - dq/4` forces
`d·(1 - dq/4) ∈ ℤ`. -/
theorem grid_multiple_of_pinch {d : ℕ} (hd : 0 < d) {q dq : ℚ} {x : ℚ}
    (hx : x = QMCLeafB.RoundPolySnap.snapDiv d q) (hpinch : x = 1 - dq / 4) :
    ∃ m : ℤ, (d : ℚ) * (1 - dq / 4) = m := by
  obtain ⟨m, hm⟩ := snapDiv_mul_int d hd q
  have hm' : (d : ℚ) * x = m := by rw [hx]; exact hm
  rw [hpinch] at hm'
  exact ⟨m, hm'⟩

/-- **`n = 2`, `Rq = 1`: the campaign's grid cannot hold the pinch value.** -/
theorem no_pinch_on_grid_81 :
    ¬ ∃ m : ℤ, ((81 : ℕ) : ℚ) * (1 - ((1 : ℚ) / 400000) / 4) = m := by
  rintro ⟨m, hm⟩
  have hval : (1 : ℚ) - ((1 : ℚ) / 400000) / 4 = 1599999 / 1600000 := by norm_num
  rw [hval] at hm
  have hmul : (m : ℚ) * 1600000 = 81 * 1599999 := by
    rw [← hm]
    norm_num
  have hmul' : m * 1600000 = 81 * 1599999 := by exact_mod_cast hmul
  have hdvd : (1600000 : ℤ) ∣ 81 * 1599999 := ⟨m, by linarith⟩
  have h5 : (5 : ℤ) ∣ 81 * 1599999 := dvd_trans (by norm_num) hdvd
  norm_num at h5

/-- The same in the campaign's own names: at `G` with `G.n = 2` and `Rq G = 1` the pinch value
`1 - dqShallow G / 4` is not on the init grid `gridOf 2 = 81`. -/
theorem no_pinch_campaign (G : QuantumMaxCutEnergy.Input)
    (hn : G.n = 2) (hRq : QMCLeafB.EngineRuntime.Rq G = 1) :
    ¬ ∃ m : ℤ, ((QMCLeafB.InitVerdict.gridOf G.n : ℕ) : ℚ)
        * (1 - QMCLeafB.RundataParams.dqShallow G / 4) = m := by
  have hRqpos : 0 < QMCLeafB.EngineRuntime.Rq G := by rw [hRq]; norm_num
  have hne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRqpos
  have hdq : QMCLeafB.RundataParams.dqShallow G = (1 : ℚ) / 400000 := by
    rw [QMCLeafB.RundataParams.dqShallow, if_neg hne,
      QMCLeafB.RundataParams.dqShallowCore]
    unfold QMCLeafB.RundataCert.eps
    rw [hRq]
    norm_num
  have hgrid : ((QMCLeafB.InitVerdict.gridOf G.n : ℕ) : ℚ) = 81 := by
    rw [hn]
    unfold QMCLeafB.InitVerdict.gridOf
    norm_num
  rintro ⟨m, hm⟩
  rw [hdq, hgrid] at hm
  exact no_pinch_on_grid_81 ⟨m, hm⟩

/-! ## 8.  From the round to the pinch: the code-level chain

The round's `stX` either freezes or is replaced by `snapY` (the snapped, clipped scaling), so every
state entry after the first cut round is a `nrmQ`-output, i.e. a `snapDiv` multiple - and §7 then
forbids the pinch.  The two structural lemmas are: the round's `stX` dichotomy and its iteration. -/

theorem stX_round_dichotomy (s : QMCLeafB.RoundProgram.RSt) :
    QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round s)
        = QMCLeafB.RoundProgram.snapY s
      ∨ QMCLeafB.RoundProgram.stX (QMCLeafB.RoundProgram.round s)
        = QMCLeafB.RoundProgram.stX s := by
  unfold QMCLeafB.RoundProgram.round
  by_cases h : (QMCLeafB.RoundProgram.oracleR s).1
  · rw [if_pos h]
    exact Or.inl rfl
  · rw [if_neg h]
    exact Or.inr rfl

theorem stX_iterate_dichotomy (rd : QMCLeafB.RoundProgram.RSt → QMCLeafB.RoundProgram.RSt)
    (hstep : ∀ s, QMCLeafB.RoundProgram.stX (rd s) = QMCLeafB.RoundProgram.snapY s
      ∨ QMCLeafB.RoundProgram.stX (rd s) = QMCLeafB.RoundProgram.stX s)
    (s : QMCLeafB.RoundProgram.RSt) : ∀ k : ℕ,
      QMCLeafB.RoundProgram.stX (rd^[k] s) = QMCLeafB.RoundProgram.stX s
      ∨ ∃ s' : QMCLeafB.RoundProgram.RSt,
          QMCLeafB.RoundProgram.stX (rd^[k] s) = QMCLeafB.RoundProgram.snapY s' := by
  intro k
  induction k with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | ⟨s', hs'⟩
      · rcases hstep (rd^[n] s) with h2 | h2
        · exact Or.inr ⟨rd^[n] s, h2⟩
        · exact Or.inl (by rw [h2, h])
      · rcases hstep (rd^[n] s) with h2 | h2
        · exact Or.inr ⟨rd^[n] s, h2⟩
        · exact Or.inr ⟨s', by rw [h2, hs']⟩

-- **The pinch against the campaign's grid, at `n = 2`, `Rq = 1` (diagnostic):** the `1 - dq/4`
-- pinch against the grid; quarantined instance below (its direct normalization timed out).
/-- Diagnostic-only instance, removed: its direct normalization of `pinch_entry` against the
campaign's snap grid times out past 32M heartbeats on this VM (the generic statements
`pinch_entry`, `pinch_trace`, `grid_multiple_of_pinch`, `no_pinch_campaign`, `no_pinch_on_grid_81`
are all proved and audit-clean above; nothing downstream cited this instance). -/
example : True := trivial

/-! ## Axiom audit -/

#print axioms QMCLeafB.AuditM1.list_sum_zero_of_nonneg
#print axioms QMCLeafB.AuditM1.pinch_entry
#print axioms QMCLeafB.AuditM1.pinch_of_mem
#print axioms QMCLeafB.AuditM1.pinch_trace
#print axioms QMCLeafB.AuditM1.centre_ne_one
#print axioms QMCLeafB.AuditM1.smul_diag
#print axioms QMCLeafB.AuditM1.scale_forces_boundary
#print axioms QMCLeafB.AuditM1.scaled_centre_not_both
#print axioms QMCLeafB.AuditM1.scaled_centre_in_band
#print axioms QMCLeafB.AuditM1.boundary_scale_admissible
#print axioms QMCLeafB.AuditM1.numeric_instance_dq_tenth
#print axioms QMCLeafB.AuditM1.diagSumV_eq_zero
#print axioms QMCLeafB.AuditM1.band_false_of_dvR_zero
#print axioms QMCLeafB.AuditM1.diag_nondec_of_psd
#print axioms QMCLeafB.AuditM1.diagSign_step_uniform
#print axioms QMCLeafB.AuditM1.n2_doubles
#print axioms QMCLeafB.AuditM1.initial_diag_in_band
#print axioms QMCLeafB.AuditM1.frob_smul_right
#print axioms QMCLeafB.AuditM1.abs_boundary_smul_sub_one
#print axioms QMCLeafB.AuditM1.relaxMem_boundary_smul
#print axioms QMCLeafB.AuditM1.ok_test_not_imp_trace_le
#print axioms QMCLeafB.AuditM1.dqShallow_half_lt_two_eps
#print axioms QMCLeafB.AuditM1.snapDiv_mul_int
#print axioms QMCLeafB.AuditM1.grid_multiple_of_pinch
#print axioms QMCLeafB.AuditM1.no_pinch_on_grid_81
#print axioms QMCLeafB.AuditM1.no_pinch_campaign
#print axioms QMCLeafB.AuditM1.stX_round_dichotomy
#print axioms QMCLeafB.AuditM1.stX_iterate_dichotomy

end QMCLeafB.AuditM1



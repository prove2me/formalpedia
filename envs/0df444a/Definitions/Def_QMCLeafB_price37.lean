-- Prove2me | Definitions.Def_QMCLeafB_price37
-- name    : QMCLeafB_price37
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T05:30:13.971672+00:00
-- url     : https://prove2.me/theorems/8f2b9fba-9f35-4b58-9c0e-801b4f87338f
-- title:
--   QMCLeafB price37
-- statement:
--   # `Check_price37_m4` — phase 37, member m4, direction d7 `price-as-lipschitz`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_fal36
/-
# `Check_price37_m4` — phase 37, member m4, direction d7 `price-as-lipschitz`

**The question.**  Phase 37's derivation says: give the programme an ok test that *is* membership
at the round's centre, and then at a bit-`false` point either (A) some round reports ok — the bit is
true and `hok` holds at that round's own centre by definition — or (B) every round reports a
non-member, in which case "each round's oracle cut is a GENUINE separator at its own (rational)
centre, and the only gap to `hcut` (stated at `Cat k`) is m4/ph36's PRICE
`n ⬝ (flat (cX k) − Cat k)`" — so that (B) reduces to paying the price within the ledger.  The
claim to test: *"Either way the collar disappears from the argument."*

**The answer, machine-checked below.**

* **§1 `exists_depth_iff` — the feasible depths at a round are exactly the interval
  `[max 0 (margin − price), ρ·√σ]`.**  Nonempty **iff** `margin − price ≤ ρ·√σ`.  This is a
  two-sided criterion, not a sufficient condition: `del := max 0 (margin − price)` is the least
  legal depth and it is rational, so nothing is lost by the rational ledger.

* **§2 `centre_eq_iff` — B1 is NOT enough, and the derivation's step "price = 0, hence
  `shallowCut_of_separating` gives `del ≡ 0`" is a non-sequitur.**  Making the tested centre *be*
  the accumulated centre kills the price (`enc = 0`), but it leaves `del ≥ margin`; the round is
  then payable **iff the ORACLE'S OWN MARGIN fits the ledger**, `margin ≤ ρ·√σ`.  `margin > 0`
  always, so this is a strictly positive demand that the price analysis never pays.  Receipts:
  `zero_price_infeasible` (price exactly zero, round unpayable — rational numbers), and
  `del_zero_iff_escape` (depth `0`, the only class that dodges the `σ`-decay squeeze, needs the
  ESCAPE inequality `margin ≤ enc`, i.e. the accumulated centre at least `margin` *beyond* the
  tested centre in the cut direction — with `enc = 0` and `margin > 0` that is impossible).

* **§3 `price_abs_le` / `price_attained` — the price is exactly a displacement cost**, and the bound
  is attained.  So B2's demand is precisely a *displacement* statement
  `margin − ‖c‖·‖cX k − Cat k‖ ≤ ρ·√σ_k`, and no cleverness improves the constant.

* **§4 `sqrt_sigma_rat_of_step_rational` / `Cat_sigma_square` — the exact-centre obstruction is
  NOT an artefact of `NormalCut`+`rStep` at `k = 1`: it holds at EVERY round and for EVERY admissible
  depth.**  The engine's step is `a ↦ a + (γ(ρ)/√σ) • p` with `p` rational, `σ = c ⬝ᵥ p` rational,
  and `γ(ρ) = (1−ρ)/(N+1) ≠ 0` for every `ρ ≠ 1` — and every record has `ρ ≤ rmax < 1`.  So a
  coding whose centres are rational forces `σ_k` to be a **rational square at every round**.  That is
  a number-theoretic constraint on the cut data, not on the presentation; it is escapable only by
  choosing the normals so that `σ_k` is a square (which the standard `rStep` permits but does not
  provide), never by rescaling or re-normalising.

* **§4c `support_of_not_relaxBodyLE` — the separation step is EXPLICIT, no Hahn–Banach.**  The
  relaxation is a conjunction of three constraints, so a non-member violates one of them, and each
  violation carries its own nonzero normal supporting the WHOLE relaxation at the point with depth
  `0`: the rank-one normal `v vᵀ` for a violated relaxed PSD, the single-entry normal `± eᵢᵢ` for a
  violated diagonal band, and the objective normal `−A` for a violated objective bound.  So case (B)
  does not need a separation theorem; what it needs is that the accumulated centres are non-members,
  i.e. the hull escape, and nothing else.

* **§4b `cat_rational_iff_square_sigma` — THE DECISION ON B1, both ways.**  For a cut stream with a
  rational start, nonzero witnesses and admissible depths, the accumulated centres are ALL rational
  **iff** every `σ_k = c_k ⬝ᵥ p_k` is a rational square with a positive rational root.  Sufficiency is
  `gamma_div_sqrt_of_square` (`γ/√σ = γ/t` when `σ = t²`), necessity is `Cat_sigma_square`.  So B1 is
  realisable exactly when the normal stream can be steered to make `σ_k` square at every round — and
  no renormalisation, no depth re-parametrisation and no change of presentation substitutes for it.

* **§5 `caseB_iff_depths` — case (B) as an obligation.**  The dichotomy's case (B), written with the
  oracle's own cuts, is *equivalent* to a per-round inequality that is `ShallowCut`'s own content at
  the oracle's normals.  It is therefore a re-statement of the collar's obligation, not a reduction
  of it: the collar does not disappear; it is renamed.

Discipline: `set_option autoImplicit false`; no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`;
`#print axioms` after every theorem, each exactly `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

namespace QMCLeafB.Price37M4

/-! ### The budget arithmetic, in the two directions used everywhere below -/

/-- From `x ≥ 0` and `x² ≤ ρ²σ`: `x` fits the budget `ρ√σ`. -/
theorem le_budget_of_sq {x ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hx : 0 ≤ x)
    (h : x ^ 2 ≤ ρ ^ 2 * σ) : x ≤ ρ * Real.sqrt σ := by
  have hb : (ρ * Real.sqrt σ) ^ 2 = ρ ^ 2 * σ := by rw [mul_pow, Real.sq_sqrt hσ]
  have hb0 : 0 ≤ ρ * Real.sqrt σ := mul_nonneg hρ (Real.sqrt_nonneg σ)
  nlinarith [h, hb, hx, hb0]

/-- From `0 ≤ x ≤ ρ√σ`: `x²` fits the ledger `ρ²σ`. -/
theorem sq_le_of_le_budget {x ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (h : x ≤ ρ * Real.sqrt σ) (hx0 : 0 ≤ x) : x ^ 2 ≤ ρ ^ 2 * σ := by
  have hb : (ρ * Real.sqrt σ) ^ 2 = ρ ^ 2 * σ := by rw [mul_pow, Real.sq_sqrt hσ]
  have hb0 : 0 ≤ ρ * Real.sqrt σ := mul_nonneg hρ (Real.sqrt_nonneg σ)
  nlinarith [h, hb, hx0, hb0]

#print axioms QMCLeafB.Price37M4.le_budget_of_sq
#print axioms QMCLeafB.Price37M4.sq_le_of_le_budget

/-! ## 1.  The feasible depth interval at one round

At a round the record must produce a rational depth `del` with two properties: it must be at least
the price `margin − enc` that re-anchors the oracle's cut from its own rational centre at the
engine's accumulated centre, and it must fit the ledger `del² ≤ ρ²σ`.  The next theorem says
exactly which depths are legal. -/

/-- **MAIN — the feasible depths form an interval, and the interval is nonempty exactly when the
price fits the budget.**  For rational `margin`, `price`-data `enc`, depth ratio `ρ ≥ 0` and squared
cut norm `σ > 0`:

  `∃ del, 0 ≤ del ∧ margin − enc ≤ del ∧ del² ≤ ρ²σ`  ⟺  `margin − enc ≤ ρ·√σ`.

Both directions are used below: the forward one is the *falsification* (a round whose margin exceeds
the budget admits no depth at all), the backward one is the *construction* (`del := max 0 (…)`). -/
theorem exists_depth_iff {mg ρ σ enc : ℚ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) :
    (∃ del : ℚ, 0 ≤ del ∧ mg - enc ≤ del
        ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)))
      ↔ (((mg - enc : ℚ) : ℝ)) ≤ (((ρ : ℚ) : ℝ)) * Real.sqrt (((σ : ℚ) : ℝ)) := by
  have hS : (0 : ℝ) < ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  have hR : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) := by exact_mod_cast hρ
  have hb0 : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) :=
    mul_nonneg hR (Real.sqrt_nonneg _)
  constructor
  · rintro ⟨del, h0, hle, hsq⟩
    have hd0 : (0 : ℝ) ≤ ((del : ℚ) : ℝ) := by exact_mod_cast h0
    have hd : ((del : ℚ) : ℝ) ≤ ((ρ : ℚ) : ℝ) * Real.sqrt ((σ : ℚ) : ℝ) :=
      le_budget_of_sq hR hS.le hd0 hsq
    have hp : (((mg - enc : ℚ) : ℝ)) ≤ ((del : ℚ) : ℝ) := by exact_mod_cast hle
    linarith
  · intro hmain
    have hcast : ((max 0 (mg - enc) : ℚ) : ℝ) = max 0 ((mg - enc : ℚ) : ℝ) := by
      rw [Rat.cast_max, Rat.cast_zero]
    refine ⟨max 0 (mg - enc), le_max_left _ _, le_max_right _ _, ?_⟩
    rw [hcast]
    rcases le_or_gt (mg - enc) 0 with hle | hlt
    · rw [max_eq_left (by exact_mod_cast hle : ((mg - enc : ℚ) : ℝ) ≤ 0)]
      have h0 : (0 : ℝ) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)) := by
        have h := mul_nonneg (sq_nonneg ((ρ : ℚ) : ℝ)) hS.le
        simpa using h
      simpa using h0
    · rw [max_eq_right (by exact_mod_cast hlt.le : (0 : ℝ) ≤ ((mg - enc : ℚ) : ℝ))]
      have hM0 : (0 : ℝ) ≤ (((mg - enc : ℚ) : ℝ)) := by exact_mod_cast hlt.le
      exact sq_le_of_le_budget hR hS.le hmain hM0

#print axioms QMCLeafB.Price37M4.exists_depth_iff

/-- **The least legal depth is `max 0 (margin − enc)`, and it is rational.**  So working with the
rational ledger loses nothing: the criterion above is not weakened by rationality. -/
theorem least_depth_is_max {mg enc : ℚ} :
    ∃ del : ℚ, del = max 0 (mg - enc) ∧ 0 ≤ del ∧ mg - enc ≤ del :=
  ⟨max 0 (mg - enc), rfl, le_max_left _ _, le_max_right _ _⟩

#print axioms QMCLeafB.Price37M4.least_depth_is_max

/-- **The canonical witness depth** — `del := max 0 (margin − enc)` — is legal whenever the price fits
the budget.  This is the exact content of the criterion's backward direction, packaged for streams. -/
theorem depth_witness {mg ρ σ enc : ℚ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    (h : (((mg - enc : ℚ) : ℝ)) ≤ (((ρ : ℚ) : ℝ)) * Real.sqrt (((σ : ℚ) : ℝ))) :
    0 ≤ max 0 (mg - enc) ∧ mg - enc ≤ max 0 (mg - enc)
      ∧ (((max 0 (mg - enc) : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)) := by
  have hR : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) := by exact_mod_cast hρ
  have hS : (0 : ℝ) < ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  refine ⟨le_max_left _ _, le_max_right _ _, ?_⟩
  have hcast : ((max 0 (mg - enc) : ℚ) : ℝ) = max 0 ((mg - enc : ℚ) : ℝ) := by
    rw [Rat.cast_max, Rat.cast_zero]
  rw [hcast]
  rcases le_or_gt (mg - enc) 0 with hle | hlt
  · rw [max_eq_left (by exact_mod_cast hle : ((mg - enc : ℚ) : ℝ) ≤ 0)]
    have h0 : (0 : ℝ) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)) := by
      have hh : (0 : ℝ) ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)) :=
        mul_nonneg (sq_nonneg _) hS.le
      simpa using hh
    simpa using h0
  · rw [max_eq_right (by exact_mod_cast hlt.le : (0 : ℝ) ≤ ((mg - enc : ℚ) : ℝ))]
    exact sq_le_of_le_budget hR hS.le h (by exact_mod_cast hlt.le)

#print axioms QMCLeafB.Price37M4.depth_witness

/-! ## 2.  B1 is not enough: the price is not the whole gap

The derivation's case (B) says the only gap to `hcut` at `Cat k` is the price.  That is true of
`hcut` — and useless for the record, whose ledger also caps the depth.  With the tested centre
equal to the accumulated centre the price *vanishes*, and what is left is the oracle's own margin
against the budget.  The two receipts below are the point: a zero price can still leave no legal
depth at all (`zero_price_infeasible`), and the depth `0` escape needs an inequality that `enc = 0`
makes impossible (`del_zero_iff_escape`). -/

/-- **B1's residual, exactly.**  If the tested centre is the accumulated centre (`enc = 0`), the
round is payable **iff the oracle's own margin fits the ledger** — not `del ≡ 0`, and not free. -/
theorem centre_eq_iff {mg ρ σ : ℚ} (hσ : 0 < σ) (hρ : 0 ≤ ρ) :
    (∃ del : ℚ, 0 ≤ del ∧ mg ≤ del
        ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ)))
      ↔ ((mg : ℚ) : ℝ) ≤ ((ρ : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ)) := by
  have h := exists_depth_iff (mg := mg) (enc := 0) (ρ := ρ) (σ := σ) hσ hρ
  simpa using h

#print axioms QMCLeafB.Price37M4.centre_eq_iff

/-- **FALSIFICATION RECEIPT — price exactly zero, round still unpayable.**  Let the depth ratio
satisfy `ρ < 1` (in the campaign every record has `ρ ≤ rmax < 1`; the campaign's own choice
`rmax = 1/(4n²)` is `1/16` at `n = 2`), take `σ = 1` and an oracle margin `mg = 1`.  The centre
identity `enc = 0` holds, so m4/ph36's price `mg − enc = 1` is entirely absorbed by
`hcut_of_relaxCut_price` at `del = 1` — and yet **no rational depth satisfies the ledger**:
`1 ≤ del` forces `del² ≥ 1 > ρ²`.  So "price = 0 ⟹ `ShallowCut` with `del ≡ 0`" is false as an
inference: the price does not vanish into depth `0`, it vanishes into depth `mg = 1`, which the
ledger refuses. -/
theorem zero_price_infeasible_of_lt_one {ρ : ℚ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ¬ ∃ del : ℚ, 0 ≤ del ∧ (1 : ℚ) ≤ del
        ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((1 : ℚ) : ℝ)) := by
  rintro ⟨del, h0, h1, h2⟩
  have h1R : (1 : ℝ) ≤ ((del : ℚ) : ℝ) := by exact_mod_cast h1
  have hρ1R : ((ρ : ℚ) : ℝ) < 1 := by exact_mod_cast hρ1
  have hρ0R : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) := by exact_mod_cast hρ0
  have hsq : (1 : ℝ) ≤ (((del : ℚ) : ℝ)) ^ 2 := by
    have hm := mul_le_mul h1R h1R zero_le_one (by linarith)
    nlinarith [hm]
  have h1c : (((1 : ℚ) : ℝ)) = 1 := by norm_num
  have hb : (((ρ : ℚ) : ℝ)) ^ 2 < 1 := by
    have h2' : (((ρ : ℚ) : ℝ)) ^ 2 * (((1 : ℚ) : ℝ)) < 1 := by
      have hlt : (((ρ : ℚ) : ℝ)) ^ 2 < 1 := by nlinarith
      simpa using hlt
    rwa [h1c, mul_one] at h2'
  have h2'' : (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 := by
    rw [h1c, mul_one] at h2
    exact h2
  linarith

#print axioms QMCLeafB.Price37M4.zero_price_infeasible_of_lt_one

/-- The campaign's own depth ratio `1/16` as an instance. -/
theorem zero_price_infeasible :
    ¬ ∃ del : ℚ, 0 ≤ del ∧ (1 : ℚ) ≤ del
        ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((1 / 16 : ℚ) : ℝ)) ^ 2 * (((1 : ℚ) : ℝ)) :=
  zero_price_infeasible_of_lt_one (by norm_num) (by norm_num)

#print axioms QMCLeafB.Price37M4.zero_price_infeasible

/-- **The other side: a NEGATIVE price makes the round free.**  With the accumulated centre `2`
*beyond* the tested centre in the cut direction (`enc = 2`) and margin `1`, the least legal depth is
`max 0 (1 − 2) = 0`, and `0² ≤ rmax²σ`.  So depth `0` is bought by the ESCAPE inequality, never by
the centre identity. -/
theorem negative_price_free :
    ∃ del : ℚ, 0 ≤ del ∧ (1 : ℚ) - 2 ≤ del
        ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((1 / 16 : ℚ) : ℝ)) ^ 2 * (((1 : ℚ) : ℝ)) :=
  ⟨0, le_refl 0, by norm_num, by norm_num⟩

#print axioms QMCLeafB.Price37M4.negative_price_free

/-- **Depth `0` is exactly the escape inequality.**  For any rate `mg`, the least legal depth is `0`
exactly when the accumulated centre is at least `mg` beyond the tested centre in the cut direction.
This is the reading of `del ≡ 0` that m6/ph35's `shallowCut_of_separating` needs, and it is
**impossible** when the tested centre *is* the accumulated centre and the margin is positive. -/
theorem del_zero_iff_escape {mg enc : ℚ} :
    mg - enc ≤ 0 ↔ mg ≤ enc := by
  constructor <;> intro h <;> linarith

#print axioms QMCLeafB.Price37M4.del_zero_iff_escape

/-- **Hence: at the exact centre, depth `0` is unavailable at every round with a positive margin.** -/
theorem centre_eq_no_zero_depth {mg : ℚ} (hm : 0 < mg) : ¬ (mg - 0 ≤ 0) := by
  rw [del_zero_iff_escape]
  linarith

#print axioms QMCLeafB.Price37M4.centre_eq_no_zero_depth

/-- **Depth `0` for a whole stream, exactly.**  A record with `del ≡ 0` exists through these cuts
iff the accumulated centre is at least the `k`-th margin beyond the `k`-th tested centre in the
`k`-th cut direction — the ESCAPE inequality, round by round.  At the exact centre (`en ≡ 0`) no
stream with positive margins satisfies it. -/
theorem zero_depth_stream_iff {Km : ℕ} {mg en : ℕ → ℚ} :
    (∀ k, k < Km → mg k - en k ≤ 0) ↔ ∀ k, k < Km → mg k ≤ en k := by
  constructor
  · intro H k hk; have := H k hk; linarith
  · intro H k hk; have := H k hk; linarith

#print axioms QMCLeafB.Price37M4.zero_depth_stream_iff

/-! ## 3.  The price is a displacement cost, and the constant is attained

`enc = c ⬝ᵥ (cX − Cat k)` is a bilinear pairing, so by Cauchy–Schwarz it is bounded by the normal's
length times the centre displacement.  The bound is *attained*, so the price really is a displacement
cost with no improvable constant: B2 is a statement about how far the programme's rational centre may
sit from the engine's accumulated point. -/

/-- **Cauchy–Schwarz in the flat coordinates**: `|c ⬝ᵥ u| ≤ ‖c‖·‖u‖`. -/
theorem price_abs_le {N : ℕ} (c u : Fin N → ℝ) :
    |∑ i, c i * u i| ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, u i ^ 2) := by
  have hA : (0 : ℝ) ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hB : (0 : ℝ) ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hCS : (∑ i, c i * u i) ^ 2 ≤ (∑ i, c i ^ 2) * (∑ i, u i ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ) c u
  have h := Real.sqrt_le_sqrt hCS
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hA] at h
  exact h

#print axioms QMCLeafB.Price37M4.price_abs_le

/-- **SHARP — the displacement bound is attained.**  The worst case is `u = c`: the price is then
exactly `‖c‖·‖u‖`.  So no argument (no choice of normal, no renormalisation, no averaging) improves
the constant in B2's demand. -/
theorem price_attained {N : ℕ} (c : Fin N → ℝ) :
    ∃ u : Fin N → ℝ,
      ∑ i, c i * u i = Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, u i ^ 2) := by
  refine ⟨c, ?_⟩
  have hA : (0 : ℝ) ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have h1 : (∑ i, c i * c i) = ∑ i, c i ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by ring)
  have h2 : Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, c i ^ 2) = ∑ i, c i ^ 2 := by
    rw [← pow_two, Real.sq_sqrt hA]
  rw [h1, h2]

#print axioms QMCLeafB.Price37M4.price_attained

/-- **NECESSITY, for an ARBITRARY (even irrational) price.**  Whatever normal is chosen and whatever
the actual pairing `enc` is, a legal round at depth `del` forces `margin − enc ≤ ρ·√σ`.  This is the
direction that bites: it is an upper bound on how much price the budget can absorb. -/
theorem price_must_fit {mg ρ σ : ℚ} {enc : ℝ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {del : ℚ} (h0 : 0 ≤ del) (hle : ((mg : ℚ) : ℝ) - enc ≤ ((del : ℚ) : ℝ))
    (hsq : (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ))) :
    ((mg : ℚ) : ℝ) - enc ≤ ((ρ : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ)) := by
  have hS : (0 : ℝ) < ((σ : ℚ) : ℝ) := by exact_mod_cast hσ
  have hR : (0 : ℝ) ≤ ((ρ : ℚ) : ℝ) := by exact_mod_cast hρ
  have hd0 : (0 : ℝ) ≤ ((del : ℚ) : ℝ) := by exact_mod_cast h0
  have hd := le_budget_of_sq hR hS.le hd0 hsq
  linarith

#print axioms QMCLeafB.Price37M4.price_must_fit

/-- **The price, in the engine's flat coordinates.**  With `enc = c ⬝ᵥ u` the round's budget absorbs
the pairing additively: a legal round forces `margin − c ⬝ᵥ u ≤ ρ·√σ`.  By `price_abs_le` the price
is at most `‖c‖·‖u‖`, and by `price_attained` that is attained — so B2 is exactly the statement that
the accumulated centre stays within `(margin − ρ√σ)/‖c‖` of the tested centre. -/
theorem displacement_form {N : ℕ} {mg ρ σ : ℚ} (hσ : 0 < σ) (hρ : 0 ≤ ρ)
    {c u : Fin N → ℝ} {del : ℚ} (h0 : 0 ≤ del)
    (hle : ((mg : ℚ) : ℝ) - ∑ i, c i * u i ≤ ((del : ℚ) : ℝ))
    (hsq : (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ))) :
    ((mg : ℚ) : ℝ) - (∑ i, c i * u i)
      ≤ ((ρ : ℚ) : ℝ) * Real.sqrt (((σ : ℚ) : ℝ)) :=
  price_must_fit hσ hρ h0 hle hsq

#print axioms QMCLeafB.Price37M4.displacement_form

/-! ## 4.  The exact-centre obstruction, at every round and every depth

m1/ph30's `hctr_one_forces_square` says `Cat 1 = (γ/√σ) • p` with `cX` rational forces `σ` to be a
square, and `not_hctr_initShape_two` then kills the shelf's init.  The question for phase 37 is
whether this binds *every* coding or only that one `NormalCut`/`rStep` choice.  The answer below is
the abstract form: it is a property of the STEP, not of the presentation — the displacement is
`(γ(ρ)/√σ) • p` with `p` rational and `σ` rational, so a rational centre forces `√σ` rational.  It
holds at every round, at every depth ratio, and for every normal stream. -/

/-- **The algebraic core.**  If a rational point `x` is displaced to a rational point `y` by
`(g/√s) • p` with `p ≠ 0`, `g ≠ 0` and `s > 0`, then `√s` is rational.  Nothing here refers to the
ellipsoid method: this is why the square condition is unavoidable. -/
theorem sqrt_sigma_rat_of_step_rational {N : ℕ} {x y p : Fin N → ℚ} {g s : ℚ}
    (hp : p ≠ 0) (hg : g ≠ 0) (hs : 0 < s)
    (hstep : ∀ i, ((y i : ℚ) : ℝ)
        = ((x i : ℚ) : ℝ) + (((g : ℚ) : ℝ) / Real.sqrt (((s : ℚ) : ℝ))) * ((p i : ℚ) : ℝ)) :
    ∃ t : ℚ, ((t : ℚ) : ℝ) = Real.sqrt (((s : ℚ) : ℝ)) := by
  have hex : ∃ i, p i ≠ 0 := by
    by_contra h
    push Not at h
    exact hp (funext h)
  obtain ⟨i, hi⟩ := hex
  have hgR : ((g : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hg
  have hpiR : ((p i : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hi
  have hsR : (0 : ℝ) < ((s : ℚ) : ℝ) := by exact_mod_cast hs
  have hsqR : (0 : ℝ) < Real.sqrt (((s : ℚ) : ℝ)) := Real.sqrt_pos.mpr hsR
  have hmul : (((y i - x i : ℚ) : ℝ)) * Real.sqrt (((s : ℚ) : ℝ))
      = ((g : ℚ) : ℝ) * ((p i : ℚ) : ℝ) := by
    have h := hstep i
    have hcast : (((y i - x i : ℚ) : ℝ))
        = ((y i : ℚ) : ℝ) - ((x i : ℚ) : ℝ) := by push_cast; ring
    rw [hcast, h]
    field_simp
    ring
  have hqne : (y i - x i : ℚ) ≠ 0 := by
    intro h
    rw [h] at hmul
    simp only [Rat.cast_zero, zero_mul] at hmul
    exact mul_ne_zero hgR hpiR hmul.symm
  refine ⟨(g * p i) / (y i - x i), ?_⟩
  have hcast : (((g * p i) / (y i - x i) : ℚ) : ℝ)
      = (((g : ℚ) : ℝ) * ((p i : ℚ) : ℝ)) / (((y i - x i : ℚ) : ℝ)) := by
    push_cast
    ring
  rw [hcast, div_eq_iff (by exact_mod_cast hqne)]
  rw [mul_comm (Real.sqrt (((s : ℚ) : ℝ)))]
  exact hmul.symm

#print axioms QMCLeafB.Price37M4.sqrt_sigma_rat_of_step_rational

/-- `γ(ρ) = (1 − ρ)/(N + 1)` vanishes only at `ρ = 1`; every admissible depth ratio is `< 1`. -/
theorem gammaR_ne_zero_iff {N : ℕ} {ρ : ℝ} :
    QMCLeafB.EngineIterates.gammaR N ρ = 0 ↔ ρ = 1 := by
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  rw [QMCLeafB.EngineIterates.gammaR, div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linarith
    · exact absurd h hN
  · intro h
    exact Or.inl (by rw [h]; ring)

#print axioms QMCLeafB.Price37M4.gammaR_ne_zero_iff

/-- **THE EXACT-CENTRE OBSTRUCTION AT EVERY ROUND.**  At round `k` of ANY cut stream: if the round's
witness `p_k` is nonzero, its depth ratio is not `1`, both the accumulated centre `Cat k` and the next
one `Cat (k+1)` are rational vectors, and `σ_k = c_k ⬝ᵥ p_k` is positive, then `√σ_k` is rational —
i.e. `σ_k` is a rational square.

Consequently no re-normalisation, re-parametrisation of the depth, or change of the normal stream
makes the accumulated centre rational: the ONLY way is to choose the cut data so that `σ_k` is a
square at every round.  This is the intrinsic form of m1/ph30's `hctr_one_forces_square`. -/
theorem Cat_sigma_square {N : ℕ} {a0 : Fin N → ℝ} {cd : ℕ → QMCLeafB.EngineIterates.CutData N}
    {k : ℕ} (hp : (cd k).p ≠ 0) (hrho : (cd k).rho ≠ 1)
    (hσ : 0 < QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p)
    (hk : ∃ x : Fin N → ℚ, ∀ i, QMCLeafB.EngineIterates.Cat N a0 cd k i = ((x i : ℚ) : ℝ))
    (hk1 : ∃ x : Fin N → ℚ, ∀ i, QMCLeafB.EngineIterates.Cat N a0 cd (k + 1) i
      = ((x i : ℚ) : ℝ)) :
    ∃ t : ℚ, ((t : ℚ) : ℝ)
      = Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)) := by
  obtain ⟨x, hx⟩ := hk
  obtain ⟨y, hy⟩ := hk1
  -- the rational step coefficient `g = (1 - ρ)/(N + 1)`
  set g : ℚ := (1 - (cd k).rho) / ((N : ℚ) + 1) with hgdef
  have hgR : (((g : ℚ) : ℝ)) = QMCLeafB.EngineIterates.gammaR N (((cd k).rho : ℚ) : ℝ) := by
    rw [hgdef]
    simp only [QMCLeafB.EngineIterates.gammaR]
    push_cast
    ring
  have hg : g ≠ 0 := by
    have h1 : (1 - (cd k).rho) ≠ 0 := by
      intro h
      apply hrho
      have : ((cd k).rho : ℚ) = 1 := by linarith
      exact this
    have h2 : ((N : ℚ) + 1) ≠ 0 := by positivity
    rw [hgdef]
    exact div_ne_zero h1 h2
  -- assemble the step identity
  have hstep : ∀ i, ((y i : ℚ) : ℝ)
      = ((x i : ℚ) : ℝ) + (((g : ℚ) : ℝ)
          / Real.sqrt (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)))
          * ((cd k).p i : ℚ) := by
    intro i
    have hunf : QMCLeafB.EngineIterates.Cat N a0 cd (k + 1)
        = QMCLeafB.EngineIterates.stepCentre N (QMCLeafB.EngineIterates.Cat N a0 cd k)
            (QMCLeafB.EngineIterates.cutCR cd k) (QMCLeafB.EngineIterates.cutPR cd k)
            (((cd k).rho : ℚ) : ℝ) :=
      QMCLeafB.EngineIterates.Cat_unfold a0 cd k
    have h1 := congrFun hunf i
    rw [hy i] at h1
    simp only [QMCLeafB.EngineIterates.stepCentre,
      QMCLeafB.EngineIterates.cutPR, QMCLeafB.EngineIterates.sqrtSigmaR,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [hx i] at h1
    rw [← QMCLeafB.EngineIterates.cast_sigmaQ (cd k).c (cd k).p, ← hgR] at h1
    exact h1
  exact sqrt_sigma_rat_of_step_rational (x := x) (y := y) (p := (cd k).p) (g := g)
    (s := QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p) hp hg hσ hstep

#print axioms QMCLeafB.Price37M4.Cat_sigma_square

/-- **The escape hatch, made explicit.**  If `σ = t²` with `t > 0` then `g/√σ = g/t`, so the step is
the RATIONAL multiple `(g/t) • p` and a rational centre stays rational.  Steering the normals so that
every `σ_k` is a square is therefore the ONLY repair of the exact-centre obstruction. -/
theorem gamma_div_sqrt_of_square {g t : ℚ} (ht : 0 < t) :
    ((g : ℚ) : ℝ) / Real.sqrt (((t * t : ℚ) : ℝ)) = ((g / t : ℚ) : ℝ) := by
  have hcast : (((t * t : ℚ) : ℝ)) = ((t : ℚ) : ℝ) ^ 2 := by push_cast; ring
  have htR : (0 : ℝ) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast ht.le
  rw [hcast, Real.sqrt_sq htR]
  have htne : ((t : ℚ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  push_cast
  field_simp

#print axioms QMCLeafB.Price37M4.gamma_div_sqrt_of_square

/-! ### 4c.  The separation step is EXPLICIT: no Hahn–Banach, three named normals

Case (B) needs, at each round, a normal that supports the relaxation at the accumulated centre.  That
is not an appeal to a separation theorem: the relaxation is a conjunction of three constraints, so a
non-member violates one of them, and each violation carries its own normal —

* violated relaxed PSD at `v`  ⟹ the rank-one normal `v vᵀ`;
* violated diagonal band at `i` ⟹ the single-entry normal `± eᵢᵢ`;
* violated objective bound      ⟹ the objective normal `−A`.

In every case `⟪N, X₀⟫ ≤ ⟪N, X⟫` for the WHOLE relaxation, i.e. depth `0` on the nose.  So the only
geometric content left in the record horn is the *hull escape* — that the accumulated centres avoid
the relaxation — and not the existence of a separator. -/

/-- The Frobenius pairing with a single-entry normal. -/
theorem frob_single {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (a : ℝ) :
    QMCLeafB.BallFloor.frob (Matrix.single i i a) X = a * X i i := by
  rw [QMCLeafB.BallFloor.frob, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
    · intro x _ hx
      rw [Matrix.single_apply, if_neg (by rintro ⟨-, h⟩; exact hx h.symm)]
      exact zero_mul _
    · intro h; exact absurd (Finset.mem_univ i) h
  · intro j _ hj
    refine Finset.sum_eq_zero (fun x _ => ?_)
    rw [Matrix.single_apply, if_neg (by rintro ⟨h, -⟩; exact hj h.symm)]
    exact zero_mul _
  · intro h; exact absurd (Finset.mem_univ i) h

#print axioms QMCLeafB.Price37M4.frob_single

/-- A single-entry normal is nonzero. -/
theorem single_ne_zero {n : ℕ} {i : Fin n} {a : ℝ} (ha : a ≠ 0) :
    Matrix.single i i a ≠ 0 := by
  intro h
  have h' : Matrix.single i i a i i = (0 : Matrix (Fin n) (Fin n) ℝ) i i := by rw [h]
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩] at h'
  simp at h'
  exact ha h'

#print axioms QMCLeafB.Price37M4.single_ne_zero

/-- The rank-one normal is nonzero when the direction is. -/
theorem vecMulVec_ne_zero {n : ℕ} {v : Fin n → ℝ} (hv : v ≠ 0) :
    Matrix.vecMulVec v v ≠ 0 := by
  intro h
  apply hv
  funext i
  have h' : Matrix.vecMulVec v v i i = (0 : Matrix (Fin n) (Fin n) ℝ) i i := by rw [h]
  simp only [Matrix.vecMulVec_apply, Matrix.zero_apply] at h'
  exact mul_self_eq_zero.mp h'

#print axioms QMCLeafB.Price37M4.vecMulVec_ne_zero

/-- FROBENIUS SIGN: `⟪−A, X⟫ = −⟪A, X⟫`. -/
theorem frob_neg_left {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) :
    QMCLeafB.BallFloor.frob (-A) X = -QMCLeafB.BallFloor.frob A X := by
  simp only [QMCLeafB.BallFloor.frob, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

#print axioms QMCLeafB.Price37M4.frob_neg_left

/-- The `BallFloor` form of the rank-one identity (`RelaxOracle`'s is stated for `SepOracle`'s
pairing; both are the same function). -/
theorem qfR_eq_frob_vecMulVec {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    QMCLeafB.BallFloor.frob (Matrix.vecMulVec v v) X = QMCLeafB.BallFloor.qfR X v :=
  (QMCLeafB.SepOracle.qf_eq_frob X v).symm

#print axioms QMCLeafB.Price37M4.qfR_eq_frob_vecMulVec

/-- **SUPPORT AT A NON-MEMBER, EXPLICITLY.**  If `X₀` is not in the relaxation then an explicit
nonzero normal supports the relaxation at `X₀` with depth exactly `0`. -/
theorem support_of_not_relaxBodyLE {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u δ : ℝ}
    {X₀ : Matrix (Fin n) (Fin n) ℝ} (hA : A ≠ 0)
    (h : ¬ QMCLeafB.BallFloor.relaxBodyLE A u δ X₀) :
    ∃ N : Matrix (Fin n) (Fin n) ℝ, N ≠ 0 ∧
      ∀ X, QMCLeafB.BallFloor.relaxBodyLE A u δ X →
        QMCLeafB.BallFloor.frob N X₀ ≤ QMCLeafB.BallFloor.frob N X := by
  by_cases hP : ∀ x : Fin n → ℝ,
      -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.BallFloor.qfR X₀ x
  · by_cases hQ : ∀ i, |X₀ i i - 1| ≤ δ / 4
    · -- the objective bound is violated: normal `−A`
      have hR : ¬ (QMCLeafB.BallFloor.frob A X₀ ≤ u + δ / 2) := by
        intro hR'; exact h ⟨hP, hQ, hR'⟩
      refine ⟨-A, neg_ne_zero.mpr hA, ?_⟩
      intro X hX
      obtain ⟨-, -, hX3⟩ := hX
      rw [frob_neg_left, frob_neg_left]
      linarith
    · -- the diagonal band is violated: normal `± eᵢᵢ`
      push Not at hQ
      obtain ⟨i, hi⟩ := hQ
      rw [lt_abs] at hi
      rcases hi with hgt | hlt
      · -- `1 + δ/4 < X₀ i i`: normal `− eᵢᵢ`
        refine ⟨Matrix.single i i (-1), single_ne_zero (by norm_num), ?_⟩
        intro X hX
        obtain ⟨-, hX2, -⟩ := hX
        rw [frob_single, frob_single]
        have h2 := abs_le.1 (hX2 i)
        have hδ0 : (0 : ℝ) ≤ δ := by linarith [h2.1, h2.2]
        nlinarith [h2.1]
      · -- `X₀ i i < 1 - δ/4`: normal `+ eᵢᵢ`
        refine ⟨Matrix.single i i 1, single_ne_zero one_ne_zero, ?_⟩
        intro X hX
        obtain ⟨-, hX2, -⟩ := hX
        rw [frob_single, frob_single]
        have h2 := abs_le.1 (hX2 i)
        have hδ0 : (0 : ℝ) ≤ δ := by linarith [h2.1, h2.2]
        nlinarith [h2.2]
  · -- the relaxed PSD is violated: normal `v vᵀ`
    push Not at hP
    obtain ⟨v, hv⟩ := hP
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0] at hv
      simp [QMCLeafB.BallFloor.qfR] at hv
    refine ⟨Matrix.vecMulVec v v, vecMulVec_ne_zero hv0, ?_⟩
    intro X hX
    obtain ⟨hX1, -, -⟩ := hX
    rw [qfR_eq_frob_vecMulVec, qfR_eq_frob_vecMulVec]
    exact le_of_lt (lt_of_lt_of_le hv (hX1 v))

#print axioms QMCLeafB.Price37M4.support_of_not_relaxBodyLE

/-! ### 4b.  THE DECISION ON B1: exact-centre coding exists iff every `σ_k` is a rational square

`Cat_sigma_square` is the necessity.  The sufficiency is the escape: if `σ_k = t_k²` with `t_k > 0`
then `γ(ρ_k)/√σ_k = γ(ρ_k)/t_k` is rational, so the step is a rational multiple of the rational
witness and the whole centre stream stays in `ℚ^N`.  Together: the exact-centre coding is realisable
**exactly** when the normal stream can be chosen so that `σ_k` is a square at every round. -/

/-- **THE DECISION ON B1.**  For a cut stream with a rational start, nonzero witnesses and admissible
depths (`ρ_k ≠ 1`), the accumulated centres are ALL rational **iff** every `σ_k = c_k ⬝ᵥ p_k` is a
rational square with a positive rational root.  Nothing else is needed, and nothing less suffices:
no re-normalisation, no re-parametrisation of the depth and no change of the presentation escapes the
square condition, because it is the *step law* `a ↦ a + (γ(ρ)/√σ) • p` that forces it. -/
theorem cat_rational_iff_square_sigma {N : ℕ} {a0 : Fin N → ℚ}
    {cd : ℕ → QMCLeafB.EngineIterates.CutData N}
    (hp : ∀ k, (cd k).p ≠ 0) (hrho : ∀ k, (cd k).rho ≠ 1)
    (hσ : ∀ k, 0 < QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p) :
    (∀ k, ∃ x : Fin N → ℚ,
        ∀ i, QMCLeafB.EngineIterates.Cat N (fun i => ((a0 i : ℚ) : ℝ)) cd k i
          = ((x i : ℚ) : ℝ))
      ↔ ∀ k, ∃ t : ℚ, 0 < t ∧ t * t = QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p := by
  constructor
  · intro H k
    obtain ⟨t, ht⟩ := Cat_sigma_square (a0 := fun i => ((a0 i : ℚ) : ℝ)) (cd := cd)
      (k := k) (hp k) (hrho k) (hσ k) (H k) (H (k + 1))
    have hσR : (0 : ℝ) < (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)) := by
      exact_mod_cast hσ k
    have htR : (0 : ℝ) < ((t : ℚ) : ℝ) := by
      rw [ht]; exact Real.sqrt_pos.mpr hσR
    refine ⟨t, ?_, ?_⟩
    · exact_mod_cast htR
    · have hsq : ((t * t : ℚ) : ℝ)
          = (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)) := by
        have ht2 : (((t : ℚ) : ℝ)) ^ 2
            = (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ)) := by
          rw [ht, Real.sq_sqrt hσR.le]
        have hcast : ((t * t : ℚ) : ℝ) = (((t : ℚ) : ℝ)) ^ 2 := by push_cast; ring
        rw [hcast, ht2]
      exact_mod_cast hsq
  · intro H
    choose t htpos htsq using H
    set g : ℕ → ℚ := fun k => (1 - (cd k).rho) / ((N : ℚ) + 1) with hgdef
    set F : ℕ → Fin N → ℚ := fun k =>
      Nat.rec a0 (fun k f => f + fun i => (g k / t k) * (cd k).p i) k with hFdef
    have hF0 : F 0 = a0 := rfl
    have hFs : ∀ k, F (k + 1) = F k + fun i => (g k / t k) * (cd k).p i := fun k => rfl
    have hmain : ∀ k, ∀ i, QMCLeafB.EngineIterates.Cat N
        (fun i => ((a0 i : ℚ) : ℝ)) cd k i = ((F k i : ℚ) : ℝ) := by
      intro k
      induction k with
      | zero =>
          intro i
          rfl
      | succ k ih =>
          intro i
          have hunf : QMCLeafB.EngineIterates.Cat N (fun i => ((a0 i : ℚ) : ℝ)) cd (k + 1)
              = QMCLeafB.EngineIterates.stepCentre N
                  (QMCLeafB.EngineIterates.Cat N (fun i => ((a0 i : ℚ) : ℝ)) cd k)
                  (QMCLeafB.EngineIterates.cutCR cd k)
                  (QMCLeafB.EngineIterates.cutPR cd k) (((cd k).rho : ℚ) : ℝ) :=
            QMCLeafB.EngineIterates.Cat_unfold _ cd k
          have h1 := congrFun hunf i
          unfold QMCLeafB.EngineIterates.stepCentre at h1
          simp only [QMCLeafB.EngineIterates.cutPR,
            QMCLeafB.EngineIterates.sqrtSigmaR,
            Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
          rw [ih i] at h1
          have hcre : QMCLeafB.EngineIterates.cutCR cd k
              = (fun i => (((cd k).c i : ℚ) : ℝ)) := rfl
          have hpre : QMCLeafB.EngineIterates.cutPR cd k
              = (fun i => (((cd k).p i : ℚ) : ℝ)) := rfl
          rw [hcre, hpre] at h1
          rw [← QMCLeafB.EngineIterates.cast_sigmaQ (cd k).c (cd k).p] at h1
          have hσeq : (((QMCLeafB.EngineIterates.sigmaQ (cd k).c (cd k).p : ℚ) : ℝ))
              = (((t k * t k : ℚ) : ℝ)) := by
            rw [htsq k]
          have hgR : (((g k : ℚ) : ℝ))
              = QMCLeafB.EngineIterates.gammaR N (((cd k).rho : ℚ) : ℝ) := by
            rw [hgdef]
            simp only [QMCLeafB.EngineIterates.gammaR]
            push_cast
            ring
          rw [hσeq, ← hgR] at h1
          rw [QMCLeafB.Price37M4.gamma_div_sqrt_of_square (g := g k) (t := t k) (htpos k)] at h1
          rw [hFs k]
          simp only [Pi.add_apply]
          push_cast
          push_cast at h1
          linarith [h1]
    exact fun k => ⟨F k, hmain k⟩

#print axioms QMCLeafB.Price37M4.cat_rational_iff_square_sigma

/-! ## 5.  Case (B) as an obligation: it is the collar, renamed

The dichotomy's case (B) says: every round reports a non-member, so every round's oracle cut is a
genuine separator at its own centre.  Written with the depths and the ledger, that is exactly the
per-round criterion of §1 — the same inequality the record has always owed.  It is *equivalent* to
the depth stream's existence, so it is neither weaker nor stronger than the collar's obligation. -/

/-- **The case-(B) obligation, per round**: the oracle's own cut, re-anchored at the accumulated
centre, fits the depth ledger. -/
def CaseB (Km : ℕ) (mg rh sg en : ℕ → ℚ) : Prop :=
  ∀ k, k < Km → (((mg k - en k : ℚ) : ℝ))
    ≤ (((rh k : ℚ) : ℝ)) * Real.sqrt (((sg k : ℚ) : ℝ))

/-- **Case (B) ⟺ a legal depth stream.**  So case (B) is not a reduction of the collar's obligation:
it IS the collar's obligation, stated in the oracle's own data.  In particular (A)∨(B) does not
remove the ball/cube/parallelotope analysis — at a collar point with all centres non-members the
whole content is still `CaseB`. -/
theorem caseB_iff_depths {Km : ℕ} {mg rh sg en : ℕ → ℚ}
    (hσ : ∀ k, 0 < sg k) (hρ : ∀ k, 0 ≤ rh k) :
    CaseB Km mg rh sg en
      ↔ ∃ del : ℕ → ℚ, (∀ k, k < Km → 0 ≤ del k)
          ∧ (∀ k, k < Km → mg k - en k ≤ del k)
          ∧ (∀ k, k < Km → (((del k : ℚ) : ℝ)) ^ 2
              ≤ (((rh k : ℚ) : ℝ)) ^ 2 * (((sg k : ℚ) : ℝ))) := by
  constructor
  · intro H
    exact ⟨fun k => max 0 (mg k - en k),
      fun k _ => (depth_witness (hσ k) (hρ k) (H k ‹k < Km›)).1,
      fun k _ => (depth_witness (hσ k) (hρ k) (H k ‹k < Km›)).2.1,
      fun k hk => (depth_witness (hσ k) (hρ k) (H k hk)).2.2⟩
  · rintro ⟨del, h0, h1, h2⟩ k hk
    have hpk := price_must_fit (mg := mg k) (ρ := rh k) (σ := sg k) (del := del k)
      (enc := ((en k : ℚ) : ℝ)) (hσ k) (hρ k) (h0 k hk)
      (by exact_mod_cast h1 k hk) (h2 k hk)
    simpa only [Rat.cast_sub] using hpk

#print axioms QMCLeafB.Price37M4.caseB_iff_depths

/-- **The dichotomy's own reading, and what it costs.**  If case (B) is discharged round by round
through the ORACLE's cut, then at a round whose tested centre is the accumulated centre (`en = 0`)
the obligation is `mg k ≤ rh k·√(sg k)` — the oracle's margin against the budget — and NOT
`del ≡ 0`.  Combined with §4 this is the whole content: the fork is a displacement/margin estimate at
every round, i.e. exactly `ShallowCut`, and (A)∨(B) neither weakens it nor confines it to a stratum. -/
theorem caseB_at_centre_is_margin_bound {Km : ℕ} {mg rh sg : ℕ → ℚ}
    (hσ : ∀ k, 0 < sg k) (hρ : ∀ k, 0 ≤ rh k) :
    CaseB Km mg rh sg (fun _ => 0)
      ↔ ∀ k, k < Km → ((mg k : ℚ) : ℝ)
          ≤ (((rh k : ℚ) : ℝ)) * Real.sqrt (((sg k : ℚ) : ℝ)) := by
  constructor
  · intro H k hk
    simpa using H k hk
  · intro H k hk
    simpa using H k hk

#print axioms QMCLeafB.Price37M4.caseB_at_centre_is_margin_bound


/-! ## 6.  The assembled round slot: the exact triple case (B) must produce

At one round, three rational inequalities carry everything: the depth is nonnegative, the oracle's
cut re-anchored at the engine's accumulated centre (`hcut_of_relaxCut_price`, m4/ph36) holds with
slack `del`, and `del` fits the ledger `ρ√σ`.  This is the object case (B) owes at every round, and by
`price_must_fit` it exists only when `margin − enc ≤ ρ√σ`. -/

/-- **The round slot.**  The oracle's own normal separates the engine's accumulated centre from the
relaxation with slack `del`, and the ledger controls that slack. -/
theorem round_slot {n : ℕ} {A cX : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ} {M : ℝ}
    (C : QMCLeafB.RelaxOracle.RelaxCut A cX u δ) (a : Fin (n * n) → ℝ) {del ρ σ : ℚ}
    (h0 : 0 ≤ del)
    (hprice : ((C.margin : ℚ) : ℝ)
      - (fun i => ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ
          (QMCLeafB.AnswerProducer.flat (QMCLeafB.SepOracle.castMat cX) - a)
        ≤ ((del : ℚ) : ℝ))
    (hledger : (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ))) :
    0 ≤ del ∧ (((del : ℚ) : ℝ)) ^ 2 ≤ (((ρ : ℚ) : ℝ)) ^ 2 * (((σ : ℚ) : ℝ))
      ∧ ∀ z, z ∈ QMCLeafB.Boundary.relaxBall (QMCLeafB.SepOracle.castMat A)
          ((u : ℚ) : ℝ) ((δ : ℚ) : ℝ) M →
        -(((del : ℚ) : ℝ)) ≤ (fun i =>
            ((QMCLeafB.RelaxOracle.flatQ C.normal i : ℚ) : ℝ)) ⬝ᵥ (z - a) :=
  ⟨h0, hledger, QMCLeafB.Fal36M4.hcut_of_relaxCut_price C a hprice⟩

#print axioms QMCLeafB.Price37M4.round_slot

end QMCLeafB.Price37M4



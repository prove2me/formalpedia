-- Prove2me | Definitions.Def_QMCLeafB_vol32
-- name    : QMCLeafB_vol32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:03:13.240636+00:00
-- url     : https://prove2.me/theorems/85a2f879-919f-488f-9b63-f4cf7488af7c
-- title:
--   QMCLeafB vol32
-- statement:
--   # `Check_vol32_m7` — phase 32, member m7, direction `volume-threshold` (d6)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_ball_floor
import Definitions.Def_QMCLeafB_emptybody
import Definitions.Def_QMCLeafB_mech31
/-
# `Check_vol32_m7` — phase 32, member m7, direction `volume-threshold` (d6)

**The residual statement.**  `MechM6.leaf_of_hok_and_complete` needs
`hcomplete : ¬ EmptyBody G t ⟹ bit G t = true`, i.e. "the relaxed body is non-empty ⟹ the search
reports `ok`".  The only banked route into it is *volume*: a Euclidean ball inside the body floors
the engine's determinant potential (`BallFloor.pow_le_volPot`, `BallFloor.no_run_of_ball`; at the
record level `BallM2.no_runParts_of_ball`, hence `BallM2.residParts_bit_true_of_ball`).  The
hypothesis that manufactures that ball is `BallFloor.ball_subset_relaxBodyLE`: a **half-tolerance**
body point (`relaxBodyLE A u (δ/2)`), giving a ball of radius `δ/(8(c_A+1))`.

**What this file pins.**  At a single-edge input the relaxed body is explicit, and:

* §1 the exact non-emptiness threshold is `uStar w δ = -(2w(1+3δ/4) + δ/2)`: membership at it
  (`corner_mem`), emptiness below it (`empty_below`), and every body point at it is *pinned* — the
  objective inequality is an equality (`frob_eq_at_threshold`);
* §2 consequently **no Frobenius ball of any positive radius sits in the body at the threshold**
  (`no_ball_at_threshold`).  This is a dimension/equality statement, not a constant chase: the
  body is squeezed onto the level constraint, so no measure-based certificate can fire there;
* §3 the two-sided quantitative form for a ball of radius `r`:
  `w·r ≤ u - uStar` **necessary** (`ball_radius_le_slack`) and `6·r ≤ u - uStar` **sufficient**
  (`ball_exists_of_slack`, explicit centre `!![1+δ/4-r, -(1+3δ/4)+2r; ·, 1+δ/4-r]`).  So the
  volume/ball route's blind band at the threshold is exactly `Θ(r)`: for the campaign radius
  `r_c = dq/(8(c_A+1))` it is `[tStar, tStar + Θ(dq))`, i.e. a `Θ(dq)` slab and not a stray point;
* §4 at the campaign's exemplar `G₁` (`n = 2`, one edge of weight `1`, `Rq = 2`,
  `eps = 1/20000`, `dqShallow = 1/380000`, campaign radius `dq/24 = 1/9120000`): the threshold is
  exactly the campaign's dreg-band floor `tStar = -2 + 17/380000 = -Rq + eps - 2·dqShallow`, it is
  **interior**, the body is **non-empty** (`not_emptyBody_G₁`, `empty_below_G₁`), **no ball of any
  radius** sits in it (`no_ball_G₁`), **no ball of the campaign radius** sits in it below
  `tStar + 1/9120000` (`no_campaign_ball_G₁`), and one does exist from `tStar + 6·dq/24` on
  (`campaign_ball_above_G₁`).

**Consequence for the residual.**  `hcomplete` is not a volume statement.  On the `Θ(dq)` band
`[tStar, tStar + Θ(dq))` at the exemplar the member set is thin and at the bottom zero-dimensional,
so a volume certificate cannot reach it: `hcomplete` there is a *hitting* statement about the
trajectory (the thin-visit lane) or a program change.  Above the band the banked ball route fires,
which is what `residParts_bit_true_of_ball` already consumes.  The exact residual stratum is
therefore "interior points within `Θ(dq)` of `-Rq + eps - 2·dqShallow`, at every input", and the
right normal form of `hcomplete` is a statement about that slab only.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.VolM7

open QuantumMaxCutEnergy

/-! ## 0.  The single-edge body, in closed form -/

/-- The weight matrix of the single-edge input on two vertices. -/
def edgeA (w : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, w; w, 0]

/-- The symmetric matrix `!![a,s;s,b]`. -/
def sym2 (a b s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, s; s, b]

/-- **The exact non-emptiness threshold of the single-edge relaxed body.** -/
def uStar (w δ : ℝ) : ℝ := -(2 * w * (1 + 3 * δ / 4)) - δ / 2

theorem sym2_00 (a b s : ℝ) : sym2 a b s 0 0 = a := by simp [sym2]

theorem sym2_11 (a b s : ℝ) : sym2 a b s 1 1 = b := by simp [sym2]

theorem sym2_01 (a b s : ℝ) : sym2 a b s 0 1 = s := by simp [sym2]

theorem sym2_10 (a b s : ℝ) : sym2 a b s 1 0 = s := by simp [sym2]

/-- Case analysis for `Fin 2`, in the form that keeps the literal indices. -/
theorem forall_fin_two {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem qfR_sym2 (a b s : ℝ) (x : Fin 2 → ℝ) :
    BallFloor.qfR (sym2 a b s) x
      = a * x 0 ^ 2 + 2 * s * (x 0 * x 1) + b * x 1 ^ 2 := by
  simp [BallFloor.qfR, sym2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem qfR_fin2 (X : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    BallFloor.qfR X x
      = X 0 0 * x 0 ^ 2 + X 0 1 * (x 0 * x 1) + X 1 0 * (x 1 * x 0)
        + X 1 1 * x 1 ^ 2 := by
  simp [BallFloor.qfR, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem qfR_const_one (X : Matrix (Fin 2) (Fin 2) ℝ) :
    BallFloor.qfR X (fun _ => (1:ℝ)) = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
  rw [qfR_fin2]
  norm_num

theorem sum_sq_const_one : (∑ i : Fin 2, ((fun _ => (1:ℝ)) i) ^ 2) = 2 := by
  simp [Fin.sum_univ_two]

theorem frob_edgeA (w : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    BallFloor.frob (edgeA w) X = w * (X 0 1 + X 1 0) := by
  simp [BallFloor.frob, edgeA, Fin.sum_univ_two]
  ring

/-! ## 1.  The threshold: membership above it, emptiness below it -/

/-- **The threshold point is in the body** (equality in the diagonal and objective fields). -/
theorem corner_mem (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ) :
    BallFloor.relaxBodyLE (edgeA w) (uStar w δ) δ
      (sym2 (1 + δ / 4) (1 + δ / 4) (-(1 + 3 * δ / 4))) := by
  have hδ4 : (0:ℝ) ≤ δ / 4 := by linarith
  have hpos : (0:ℝ) < 1 + 3 * δ / 4 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hsum2 : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by
      rw [Fin.sum_univ_two]
    rw [qfR_sym2, hsum2]
    have hsq : (0:ℝ) ≤ (1 + 3 * δ / 4) * (x 0 - x 1) ^ 2 :=
      mul_nonneg (le_of_lt hpos) (sq_nonneg _)
    have hexp : (1 + 3 * δ / 4) * (x 0 - x 1) ^ 2
        = (1 + δ / 4) * x 0 ^ 2 + 2 * (-(1 + 3 * δ / 4)) * (x 0 * x 1)
          + (1 + δ / 4) * x 1 ^ 2 + δ / 2 * (x 0 ^ 2 + x 1 ^ 2) := by
      ring
    linarith
  · refine forall_fin_two ?_ ?_
    · rw [sym2_00, show (1:ℝ) + δ / 4 - 1 = δ / 4 by ring, abs_of_nonneg hδ4]
    · rw [sym2_11, show (1:ℝ) + δ / 4 - 1 = δ / 4 by ring, abs_of_nonneg hδ4]
  · rw [frob_edgeA, sym2_01, sym2_10]
    have hres : uStar w δ + δ / 2 = w * (-(1 + 3 * δ / 4) + -(1 + 3 * δ / 4)) := by
      unfold uStar
      ring
    rw [hres]

/-- **Every body point at the threshold is pinned**: the objective value is exactly `u + δ/2`. -/
theorem frob_eq_at_threshold (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ)
    {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : BallFloor.relaxBodyLE (edgeA w) (uStar w δ) δ X) :
    BallFloor.frob (edgeA w) X = uStar w δ + δ / 2 := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  have hpsd1 : -(δ / 2) * 2 ≤ X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    have h := hpsd (fun _ => (1 : ℝ))
    rwa [qfR_const_one, sum_sq_const_one] at h
  have hd0 : X 0 0 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 0)).2
    linarith
  have hd1 : X 1 1 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 1)).2
    linarith
  have hsum : -(2 : ℝ) - 3 * δ / 2 ≤ X 0 1 + X 1 0 := by linarith
  have hlow : w * (-(2 : ℝ) - 3 * δ / 2) ≤ w * (X 0 1 + X 1 0) :=
    mul_le_mul_of_nonneg_left hsum (le_of_lt hw)
  have hstar : uStar w δ + δ / 2 = w * (-(2 : ℝ) - 3 * δ / 2) := by
    unfold uStar
    ring
  have htr' : w * (X 0 1 + X 1 0) ≤ w * (-(2 : ℝ) - 3 * δ / 2) := by
    rw [frob_edgeA, hstar] at htr
    exact htr
  rw [frob_edgeA, hstar]
  exact le_antisymm htr' hlow

/-- **Nothing below the threshold is in the body** — the threshold is exact. -/
theorem empty_below (w δ u : ℝ) (hw : 0 < w) (hδ : 0 < δ) (hu : u < uStar w δ) :
    ∀ X : Matrix (Fin 2) (Fin 2) ℝ, ¬ BallFloor.relaxBodyLE (edgeA w) u δ X := by
  intro X hX
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  have hpsd1 : -(δ / 2) * 2 ≤ X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    have h := hpsd (fun _ => (1 : ℝ))
    rwa [qfR_const_one, sum_sq_const_one] at h
  have hd0 : X 0 0 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 0)).2
    linarith
  have hd1 : X 1 1 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 1)).2
    linarith
  have hsum : -(2 : ℝ) - 3 * δ / 2 ≤ X 0 1 + X 1 0 := by linarith
  have hlow : w * (-(2 : ℝ) - 3 * δ / 2) ≤ w * (X 0 1 + X 1 0) :=
    mul_le_mul_of_nonneg_left hsum (le_of_lt hw)
  have htr' : w * (X 0 1 + X 1 0) ≤ u + δ / 2 := by
    rw [frob_edgeA] at htr
    exact htr
  have hstar : uStar w δ = w * (-(2 : ℝ) - 3 * δ / 2) - δ / 2 := by
    unfold uStar
    ring
  rw [hstar] at hu
  linarith

/-! ## 2.  Why no measure argument can reach a tight level: the general statement -/

/-- **Tolerance monotonicity**: a tighter relaxation is a body point at any looser tolerance. -/
theorem relaxBodyLE_mono_tol {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {u κ δ : ℝ}
    (hκδ : κ ≤ δ) {X : Matrix (Fin n) (Fin n) ℝ} (hX : BallFloor.relaxBodyLE A u κ X) :
    BallFloor.relaxBodyLE A u δ X := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hx2 : (0:ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have h := hpsd x
    nlinarith
  · intro i
    have h := hdiag i
    have := abs_nonneg (X i i - 1)
    rw [abs_le] at h ⊢
    constructor <;> linarith [h.1, h.2]
  · linarith

/-- **A level that is tight at every body point is ball-free.**  If the objective is constant on the
body and some Frobenius-small `E` has nonzero objective, no Frobenius ball sits in the body.  This
is the structural reason the volume/ball route cannot see a degenerate stratum: it needs objective
slack, which a tight level does not have. -/
theorem no_ball_of_tight {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {body : Set (Matrix (Fin n) (Fin n) ℝ)} {c r : ℝ} {X₀ : Matrix (Fin n) (Fin n) ℝ}
    (htight : ∀ X ∈ body, BallFloor.frob A X = c) (hX₀ : X₀ ∈ body)
    {E : Matrix (Fin n) (Fin n) ℝ} (hE : BallFloor.frob A E ≠ 0)
    (hEnorm : BallFloor.frobNormSq E ≤ r ^ 2) :
    ¬ (BallFloor.matBall X₀ r ⊆ body) := by
  intro hsub
  have hmem : X₀ + E ∈ BallFloor.matBall X₀ r := by
    simp only [BallFloor.matBall, Set.mem_setOf_eq]
    have hsub' : X₀ + E - X₀ = E := by abel
    rw [hsub']
    exact hEnorm
  have h1 := htight (X₀ + E) (hsub hmem)
  have h2 := htight X₀ hX₀
  rw [BallFloor.frob_add] at h1
  exact hE (by linarith)

/-! ## 2.  No Frobenius ball sits in the body at the threshold -/

theorem frobNormSq_col (c : ℝ) :
    BallFloor.frobNormSq (!![0, c; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = c ^ 2 := by
  simp [BallFloor.frobNormSq, Fin.sum_univ_two]

theorem col_01 (c : ℝ) : (!![0, c; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = c := by simp

theorem col_10 (c : ℝ) : (!![0, c; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp

theorem no_ball_at_threshold (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ) (r : ℝ) (hr : 0 < r)
    (X₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (BallFloor.matBall X₀ r ⊆ {X | BallFloor.relaxBodyLE (edgeA w) (uStar w δ) δ X}) := by
  intro hsub
  have hzero : BallFloor.frobNormSq (X₀ - X₀) = 0 := by
    rw [sub_self]
    simp [BallFloor.frobNormSq]
  have h0mem : X₀ ∈ BallFloor.matBall X₀ r := by
    simp only [BallFloor.matBall, Set.mem_setOf_eq]
    rw [hzero]
    nlinarith [sq_nonneg r]
  have hEmem : X₀ + (!![0, r / 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
      ∈ BallFloor.matBall X₀ r := by
    simp only [BallFloor.matBall, Set.mem_setOf_eq]
    have hsub' : X₀ + !![0, r / 2; 0, 0] - X₀ = !![0, r / 2; 0, 0] := by abel
    rw [hsub', frobNormSq_col]
    nlinarith
  have hp0 := frob_eq_at_threshold w δ hw hδ (hsub h0mem)
  have hp1 := frob_eq_at_threshold w δ hw hδ (hsub hEmem)
  rw [BallFloor.frob_add] at hp1
  have hle : BallFloor.frob (edgeA w) (!![0, r / 2; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≤ 0 := by
    linarith
  rw [frob_edgeA, col_01, col_10] at hle
  nlinarith

/-- **The banked ball lemma's hypothesis fails at the threshold**: there is no half-tolerance body
point there.  This is the exact statement that `BallFloor.ball_subset_relaxBodyLE` cannot be applied
at `u = uStar`, so `BallM2.no_runParts_of_ball` has nothing to consume. -/
theorem no_halfTolerance_at_threshold (w δ : ℝ) (hw : 0 < w) (hδ : 0 < δ) :
    ∀ X : Matrix (Fin 2) (Fin 2) ℝ, ¬ BallFloor.relaxBodyLE (edgeA w) (uStar w δ) (δ / 2) X := by
  intro X hX
  have hloose : BallFloor.relaxBodyLE (edgeA w) (uStar w δ) δ X :=
    relaxBodyLE_mono_tol (by linarith) hX
  have hpinned := frob_eq_at_threshold w δ hw hδ hloose
  have htight : BallFloor.frob (edgeA w) X ≤ uStar w δ + δ / 4 := by
    have h := hX.2.2
    linarith
  linarith

/-! ## 3.  The quantitative bound: a ball of radius `r` forces objective slack `w·r` -/

/-- **The off-diagonal pairing is bounded below on every body point** (from the `(1,1)` test
vector and the diagonal slab). -/
theorem offDiag_sum_lower (w : ℝ) {u δ : ℝ} {X : Matrix (Fin 2) (Fin 2) ℝ}
    (hX : BallFloor.relaxBodyLE (edgeA w) u δ X) :
    -(2 : ℝ) - 3 * δ / 2 ≤ X 0 1 + X 1 0 := by
  obtain ⟨hpsd, hdiag, htr⟩ := hX
  have hpsd1 : -(δ / 2) * 2 ≤ X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
    have h := hpsd (fun _ => (1 : ℝ))
    rwa [qfR_const_one, sum_sq_const_one] at h
  have hd0 : X 0 0 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 0)).2
    linarith
  have hd1 : X 1 1 ≤ 1 + δ / 4 := by
    have h := (abs_le.mp (hdiag 1)).2
    linarith
  linarith

/-- **The volume route's blind band, quantitatively.**  If a Frobenius ball of radius `r` sits in
the body at level `u`, then `w·r ≤ u - uStar w δ`: the ball route cannot see the band
`[uStar, uStar + w·r)`. -/
theorem ball_radius_le_slack (w δ u r : ℝ) (hw : 0 < w) (hδ : 0 < δ) (hr : 0 < r)
    (X₀ : Matrix (Fin 2) (Fin 2) ℝ)
    (hsub : BallFloor.matBall X₀ r ⊆ {X | BallFloor.relaxBodyLE (edgeA w) u δ X}) :
    w * r ≤ u - uStar w δ := by
  set E : Matrix (Fin 2) (Fin 2) ℝ := !![0, r / 2; 0, 0] with hE
  have hEnorm : BallFloor.frobNormSq E ≤ r ^ 2 := by
    rw [hE, frobNormSq_col]
    nlinarith
  have hplus : BallFloor.relaxBodyLE (edgeA w) u δ (X₀ + E) := by
    apply hsub
    simp only [BallFloor.matBall, Set.mem_setOf_eq]
    have hsub' : X₀ + E - X₀ = E := by abel
    rw [hsub', hE, frobNormSq_col]
    nlinarith
  have hminus : BallFloor.relaxBodyLE (edgeA w) u δ (X₀ - E) := by
    apply hsub
    simp only [BallFloor.matBall, Set.mem_setOf_eq]
    have hsub' : X₀ - E - X₀ = -E := by abel
    rw [hsub']
    have : BallFloor.frobNormSq (-E) = BallFloor.frobNormSq E := by
      simp [BallFloor.frobNormSq]
    rw [this, hE, frobNormSq_col]
    nlinarith
  have hfrob : BallFloor.frob (edgeA w) (X₀ + E) ≤ u + δ / 2 := hplus.2.2
  have hlow := offDiag_sum_lower w hminus
  have hE01 : E 0 1 = r / 2 := by rw [hE]; exact col_01 (r / 2)
  have hE10 : E 1 0 = 0 := by rw [hE]; exact col_10 (r / 2)
  have hfrobE : BallFloor.frob (edgeA w) (X₀ + E)
      = w * ((X₀ 0 1 + X₀ 1 0) + r / 2) := by
    rw [BallFloor.frob_add, frob_edgeA, frob_edgeA, hE01, hE10]
    ring
  rw [hfrobE] at hfrob
  have hstep1 : (X₀ - E) 0 1 = X₀ 0 1 - E 0 1 := Matrix.sub_apply X₀ E 0 1
  have hstep2 : (X₀ - E) 1 0 = X₀ 1 0 - E 1 0 := Matrix.sub_apply X₀ E 1 0
  rw [hstep1, hstep2, hE01, hE10] at hlow
  have hlow2 : -(2 : ℝ) - 3 * δ / 2 ≤ (X₀ 0 1 + X₀ 1 0) - r / 2 := by linarith
  have hmul : w * (-(2 : ℝ) - 3 * δ / 2) ≤ w * ((X₀ 0 1 + X₀ 1 0) - r / 2) :=
    mul_le_mul_of_nonneg_left hlow2 (le_of_lt hw)
  have hstar : u - uStar w δ = u + δ / 2 + (2 * w + 3 * w * δ / 2) := by
    unfold uStar
    ring
  rw [hstar]
  nlinarith [hmul, hfrob, hw]

/-- **The ball route fires as soon as the level is `4r` above the threshold.**  The explicit
point `!![1+δ/4-r, -(1+3δ/4)+r; ·, 1+δ/4-r]` has all three slacks, so the whole Frobenius ball of
radius `r` sits in the `δ`-body.  Together with `ball_radius_le_slack` (which forces `r ≤ u-uStar`)
this pins the blind band of the volume/ball route to `Θ(r)` at the threshold (sharp constants are
`r ≤ u-uStar` from `ball_radius_le_slack` and `(2+√2)r` from Cauchy–Schwarz `√2·r` on the two
off-diagonal entries; `4r` keeps the arithmetic elementary). -/
theorem ball_exists_of_slack (δ u r : ℝ) (hδ : 0 < δ) (hr : 0 < r) (hrδ : 4 * r ≤ δ)
    (hslack : uStar 1 δ + 6 * r ≤ u) :
    ∃ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
      BallFloor.matBall X₀ r ⊆ {X | BallFloor.relaxBodyLE (edgeA 1) u δ X} := by
  refine ⟨sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r), ?_⟩
  intro X hX
  simp only [BallFloor.matBall, Set.mem_setOf_eq] at hX
  set E : Matrix (Fin 2) (Fin 2) ℝ :=
    X - sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r) with hE
  have hXeq : X = sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r) + E := by
    rw [hE]; abel
  have hr0 : (0:ℝ) ≤ r := le_of_lt hr
  have hδr : r ≤ δ / 4 := by linarith
  have hsneg : -(1 + 3 * δ / 4) + 2 * r ≤ 0 := by linarith
  have hsum : 6 * r ≤ u - uStar 1 δ := by
    have h : uStar 1 δ + 6 * r ≤ u := hslack
    linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hpert := BallFloor.abs_qfR_le_of_frobNormSq_le (x := x) (E := E) hr0 hX
    have hpert' : -(r * (∑ i : Fin 2, x i ^ 2)) ≤ BallFloor.qfR E x := (abs_le.mp hpert).1
    have hsum2 : (∑ i : Fin 2, x i ^ 2) = x 0 ^ 2 + x 1 ^ 2 := by rw [Fin.sum_univ_two]
    have h0 : BallFloor.qfR (sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r)) x
        ≥ (-(δ / 2) + r) * (x 0 ^ 2 + x 1 ^ 2) := by
      rw [qfR_sym2]
      have hsq := sq_nonneg (x 0 - x 1)
      nlinarith [hsq, hsneg]
    rw [hXeq, BallFloor.qfR_add, hsum2]
    have hx2 : (0:ℝ) ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
    nlinarith [h0, hpert', hx2]
  · intro i
    have hentry := BallFloor.abs_apply_le_of_frobNormSq_le hr0 hX i i
    have hdiag : (sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r)) i i
        = 1 + δ / 4 - r := by
      rcases i with ⟨_ | _ | k, hk⟩
      · exact sym2_00 _ _ _
      · exact sym2_11 _ _ _
      · exact absurd hk (by omega)
    rw [hXeq, Matrix.add_apply, hdiag]
    have h1 : |1 + δ / 4 - r - 1| ≤ δ / 4 - r := by
      rw [show (1:ℝ) + δ / 4 - r - 1 = δ / 4 - r by ring, abs_of_nonneg (by linarith)]
    rw [show (1:ℝ) + δ / 4 - r + E i i - 1 = (1 + δ / 4 - r - 1) + E i i by ring]
    calc |(1 + δ / 4 - r - 1) + E i i| ≤ |1 + δ / 4 - r - 1| + |E i i| := abs_add_le _ _
      _ ≤ (δ / 4 - r) + r := by linarith
      _ = δ / 4 := by ring
  · have hentry := BallFloor.abs_frob_le (A := edgeA 1) (E := E) hr0 hX
    have hX0frob : BallFloor.frob (edgeA 1)
        (sym2 (1 + δ / 4 - r) (1 + δ / 4 - r) (-(1 + 3 * δ / 4) + 2 * r))
        = 2 * (-(1 + 3 * δ / 4) + 2 * r) := by
      rw [frob_edgeA, sym2_01, sym2_10]
      ring
    have hasum : (∑ i : Fin 2, ∑ j : Fin 2, |edgeA 1 i j|) = 2 := by
      norm_num [edgeA, Fin.sum_univ_two]
    have hEbound : BallFloor.frob (edgeA 1) E ≤ r * 2 := by
      have h1 : BallFloor.frob (edgeA 1) E ≤ r * (∑ i : Fin 2, ∑ j : Fin 2, |edgeA 1 i j|) :=
        (abs_le.mp hentry).2
      rwa [hasum] at h1
    rw [hXeq, BallFloor.frob_add, hX0frob]
    have hstar : uStar 1 δ = -2 - 2 * δ := by unfold uStar; ring
    nlinarith [hEbound, hsum, hstar, hr, hδ]

/-! ## 4.  The campaign exemplar -/

/-- The campaign exemplar input (two vertices, one edge of weight `1`). -/
abbrev G₁ : QuantumMaxCutEnergy.Input := QMCLeafB.EmptyBodyM5.G₁

/-- **The exemplar's objective pairing is the single-edge one.** -/
theorem frob_wMatrix_G₁ (X : Matrix (Fin 2) (Fin 2) ℝ) :
    BallFloor.frob (QMCLeafB.wMatrix G₁) X = X 0 1 + X 1 0 := by
  have h00 : QMCLeafB.wMatrix G₁ 0 0 = 0 := QMCLeafB.wMatrix_apply_of_eq
  have h11 : QMCLeafB.wMatrix G₁ 1 1 = 0 := QMCLeafB.wMatrix_apply_of_eq
  have h01 : QMCLeafB.wMatrix G₁ 0 1 = 1 := by
    rw [QMCLeafB.wMatrix_apply_of_lt (show (0 : Fin 2) < 1 by decide)]
    simp [G₁, QMCLeafB.EmptyBodyM5.G₁]
  have h10 : QMCLeafB.wMatrix G₁ 1 0 = 1 := by
    rw [QMCLeafB.wMatrix_apply_of_gt (show (0 : Fin 2) < 1 by decide)]
    simp [G₁, QMCLeafB.EmptyBodyM5.G₁]
  simp only [BallFloor.frob, Fin.sum_univ_two, h00, h11, h01, h10]
  ring

/-- **Transfer of `relaxBodyLE` along an equality of objective pairings.** -/
theorem relaxBodyLE_congr {A A' : Matrix (Fin 2) (Fin 2) ℝ}
    (h : ∀ X, BallFloor.frob A X = BallFloor.frob A' X) :
    ∀ (u δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ),
      (BallFloor.relaxBodyLE A u δ X ↔ BallFloor.relaxBodyLE A' u δ X) := by
  intro u δ X
  unfold BallFloor.relaxBodyLE
  rw [h X]

/-- The exemplar's `relaxBodyLE` is the single-edge one. -/
theorem relaxBodyLE_wMatrix_G₁ (u δ : ℝ) (X : Matrix (Fin 2) (Fin 2) ℝ) :
    (BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁) u δ X
      ↔ BallFloor.relaxBodyLE (edgeA 1) u δ X) := by
  refine relaxBodyLE_congr (A' := edgeA 1) ?_ u δ X
  intro Y
  rw [frob_wMatrix_G₁, frob_edgeA]
  ring

/-- The exemplar's tolerance, in `ℝ`. -/
theorem dq_G₁ : (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) = 1 / 380000 := by
  have h : (QMCLeafB.UnionShallow.paramsKbc2 G₁).dq = 1 / 380000 := by
    rw [QMCLeafB.UnionShallow.paramsKbc2_dq]
    exact QMCLeafB.EmptyBodyM5.dqShallow_G₁
  rw [h]
  norm_num

/-- The exemplar's rounding slack `eps = Rq/40000`, in `ℝ`. -/
theorem eps_G₁ : (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) = 1 / 20000 := by
  rw [QMCLeafB.EmptyBodyM5.Rq_G₁]
  norm_num

/-- **The campaign's dreg-band floor** at the exemplar: `-Rq + eps - 2·dqShallow`. -/
def tStar : ℚ := -2 + 17 / 380000

theorem tStar_cast : ((tStar : ℚ) : ℝ) = -2 + 17 / 380000 := by
  unfold tStar
  norm_num

/-- The threshold level, in the shape `relaxBodyLE` uses. -/
theorem level_G₁ : ((tStar : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
    = uStar 1 (1 / 380000) := by
  rw [tStar_cast, eps_G₁]
  unfold uStar
  norm_num

/-- The threshold is inside the interior bracket. -/
theorem interior_G₁ : AsmM8.Interior G₁ tStar := by
  constructor
  · rw [QMCLeafB.EmptyBodyM5.Rq_G₁]
    unfold tStar
    norm_num
  · rw [eps_G₁, tStar_cast]
    norm_num

/-- **The exemplar's body is non-empty at the threshold** — `EmptyBody` fails there. -/
theorem not_emptyBody_G₁ :
    ¬ AsmM8.EmptyBody G₁ tStar (QMCLeafB.UnionShallow.paramsKbc2 G₁) := by
  intro hempty
  unfold AsmM8.EmptyBody at hempty
  have hbody := corner_mem (w := 1) (δ := 1 / 380000) one_pos (by norm_num)
  rw [level_G₁, dq_G₁] at hempty
  exact hempty _ ((relaxBodyLE_wMatrix_G₁ _ _ _).mpr hbody)

/-- **No Frobenius ball of any positive radius sits in the exemplar's body at the threshold.** -/
theorem no_ball_G₁ (r : ℝ) (hr : 0 < r) (X₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (BallFloor.matBall X₀ r ⊆ {X | BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        (((tStar : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) X}) := by
  intro hsub
  rw [level_G₁, dq_G₁] at hsub
  exact no_ball_at_threshold 1 (1 / 380000) one_pos (by norm_num) r hr X₀
    (fun Y hY => (relaxBodyLE_wMatrix_G₁ _ _ _).mp (hsub hY))

/-- **The threshold is exact at the exemplar**: below `tStar` the relaxed body is empty. -/
theorem empty_below_G₁ (t : ℚ) (ht : t < tStar) :
    AsmM8.EmptyBody G₁ t (QMCLeafB.UnionShallow.paramsKbc2 G₁) := by
  intro X hX
  rw [dq_G₁] at hX
  have hX' := (relaxBodyLE_wMatrix_G₁ _ _ _).mp hX
  refine empty_below 1 (1 / 380000) (((t : ℚ) : ℝ)
    - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) one_pos (by norm_num) ?_ X hX'
  have h1 : ((t : ℚ) : ℝ) < ((tStar : ℚ) : ℝ) := by exact_mod_cast ht
  have h2 : ((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      < ((tStar : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) := by linarith
  rw [level_G₁] at h2
  exact h2

/-- **No ball of the campaign radius sits in the exemplar's body below `tStar + dq/24`.**  The
campaign radius at `G₁` is `dq/(8·(c_A+1)) = dq/24 = 1/9120000` (`c_A = Rq G₁ = 2`): this is the
exact statement that the volume route cannot reach the bottom band of the non-empty interior. -/
theorem no_campaign_ball_G₁ (t : ℚ) (ht : t < tStar + 1 / 9120000)
    (X₀ : Matrix (Fin 2) (Fin 2) ℝ) :
    ¬ (BallFloor.matBall X₀ (1 / 9120000) ⊆ {X | BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        (((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) X}) := by
  intro hsub
  rw [dq_G₁] at hsub
  have hsub' : BallFloor.matBall X₀ (1 / 9120000)
      ⊆ {X | BallFloor.relaxBodyLE (edgeA 1)
          (((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
          (1 / 380000) X} :=
    fun Y hY => (relaxBodyLE_wMatrix_G₁ _ _ _).mp (hsub hY)
  have hslack := ball_radius_le_slack 1 (1 / 380000)
    (((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) (1 / 9120000)
    one_pos (by norm_num) (by norm_num) X₀ hsub'
  have ht' : ((t : ℚ) : ℝ) < ((tStar : ℚ) : ℝ) + 1 / 9120000 := by
    have h1 : ((t : ℚ) : ℝ) < ((tStar + 1 / 9120000 : ℚ) : ℝ) := by exact_mod_cast ht
    have h2 : (((tStar + 1 / 9120000 : ℚ)) : ℝ) = ((tStar : ℚ) : ℝ) + (1 / 9120000) := by
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hlevel : ((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
      < uStar 1 (1 / 380000) + 1 / 9120000 := by
    have h3 : ((tStar : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
        = uStar 1 (1 / 380000) := level_G₁
    linarith
  linarith

/-- **Above the blind band a campaign-radius ball exists at the exemplar.**  So the exemplar's
volume route is complete off the `Θ(dq)` band starting at `tStar`. -/
theorem campaign_ball_above_G₁ (t : ℚ) (ht : tStar + 6 * (1 / 9120000) ≤ t) :
    ∃ X₀ : Matrix (Fin 2) (Fin 2) ℝ,
      BallFloor.matBall X₀ (1 / 9120000) ⊆ {X | BallFloor.relaxBodyLE (QMCLeafB.wMatrix G₁)
        (((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ))
        (((QMCLeafB.UnionShallow.paramsKbc2 G₁).dq : ℚ) : ℝ) X} := by
  have ht' : ((tStar : ℚ) : ℝ) + 6 * (1 / 9120000) ≤ ((t : ℚ) : ℝ) := by
    have h1 : ((tStar + 6 * (1 / 9120000) : ℚ) : ℝ) ≤ ((t : ℚ) : ℝ) := by exact_mod_cast ht
    have h2 : (((tStar + 6 * (1 / 9120000) : ℚ)) : ℝ)
        = ((tStar : ℚ) : ℝ) + 6 * (1 / 9120000) := by
      push_cast
      ring
    rw [h2] at h1
    exact h1
  have hlevel : uStar 1 (1 / 380000) + 6 * (1 / 9120000)
      ≤ ((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ) := by
    have h3 : ((tStar : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)
        = uStar 1 (1 / 380000) := level_G₁
    linarith
  obtain ⟨X₀, hX₀⟩ := ball_exists_of_slack (1 / 380000)
    (((t : ℚ) : ℝ) - (((QMCLeafB.EngineRuntime.Rq G₁ / 40000 : ℚ)) : ℝ)) (1 / 9120000)
    (by norm_num) (by norm_num) (by norm_num) hlevel
  refine ⟨X₀, ?_⟩
  rw [dq_G₁]
  exact fun Y hY => (relaxBodyLE_wMatrix_G₁ _ _ _).mpr (hX₀ hY)

end QMCLeafB.VolM7

/-! ## 4.  Axiom audit -/

#print axioms QMCLeafB.VolM7.corner_mem
#print axioms QMCLeafB.VolM7.frob_eq_at_threshold
#print axioms QMCLeafB.VolM7.empty_below
#print axioms QMCLeafB.VolM7.relaxBodyLE_mono_tol
#print axioms QMCLeafB.VolM7.no_ball_of_tight
#print axioms QMCLeafB.VolM7.no_ball_at_threshold
#print axioms QMCLeafB.VolM7.no_halfTolerance_at_threshold
#print axioms QMCLeafB.VolM7.frob_wMatrix_G₁
#print axioms QMCLeafB.VolM7.level_G₁
#print axioms QMCLeafB.VolM7.interior_G₁
#print axioms QMCLeafB.VolM7.not_emptyBody_G₁
#print axioms QMCLeafB.VolM7.no_ball_G₁
#print axioms QMCLeafB.VolM7.empty_below_G₁
#print axioms QMCLeafB.VolM7.offDiag_sum_lower
#print axioms QMCLeafB.VolM7.ball_radius_le_slack
#print axioms QMCLeafB.VolM7.no_campaign_ball_G₁
#print axioms QMCLeafB.VolM7.ball_exists_of_slack
#print axioms QMCLeafB.VolM7.campaign_ball_above_G₁



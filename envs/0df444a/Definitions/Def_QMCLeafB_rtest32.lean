-- Prove2me | Definitions.Def_QMCLeafB_rtest32
-- name    : QMCLeafB_rtest32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:06:50.096202+00:00
-- url     : https://prove2.me/theorems/a3a16c83-6581-412e-b17e-2dd549fc99f3
-- title:
--   QMCLeafB rtest32
-- statement:
--   # `Check_rtest32_m8` — phase 32, member m8, direction `release-test` (d9)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_lvl32
/-
# `Check_rtest32_m8` — phase 32, member m8, direction `release-test` (d9)

The release has to change the programme's `ok` test: the current test is gated on the **exact** unit
diagonal (`OkLower.oracleV` reads `if dvR s = 0 then threshV s else …`, `dvR s = ∑ᵢ |Xᵢᵢ − 1|`), and
d2/m2's `campaign_hcomplete_false` shows that at `(G₁, t_W)` the body is non-empty but contains no
unit-diagonal matrix, so `hcomplete` is empty at the campaign programme.  d2's recommended repair
replaces the gate by a tolerance: `dvR s ≤ dqOf s / 4`.

**This file shows that no `dvR`-based (SUM) tolerance can do the job, and says what the test must be
instead.**  Write `dsum X = ∑ᵢ |Xᵢᵢ − 1|` for the state's `dvR` transported to the matrix (the bridge
is `dvR = dsum (stMat …)`: `idxs_of_le` + `Fin.sum_univ_eq_sum_range` + `absq_eq`).  Then:

* **sound** (`diag_of_dsum_le`): `dsum X ≤ τ` with `τ ≤ δ/4` implies the body's diagonal clause
  `∀ i, |Xᵢᵢ − 1| ≤ δ/4` — because each summand is at most the sum;
* **incomplete** (`dsum_of_all_eq`, `sum_gate_rejects_fam`): a matrix with every deviation exactly
  `δ/4` — in particular the witness `fam d b` that §3 of `Check_lvl32_m8` produces at *every* input
  where the body is non-empty — has `dsum = n·δ/4`, which exceeds `δ/4` as soon as `n ≥ 2`.  So the
  repaired gate still rejects members, exactly at the inputs the repair is for;
* **no sum gate does both** (`no_sum_gate`): for `n ≥ 2` and `δ > 0` there is no `τ` for which
  `dsum X ≤ τ` is both sound and covering.

Hence the released test must read the diagonal **per coordinate** — the gate
`∀ i, |Xᵢᵢ − 1| ≤ dqOf/4`, which is *literally* `RelaxMem`'s `diag_near` clause (so it is sound and
covering by definition) — and the state has to carry a *max*-type diagonal register (`maxᵢ |Xᵢᵢ − 1|`),
not the sum `dvR`.  Equivalently: keep `ok` as "the centre is a `RelaxMem` member", decided from
`stX` directly, instead of testing a scalar summary of the diagonal.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` after every
declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace RTest32M8

open QuantumMaxCutEnergy

/-! ## 1.  The sum statistic and its two failure modes -/

/-- `dvR` in matrix form: the **sum** of the diagonal deviations. -/
def dsum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) : ℚ := ∑ i, |X i i - 1|

/-- Each deviation is at most the sum. -/
theorem le_dsum {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) (i : Fin n) : |X i i - 1| ≤ dsum X :=
  Finset.single_le_sum (f := fun j : Fin n => |X j j - 1|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- **A sum gate below `δ/4` is sound for the body's diagonal clause.** -/
theorem diag_of_dsum_le {n : ℕ} {X : Matrix (Fin n) (Fin n) ℚ} {δ τ : ℚ} (hτ : τ ≤ δ / 4)
    (h : dsum X ≤ τ) : ∀ i, |X i i - 1| ≤ δ / 4 := by
  intro i
  exact le_trans (le_dsum X i) (le_trans h hτ)

/-- **Every deviation at `δ/4` forces `dsum = n·δ/4`** — the incompleteness of every sound sum gate. -/
theorem dsum_of_all_eq {n : ℕ} (X : Matrix (Fin n) (Fin n) ℚ) {δ : ℚ}
    (h : ∀ i, |X i i - 1| = δ / 4) : dsum X = (n : ℚ) * (δ / 4) := by
  unfold dsum
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- Soundness bounds the tolerance by `δ/4`: above it, a matrix with a large deviation on one
coordinate and a compensating one elsewhere still has `dsum ≤ τ`. -/
theorem le_of_sound {n : ℕ} (hn : 1 ≤ n) {δ τ : ℚ} (hδ : 0 < δ)
    (hsound : ∀ X : Matrix (Fin n) (Fin n) ℚ, dsum X ≤ τ → ∀ i, |X i i - 1| ≤ δ / 4) :
    τ ≤ δ / 4 := by
  haveI : NeZero n := ⟨by omega⟩
  by_contra hcon
  rw [not_le] at hcon
  set ε : ℚ := (τ - δ / 4) / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  set X : Matrix (Fin n) (Fin n) ℚ :=
    fun i j => if i = 0 ∧ j = 0 then 1 + δ / 4 + ε else if i = j then 1 else 0 with hXdef
  have hdiag : ∀ i : Fin n, X i i - 1 = if i = 0 then δ / 4 + ε else 0 := by
    intro i
    by_cases hi : i = 0
    · subst hi
      have h1 : X 0 0 = 1 + δ / 4 + ε := by
        simp only [hXdef, if_pos (And.intro rfl rfl)]
      rw [h1, if_pos rfl]
      ring
    · have hii : ¬ (i = 0 ∧ i = 0) := fun h => hi h.1
      have h2 : X i i = 1 := by
        simp [hXdef, hii, hi]
      rw [h2, if_neg hi]
      ring
  have hsum : dsum X = δ / 4 + ε := by
    unfold dsum
    rw [Finset.sum_congr rfl (fun i _ => by rw [hdiag i])]
    have hpos : (0 : ℚ) ≤ δ / 4 + ε := by linarith
    have habs : ∀ i : Fin n, |(if i = 0 then δ / 4 + ε else 0)|
        = (if i = 0 then δ / 4 + ε else 0) := by
      intro i
      by_cases hi : i = 0
      · subst hi; simp [abs_of_pos (by linarith : (0:ℚ) < δ / 4 + ε)]
      · simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => habs i)]
    rw [Finset.sum_eq_single (0 : Fin n)]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin n)) h
  have hle : dsum X ≤ τ := by rw [hsum]; rw [hεdef]; linarith
  have hbig := hsound X hle 0
  have h0 : X 0 0 - 1 = δ / 4 + ε := by rw [hdiag 0]; simp
  rw [h0, abs_of_pos (by linarith : (0:ℚ) < δ / 4 + ε)] at hbig
  linarith

/-- Covering forces `τ ≥ n·δ/4` (test the matrix `(1 + δ/4)·1`, all of whose deviations are
exactly `δ/4`). -/
theorem ge_of_cover {n : ℕ} {δ τ : ℚ} (hδ : 0 ≤ δ)
    (hcover : ∀ X : Matrix (Fin n) (Fin n) ℚ, (∀ i, |X i i - 1| ≤ δ / 4) → dsum X ≤ τ) :
    (n : ℚ) * (δ / 4) ≤ τ := by
  have hdiag : ∀ i : Fin n,
      |((1 + δ / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) i i - 1| = δ / 4 := by
    intro i
    have h1 : ((1 + δ / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) i i = 1 + δ / 4 := by simp
    rw [h1, show 1 + δ / 4 - 1 = δ / 4 by ring, abs_of_nonneg (by linarith)]
  have h := hcover _ (fun i => le_of_eq (hdiag i))
  have hd : dsum ((1 + δ / 4) • (1 : Matrix (Fin n) (Fin n) ℚ)) = (n : ℚ) * (δ / 4) :=
    dsum_of_all_eq _ hdiag
  rw [hd] at h
  exact h

/-- **No `dvR`-based tolerance gate is both sound and covering** (for `n ≥ 2`, `δ > 0`). -/
theorem no_sum_gate {n : ℕ} (hn : 2 ≤ n) {δ τ : ℚ} (hδ : 0 < δ)
    (hsound : ∀ X : Matrix (Fin n) (Fin n) ℚ, dsum X ≤ τ → ∀ i, |X i i - 1| ≤ δ / 4)
    (hcover : ∀ X : Matrix (Fin n) (Fin n) ℚ, (∀ i, |X i i - 1| ≤ δ / 4) → dsum X ≤ τ) :
    False := by
  have hup : τ ≤ δ / 4 := le_of_sound (by omega) hδ hsound
  have hlow : (n : ℚ) * (δ / 4) ≤ τ := ge_of_cover (le_of_lt hδ) hcover
  have hn' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

/-! ## 2.  The campaign witness is rejected by every sound sum gate

§3 of `Check_lvl32_m8` produces, at every input whose level exceeds
`-Rq·(1 + 3δ/4)/(n−1)`, the symmetric rational member `fam d b = d·1 + b·J` with
`d + b = 1 + δ/4`.  Its diagonal is constantly `1 + δ/4`, so its `dsum` is `n·δ/4`. -/

theorem dsum_fam {n : ℕ} {d b δ : ℚ} (hδ : 0 ≤ δ) (hdb : d + b = 1 + δ / 4) :
    dsum (Lvl32M8.fam n d b) = (n : ℚ) * (δ / 4) := by
  refine dsum_of_all_eq _ (fun i => ?_)
  rw [Lvl32M8.fam_apply_self, hdb, show 1 + δ / 4 - 1 = δ / 4 by ring,
    abs_of_nonneg (by linarith)]

/-- **The repair's witness is rejected by the repaired gate.**  Any sound sum tolerance
(`τ ≤ δ/4`) refuses the explicit member that closes the body at the same input. -/
theorem sum_gate_rejects_fam {n : ℕ} (hn : 2 ≤ n) {d b δ τ : ℚ} (hδ : 0 < δ)
    (hdb : d + b = 1 + δ / 4) (hτ : τ ≤ δ / 4) :
    ¬ (dsum (Lvl32M8.fam n d b) ≤ τ) := by
  have h : dsum (Lvl32M8.fam n d b) = (n : ℚ) * (δ / 4) := dsum_fam (le_of_lt hδ) hdb
  have hn' : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  rw [h]
  intro hle
  nlinarith

/-- The same statement at the campaign's own parameters, in the shape `exists_mem_of_level_ge`
produces: the witness for the level threshold `-(1 + 3δ/4)/(n−1)·Rq` has `dsum = n·δ/4`. -/
theorem campaign_witness {n : ℕ} (hn : 2 ≤ n) {δ : ℚ} (hδ : 0 < δ) (b : ℚ) :
    dsum (Lvl32M8.fam n ((1 + δ / 4) - b) b) = (n : ℚ) * (δ / 4) :=
  dsum_fam (le_of_lt hδ) (by ring)

/-- **The released test must be per-coordinate.**  The per-coordinate gate is *literally* the
body's `diag_near` clause — sound and covering by definition, so it is the only gate that costs
nothing on either side. -/
theorem diagGate_of_relaxMem {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ}
    {A : Matrix (Fin n) (Fin n) ℚ} {u δ : ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem A cX u δ) : ∀ i, |cX i i - 1| ≤ δ / 4 :=
  fun i => h.diag_near i

/-- And no `dvR`-based tolerance can replace it: the packaged impossibility. -/
theorem no_sum_test {n : ℕ} (hn : 2 ≤ n) {δ : ℚ} (hδ : 0 < δ) :
    ¬ ∃ τ : ℚ,
      (∀ X : Matrix (Fin n) (Fin n) ℚ, dsum X ≤ τ → ∀ i, |X i i - 1| ≤ δ / 4) ∧
      (∀ X : Matrix (Fin n) (Fin n) ℚ, (∀ i, |X i i - 1| ≤ δ / 4) → dsum X ≤ τ) := by
  rintro ⟨τ, h1, h2⟩
  exact no_sum_gate hn hδ h1 h2


/-! ## 3.  The sliver: the repaired tolerance is EXACTLY tight at the refutation point

At d2's point `(G₁, t_W)` (`G₁`: two vertices, one edge of weight `1`, `Rq = 2`, `δ = 1/380000`,
`u_W = -(2 + 7δ/4)`), the sum statistic cannot do better than the gate's own tolerance: **every**
member has `dsum ≥ δ/4`, and the bound is ATTAINED.  So a `dvR ≤ δ/4` gate accepts a member only at
exact equality — no slack at all — while §2 shows that in general it rejects the campaign's own
witness.  Together: the released test must be per coordinate. -/

/-- The sliver input: two vertices, the single edge of weight `1`. -/
abbrev G₁m : QuantumMaxCutEnergy.Input := ⟨2, fun _ => (1 : ℚ≥0)⟩

/-- The sliver's tolerance `dqShallow G₁ = 1/380000`. -/
def δW : ℚ := 1 / 380000

/-- The window level `u_W = -(2 + 7δ/4)` (d2's `t_W − eps`). -/
def uW : ℚ := -(2 + 7 * δW / 4)

theorem Rq_G₁m : QMCLeafB.EngineRuntime.Rq G₁m = 2 := by
  unfold QMCLeafB.EngineRuntime.Rq
  show 2 * (∑ e : Edge G₁m.n, ((G₁m.weights e : ℚ≥0) : ℚ)) = 2
  rw [QMCLeafB.ResidRefute.univ_edge_two, Finset.sum_singleton]
  norm_num

theorem dqShallow_G₁m : QMCLeafB.RundataParams.dqShallow G₁m = δW := by
  rw [QMCLeafB.RundataParams.dqShallow, QMCLeafB.RundataParams.dqShallowCore,
    QMCLeafB.RundataCert.eps, Rq_G₁m, δW]
  norm_num

/-- The off-diagonal of the weight matrix of the sliver. -/
theorem wMatrixQ_G₁m_off : QMCLeafB.Finalization.wMatrixQ G₁m 0 1 = 1 := by
  simp [QMCLeafB.Finalization.wMatrixQ_apply, G₁m]

theorem wMatrixQ_G₁m_off' : QMCLeafB.Finalization.wMatrixQ G₁m 1 0 = 1 := by
  simp [QMCLeafB.Finalization.wMatrixQ_apply, G₁m]

theorem frob_wMatrixQ_G₁m (X : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₁m) X = X 0 1 + X 1 0 := by
  rw [QMCLeafB.SepOracle.frob, Fin.sum_univ_two]
  simp [wMatrixQ_G₁m_off, wMatrixQ_G₁m_off', QMCLeafB.Finalization.wMatrixQ_apply, G₁m]

theorem qf_ones (X : Matrix (Fin 2) (Fin 2) ℚ) :
    QMCLeafB.SepOracle.qf X (fun _ => (1 : ℚ)) = X 0 0 + X 0 1 + X 1 0 + X 1 1 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two]
  simp [Fin.sum_univ_two]
  ring

/-- **Every member at the sliver window pays at least the gate's tolerance.** -/
theorem dsum_member_ge {X : Matrix (Fin 2) (Fin 2) ℚ}
    (h : QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁m) X uW δW) :
    δW / 4 ≤ dsum X := by
  have hpsd := h.psd_margin (fun _ => (1 : ℚ))
  rw [qf_ones] at hpsd
  have htr : X 0 1 + X 1 0 ≤ uW + δW / 2 := by
    have h2 := h.trace_le
    rw [frob_wMatrixQ_G₁m] at h2
    exact h2
  have hsum : (∑ i : Fin 2, (1 : ℚ) ^ 2) = 2 := by norm_num
  rw [hsum] at hpsd
  have hd0 := h.diag_near 0
  have hd1 := h.diag_near 1
  have hle0 : X 0 0 - 1 ≤ |X 0 0 - 1| := le_abs_self _
  have hle1 : X 1 1 - 1 ≤ |X 1 1 - 1| := le_abs_self _
  have hd : dsum X = |X 0 0 - 1| + |X 1 1 - 1| := by
    rw [dsum, Fin.sum_univ_two]
  have huw : uW = -(2 + 7 * δW / 4) := rfl
  rw [hd]
  rw [huw] at htr
  linarith

/-- The member that attains it: diagonal `1 + δ/8`, off-diagonal `-(1 + 5δ/8)` — the point where the
psd margin and the trace clause are both exactly tight. -/
def MW : Matrix (Fin 2) (Fin 2) ℚ :=
  Lvl32M8.fam 2 ((1 + δW / 8) - (-(1 + 5 * δW / 8))) (-(1 + 5 * δW / 8))

theorem MW_member :
    QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁m) MW uW δW := by
  have hδ : (0 : ℚ) < δW := by rw [δW]; norm_num
  have hdb : ((1 + δW / 8) - (-(1 + 5 * δW / 8))) + (-(1 + 5 * δW / 8)) = 1 + δW / 8 := by ring
  have hb : (-(1 + 5 * δW / 8)) < 0 := by linarith
  have hkey : ((1 + δW / 8) - (-(1 + 5 * δW / 8))) + (2 : ℚ) * (-(1 + 5 * δW / 8))
      = -(δW / 2) := by ring
  refine ⟨hδ, ?_, ?_, ?_⟩
  · refine Lvl32M8.psd_clause_fam _ _ δW (Or.inr ⟨hb, ?_⟩)
    show -(δW / 2) ≤ ((1 + δW / 8) - (-(1 + 5 * δW / 8)))
      + (2 : ℚ) * (-(1 + 5 * δW / 8))
    rw [hkey]
  · intro i
    have hdiag : MW i i = 1 + δW / 8 := by
      rw [MW, Lvl32M8.fam_apply_self, hdb]
    rw [hdiag, show 1 + δW / 8 - 1 = δW / 8 by ring, abs_of_nonneg (by linarith)]
    linarith
  · rw [MW, Lvl32M8.frob_fam _ _ _ (Lvl32M8.wMatrixQ_diag_zero G₁m),
      Lvl32M8.sum_wMatrixQ_eq_Rq, Rq_G₁m]
    have : uW = -(2 + 7 * δW / 4) := rfl
    rw [this]
    ring_nf
    linarith

/-- **The tolerance is attained.** -/
theorem dsum_MW : dsum MW = δW / 4 := by
  have hδ : (0 : ℚ) < δW := by rw [δW]; norm_num
  have hdb : ((1 + δW / 8) - (-(1 + 5 * δW / 8))) + (-(1 + 5 * δW / 8)) = 1 + δW / 8 := by ring
  have hdiag : ∀ i : Fin 2, |MW i i - 1| = (δW / 2) / 4 := by
    intro i
    have h1 : MW i i = 1 + δW / 8 := by rw [MW, Lvl32M8.fam_apply_self, hdb]
    rw [h1, show 1 + δW / 8 - 1 = δW / 8 by ring, abs_of_nonneg (by linarith)]
    ring
  have h := dsum_of_all_eq (n := 2) MW (δ := δW / 2) hdiag
  rw [h]
  ring

/-- **The repaired gate at the sliver's window has ZERO slack**: its tolerance `δ/4` is exactly the
minimum of `dsum` over the body, and the minimum is attained.  A `dvR ≤ δ/4` test accepts a member
there only when the member sits exactly on the boundary. -/
theorem gate_tight_at_window :
    (∃ cX : Matrix (Fin 2) (Fin 2) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁m) cX uW δW ∧
        dsum cX = δW / 4) ∧
      (∀ cX : Matrix (Fin 2) (Fin 2) ℚ,
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₁m) cX uW δW →
        δW / 4 ≤ dsum cX) := by
  refine ⟨⟨MW, ?_, MW_member, dsum_MW⟩, fun cX h => dsum_member_ge h⟩
  rw [MW, Lvl32M8.fam_symm]


/-! ## 4.  The diagonal fallback cut's TRUE margin against the relaxed body

`RoundProgram.diagSignF` cuts with the diagonal normal `sᵢ = sgn (1 − cXᵢᵢ)`, i.e. it points every
coordinate at `1`.  Against the *exact* unit-diagonal body that is exactly right (`X` has `Xᵢᵢ = 1`,
so the cut at a state with `cXᵢᵢ ≠ 1` separates with margin `dvR`).  Against the RELAXED body
(`|Xᵢᵢ − 1| ≤ δ/4`) the margin loses `δ/4` per coordinate:

    frob (diag s) (X − cX) = ∑ᵢ sᵢ (Xᵢᵢ − cXᵢᵢ) ≥ dsum cX − n·(δ/4),

so the cut is valid (positive margin) only when `dvR cX > n·δ/4` — while a per-coordinate gate fires
the fallback as soon as ONE deviation exceeds `δ/4`, i.e. from `dvR = δ/4 + ε` up.  So the repair has
**two** coupled constraints, not one: the gate AND the fallback's normal must both be relaxed; the
fallback's normal has to be supported on the *violated* coordinates only, or the descent makes
non-separating cuts against the relaxed body (an invalid `RelaxCut`, which `hcut`/the volume
argument cannot tolerate). -/

/-- The sign of a rational, with its two defining properties. -/
theorem sgnOf_spec (q : ℚ) :
    QMCLeafB.RoundProgram.sgnOf q * q = |q| ∧ |QMCLeafB.RoundProgram.sgnOf q| ≤ 1 := by
  unfold QMCLeafB.RoundProgram.sgnOf
  by_cases h1 : q < 0
  · have h1' : ¬ q = 0 := ne_of_lt h1
    simp [h1, h1', abs_of_neg h1]
  · by_cases h2 : q = 0
    · simp [h1, h2]
    · have h3 : 0 < q := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
      simp [h1, h2, abs_of_pos h3]

/-- **The diagonal normal's margin over the relaxed body.**  For any sign vector `s` with
`sᵢ(1 − cXᵢᵢ) = |1 − cXᵢᵢ|` and `|sᵢ| ≤ 1`, every point `X` with the body's diagonal clause satisfies
`frob (diag s) (X − cX) ≥ dsum cX − n·(δ/4)`. -/
theorem diagSign_margin {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} (s : Fin n → ℚ)
    (hs : ∀ i, s i * (1 - cX i i) = |1 - cX i i|) (hs1 : ∀ i, |s i| ≤ 1)
    (X : Matrix (Fin n) (Fin n) ℚ) (hd : ∀ i, |X i i - 1| ≤ δ / 4) :
    dsum cX - (n : ℚ) * (δ / 4) ≤ ∑ i, s i * (X i i - cX i i) := by
  have hterm : ∀ i : Fin n, -(δ / 4) ≤ s i * (X i i - 1) := by
    intro i
    have h2 : |s i * (X i i - 1)| ≤ |X i i - 1| := by
      rw [abs_mul]
      have h3 := abs_nonneg (X i i - 1)
      nlinarith [hs1 i]
    have h4 := neg_abs_le (s i * (X i i - 1))
    linarith [hd i]
  have h1 : dsum cX - (n : ℚ) * (δ / 4)
      = (∑ i, |1 - cX i i|) + ∑ _i : Fin n, (-(δ / 4)) := by
    rw [dsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show (∑ i : Fin n, |cX i i - 1|) = ∑ i : Fin n, |1 - cX i i| from
      Finset.sum_congr rfl fun i _ => abs_sub_comm (cX i i) 1]
    ring
  rw [h1]
  have h2 : ∀ i : Fin n, |1 - cX i i| + (-(δ / 4)) ≤ |1 - cX i i| + s i * (X i i - 1) := by
    intro i; have := hterm i; linarith
  calc (∑ i, |1 - cX i i|) + ∑ _i : Fin n, (-(δ / 4))
      = ∑ i, (|1 - cX i i| + (-(δ / 4))) := Finset.sum_add_distrib.symm
    _ ≤ ∑ i, (|1 - cX i i| + s i * (X i i - 1)) := Finset.sum_le_sum fun i _ => h2 i
    _ = ∑ i, s i * (X i i - cX i i) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have := hs i
        linarith

/-- The cut that `diagSignF` actually expresses at the state `cX`, with the sign vector `QMCLeafB.RoundProgram.sgnOf`. -/
theorem diagSignF_margin {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (X : Matrix (Fin n) (Fin n) ℚ) (hd : ∀ i, |X i i - 1| ≤ δ / 4) :
    dsum cX - (n : ℚ) * (δ / 4)
      ≤ ∑ i, QMCLeafB.RoundProgram.sgnOf (1 - cX i i) * (X i i - cX i i) :=
  diagSign_margin (fun i => QMCLeafB.RoundProgram.sgnOf (1 - cX i i)) (fun i => (sgnOf_spec _).1)
    (fun i => (sgnOf_spec _).2) X hd

/-- **The fallback is not separating in the band `δ/4 < dvR ≤ n·δ/4`**: there the `diagSignF` margin
bound is non-positive, so the cut cannot certify `RelaxCut`'s `0 < margin`. -/
theorem diagSign_cut_insufficient {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ}
    (hlo : δ / 4 < dsum cX) (hhi : dsum cX ≤ (n : ℚ) * (δ / 4)) :
    ¬ (0 < dsum cX - (n : ℚ) * (δ / 4)) := by
  intro h
  linarith


/-- **The repaired fallback: support the normal on the VIOLATED coordinates only.**  If the sign
vector vanishes off a coordinate set `S` and the sign condition holds on `S`, the cut's margin against
the relaxed body is `∑_{i∈S} (|1 − cXᵢᵢ| − δ/4)` — no `δ/4` is charged for the coordinates the test
did not need to push. -/
theorem diag_cut_margin_on {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} (S : Finset (Fin n))
    (s : Fin n → ℚ) (hS : ∀ i, i ∉ S → s i = 0)
    (hs : ∀ i, i ∈ S → s i * (1 - cX i i) = |1 - cX i i|) (hs1 : ∀ i, |s i| ≤ 1)
    (X : Matrix (Fin n) (Fin n) ℚ) (hd : ∀ i, |X i i - 1| ≤ δ / 4) :
    ∑ i ∈ S, (|1 - cX i i| - δ / 4) ≤ ∑ i, s i * (X i i - cX i i) := by
  have hterm : ∀ i, i ∈ S → -(δ / 4) ≤ s i * (X i i - 1) := by
    intro i _
    have h2 : |s i * (X i i - 1)| ≤ |X i i - 1| := by
      rw [abs_mul]
      have h3 := abs_nonneg (X i i - 1)
      nlinarith [hs1 i]
    have h4 := neg_abs_le (s i * (X i i - 1))
    linarith [hd i]
  have hsplit : (∑ i, s i * (X i i - cX i i)) = ∑ i ∈ S, s i * (X i i - cX i i) := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => ?_)]
    rw [hS i hi]; ring
  rw [hsplit]
  refine Finset.sum_le_sum fun i hi => ?_
  have h1 : s i * (X i i - cX i i) = s i * (X i i - 1) + |1 - cX i i| := by
    have h := hs i hi
    linarith
  have h2 := hterm i hi
  rw [h1]
  linarith

/-- A nonempty set of violated coordinates gives a strictly positive margin — the repaired fallback
certifies `RelaxCut`'s `0 < margin` whenever the gate rejects. -/
theorem diag_cut_margin_pos {n : ℕ} {cX : Matrix (Fin n) (Fin n) ℚ} {δ : ℚ} (S : Finset (Fin n))
    (hne : S.Nonempty) (hviol : ∀ i ∈ S, δ / 4 < |1 - cX i i|) :
    0 < ∑ i ∈ S, (|1 - cX i i| - δ / 4) := by
  obtain ⟨i0, hi0⟩ := hne
  refine Finset.sum_pos' (fun i _ => by linarith [hviol i ‹i ∈ S›]) ⟨i0, hi0, ?_⟩
  linarith [hviol i0 hi0]

end RTest32M8

/-! ## Axiom audit -/

#print axioms RTest32M8.le_dsum
#print axioms RTest32M8.diag_of_dsum_le
#print axioms RTest32M8.dsum_of_all_eq
#print axioms RTest32M8.le_of_sound
#print axioms RTest32M8.ge_of_cover
#print axioms RTest32M8.no_sum_gate
#print axioms RTest32M8.dsum_fam
#print axioms RTest32M8.sum_gate_rejects_fam
#print axioms RTest32M8.campaign_witness
#print axioms RTest32M8.diagGate_of_relaxMem
#print axioms RTest32M8.no_sum_test
#print axioms RTest32M8.dsum_member_ge
#print axioms RTest32M8.MW_member
#print axioms RTest32M8.dsum_MW
#print axioms RTest32M8.gate_tight_at_window
#print axioms RTest32M8.sgnOf_spec
#print axioms RTest32M8.diagSign_margin
#print axioms RTest32M8.diagSignF_margin
#print axioms RTest32M8.diagSign_cut_insufficient
#print axioms RTest32M8.diag_cut_margin_on
#print axioms RTest32M8.diag_cut_margin_pos



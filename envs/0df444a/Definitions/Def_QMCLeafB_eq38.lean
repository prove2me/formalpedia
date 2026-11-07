-- Prove2me | Definitions.Def_QMCLeafB_eq38
-- name    : QMCLeafB_eq38
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:26:58.80525+00:00
-- url     : https://prove2.me/theorems/1bf89148-113b-448a-9bc1-d3548587e3b7
-- title:
--   QMCLeafB eq38
-- statement:
--   # `Check_eq38_m2` — phase 38, member m2, direction `equivalence-elimination`
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_runparts_dilate_m5
import Definitions.Def_QMCLeafB_sim_loop_m6
/-
# `Check_eq38_m2` — phase 38, member m2, direction `equivalence-elimination`

## What is decided here

Leaf B's residual is "ONE inequality": at every round `k < K·m`,

    sup_{z ∈ body} c_k ⬝ (Cat_k − z)  ≤  rmax · √σ_k ,      σ_k = c_k ⬝ p_k,  A_k p_k = c_k,

read in the campaign notes as *"the ellipsoid centre stays within `rmax` of the body in the current
`A_k`-norm"*.  This file decides what that inequality actually is, and what it is not.

* **§1 — it is NOT a distance statement.**  Three machine-checked facts at one round, for an
  arbitrary positive definite `A`, an arbitrary centre `a` and an arbitrary body:
  * `support_le_sqrt` : the *trivial* bound is `√σ` (Cauchy–Schwarz in the `A`-inner product plus
    `body ⊆ E(A,a)`), not `rmax·√σ` — the leaf asks for a factor `4N` better than containment gives;
  * `no_shallow_of_ball` : if the body contains the `A`-ball of radius `r` about `a` with `r > rmax`
    then **every** nonzero normal violates the bound at that round.  The witness is explicit:
    `z = a − (r/√σ)·p` lies in that ball and has `c ⬝ᵥ (a − z) = r√σ > rmax√σ`;
  * `shallow_of_supporting` : if the body lies beyond a supporting hyperplane through `a`
    (`0 ≤ c ⬝ᵥ (z − a)` for `z` in the body), the bound holds with the **whole `rmax` budget unspent**.
  So the quantity the leaf bounds is a *half-space depth* of the centre relative to the body, which is
  strictly stronger than `dist_A(Cat, body) ≤ rmax`: in `ellipsoid_body_fails_every_normal` the body
  IS the ellipsoid `E(1,0)` at `N = 4` (so `body_containment` holds with equality and the centre is a
  body point, `dist_A = 0 ≤ rmax = 1/16`), and yet no normal satisfies the bound.

* **§2 — the record class inherits the criterion; its failure mode is the FAT body, not the far
  body.**  `bodyRec_shallowAt` restates the banked `ThinRec34M4.encl_of_bodyRec` as `(L_k)` at every
  round of the run's own transcript.  `false_of_ball_at_round` + `not_bodyRec_of_fat_centre`: if at
  some round `k < K·m` the relaxation contains the `A_k`-ball of radius `r > rmax` about the run's own
  `Cat_k`, then the all-cut record does not exist — no trajectory, no normal stream, no depth ledger,
  and NO volume hypothesis (the banked horizon theorems need `r ≳ 10^{-160639}`; the record's own
  threshold is `rmax = 1/(4n²)`).  This is the sharp counterpart of `no_price_of_deep_point`: one deep
  point kills one normal, a fat ball kills all of them.

* **§3 — the quantitative gap: the leaf is off by the constant `4`, uniformly in `N`.**  After a
  supporting cut the *same* normal ranks the next round at `(1−ρ)/(N+ρ)` (exactly:
  `sqrtSigmaR_inv_stepShape`, `support_stepCentre_le`, `supporting_normal_ratio`), while the leaf asks
  for `rmax = 1/(4N)`; at the only legal depth `ρ ≤ rmax` the guarantee exceeds the allowance by
  `4N(1−ρ)/(N+ρ) → 4` (`ratio_gt_rmax`, `reuse_short_of_leaf`).  So the inequality is nearly true —
  and the deficiency of the natural cut is the constant `4`, not a numerical accident.

* **§4 — the verdict at the campaign's own constant** (`rmaxOf 4 = 1/16`):
  `leaf_not_implied_by_containment` packages the refutation in the leaf's own terms.

Discipline: `set_option autoImplicit false`; no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`;
`#print axioms` after every load-bearing declaration, each exactly
`[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Eq38M2

open QMCLeafB
open QMCLeafB.EngineIterates
open QuantumMaxCutEnergy

/-! ## 1.  One round: the inequality is a half-space depth, not a distance

Fix a positive definite shape `A`, a centre `a`, a nonzero normal `c` with rational witness `p`
(`A p = c`) and an arbitrary body `body`.  The leaf's inequality at this round at level `r` is

    ShallowAt body a c p r  :=  ∀ z, body z → c ⬝ᵥ (a − z) ≤ r · √σ. -/

/-- **The leaf's inequality at one round**, in support form. -/
def ShallowAt {N : ℕ} (body : (Fin N → ℝ) → Prop) (a : Fin N → ℝ) (c p : Fin N → ℝ)
    (r : ℝ) : Prop :=
  ∀ z, body z → c ⬝ᵥ (a - z) ≤ r * sqrtSigmaR c p

/-! ### 1.1  The trivial bound: containment alone gives `√σ`, never `rmax·√σ` -/

/-- `(a − z)` and `(z − a)` have the same `A`-quadratic form. -/
theorem qf_swap {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (a z : Fin N → ℝ) :
    (a - z) ⬝ᵥ (A *ᵥ (a - z)) = (z - a) ⬝ᵥ (A *ᵥ (z - a)) := by
  rw [show a - z = -(z - a) by abel, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

/-- **Cauchy–Schwarz at the round's own data**: a body inside the ellipsoid satisfies the support
bound at level `1` — and `1 ≫ rmax`.  This is the *only* bound that `body_containment` supplies, so
the leaf's `rmax` is a factor `4N` beyond what containment gives. -/
theorem support_le_sqrt {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a z : Fin N → ℝ}
    (hz : z ∈ Ell A a) :
    c ⬝ᵥ (a - z) ≤ sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hr : 0 < sqrtSigmaR c p := sqrtSigmaR_pos hA hAp hc
  have hrr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hq : (a - z) ⬝ᵥ (A *ᵥ (a - z)) ≤ 1 := by
    rw [qf_swap]; exact hz
  have hcau := cauchy_sigmaR hA hAp hc (a - z)
  have hsq2 : sqrtSigmaR c p ^ 2 = sigmaR c p := by rw [pow_two]; exact hrr
  have hsq : (c ⬝ᵥ (a - z)) ^ 2 ≤ sqrtSigmaR c p ^ 2 := by
    rw [hsq2]
    calc (c ⬝ᵥ (a - z)) ^ 2 ≤ sigmaR c p * ((a - z) ⬝ᵥ (A *ᵥ (a - z))) := hcau
      _ ≤ sigmaR c p * 1 := by
          exact mul_le_mul_of_nonneg_left hq hσ.le
      _ = sigmaR c p := by ring
  have hprod : 0 ≤ (sqrtSigmaR c p - c ⬝ᵥ (a - z)) * (sqrtSigmaR c p + c ⬝ᵥ (a - z)) := by
    nlinarith [hsq]
  nlinarith [hprod, hr]

#print axioms QMCLeafB.Eq38M2.support_le_sqrt

/-! ### 1.2  A fat body kills EVERY normal

The witness `z = a − (r/√σ)·p` is the point of the `A`-ball of radius `r` about `a` that is deepest
in the direction of the normal `c`, and it is deepest by exactly `r·√σ`.  So a body that contains
that ball admits no normal at level `< r` whatsoever. -/

/-- **The witness point lies on the `A`-sphere of radius `r` about `a`.** -/
theorem ball_witness_qf {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) (a : Fin N → ℝ) (r : ℝ) :
    ((a - (r / sqrtSigmaR c p) • p) - a) ⬝ᵥ
        (A *ᵥ ((a - (r / sqrtSigmaR c p) • p) - a)) = r ^ 2 := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hsq : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hApp : p ⬝ᵥ (A *ᵥ p) = sigmaR c p := by rw [hAp]; exact dotProduct_comm p c
  have hsub : (a - (r / sqrtSigmaR c p) • p) - a = -((r / sqrtSigmaR c p) • p) := by abel
  rw [hsub, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul, hApp]
  have hsne : sqrtSigmaR c p ≠ 0 := ne_of_gt (sqrtSigmaR_pos hA hAp hc)
  have hkey : (sqrtSigmaR c p * sqrtSigmaR c p) * (sqrtSigmaR c p)⁻¹ ^ 2 = 1 := by
    field_simp
  rw [← hsq]
  linear_combination (r ^ 2) * hkey

#print axioms QMCLeafB.Eq38M2.ball_witness_qf

/-- **The witness point beats the normal by exactly `r·√σ`.** -/
theorem ball_witness_support {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) (a : Fin N → ℝ) {r : ℝ}
    (hr : 0 ≤ r) :
    c ⬝ᵥ (a - (a - (r / sqrtSigmaR c p) • p)) = r * sqrtSigmaR c p := by
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hsq : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hsub : a - (a - (r / sqrtSigmaR c p) • p) = (r / sqrtSigmaR c p) • p := by abel
  rw [hsub, dotProduct_smul, smul_eq_mul]
  change (r / sqrtSigmaR c p) * sigmaR c p = r * sqrtSigmaR c p
  rw [← hsq]
  field_simp

#print axioms QMCLeafB.Eq38M2.ball_witness_support

/-- **A fat body admits NO nonzero normal.**  If the body contains the `A`-ball of radius `r` about
`a` and `rmax < r`, then at that round the leaf's inequality fails for every normal `c` and every
witness `p`.  Nothing else is used about the body, and nothing about the trajectory. -/
theorem no_shallow_of_ball {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {r rmax : ℝ}
    (hr : 0 ≤ r) (hlt : rmax < r) {body : (Fin N → ℝ) → Prop}
    (hball : ∀ z : Fin N → ℝ, (z - a) ⬝ᵥ (A *ᵥ (z - a)) ≤ r ^ 2 → body z) :
    ¬ ShallowAt body a c p rmax := by
  intro h
  have hr2 : 0 < sqrtSigmaR c p := sqrtSigmaR_pos hA hAp hc
  have hmem := hball _ (le_of_eq (ball_witness_qf hA hc hAp a r))
  have hb := h _ hmem
  rw [ball_witness_support hA hc hAp a hr] at hb
  nlinarith

#print axioms QMCLeafB.Eq38M2.no_shallow_of_ball

/-! ### 1.3  A supporting half-space satisfies the bound with the whole budget unspent -/

/-- **The supporting cut is free.**  If the body lies beyond the hyperplane through the centre with
normal `c`, the inequality holds at level `0` — so at level `rmax` with nothing spent.  This is the
only direction in which the record is ever produced. -/
theorem shallow_of_supporting {N : ℕ} {body : (Fin N → ℝ) → Prop} {a c p : Fin N → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hsupp : ∀ z, body z → 0 ≤ c ⬝ᵥ (z - a)) :
    ShallowAt body a c p r := by
  intro z hz
  have h1 : c ⬝ᵥ (a - z) ≤ 0 := by
    rw [show a - z = -(z - a) by abel, dotProduct_neg]
    linarith [hsupp z hz]
  have h2 : 0 ≤ r * sqrtSigmaR c p := mul_nonneg hr (Real.sqrt_nonneg _)
  linarith

#print axioms QMCLeafB.Eq38M2.shallow_of_supporting

/-! ### 1.4  The exact rational instance: distance `0`, every normal fails

`N = 4` (`n = 2`), `A = 1`, centre `a = 0`, body = the unit Euclidean ball = the ellipsoid `E(1,0)`
itself, `rmax = 1/16 = rmaxOf 4`.  `body_containment` holds with EQUALITY, the centre is a body point
so the `A`-norm distance of the centre to the body is `0 ≤ rmax` — and no nonzero normal satisfies
the leaf's inequality.  Hence the campaign's "bounded distance" reading and the record's support
requirement are different conditions, and the leaf is the latter. -/

/-- The centre is a point of the body (`dist_A = 0`), in the ellipsoid-filling instance. -/
theorem centre_mem_unit_ball : (fun _ : Fin 4 => (0 : ℝ)) ⬝ᵥ
    ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ (fun _ => (0 : ℝ))) ≤ (1 : ℝ) := by
  simp [dotProduct]

#print axioms QMCLeafB.Eq38M2.centre_mem_unit_ball

/-- **The ellipsoid-filling body fails the leaf's inequality for every normal**, at `N = 4`,
`rmax = 1/16`.  (`rmaxOf 4 = 1/16`.) -/
theorem ellipsoid_body_fails_every_normal :
    ¬ ∃ (c p : Fin 4 → ℝ), c ≠ 0 ∧ (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ p = c ∧
      ShallowAt (fun z : Fin 4 → ℝ => z ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ z) ≤ 1)
        (fun _ => (0 : ℝ)) c p (1 / 16) := by
  rintro ⟨c, p, hc, hAp, h⟩
  refine no_shallow_of_ball (A := (1 : Matrix (Fin 4) (Fin 4) ℝ))
    (Matrix.PosDef.one) hc hAp (a := fun _ => (0 : ℝ)) (r := 1) (rmax := 1 / 16)
    (by norm_num) (by norm_num)
    (fun z hz => by simpa using hz) h

#print axioms QMCLeafB.Eq38M2.ellipsoid_body_fails_every_normal

/-! ## 2.  The record's own constraint, at EVERY round

`ThinRec34M4.encl_of_bodyRec` (banked) already extracts the bounded-distance inequality from an
all-cut record.  §1.2 sharpens it into a statement about the RECORD CLASS: at any round whose centre
carries an `rmax`-fat `A_k`-ball, no transcript exists at all.  The names below abbreviate the
record's own shape and centre so that the statements stay readable. -/

/-- The record's own initial shape at `P` (the one `RunParts.hwit` speaks). -/
abbrev recA0 (G : QuantumMaxCutEnergy.Input) (P : QMCLeafB.FinalStroke.RunParams G) :
    Matrix (Fin (G.n * G.n)) (Fin (G.n * G.n)) ℚ :=
  QMCLeafB.Boundary.initShapeOf (G.n * G.n) (2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2)

/-- The record's own accumulated centre at round `k`. -/
abbrev recCat {G : QuantumMaxCutEnergy.Input}
    (cd : ℕ → QMCLeafB.EngineIterates.CutData (G.n * G.n)) (k : ℕ) : Fin (G.n * G.n) → ℝ :=
  QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ) cd k

/-- **Every round of an all-cut record satisfies the leaf's inequality** — the banked
`encl_of_bodyRec`, restated in the support form `ShallowAt` so that §1 applies to it verbatim. -/
theorem bodyRec_shallowAt {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G}
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P) :
    ∀ k, k < P.K * P.m →
      ShallowAt (QMCLeafB.ThinRec34M4.relaxBallP G t P) (recCat B.cd k)
        (QMCLeafB.EngineIterates.cutCR B.cd k) (QMCLeafB.EngineIterates.cutPR B.cd k)
        ((P.rmax : ℚ) : ℝ) := by
  intro k hk z hz
  have h := QMCLeafB.ThinRec34M4.encl_of_bodyRec B k hk z hz
  have hcast : ((QMCLeafB.EngineIterates.sigmaQ (B.cd k).c (B.cd k).p : ℚ) : ℝ)
      = sigmaR (QMCLeafB.EngineIterates.cutCR B.cd k)
          (QMCLeafB.EngineIterates.cutPR B.cd k) :=
    QMCLeafB.EngineIterates.cast_sigmaQ _ _
  rw [hcast] at h
  rw [dotProduct_sub]
  exact h

#print axioms QMCLeafB.Eq38M2.bodyRec_shallowAt

/-- **A fat ball at a round kills the whole all-cut record.**  If at some round `k < K·m` the
relaxation contains the `A_k`-ball of radius `r > rmax` about the run's own centre `Cat_k`, then the
transcript cannot exist: `encl_of_bodyRec` puts the centre in a supporting half-space at depth
`rmax·√σ_k`, and §1.2 exhibits a body point beating that by `r√σ_k`.  No volume hypothesis, no
collar, no depth ledger. -/
theorem false_of_ball_at_round {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n)
    (B : QMCLeafB.FinalStroke.RunParts QMCLeafB.ThinRec34M4.falseBit G t P)
    {k : ℕ} (hk : k < P.K * P.m) {r : ℝ} (hr : 0 ≤ r)
    (hfat : ((P.rmax : ℚ) : ℝ) < r)
    (hball : ∀ z : Fin (G.n * G.n) → ℝ,
      (z - recCat B.cd k) ⬝ᵥ
        ((QMCLeafB.EngineIterates.castM
          (QMCLeafB.EngineIterates.Aat (G.n * G.n) (recA0 G P) B.cd k)) *ᵥ
          (z - recCat B.cd k)) ≤ r ^ 2 →
      z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P) : False := by
  have hany : QMCLeafB.SimLoop.anyOk B.ok (P.K * P.m) = false := B.hverdict.symm
  have hall : ∀ j, j < P.K * P.m → B.ok j = false :=
    (QMCLeafB.SimLoop.anyOk_eq_false_iff B.ok (P.K * P.m)).1 hany
  have hNr : (0 : ℚ) < 2 * (G.n : ℚ) ^ 2 + 2 * P.dq ^ 2 := by positivity
  have hA0 : (QMCLeafB.EngineIterates.castM (recA0 G P)).PosDef :=
    QMCLeafB.Boundary.initShapeOf_cast_posDef hNr
  have hn' : 2 ≤ G.n * G.n := by
    have h : 2 * 2 ≤ G.n * G.n := Nat.mul_le_mul hn hn
    omega
  have hpos := QMCLeafB.SimLoop.Aat_cast_posDef_prefix (n := G.n * G.n) hn' hA0
    (fun j hj => B.hwit j hj (hall j hj)) (fun j hj => B.hrho j hj (hall j hj))
    (fun j hj => B.hcne j hj (hall j hj)) k (le_of_lt hk)
  have hrel : QMCLeafB.EngineIterates.castM
        (QMCLeafB.EngineIterates.Aat (G.n * G.n) (recA0 G P) B.cd k) *ᵥ
        QMCLeafB.EngineIterates.cutPR B.cd k = QMCLeafB.EngineIterates.cutCR B.cd k := by
    rw [QMCLeafB.EngineIterates.cast_mulVec, B.hwit k hk (hall k hk)]
  have hne : QMCLeafB.EngineIterates.cutCR B.cd k ≠ 0 :=
    QMCLeafB.EngineIterates.cast_normal_ne (B.hcne k hk (hall k hk))
  exact no_shallow_of_ball (A := QMCLeafB.EngineIterates.castM
      (QMCLeafB.EngineIterates.Aat (G.n * G.n) (recA0 G P) B.cd k)) hpos hne hrel
    (a := recCat B.cd k) hr hfat hball (bodyRec_shallowAt B k hk)

#print axioms QMCLeafB.Eq38M2.false_of_ball_at_round

/-- **The all-cut record class is EMPTY at a fat body** — the normal-free form of the verdict: no
choice of normals, depths or margins produces a transcript. -/
theorem not_bodyRec_of_fat_centre {G : QuantumMaxCutEnergy.Input} {t : ℚ}
    {P : QMCLeafB.FinalStroke.RunParams G} (hn : 2 ≤ G.n) (hKm : 1 ≤ P.K * P.m)
    {r : ℝ} (hr : 0 ≤ r) (hfat : ((P.rmax : ℚ) : ℝ) < r)
    (hball : ∀ z : Fin (G.n * G.n) → ℝ,
      z ⬝ᵥ ((QMCLeafB.EngineIterates.castM (recA0 G P)) *ᵥ z) ≤ r ^ 2 →
      z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t P) :
    ¬ QMCLeafB.ThinRec34M4.BodyRec G t P := by
  rintro ⟨B⟩
  refine false_of_ball_at_round hn B (k := 0) (by omega) hr hfat ?_
  intro z hz
  have hz' : (z - recCat B.cd 0) = z := by
    show z - (0 : Fin (G.n * G.n) → ℝ) = z
    abel
  rw [hz'] at hz
  exact hball z hz

#print axioms QMCLeafB.Eq38M2.not_bodyRec_of_fat_centre

/-! ## 3.  The exact one-step trade-off: the supporting normal is off by the factor `≈ 4`

A supporting cut is the only kind the record ever uses (§1.3), and it spends none of the `rmax`
budget.  What does the SAME normal cost one round later?  The step moves the centre by `γ/√σ · p`
and rescales the shape, and the computation below gives the exact ratio `(1−ρ)/(N+ρ)`.  At the only
legal depth `ρ = rmax = 1/(4N)` that ratio **exceeds** `rmax`, by a factor tending to `4`: the leaf's
inequality is exactly four times too tight to be invariant under the natural cut. -/

/-- The step's own witness for the same normal: `A' ⬝ᵥ ((α(1+β))⁻¹ p) = c`. -/
theorem mulVec_stepShape_wit {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    stepShape N A c p ρ *ᵥ ((1 / (alphaR N ρ * (1 + betaR N))) • p) = c := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := natCast_two_le hn
  have hα : alphaR N ρ ≠ 0 := by
    rw [alphaR]
    have h1 : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
    have h2 : (0 : ℝ) < ((N : ℝ) + ρ) ^ 2 := by positivity
    exact div_ne_zero (ne_of_gt h1) (ne_of_gt h2)
  have hβ : (1 : ℝ) + betaR N ≠ 0 := by
    rw [one_add_betaR hn]
    have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    exact div_ne_zero (ne_of_gt h2) (ne_of_gt h1)
  have hσ : sigmaR c p ≠ 0 := ne_of_gt (sigmaR_pos hA hAp hc)
  rw [stepShape, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.add_mulVec, hAp,
    smul_vecMulVec_mulVec]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  have hσp : c ⬝ᵥ p = sigmaR c p := rfl
  field_simp
  rw [hσp]
  ring

#print axioms QMCLeafB.Eq38M2.mulVec_stepShape_wit

/-- **`σ` after one step, in the step's own normal**: `σ' = σ / (α(1+β))`. -/
theorem sigmaR_inv_stepShape {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    sigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = sigmaR c p / (alphaR N ρ * (1 + betaR N)) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hn hA hc hAp hρ
  rw [inv_mulVec_eq_of_mulVec_eq hA' (mulVec_stepShape_wit hn hA hc hAp hρ)]
  show c ⬝ᵥ ((1 / (alphaR N ρ * (1 + betaR N))) • p)
      = sigmaR c p / (alphaR N ρ * (1 + betaR N))
  rw [dotProduct_smul, smul_eq_mul, sigmaR]
  ring

#print axioms QMCLeafB.Eq38M2.sigmaR_inv_stepShape

/-- **`√σ` after one step**: `√σ' = √σ ⬝ᵥ (N+ρ)/(N+1)`. -/
theorem sqrtSigmaR_inv_stepShape {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = sqrtSigmaR c p * (((N : ℝ) + ρ) / ((N : ℝ) + 1)) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := natCast_two_le hn
  have hα : alphaR N ρ ≠ 0 := by
    rw [alphaR]
    have h1 : (0 : ℝ) < (N : ℝ) ^ 2 - 1 := by nlinarith
    have h2 : (0 : ℝ) < ((N : ℝ) + ρ) ^ 2 := by positivity
    exact div_ne_zero (ne_of_gt h1) (ne_of_gt h2)
  have hβ : (1 : ℝ) + betaR N ≠ 0 := by
    rw [one_add_betaR hn]
    have h1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    exact div_ne_zero (ne_of_gt h2) (ne_of_gt h1)
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  -- `1/(α(1+β)) = ((N+ρ)/(N+1))^2`
  have hαβ : alphaR N ρ * (1 + betaR N) = 1 / ((1 - gammaR N ρ) ^ 2) := by
    rw [alphaR_eq hn hρ]
    field_simp
  have hkey : (alphaR N ρ * (1 + betaR N))⁻¹ = (((N : ℝ) + ρ) / ((N : ℝ) + 1)) ^ 2 := by
    rw [hαβ, one_sub_gammaR]
    field_simp
  have hrew : sigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      = sigmaR c p * (((N : ℝ) + ρ) / ((N : ℝ) + 1)) ^ 2 := by
    rw [sigmaR_inv_stepShape hn hA hc hAp hρ, div_eq_mul_inv, hkey]
  rw [sqrtSigmaR, hrew, sqrtSigmaR, Real.sqrt_mul hσ.le, Real.sqrt_sq (by positivity)]

#print axioms QMCLeafB.Eq38M2.sqrtSigmaR_inv_stepShape

/-- **The centre moves by `γ·√σ` in the cut's own direction**: the triangle `a, a', z` in the
support.  This is the "deep cut moves the centre" half of the trade-off. -/
theorem support_stepCentre_le {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ}
    {body : (Fin N → ℝ) → Prop} (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) :
    ∀ z, body z → c ⬝ᵥ (stepCentre N a c p ρ - z) ≤ gammaR N ρ * sqrtSigmaR c p := by
  intro z hz
  have hσ : 0 < sigmaR c p := sigmaR_pos hA hAp hc
  have hr : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hstep : stepCentre N a c p ρ - z
      = (a - z) + ((gammaR N ρ / sqrtSigmaR c p) • p) := by
    rw [stepCentre]; abel
  rw [hstep, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have h1 := hsupp z hz
  have h2 : (gammaR N ρ / sqrtSigmaR c p) * (c ⬝ᵥ p) = gammaR N ρ * sqrtSigmaR c p := by
    have hσ' : c ⬝ᵥ p = sqrtSigmaR c p * sqrtSigmaR c p := by rw [hr]; rfl
    rw [hσ']
    have hsne : sqrtSigmaR c p ≠ 0 := ne_of_gt (sqrtSigmaR_pos hA hAp hc)
    field_simp
  linarith

#print axioms QMCLeafB.Eq38M2.support_stepCentre_le

/-- **THE EXACT TRADE-OFF.**  One step after a supporting cut in the normal `c`, the same normal sees
the body at `(1−ρ)/(N+ρ) ⬝ᵥ √σ'`.  Nothing is estimated but the one supporting inequality. -/
theorem supporting_normal_ratio {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) {body : (Fin N → ℝ) → Prop}
    (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) {z : Fin N → ℝ} (hz : body z) :
    c ⬝ᵥ (stepCentre N a c p ρ - z)
      ≤ ((1 - ρ) / ((N : ℝ) + ρ))
        * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := natCast_two_le hn
  have h1 := support_stepCentre_le (ρ := ρ) hA hc hAp hsupp z hz
  have h2 := sqrtSigmaR_inv_stepShape hn hA hc hAp hρ
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hγ : gammaR N ρ * sqrtSigmaR c p
      = ((1 - ρ) / ((N : ℝ) + ρ))
        * (sqrtSigmaR c p * (((N : ℝ) + ρ) / ((N : ℝ) + 1))) := by
    rw [gammaR]
    field_simp
  calc c ⬝ᵥ (stepCentre N a c p ρ - z)
      ≤ gammaR N ρ * sqrtSigmaR c p := h1
    _ = ((1 - ρ) / ((N : ℝ) + ρ))
          * (sqrtSigmaR c p * (((N : ℝ) + ρ) / ((N : ℝ) + 1))) := hγ
    _ = ((1 - ρ) / ((N : ℝ) + ρ))
          * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by rw [h2]

#print axioms QMCLeafB.Eq38M2.supporting_normal_ratio

/-- **`rmax = 1/(4N)` is strictly below the ratio.**  So the ratio of §3 is not a near miss: it
exceeds the leaf's allowance by the factor `4N(1−ρ)/(N+ρ)`, which tends to `4`. -/
theorem ratio_gt_rmax {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρN : ρ ≤ 1 / (4 * (N : ℝ))) :
    1 / (4 * (N : ℝ)) < (1 - ρ) / ((N : ℝ) + ρ) := by
  have hN1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpos : (0 : ℝ) < 4 * (N : ℝ) := by positivity
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have h4 : ρ * (4 * (N : ℝ) + 1) ≤ 1 + 1 / (4 * (N : ℝ)) := by
    have hle : (0 : ℝ) ≤ 4 * (N : ℝ) + 1 := by linarith
    have h := mul_le_mul_of_nonneg_right hρN hle
    calc ρ * (4 * (N : ℝ) + 1) ≤ (1 / (4 * (N : ℝ))) * (4 * (N : ℝ) + 1) := h
      _ = 1 + 1 / (4 * (N : ℝ)) := by field_simp
  have h5 : 1 / (4 * (N : ℝ)) ≤ 1 := by
    rw [div_le_one hpos]
    linarith
  rw [← sub_pos]
  have hkey : (1 - ρ) / ((N : ℝ) + ρ) - 1 / (4 * (N : ℝ))
      = (3 * (N : ℝ) - ρ * (4 * (N : ℝ) + 1)) / (((N : ℝ) + ρ) * (4 * (N : ℝ))) := by
    field_simp
    ring
  rw [hkey]
  apply div_pos _ (by positivity)
  nlinarith [h4, h5, hN2, hρ0]

#print axioms QMCLeafB.Eq38M2.ratio_gt_rmax

/-- **THE VERDICT OF §3, in one line.**  At every legal depth `ρ ≤ rmax = 1/(4N)` the supporting
cut's own guarantee at the NEXT round — `(1−ρ)/(N+ρ)`, in the next round's units — exceeds the leaf's
allowance `rmax`.  So reusing the natural normal cannot certify the leaf: the bound the cut supplies
is above what the leaf grants, by the factor `4N(1−ρ)/(N+ρ) → 4`.  A fresh direction is needed at
every round, and this is exactly where the factor `4` sits. -/
theorem reuse_short_of_leaf {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρN : ρ ≤ 1 / (4 * (N : ℝ))) :
    (1 / (4 * (N : ℝ))) * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c)
      < ((1 - ρ) / ((N : ℝ) + ρ))
        * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have hA' : (stepShape N A c p ρ).PosDef := stepShape_posDef hn hA hc hAp hρ
  have hinv : (stepShape N A c p ρ) *ᵥ ((stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have h3 : 0 < sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) :=
    sqrtSigmaR_pos hA' hinv hc
  have h2 := ratio_gt_rmax (le_trans (by norm_num : 1 ≤ 2) hn) hρ hρN
  exact mul_lt_mul_of_pos_right h2 h3

#print axioms QMCLeafB.Eq38M2.reuse_short_of_leaf

/-! ## 4.  The verdict, at the campaign's own constant

`rmax = rmaxOf (n·n) = 1/(4·n²)`, so at `n = 2` the leaf's constant is `rmaxOf 4 = 1/16`.  The
packaged statement below is the refutation in the leaf's own terms: the ellipsoid-filling body
satisfies `body_containment` with EQUALITY and contains its own centre, `A`-norm distance `0`, and
still no nonzero normal satisfies the leaf's inequality. -/

/-- The campaign's constant at `n = 2`. -/
theorem rmaxOf_four : QMCLeafB.RundataHalving.rmaxOf 4 = 1 / 16 := by
  rw [QMCLeafB.RundataHalving.rmaxOf]
  norm_num

#print axioms QMCLeafB.Eq38M2.rmaxOf_four

/-- **THE VERDICT.**  The leaf's inequality is NOT a consequence of the machine-checked ingredients
(`body_containment` + a centre + a shape), and it is not the bounded-distance statement the campaign
notes describe: for the body that fills the ellipsoid `E(1,0)` at `N = 4` the centre is a body point
(`dist_A = 0`), and yet every nonzero normal violates

    sup_{z ∈ body} c ⬝ (Cat − z)  ≤  rmax ⬝ᵥ √σ ,     rmax = rmaxOf 4 = 1/16.

The inequality is a HALF-SPACE-DEPTH condition: it holds with the whole `rmax` budget unspent exactly
when the body leaves the centre on the far side of a supporting hyperplane (§1.3), and it fails for
every normal exactly when the body is `rmax`-fat about the centre (§1.2).  The record class inherits
this: §2 shows the transcript is empty at every `rmax`-fat round. -/
theorem leaf_not_implied_by_containment :
    (fun _ : Fin 4 => (0 : ℝ)) ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ (fun _ => (0 : ℝ))) ≤ 1 ∧
      ¬ ∃ (c p : Fin 4 → ℝ), c ≠ 0 ∧ (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ p = c ∧
        ShallowAt (fun z : Fin 4 → ℝ => z ⬝ᵥ ((1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ z) ≤ 1)
          (fun _ => (0 : ℝ)) c p (1 / 16) :=
  ⟨centre_mem_unit_ball, ellipsoid_body_fails_every_normal⟩

#print axioms QMCLeafB.Eq38M2.leaf_not_implied_by_containment

/-- **SHARPNESS: the ratio `(1−ρ)/(N+ρ)` is ATTAINED.**  For the body consisting of the centre alone,
the same normal sees exactly `γ√σ = ((1−ρ)/(N+ρ))·√σ'` one round later.  So §3 is not an estimate:
`4` is the exact factor by which the natural cut misses the leaf at `ρ = rmax`, and the miss is not
recoverable by any choice of the body consistent with the supporting cut. -/
theorem supporting_ratio_attained {N : ℕ} (hn : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.PosDef) {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ}
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    c ⬝ᵥ (stepCentre N a c p ρ - a)
      = ((1 - ρ) / ((N : ℝ) + ρ))
        * sqrtSigmaR c ((stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have hstep : stepCentre N a c p ρ - a = (gammaR N ρ / sqrtSigmaR c p) • p := by
    rw [stepCentre]; abel
  rw [hstep, dotProduct_smul, smul_eq_mul,
    sqrtSigmaR_inv_stepShape hn hA hc hAp hρ]
  have hsq : sqrtSigmaR c p * sqrtSigmaR c p = sigmaR c p := sqrtSigmaR_mul_self hA hAp hc
  have hsne : sqrtSigmaR c p ≠ 0 := ne_of_gt (sqrtSigmaR_pos hA hAp hc)
  rw [show c ⬝ᵥ p = sqrtSigmaR c p * sqrtSigmaR c p from by rw [hsq]; rfl, gammaR]
  field_simp

#print axioms QMCLeafB.Eq38M2.supporting_ratio_attained



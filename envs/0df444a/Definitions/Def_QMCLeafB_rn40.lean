-- Prove2me | Definitions.Def_QMCLeafB_rn40
-- name    : QMCLeafB_rn40
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T06:49:08.717764+00:00
-- url     : https://prove2.me/theorems/3df81569-c2e8-4d4b-8e9e-12b9c238a4e9
-- title:
--   QMCLeafB rn40
-- statement:
--   # `Check_rn40_m4` — phase 40, member m4, direction d4 (`rational-normals`)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_price37
import Definitions.Def_QMCLeafB_thinrec34
import Definitions.Def_QMCLeafB_rf38
import Definitions.Def_QMCLeafB_eq38
/-
# `Check_rn40_m4` — phase 40, member m4, direction d4 (`rational-normals`)

**Task.**  `SepStream` (`Rf38M1.SepStream`, the leaf's last object) asks for a stream

    c : (G) → ℚ → ℕ → Fin (G.n * G.n) → ℚ,     hc : ∀ G t k, c G t k ≠ 0,

with, at every round `k < K·m`, `c k ⬝ Cat k ≤ c k ⬝ z` for every `z` in the relaxation.  Two of
its slots are *presentational*: the normal must be RATIONAL (`c` lands in `ℚ`, because the engine's
`CutData.c` is `ℚ`-valued and `NormalCut` is `runCut`), and it must be NONZERO (`hc`).  This file
decides both, gives the round-zero normal in closed form, and machine-checks the closing
inequality at the enlarged ceiling.

* **§0 `frob_unflat`** — the Frobenius pairing against the *unflattened* engine centre is the flat
  dot product of the row-major flattenings.  So matrix-form separation transports to the
  `Fin (n*n)` shape that `cutCR`/`Cat` speak, with the rational normal `flatRat N`.
* **§1–§2 rationality is FREE (the density lemma).**  `exists_rat_neg_qform`: if the relaxed
  quadratic form `w ↦ qfR X w + c·∑ wᵢ²` is negative at a REAL `v`, it is negative at a RATIONAL
  `w`.  Proof is pure topology — `q` continuous, `{q < 0}` a neighbourhood of `v`, `ℚⁿ` dense via
  `exists_rat_btwn` + `dist_pi_lt_iff`.  No estimate, no conditioning.
* **§3 the rational normal at a NON-MEMBER, explicitly.**  `exists_rat_support`: for a rational
  constraint matrix `Aq` and ANY `X₀ ∉ relaxBodyLE (castMat Aq) u δ`, there is a nonzero RATIONAL
  matrix normal `N` with `frob N X₀ ≤ frob N X` at every body point — three cases mirroring
  `Price37M4.support_of_not_relaxBodyLE`, but keeping the normal rational: violated relaxed PSD ⟹
  the rank-one `w wᵀ` at a rational `w` (§2 supplies `w`); violated diagonal band ⟹ `± eᵢᵢ`;
  violated objective ⟹ `−Aq`.  `exists_rat_normal_of_not_mem` is the `hc`-shape corollary.
* **§4 the bridge into `SepStream`.**  `sepStream_of_support`: `SepStream` follows from per-round
  MATRIX-form support at the round's own accumulated centre, with `c k = flatRat N k`.
  `sepStream_of_emptyBody`: at an empty relaxation any nonzero rational stream is a `SepStream`.
* **§5 the round-zero normal, in closed form.**  `Cat 0 = 0` for every cut stream, and the
  relaxation's diagonal clause puts `X₀₀ ≥ 0` on the whole body as soon as `δ ≤ 4`, so
  `single_zero_supports`: the single-entry rational normal `e₀₀` supports the body at the origin,
  `frob e₀₀ 0 = 0 ≤ frob e₀₀ X`.  Rational, nonzero, closed form — no separation theorem, no
  density.  `zero_not_mem_relaxBodyLE`/`exists_rat_support_at_zero` are the packaged forms.  Since
  `Cat 0 = 0` does not depend on the stream, round zero is the one round whose normal is available
  BEFORE the trajectory is known.
* **§6 the factor, and the reuse step at `rmax = 1/N`.**  `ratio_le_inv`: `(1−ρ)/(N+ρ) ≤ 1/N` for
  EVERY `ρ ≥ 0` (not merely `ρ ≤ 1/N`), with equality at `ρ = 0` (`ratio_at_zero`) — the "exactly"
  of the closing move.  `reuse_step_at_inv`: composing `Eq38M2.supporting_normal_ratio` with that
  factor, a supporting cut in the normal `c` at any legal depth leaves the SAME normal inside the
  leaf's allowance `(1/N)·√σ'` one round later.  Since `rmaxOf N = 1/(4N)`, the enlargement
  `rmaxOf N → 1/N` is exactly a factor-4 move, and at the OLD ceiling the same step is false by
  exactly `4N(1−ρ)/(N+ρ) → 4` (`Eq38M2.reuse_short_of_leaf`).
* **§6b THE ENLARGED CEILING IS INADMISSIBLE — the closing move of the phase-40 charter is
  REFUTED, and this file records it.**  `rmaxOf_lt_inv`: `rmaxOf N = 1/(4N) < 1/N`, so `1/N` is
  outside `rmaxOf`'s range.  `ratio_gt_self_of_le_half`: for `N ≥ 2` and EVERY `0 ≤ ρ ≤ 1/(2N)`,
  `ρ < (1−ρ)/(N+ρ)` — so NO ceiling up to `1/(2N)` can make the reuse cut satisfy the leaf, not
  merely `1/(4N)`.  And a larger ceiling makes `hhalve` HARDER, not easier: `rho0R` is ANTITONE in
  the depth (independently machine-checked by `Check_pn40_m5.rho0R_inv_lt_one` /
  `not_hhalve_of_inv_le` / `params_rmax_lt_inv` and by `Check_fa40_m8.rho0R_antitone` /
  `no_runParams_rmax_inv_dim`), so `rmax = 1/n²` admits NO `m` at all and the family is empty.
  Consequence, recorded as a dead end: `reuse_step_at_inv` is the correct scalar half but its
  hypothesis is unreachable; **the surviving lane is the ceiling-free one** — `SepStream` with
  `del ≡ 0`, where only `P.hrmax` is used and no `ρ`/`σ` estimate enters (`Rf38M1`).  Because at
  `ρ = 0` the attained ratio is EXACTLY `1/N > 0`, a constant normal can never serve that lane
  either: `SepStream` needs a genuinely fresh separating direction at each round (hull escape),
  and that obligation is untouched here.
* **§7 the reading, and one caution.**  `cut_not_nonmember`: `hc : c ≠ 0` alone proves nothing — a
  body point can be cut by a nonzero rational normal, so `SepStream` can never be discharged from
  non-vanishing alone; the normals are useful only through their separation property.

Discipline: `set_option autoImplicit false`; no `sorry`, `admit`, `axiom`, `native_decide`,
`unsafe`; `#print axioms` after every load-bearing declaration, each exactly
`[propext, Classical.choice, Quot.sound]` (23 declarations, all checked).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

noncomputable section
open scoped BigOperators
open Matrix

namespace QMCLeafB.Rn40M4

open QuantumMaxCutEnergy
open QMCLeafB.BallFloor (frob qfR relaxBodyLE)
open QMCLeafB.SepOracle (castMat castMat_apply castMat_vecMulVec)
open QMCLeafB.Price37M4 (frob_single frob_neg_left vecMulVec_ne_zero qfR_eq_frob_vecMulVec)
open QMCLeafB.Eq38M2 (supporting_normal_ratio)
open QMCLeafB.EngineIterates (stepShape_posDef sqrtSigmaR_pos mul_inv_of_posDef)

/-! ## 0.  Self-contained flat shape -/

/-- Row-major flattening of a rational matrix (the `ℚ` counterpart of
`AnswerProducer.flat`).  It is `RelaxOracle.flatQ` up to the definition, restated here so that
this file needs no relaxation-oracle bundle. -/
def flatRat {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Fin (n * n) → ℚ :=
  fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- The Frobenius pairing against an unflattened point is the flat dot product of the row-major
flattenings.  (The transported form of the published `RelaxOracle.frob_eq_flat_dot`, proved here
against `flatRat` so the file stays inside one import cone.) -/
theorem frob_unflat {n : ℕ} (N : Matrix (Fin n) (Fin n) ℚ) (z : Fin (n * n) → ℝ) :
    frob (castMat N) (QMCLeafB.Boundary.unflat z)
      = (fun k => ((flatRat N k : ℚ) : ℝ)) ⬝ᵥ z := by
  calc frob (castMat N) (QMCLeafB.Boundary.unflat z)
      = ∑ i, ∑ j, castMat N i j * QMCLeafB.Boundary.unflat z i j := rfl
    _ = ∑ p : Fin n × Fin n,
          castMat N p.1 p.2 * QMCLeafB.Boundary.unflat z p.1 p.2 :=
        (Fintype.sum_prod_type
          (f := fun p : Fin n × Fin n =>
            castMat N p.1 p.2 * QMCLeafB.Boundary.unflat z p.1 p.2)).symm
    _ = ∑ k : Fin (n * n), ((flatRat N k : ℚ) : ℝ) * z k := by
        rw [← Equiv.sum_comp finProdFinEquiv
          (fun k : Fin (n * n) => ((flatRat N k : ℚ) : ℝ) * z k)]
        exact Finset.sum_congr rfl (fun p _ => by
          simp [castMat, flatRat, QMCLeafB.Boundary.unflat])
    _ = (fun k => ((flatRat N k : ℚ) : ℝ)) ⬝ᵥ z := rfl

#print axioms QMCLeafB.Rn40M4.frob_unflat

/-! ## 1.  Continuity of the quadratic form -/

/-- The relaxed quadratic form is continuous in the direction. -/
theorem continuous_qfR (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (fun w : Fin n → ℝ => qfR X w) := by
  have hmul : Continuous (fun w : Fin n → ℝ => X *ᵥ w) := by
    have h := (Matrix.mulVecLin X).continuous_of_finiteDimensional
    have he : (⇑(Matrix.mulVecLin X)) = (fun w : Fin n → ℝ => X *ᵥ w) := by
      funext w; exact Matrix.mulVecLin_apply X w
    rwa [he] at h
  have hq : (fun w : Fin n → ℝ => qfR X w) = (fun w : Fin n → ℝ => w ⬝ᵥ (X *ᵥ w)) := rfl
  rw [hq]
  exact continuous_id.dotProduct hmul

#print axioms QMCLeafB.Rn40M4.continuous_qfR

/-- `qfR X · + c ‖·‖²` is continuous. -/
theorem continuous_qform (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    Continuous (fun w : Fin n → ℝ => qfR X w + c * ∑ i, w i ^ 2) := by
  refine (continuous_qfR n X).add ?_
  have h1 : Continuous (fun w : Fin n → ℝ => ∑ i, w i ^ 2) :=
    continuous_finsetSum Finset.univ (fun i _ => (continuous_apply i).pow 2)
  exact h1.const_mul c

#print axioms QMCLeafB.Rn40M4.continuous_qform

/-! ## 2.  Rationality is free: the density lemma -/

theorem exists_rat_neg_qform (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (v : Fin n → ℝ)
    (hv : qfR X v + c * ∑ i, v i ^ 2 < 0) :
    ∃ w : Fin n → ℚ,
      qfR X (fun i => ((w i : ℚ) : ℝ)) + c * ∑ i, ((w i : ℚ) : ℝ) ^ 2 < 0 := by
  classical
  set q : (Fin n → ℝ) → ℝ := fun z => qfR X z + c * ∑ i, z i ^ 2 with hqdef
  have hqv : q v < 0 := hv
  have hcont : Continuous q := continuous_qform n X c
  have hpos : (0 : ℝ) < -(q v) := by linarith
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.1 hcont.continuousAt (-(q v)) hpos
  have hpick : ∀ i : Fin n, ∃ r : ℚ, |((r : ℚ) : ℝ) - v i| < η := by
    intro i
    obtain ⟨r, h1, h2⟩ := exists_rat_btwn (show v i - η < v i + η by linarith)
    exact ⟨r, by rw [abs_lt]; constructor <;> linarith⟩
  choose w hw using hpick
  refine ⟨w, ?_⟩
  have hdist : dist (fun i => ((w i : ℚ) : ℝ)) v < η := by
    rw [dist_pi_lt_iff hηpos]
    intro i
    rw [Real.dist_eq]
    exact hw i
  have hlt := hη hdist
  rw [Real.dist_eq] at hlt
  have h2 := (abs_lt.1 hlt).2
  show q (fun i => ((w i : ℚ) : ℝ)) < 0
  linarith

#print axioms QMCLeafB.Rn40M4.exists_rat_neg_qform

/-! ## 3.  The rational normal at a non-member -/

theorem single_ne_zero_rat {n : ℕ} {i : Fin n} {a : ℚ} (ha : a ≠ 0) :
    Matrix.single i i a ≠ (0 : Matrix (Fin n) (Fin n) ℚ) := by
  intro h
  have h' : Matrix.single i i a i i = (0 : Matrix (Fin n) (Fin n) ℚ) i i := by rw [h]
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, Matrix.zero_apply] at h'
  exact ha h'

#print axioms QMCLeafB.Rn40M4.single_ne_zero_rat

theorem castMat_single {n : ℕ} (i : Fin n) (a : ℚ) :
    castMat (Matrix.single i i a) = Matrix.single i i ((a : ℚ) : ℝ) := by
  ext x y
  rw [castMat_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : x = i ∧ y = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬(i = x ∧ i = y) := fun hc => h ⟨hc.1.symm, hc.2.symm⟩
    simp [h, h']

#print axioms QMCLeafB.Rn40M4.castMat_single

theorem castMat_neg {n : ℕ} (Aq : Matrix (Fin n) (Fin n) ℚ) :
    castMat (-Aq) = -castMat Aq := by
  ext i j
  simp [castMat]

#print axioms QMCLeafB.Rn40M4.castMat_neg

theorem frob_castMat_neg {n : ℕ} (Aq : Matrix (Fin n) (Fin n) ℚ)
    (Y : Matrix (Fin n) (Fin n) ℝ) :
    frob (castMat (-Aq)) Y = -frob (castMat Aq) Y := by
  rw [castMat_neg, frob_neg_left]

#print axioms QMCLeafB.Rn40M4.frob_castMat_neg

/-- **THE RATIONAL SUPPORT LEMMA.** -/
theorem exists_rat_support {n : ℕ} (hn : 1 ≤ n)
    {Aq : Matrix (Fin n) (Fin n) ℚ} {u δ : ℝ} {X₀ : Matrix (Fin n) (Fin n) ℝ}
    (h : ¬ relaxBodyLE (castMat Aq) u δ X₀) :
    ∃ N : Matrix (Fin n) (Fin n) ℚ, N ≠ 0 ∧
      ∀ X, relaxBodyLE (castMat Aq) u δ X → frob (castMat N) X₀ ≤ frob (castMat N) X := by
  classical
  by_cases hbody : ∃ X, relaxBodyLE (castMat Aq) u δ X
  · obtain ⟨X₁, hX₁⟩ := hbody
    by_cases hP : ∀ x : Fin n → ℝ, -(δ / 2) * (∑ i, x i ^ 2) ≤ qfR X₀ x
    · by_cases hQ : ∀ i, |X₀ i i - 1| ≤ δ / 4
      · have hR : ¬ (frob (castMat Aq) X₀ ≤ u + δ / 2) := fun hR' => h ⟨hP, hQ, hR'⟩
        have hAq : Aq ≠ 0 := by
          intro h0
          have hz : ∀ Y : Matrix (Fin n) (Fin n) ℝ, frob (castMat Aq) Y = 0 := by
            intro Y; rw [h0]; simp [frob, castMat]
          rw [hz X₀] at hR
          have hle : (0 : ℝ) ≤ u + δ / 2 := by
            have h3 := hX₁.2.2
            rw [hz X₁] at h3
            simpa using h3
          exact hR hle
        refine ⟨-Aq, neg_ne_zero.mpr hAq, ?_⟩
        intro X hX
        obtain ⟨-, -, hX3⟩ := hX
        rw [frob_castMat_neg, frob_castMat_neg]
        linarith
      · push_neg at hQ
        obtain ⟨i, hi⟩ := hQ
        rw [lt_abs] at hi
        rcases hi with hgt | hlt
        · refine ⟨Matrix.single i i (-1), single_ne_zero_rat (by norm_num), ?_⟩
          intro X hX
          obtain ⟨-, hX2, -⟩ := hX
          rw [castMat_single, frob_single, frob_single]
          have h2 := abs_le.1 (hX2 i)
          have hδ0 : (0 : ℝ) ≤ δ := by linarith [h2.1, h2.2]
          push_cast
          nlinarith [h2.1]
        · refine ⟨Matrix.single i i 1, single_ne_zero_rat one_ne_zero, ?_⟩
          intro X hX
          obtain ⟨-, hX2, -⟩ := hX
          rw [castMat_single, frob_single, frob_single]
          have h2 := abs_le.1 (hX2 i)
          have hδ0 : (0 : ℝ) ≤ δ := by linarith [h2.1, h2.2]
          push_cast
          nlinarith [h2.2]
    · push_neg at hP
      obtain ⟨v, hv⟩ := hP
      obtain ⟨w, hw⟩ := exists_rat_neg_qform n X₀ (δ / 2) v (by linarith)
      have hwne : w ≠ 0 := by
        intro h0
        rw [h0] at hw
        simp [qfR] at hw
      have hw0 : (fun i => ((w i : ℚ) : ℝ)) ≠ 0 := by
        intro hz
        apply hwne
        funext i
        have hi : ((w i : ℚ) : ℝ) = 0 := congrFun hz i
        exact_mod_cast hi
      refine ⟨Matrix.vecMulVec w w, ?_, ?_⟩
      · intro h0
        have hcast0 : castMat (Matrix.vecMulVec w w) = (0 : Matrix (Fin n) (Fin n) ℝ) := by
          rw [h0]; simp [castMat]
        rw [castMat_vecMulVec] at hcast0
        exact vecMulVec_ne_zero hw0 hcast0
      · intro X hX
        obtain ⟨hX1, -, -⟩ := hX
        rw [castMat_vecMulVec, qfR_eq_frob_vecMulVec, qfR_eq_frob_vecMulVec]
        have h1 := hX1 (fun i => ((w i : ℚ) : ℝ))
        linarith
  · push_neg at hbody
    exact ⟨Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ 1, single_ne_zero_rat one_ne_zero,
      fun X hX => absurd hX (hbody X)⟩

#print axioms QMCLeafB.Rn40M4.exists_rat_support

/-- **The `hc` slot, discharged in shape.** -/
theorem exists_rat_normal_of_not_mem {n : ℕ} (hn : 1 ≤ n)
    {Aq : Matrix (Fin n) (Fin n) ℚ} {u δ : ℝ} {X₀ : Matrix (Fin n) (Fin n) ℝ}
    (h : ¬ relaxBodyLE (castMat Aq) u δ X₀) :
    ∃ N : Matrix (Fin n) (Fin n) ℚ, N ≠ 0 ∧
      ∀ X, relaxBodyLE (castMat Aq) u δ X → frob (castMat N) X₀ ≤ frob (castMat N) X :=
  exists_rat_support hn h

#print axioms QMCLeafB.Rn40M4.exists_rat_normal_of_not_mem

/-! ## 4.  The bridge into `SepStream` -/

theorem sepStream_of_support
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hsupp : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (k : ℕ),
      k < (P G).K * (P G).m →
      ∃ N : Matrix (Fin G.n) (Fin G.n) ℚ,
        c G t k = flatRat N ∧
        (∀ X : Matrix (Fin G.n) (Fin G.n) ℝ,
          relaxBodyLE (QMCLeafB.wMatrix G)
            ((t : ℝ) - (((QMCLeafB.EngineRuntime.Rq G / 40000 : ℚ)) : ℝ))
            (((P G).dq : ℚ) : ℝ) X →
          frob (castMat N)
              (QMCLeafB.Boundary.unflat
                (QMCLeafB.EngineIterates.Cat (G.n * G.n) (0 : Fin (G.n * G.n) → ℝ)
                  (QMCLeafB.ThinRec34M4.NormalCut G (P G) hn (c G t) (hc G t)) k))
            ≤ frob (castMat N) X)) :
    QMCLeafB.Rf38M1.SepStream P c hc := by
  intro G t hn k hk z hz
  obtain ⟨N, hcN, hsuppN⟩ := hsupp G t hn k hk
  obtain ⟨hzbody, -⟩ := hz
  have h := hsuppN (QMCLeafB.Boundary.unflat z) hzbody
  rw [frob_unflat, frob_unflat] at h
  rw [hcN]
  exact h

#print axioms QMCLeafB.Rn40M4.sepStream_of_support

/-- **The empty stratum is free, both slots.** -/
theorem sepStream_of_emptyBody
    (P : (G : QuantumMaxCutEnergy.Input) → QMCLeafB.FinalStroke.RunParams G)
    (c : (G : QuantumMaxCutEnergy.Input) → ℚ → ℕ → Fin (G.n * G.n) → ℚ)
    (hc : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ) (k : ℕ), c G t k ≠ 0)
    (hempty : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n →
      ¬ ∃ z, z ∈ QMCLeafB.ThinRec34M4.relaxBallP G t (P G)) :
    QMCLeafB.Rf38M1.SepStream P c hc := by
  intro G t hn k hk z hz
  exact absurd ⟨z, hz⟩ (hempty G t hn)

#print axioms QMCLeafB.Rn40M4.sepStream_of_emptyBody

/-! ## 5.  The round-zero normal, explicitly `e00`

`Cat 0 = 0` for EVERY cut stream (`Cat` is a recursion from the fixed start `a0 = 0`), so round
zero is the one round whose centre does not depend on the stream.  It is also the one round whose
supporting normal is available in closed form: the relaxation's diagonal clause is
`|Xii - 1| <= delta/4`, so at `delta <= 4` every body point has `X00 >= 0 = frob e00 0`.  That
single fact is what starts the constant-normal reuse of §6. -/

theorem zero_not_mem_relaxBodyLE {n : ℕ} (hn : 1 ≤ n)
    {Aq : Matrix (Fin n) (Fin n) ℚ} {u δ : ℝ} (hδ : δ < 4) :
    ¬ relaxBodyLE (castMat Aq) u δ (0 : Matrix (Fin n) (Fin n) ℝ) := by
  intro h
  obtain ⟨-, h2, -⟩ := h
  have h3 := h2 ⟨0, hn⟩
  have h0 : ((0 : Matrix (Fin n) (Fin n) ℝ)) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := rfl
  rw [h0] at h3
  have := abs_le.1 h3
  linarith [this.1, this.2]

#print axioms QMCLeafB.Rn40M4.zero_not_mem_relaxBodyLE

/-- **THE EXPLICIT ROUND-ZERO NORMAL.** -/
theorem single_zero_supports {n : ℕ} (hn : 1 ≤ n)
    {Aq : Matrix (Fin n) (Fin n) ℚ} {u δ : ℝ} (hδ : δ ≤ 4) :
    ∀ X, relaxBodyLE (castMat Aq) u δ X →
      frob (castMat (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ (1 : ℚ)))
          (0 : Matrix (Fin n) (Fin n) ℝ)
        ≤ frob (castMat (Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ (1 : ℚ))) X := by
  intro X hX
  obtain ⟨-, h2, -⟩ := hX
  have h3 := abs_le.1 (h2 ⟨0, hn⟩)
  rw [castMat_single, frob_single, frob_single]
  have hz : ((0 : Matrix (Fin n) (Fin n) ℝ)) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := rfl
  rw [hz]
  push_cast
  nlinarith [h3.1, h3.2]

#print axioms QMCLeafB.Rn40M4.single_zero_supports

theorem single_zero_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    Matrix.single ⟨0, hn⟩ ⟨0, hn⟩ (1 : ℚ) ≠ (0 : Matrix (Fin n) (Fin n) ℚ) :=
  single_ne_zero_rat one_ne_zero

#print axioms QMCLeafB.Rn40M4.single_zero_ne_zero

/-- **Round zero, packaged at an arbitrary rational constraint matrix.** -/
theorem exists_rat_support_at_zero {n : ℕ} (hn : 1 ≤ n)
    {Aq : Matrix (Fin n) (Fin n) ℚ} {u δ : ℝ} (hδ : δ < 4) :
    ∃ N : Matrix (Fin n) (Fin n) ℚ, N ≠ 0 ∧
      ∀ X, relaxBodyLE (castMat Aq) u δ X → (0 : ℝ) ≤ frob (castMat N) X := by
  obtain ⟨N, hN, hsupp⟩ := exists_rat_support hn (u := u) (δ := δ)
    (zero_not_mem_relaxBodyLE hn (Aq := Aq) hδ)
  refine ⟨N, hN, fun X hX => ?_⟩
  have h := hsupp X hX
  rwa [show frob (castMat N) (0 : Matrix (Fin n) (Fin n) ℝ) = 0 from by simp [frob]] at h

#print axioms QMCLeafB.Rn40M4.exists_rat_support_at_zero

/-! ## 6.  The factor, and the reuse step at the enlarged ceiling -/

theorem ratio_le_inv (N : ℕ) (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) := by
  have hN1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hden : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  rw [← sub_nonneg]
  have hkey : 1 / (N : ℝ) - (1 - ρ) / ((N : ℝ) + ρ)
      = (ρ * ((N : ℝ) + 1)) / ((N : ℝ) * ((N : ℝ) + ρ)) := by
    field_simp
    ring
  rw [hkey]
  apply div_nonneg
  · exact mul_nonneg hρ (by linarith)
  · exact mul_nonneg hN1.le hden.le

#print axioms QMCLeafB.Rn40M4.ratio_le_inv

theorem ratio_at_zero (N : ℕ) (hN : 0 < N) :
    (1 - (0 : ℝ)) / ((N : ℝ) + 0) = 1 / (N : ℝ) := by
  rw [sub_zero, add_zero]

#print axioms QMCLeafB.Rn40M4.ratio_at_zero

/-- **THE REUSE STEP AT `rmax = 1/N`.** -/
theorem reuse_step_at_inv (N : ℕ) (hN : 2 ≤ N) {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef)
    {c p : Fin N → ℝ} (hc : c ≠ 0) (hAp : A *ᵥ p = c) {a : Fin N → ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    {body : (Fin N → ℝ) → Prop} (hsupp : ∀ z, body z → c ⬝ᵥ (a - z) ≤ 0) {z : Fin N → ℝ}
    (hz : body z) :
    c ⬝ᵥ (QMCLeafB.EngineIterates.stepCentre N a c p ρ - z)
      ≤ (1 / (N : ℝ)) *
          QMCLeafB.EngineIterates.sqrtSigmaR c
            ((QMCLeafB.EngineIterates.stepShape N A c p ρ)⁻¹ *ᵥ c) := by
  have h1 := supporting_normal_ratio hN hA hc hAp hρ hsupp hz
  have h2 : (1 - ρ) / ((N : ℝ) + ρ) ≤ 1 / (N : ℝ) :=
    ratio_le_inv N (le_trans (by norm_num) hN) hρ
  have hA' : (QMCLeafB.EngineIterates.stepShape N A c p ρ).PosDef :=
    stepShape_posDef hN hA hc hAp hρ
  have hinv : (QMCLeafB.EngineIterates.stepShape N A c p ρ) *ᵥ
      ((QMCLeafB.EngineIterates.stepShape N A c p ρ)⁻¹ *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, mul_inv_of_posDef hA', Matrix.one_mulVec]
  have h3 : 0 < QMCLeafB.EngineIterates.sqrtSigmaR c
      ((QMCLeafB.EngineIterates.stepShape N A c p ρ)⁻¹ *ᵥ c) := sqrtSigmaR_pos hA' hinv hc
  calc c ⬝ᵥ (QMCLeafB.EngineIterates.stepCentre N a c p ρ - z)
      ≤ ((1 - ρ) / ((N : ℝ) + ρ)) *
          QMCLeafB.EngineIterates.sqrtSigmaR c
            ((QMCLeafB.EngineIterates.stepShape N A c p ρ)⁻¹ *ᵥ c) := h1
    _ ≤ (1 / (N : ℝ)) *
          QMCLeafB.EngineIterates.sqrtSigmaR c
            ((QMCLeafB.EngineIterates.stepShape N A c p ρ)⁻¹ *ᵥ c) :=
        mul_le_mul_of_nonneg_right h2 h3.le

#print axioms QMCLeafB.Rn40M4.reuse_step_at_inv

/-! ## 6b.  The enlarged ceiling is INADMISSIBLE: the charter's closing move is refuted

`rmaxOf N = 1/(4N)`.  §6's arithmetic is correct, but its hypothesis `rmax = 1/N` lies outside
`rmaxOf`'s range, and `ratio_gt_self_of_le_half` below shows that no smaller ceiling helps either:
for every `0 <= rho <= 1/(2N)` the attained ratio `(1-rho)/(N+rho)` EXCEEDS `rho` itself.  Together
with the independently machine-checked antitonicity of `rho0R` in the depth
(`Check_pn40_m5.rho0R_inv_lt_one`/`not_hhalve_of_inv_le`/`params_rmax_lt_inv`,
`Check_fa40_m8.rho0R_antitone`/`no_runParams_rmax_inv_dim`) the reuse lane is closed and the
phase-40 charter's monotonicity claim ("a larger rmax gives a faster contraction") is BACKWARDS.
Recorded here as a dead end with receipts. -/

/-- `rmaxOf N = 1/(4N) < 1/N`: the enlarged ceiling is outside the campaign's own family. -/
theorem rmaxOf_lt_inv (N : ℕ) (hN : 1 ≤ N) :
    QMCLeafB.RundataHalving.rmaxOf N < ((N : ℚ))⁻¹ := by
  rw [QMCLeafB.RundataHalving.rmaxOf, ← sub_pos]
  have hkey : ((N : ℚ))⁻¹ - 1 / (4 * (N : ℚ)) = 3 / (4 * (N : ℚ)) := by
    field_simp
    ring
  rw [hkey]
  have hN0 : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
  positivity

#print axioms QMCLeafB.Rn40M4.rmaxOf_lt_inv

/-- **NO CEILING UP TO `1/(2N)` WORKS.**  At every depth `0 <= rho <= 1/(2N)` the supporting cut's
attained ranking `(1-rho)/(N+rho)` is STRICTLY BIGGER than `rho` itself — so a reuse cut can never
meet the leaf's allowance at any of those ceilings.  (At `rho = 0` the excess is the whole `1/N`;
it falls to the factor `~2` at `rho = 1/(2N)`, which is the largest ceiling the `rho0R` wall
could conceivably allow.) -/
theorem ratio_gt_self_of_le_half (N : ℕ) (hN : 2 ≤ N) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρh : ρ ≤ 1 / (2 * (N : ℝ))) :
    ρ < (1 - ρ) / ((N : ℝ) + ρ) := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hpos : (0 : ℝ) < (N : ℝ) + ρ := by linarith
  have hsq : ρ ^ 2 ≤ 1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ))) := by
    have h1 : ρ * ρ ≤ (1 / (2 * (N : ℝ))) * ρ := mul_le_mul_of_nonneg_right hρh hρ0
    have h2 : (1 / (2 * (N : ℝ))) * ρ ≤ (1 / (2 * (N : ℝ))) * (1 / (2 * (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hρh (by positivity)
    linarith [h1, h2, sq_nonneg ρ]
  have hcross : ρ * ((N : ℝ) + 1) ≤ (1 / (2 * (N : ℝ))) * ((N : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hρh (by linarith)
  have hkey : 1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ)))
      + (1 / (2 * (N : ℝ))) * ((N : ℝ) + 1) < 1 := by
    have h3 : 1 / (2 * (N : ℝ)) * ((N : ℝ) + 1) = 1 / 2 + 1 / (2 * (N : ℝ)) := by
      field_simp <;> ring
    have h4 : 1 / (2 * (N : ℝ)) * (1 / (2 * (N : ℝ))) = 1 / (4 * (N : ℝ) ^ 2) := by
      field_simp <;> ring
    rw [h3, h4]
    have h5 : 1 / (4 * (N : ℝ) ^ 2) ≤ 1 / 16 := by
      apply one_div_le_one_div_of_le (by norm_num)
      nlinarith
    have h6 : 1 / (2 * (N : ℝ)) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num)
      linarith
    linarith
  rw [← sub_pos]
  have hdiff : (1 - ρ) / ((N : ℝ) + ρ) - ρ
      = (1 - (ρ ^ 2 + ρ * ((N : ℝ) + 1))) / ((N : ℝ) + ρ) := by
    field_simp <;> ring
  rw [hdiff]
  apply div_pos _ hpos
  nlinarith [hsq, hcross, hkey]

#print axioms QMCLeafB.Rn40M4.ratio_gt_self_of_le_half

/-- **The reuse lane is dead at the campaign's own ceiling**, restated at `rmaxOf`. -/
theorem reuse_dead_at_rmaxOf (N : ℕ) (hN : 2 ≤ N) {s : ℝ} (hs : 0 < s) :
    (QMCLeafB.RundataHalving.rmaxOf N : ℝ) * s < (1 / (N : ℝ)) * s := by
  have h1 : ((QMCLeafB.RundataHalving.rmaxOf N : ℚ) : ℝ) < ((N : ℚ) : ℝ)⁻¹ := by
    exact_mod_cast rmaxOf_lt_inv N (le_trans (by norm_num) hN)
  have h2 : ((N : ℚ) : ℝ)⁻¹ = 1 / (N : ℝ) := by
    rw [one_div]
    push_cast
    rfl
  rw [h2] at h1
  exact mul_lt_mul_of_pos_right h1 hs

#print axioms QMCLeafB.Rn40M4.reuse_dead_at_rmaxOf

/-! ## 7.  The reading, and one caution -/

/-- **A cut does NOT certify non-membership.**  `hc : c ≠ 0` alone proves nothing: a body point
can be cut by a nonzero rational normal.  So the `hc` slot is only ever usable together with the
*separation* property, and `SepStream` cannot be discharged from non-vanishing alone. -/
theorem cut_not_nonmember :
    ∃ (c : Fin 1 → ℚ) (X : Matrix (Fin 1) (Fin 1) ℝ), c ≠ 0 ∧
      relaxBodyLE (castMat (0 : Matrix (Fin 1) (Fin 1) ℚ)) 1 0 X ∧
      (0 : ℝ) < frob (castMat (Matrix.vecMulVec c c)) X := by
  refine ⟨1, 1, one_ne_zero, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x
    have hx : qfR (1 : Matrix (Fin 1) (Fin 1) ℝ) x = x 0 * x 0 := by
      simp only [qfR, Matrix.one_mulVec, dotProduct, Fin.sum_univ_one]
    have hsum : (∑ i : Fin 1, x i ^ 2) = x 0 ^ 2 := by simp
    nlinarith [sq_nonneg (x 0)]
  · intro i
    simp
  · simp [frob, castMat]
  · have hf : frob (castMat (Matrix.vecMulVec (1 : Fin 1 → ℚ) 1))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
      simp [frob, castMat, Matrix.one_apply]
    rw [hf]
    norm_num

#print axioms QMCLeafB.Rn40M4.cut_not_nonmember

end QMCLeafB.Rn40M4



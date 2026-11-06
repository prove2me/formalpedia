-- Prove2me | Definitions.Def_QMCLeafB_lvl32
-- name    : QMCLeafB_lvl32
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:05:08.525561+00:00
-- url     : https://prove2.me/theorems/51c35e10-e82e-418e-9a9b-4bfa596817af
-- title:
--   QMCLeafB lvl32
-- statement:
--   # `Check_lvl32_m8` — phase 32, member m8, direction `level-gate` (d7)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_mech31
import Definitions.Def_QMCLeafB_hdband
/-
# `Check_lvl32_m8` — phase 32, member m8, direction `level-gate` (d7)

The phase-32 residual of the whole campaign is the pair

    hok        : bit true  → ∃ symmetric RATIONAL `RelaxMem` at `(t − eps, dqShallow)`
    hcomplete  : ¬ EmptyBody (REAL emptiness) → bit true

(`QMCLeafB.MechM6.leaf_of_hok_and_complete`).  This file audits the **level gate** between them: the
`ℚ`/`ℝ` boundary.  `hok`'s witness is a *rational* member; `hcomplete`'s hypothesis is *real*
non-emptiness (`AsmM8.EmptyBody` = `∀ X : Matrix _ _ ℝ, ¬ relaxBodyLE …`).  The library's banked
`hemptyR_campaign` gives only `real-empty → no rational member`; the converse (density of rational
members in the real body, which phase 23 named "the `hemptyR` density bridge") is NOT banked and is
NOT implied by it.

Consequences, all machine-checked below.

* §1 **The gate is an obligation of the residual pair.**  `hok` + `hcomplete` imply
  `Density G t` (`density_of_hok_complete`), i.e. real non-emptiness forces a symmetric rational
  member.  Equivalently (`residual_pair_refuted`): at an interior point with a real-nonempty body
  and NO symmetric rational member, the residual pair is jointly INCONSISTENT — no certificate work
  can close the leaf there, and the residual has to be restated.  This is a sixth-vacuity-shaped
  hazard and it is invisible in the current bookkeeping.

* §2/§3 **The gate is CLOSED by an explicit rational witness.**  For every level above
  `-Rq·(1 + 3δ/4)/(n−1)` the body contains the symmetric rational member
  `fam d b = d·1 + b·J` with `d = 1 + δ/4 − b`, `b = -(1 + 3δ/4)/(n−1)` — diagonal exactly `1 + δ/4`,
  off-diagonal constant `b`, objective exactly `b·Rq ≤ level` (`exists_mem_of_level_ge`).

* §4 **At `n = 2` the gate is closed unconditionally.**  `body_empty_lowband` (banked) says a
  nonempty real body forces `t ≥ tEmpty G`, i.e. level `≥ -Rq·(1 + 3δ/4)`; at `n = 2` the `n − 1`
  in §3 is `1`, so the two thresholds coincide: `density_n2`.  The campaign's exemplars `G₀`, `G₁`
  and the phase-25 "dreg" band all sit at `n = 2`, so the gate is closed on the whole critical
  stratum.

* §5 **The surviving gap is `n ≥ 3` in the eigenvector band** `level ∈ [-Rq(1+3δ/4), -Rq(1+3δ/4)/(n−1))`.
  There the uniform family misses the body's minimum (which is the SDP/eigenvector value), and no
  density theorem is available.  If that band is inhabited by a rational-empty body, `hok ∧
  hcomplete` is refuted at that input, i.e. the residual must be restated at the RATIONAL body.

Discipline: no `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; `#print axioms` after every
declaration.
-/

open scoped BigOperators
open Matrix

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace Lvl32M8

open QuantumMaxCutEnergy

/-! ## 1.  The `ℚ`/`ℝ` gate: an obligation of the residual pair -/

/-- **The gate.**  At an interior point, real non-emptiness of the relaxed body forces a
*symmetric rational* `RelaxMem` member at the loop's own level and tolerance. -/
def Density (G : QuantumMaxCutEnergy.Input) (t : ℚ) : Prop :=
  ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)

/-- **`hok` + `hcomplete` imply the gate.**  `hcomplete` turns real non-emptiness into `bit = true`;
`hok` turns `bit = true` into a symmetric rational member.  Nothing else is used. -/
theorem density_of_hok_complete
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      QMCLeafB.MechM6.bit0 G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → QMCLeafB.MechM6.bit0 G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t → Density G t := by
  intro G t hn hint hne
  exact hok G t hn hint (hcomplete G t hn hint hne)

/-- **The gate, refutation form.**  A real-nonempty interior point with no symmetric rational member
makes the residual pair `hok ∧ hcomplete` jointly unsatisfiable: no amount of certificate or
trajectory work can close the phase-32 leaf at that input. -/
theorem residual_pair_refuted
    (G : QuantumMaxCutEnergy.Input) (t : ℚ) (hn : 2 ≤ G.n) (hint : AsmM8.Interior G t)
    (hne : ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G))
    (hno : ∀ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX →
      ¬ QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G)) :
    ¬ ((∀ (G' : QuantumMaxCutEnergy.Input) (t' : ℚ), 2 ≤ G'.n → AsmM8.Interior G' t' →
        QMCLeafB.MechM6.bit0 G' t' = true →
        ∃ cX : Matrix (Fin G'.n) (Fin G'.n) ℚ, cXᵀ = cX ∧
          QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G') cX
            (t' - QMCLeafB.RundataCert.eps G') (QMCLeafB.RundataParams.dqShallow G')) ∧
      (∀ (G' : QuantumMaxCutEnergy.Input) (t' : ℚ), 2 ≤ G'.n → AsmM8.Interior G' t' →
        ¬ AsmM8.EmptyBody G' t' (QMCLeafB.UnionShallow.paramsKbc2 G') →
        QMCLeafB.MechM6.bit0 G' t' = true)) := by
  rintro ⟨hok, hcomplete⟩
  obtain ⟨cX, hsym, hmem⟩ :=
    (density_of_hok_complete hok hcomplete G t hn hint) hne
  exact hno cX hsym hmem

/-- **The gate is PROGRAM-INDEPENDENT.**  The residual pair's shapes mention the bit only in
`hcomplete`'s conclusion and `hok`'s hypothesis, and the proof below uses neither: any program bit
`o` with those two implications at an interior point forces `Density` there.  So the phase-32
program repair (`stepF_vec`/the normal's code length) does **not** remove this obligation — it must
be re-established, or its statement restated, for the repaired program too. -/
theorem density_of_hok_complete_generic (o : QuantumMaxCutEnergy.Input → ℚ → Bool)
    (hok : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      o G t = true →
      ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
          (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G))
    (hcomplete : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → o G t = true) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t → Density G t := by
  intro G t hn hint hne
  exact hok G t hn hint (hcomplete G t hn hint hne)

/-! ## 2.  The explicit rational family `d·1 + b·J` -/

/-- The two-parameter rational family: diagonal `d + b`, off-diagonal `b`.  Both the diagonal-`1`
family (`d = 1 − b`) and the diagonal-at-the-box-top family (`d = 1 + δ/4 − b`) are instances. -/
def fam (n : ℕ) (d b : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  d • (1 : Matrix (Fin n) (Fin n) ℚ) + b • (Matrix.of fun _ _ => (1 : ℚ))

theorem fam_symm {n : ℕ} (d b : ℚ) : (fam n d b)ᵀ = fam n d b := by
  ext i j
  rw [Matrix.transpose_apply]
  simp only [fam, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h, Matrix.one_apply]

theorem fam_apply_self {n : ℕ} (d b : ℚ) (i : Fin n) : fam n d b i i = d + b := by
  simp [fam]

theorem qf_addQ {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (M + N) x
      = QMCLeafB.SepOracle.qf M x + QMCLeafB.SepOracle.qf N x := by
  rw [QMCLeafB.SepOracle.qf, QMCLeafB.SepOracle.qf, QMCLeafB.SepOracle.qf,
    Matrix.add_mulVec, dotProduct_add]

theorem qf_oneQ {n : ℕ} (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (1 : Matrix (Fin n) (Fin n) ℚ) x = ∑ i, x i ^ 2 := by
  rw [QMCLeafB.SepOracle.qf, Matrix.one_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem qf_JQ {n : ℕ} (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (Matrix.of fun _ _ => (1 : ℚ)) x = (∑ i, x i) ^ 2 := by
  have hmv : (Matrix.of fun _ _ => (1 : ℚ) : Matrix (Fin n) (Fin n) ℚ) *ᵥ x
      = fun _ => ∑ j, x j := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  calc QMCLeafB.SepOracle.qf (Matrix.of fun _ _ => (1 : ℚ)) x
      = ∑ i, x i * (∑ j, x j) := by rw [QMCLeafB.SepOracle.qf, hmv, dotProduct]
    _ = (∑ i, x i) * (∑ j, x j) := by rw [Finset.sum_mul]
    _ = (∑ i, x i) * (∑ i, x i) := rfl
    _ = (∑ i, x i) ^ 2 := by rw [sq]

/-- The quadratic form of the family: `d·∑xᵢ² + b·(∑xᵢ)²`. -/
theorem qf_fam {n : ℕ} (d b : ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (fam n d b) x
      = d * (∑ i, x i ^ 2) + b * (∑ i, x i) ^ 2 := by
  rw [fam, qf_addQ, QMCLeafB.SepOracle.qf_smulQ, QMCLeafB.SepOracle.qf_smulQ, qf_oneQ, qf_JQ]

theorem frob_oneQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (1 : Matrix (Fin n) (Fin n) ℚ) = ∑ i, A i i := by
  rw [QMCLeafB.SepOracle.frob]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq]; ring
  · intro j _ hj
    rw [Matrix.one_apply_ne' hj]; ring
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem frob_JQ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (Matrix.of fun _ _ => (1 : ℚ)) = ∑ i, ∑ j, A i j := by
  rw [QMCLeafB.SepOracle.frob]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp

theorem frob_smulQ {n : ℕ} (c : ℚ) (A X : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.SepOracle.frob A (c • X) = c * QMCLeafB.SepOracle.frob A X := by
  rw [QMCLeafB.SepOracle.frob, QMCLeafB.SepOracle.frob, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The objective of the family against a zero-diagonal matrix: `b·∑ᵢⱼ Aᵢⱼ`. -/
theorem frob_fam {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (d b : ℚ)
    (hdiag : ∀ i, A i i = 0) :
    QMCLeafB.SepOracle.frob A (fam n d b) = b * (∑ i, ∑ j, A i j) := by
  rw [fam, QMCLeafB.SepOracle.frob_add, frob_smulQ, frob_smulQ, frob_oneQ, frob_JQ]
  have h0 : (∑ i, A i i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => hdiag i
  rw [h0]
  ring

/-! ## 3.  The psd clause and the level theorem -/

theorem psd_clause_fam {n : ℕ} (d b δ : ℚ)
    (h : (0 ≤ b ∧ -(δ / 2) ≤ d) ∨ (b < 0 ∧ -(δ / 2) ≤ d + (n : ℚ) * b)) :
    ∀ x : Fin n → ℚ, -(δ / 2) * (∑ i, x i ^ 2) ≤ QMCLeafB.SepOracle.qf (fam n d b) x := by
  intro x
  have hT : (∑ i, x i) ^ 2 ≤ (n : ℚ) * ∑ i, x i ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := x)
  have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [qf_fam]
  rcases h with ⟨hb, hd⟩ | ⟨hb, hd⟩
  · have h1 : (0 : ℚ) ≤ b * (∑ i, x i) ^ 2 := mul_nonneg hb (sq_nonneg _)
    have h2 := mul_le_mul_of_nonneg_right hd hS
    nlinarith
  · have h1 : b * ((n : ℚ) * ∑ i, x i ^ 2) ≤ b * (∑ i, x i) ^ 2 :=
      mul_le_mul_of_nonpos_left hT (le_of_lt hb)
    have h2 := mul_le_mul_of_nonneg_right hd hS
    nlinarith

theorem wMatrixQ_diag_zero (G : QuantumMaxCutEnergy.Input) (i : Fin G.n) :
    QMCLeafB.Finalization.wMatrixQ G i i = 0 := by
  rw [QMCLeafB.Finalization.wMatrixQ_apply]
  simp

theorem sum_wMatrixQ_eq_Rq (G : QuantumMaxCutEnergy.Input) :
    ∑ i, ∑ j, QMCLeafB.Finalization.wMatrixQ G i j = QMCLeafB.EngineRuntime.Rq G := by
  simpa [QMCLeafB.Finalization.Vq, QMCLeafB.EngineRuntime.Rq]
    using QMCLeafB.Finalization.Vq_wMatrixQ G

/-- **The gate, closed above the uniform threshold.**  If the level `u + δ/2` is at least
`-Rq·(1 + 3δ/4)/(n−1)` then the body contains the explicit symmetric rational member
`fam (1 + δ/4 − b) b`, `b = -(1 + 3δ/4)/(n−1)`.  Nothing about the body's non-emptiness is used:
the witness is produced from the level alone. -/
theorem exists_mem_of_level_ge (G : QuantumMaxCutEnergy.Input) (u δ : ℚ) (hn : 2 ≤ G.n)
    (hδ : 0 < δ)
    (hlev : -(QMCLeafB.EngineRuntime.Rq G * (1 + 3 * δ / 4) / ((G.n : ℚ) - 1)) ≤ u + δ / 2) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX u δ := by
  have hnm1 : (0 : ℚ) < (G.n : ℚ) - 1 := by
    have h2 : (2 : ℚ) ≤ (G.n : ℚ) := by exact_mod_cast hn
    linarith
  have hne : ((G.n : ℚ) - 1) ≠ 0 := ne_of_gt hnm1
  set b : ℚ := -((1 + 3 * δ / 4) / ((G.n : ℚ) - 1)) with hbdef
  set d : ℚ := (1 + δ / 4) - b with hddef
  have hbneg : b < 0 := by
    rw [hbdef]
    have h1 : (0 : ℚ) < 1 + 3 * δ / 4 := by linarith
    have h2 : (0 : ℚ) < (1 + 3 * δ / 4) / ((G.n : ℚ) - 1) := div_pos h1 hnm1
    linarith
  have hdbsum : d + (G.n : ℚ) * b = -(δ / 2) := by
    rw [hddef, hbdef]
    field_simp
    ring
  have hdiagval : d + b = 1 + δ / 4 := by
    rw [hddef]; ring
  have hbRq : b * QMCLeafB.EngineRuntime.Rq G
      = -(QMCLeafB.EngineRuntime.Rq G * (1 + 3 * δ / 4) / ((G.n : ℚ) - 1)) := by
    rw [hbdef]; ring
  refine ⟨fam G.n d b, fam_symm d b, hδ, ?_, ?_, ?_⟩
  · exact psd_clause_fam d b δ (Or.inr ⟨hbneg, by rw [hdbsum]⟩)
  · intro i
    rw [fam_apply_self, hdiagval]
    rw [show (1 + δ / 4 - 1) = δ / 4 by ring, abs_of_nonneg (by linarith)]
  · rw [frob_fam _ d b (wMatrixQ_diag_zero G), sum_wMatrixQ_eq_Rq, hbRq]
    linarith [hlev]

/-! ## 4.  `n = 2`: the gate is closed unconditionally -/

/-- **The band floor at the campaign's own numbers.**  A nonempty real body forces the level
`t − eps + dqShallow/2` above `-Rq·(1 + 3·dqShallow/4)` (`body_empty_lowband`'s contrapositive). -/
theorem level_ge_of_nonempty (G : QuantumMaxCutEnergy.Input) {t : ℚ}
    (hne : ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    -(QMCLeafB.EngineRuntime.Rq G * (1 + 3 * QMCLeafB.RundataParams.dqShallow G / 4))
      ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataParams.dqShallow G / 2 := by
  have hRq : (0 : ℚ) ≤ QMCLeafB.EngineRuntime.Rq G := QMCLeafB.EngineRuntime.Rq_nonneg G
  have htge : QMCLeafB.HdM7Band.tEmpty G ≤ t := by
    refine not_lt.mp (fun ht => ?_)
    exact hne (QMCLeafB.HdM7Band.body_empty_lowband G hRq ht)
  have hdq : (QMCLeafB.UnionShallow.paramsKbc2 G).dq
      = QMCLeafB.RundataParams.dqShallow G := QMCLeafB.UnionShallow.paramsKbc2_dq G
  have heps : QMCLeafB.RundataCert.eps G = QMCLeafB.EngineRuntime.Rq G / 40000 := rfl
  unfold QMCLeafB.HdM7Band.tEmpty at htge
  rw [hdq] at htge
  rw [heps]
  linarith

/-- **`n = 2`: rational density holds unconditionally.**  At every 2-vertex input — in particular the
campaign's exemplars `G₀`, `G₁` and the whole phase-25 "dreg" band — a nonempty real relaxed body
contains an explicit symmetric rational member at the loop's own level and tolerance.  So the
`ℚ`/`ℝ` gate can never be the obstruction on the critical stratum. -/
theorem density_n2 (G : QuantumMaxCutEnergy.Input) (t : ℚ) (h2 : G.n = 2)
    (hne : ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G)) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX
        (t - QMCLeafB.RundataCert.eps G) (QMCLeafB.RundataParams.dqShallow G) := by
  have hn : 2 ≤ G.n := by omega
  have hδ : 0 < QMCLeafB.RundataParams.dqShallow G := QMCLeafB.RundataParams.dqShallow_pos G
  have hbase := level_ge_of_nonempty G hne
  refine exists_mem_of_level_ge G (t - QMCLeafB.RundataCert.eps G)
    (QMCLeafB.RundataParams.dqShallow G) hn hδ ?_
  rw [h2]
  norm_num
  linarith

/-! ## 5.  What survives: the `n ≥ 3` eigenvector band

`exists_mem_of_level_ge` and `level_ge_of_nonempty` meet exactly at `n = 2`; for `n ≥ 3` they leave
the band

    level ∈ [-Rq·(1 + 3δ/4),  -Rq·(1 + 3δ/4)/(n−1))

open.  There the body's minimum is the SDP value `(1 + 3δ/4)·λ_min(A)` (attained at a top/bottom
eigenvector, rational exactly when that eigenvalue is), and the uniform family is strictly above it:
e.g. a 5-vertex star with weights `(1,1,1,ε)` has `λ_max(A) = √(3+ε²) ≈ 1.732 > Rq/(n−1) = 3/2`,
so levels in `[-1.732·(1+3δ/4), -1.5·(1+3δ/4))` admit real body points but no uniform-family member.

`Density` at those inputs is exactly the named residual: `density_of_hok_complete` says the residual
pair must supply it, and `residual_pair_refuted` says that if it fails anywhere the pair is
unsatisfiable there. -/


/-! ## 6.  The sharp form of the surviving gap: the RATIONAL ELLITOPE

Every member of the two families above has the shape `X = c·P − (δ/2)·1` with `P` a *rational
unit-diagonal PSD* matrix (an elliptope point in `ℚ`): `P = 1` gives the family of §2, `P = uuᵀ`
with `u` a sign vector gives a cut point.  In that shape the three clauses collapse:

    qf X x   = c·qf P x − (δ/2)‖x‖²,      diag X = c + (−δ/2) = 1 + δ/4,
    frob A X = c·frob A P                (the weight matrix has zero diagonal),

with `c = 1 + 3δ/4`.  Hence **`Density` is implied by the rational elliptope meeting the level**:
this is exactly the Goemans–Williamson SDP value attained above the level at a rational elliptope
point, i.e. the residual of §5 stated in the relaxation's own coordinates. -/

/-- The elliptope member `(1 + 3δ/4)·P − (δ/2)·1` attached to a unit-diagonal PSD `P`. -/
def ellip (n : ℕ) (P : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  (1 + 3 * δ / 4) • P + (-(δ / 2)) • (1 : Matrix (Fin n) (Fin n) ℚ)

theorem ellip_symm {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (hP : Pᵀ = P) (δ : ℚ) :
    (ellip n P δ)ᵀ = ellip n P δ := by
  rw [ellip, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, hP,
    Matrix.transpose_one]

theorem ellip_diag {n : ℕ} {P : Matrix (Fin n) (Fin n) ℚ} (hP : ∀ i, P i i = 1) (δ : ℚ)
    (i : Fin n) : ellip n P δ i i = 1 + δ / 4 := by
  rw [ellip]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hP i, Matrix.one_apply_eq]
  ring

theorem qf_ellip {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) (δ : ℚ) (x : Fin n → ℚ) :
    QMCLeafB.SepOracle.qf (ellip n P δ) x
      = (1 + 3 * δ / 4) * QMCLeafB.SepOracle.qf P x - (δ / 2) * (∑ i, x i ^ 2) := by
  rw [ellip, qf_addQ, QMCLeafB.SepOracle.qf_smulQ, QMCLeafB.SepOracle.qf_smulQ, qf_oneQ]
  ring

theorem frob_ellip {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (P : Matrix (Fin n) (Fin n) ℚ)
    (δ : ℚ) (hdiag : ∀ i, A i i = 0) :
    QMCLeafB.SepOracle.frob A (ellip n P δ)
      = (1 + 3 * δ / 4) * QMCLeafB.SepOracle.frob A P := by
  rw [ellip, QMCLeafB.SepOracle.frob_add, frob_smulQ, frob_smulQ, frob_oneQ]
  have h0 : (∑ i, A i i) = 0 := Finset.sum_eq_zero fun i _ => hdiag i
  rw [h0]
  ring

/-- **A rational elliptope point above the level is a symmetric rational member.** -/
theorem exists_mem_of_elliptope (G : QuantumMaxCutEnergy.Input) (u δ : ℚ) (hδ : 0 < δ)
    (P : Matrix (Fin G.n) (Fin G.n) ℚ) (hPsym : Pᵀ = P)
    (hPpsd : ∀ x : Fin G.n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf P x)
    (hPdiag : ∀ i, P i i = 1)
    (hlev : (1 + 3 * δ / 4) * QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) P
      ≤ u + δ / 2) :
    ∃ cX : Matrix (Fin G.n) (Fin G.n) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G) cX u δ := by
  have hc : (0 : ℚ) ≤ 1 + 3 * δ / 4 := by linarith
  refine ⟨ellip G.n P δ, ellip_symm hPsym δ, hδ, ?_, ?_, ?_⟩
  · intro x
    rw [qf_ellip]
    have hp : 0 ≤ QMCLeafB.SepOracle.qf P x := hPpsd x
    have hm := mul_nonneg hc hp
    linarith
  · intro i
    rw [ellip_diag hPdiag]
    rw [show (1 + δ / 4 - 1) = δ / 4 by ring, abs_of_nonneg (by linarith)]
  · rw [frob_ellip _ P δ (wMatrixQ_diag_zero G)]
    exact hlev

/-- **The gate follows from the rational elliptope.**  If at every real-nonempty interior point the
level is met by a rational unit-diagonal PSD point (the campaign relaxation's own object), then
`Density` holds there — and by §1 the residual pair `hok ∧ hcomplete` is instantiable. -/
theorem density_of_elliptope
    (Hell : ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
      ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) →
      ∃ P : Matrix (Fin G.n) (Fin G.n) ℚ, Pᵀ = P ∧
        (∀ x : Fin G.n → ℚ, 0 ≤ QMCLeafB.SepOracle.qf P x) ∧
        (∀ i, P i i = 1) ∧
        (1 + 3 * QMCLeafB.RundataParams.dqShallow G / 4)
            * QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G) P
          ≤ (t - QMCLeafB.RundataCert.eps G) + QMCLeafB.RundataParams.dqShallow G / 2) :
    ∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t → Density G t := by
  intro G t hn hint hne
  obtain ⟨P, hsym, hpsd, hdiag, hlev⟩ := Hell G t hn hint hne
  exact exists_mem_of_elliptope G (t - QMCLeafB.RundataCert.eps G)
    (QMCLeafB.RundataParams.dqShallow G) (QMCLeafB.RundataParams.dqShallow_pos G)
    P hsym hpsd hdiag hlev


/-! ## 7.  The refutation point `(G₀, −1/2)`: the gate is CLOSED there

d5/m4's phase-32 refutation reports the campaign bit is `false` at `(G₀, −1/2)` (the `n²`-code
direction bug: the orbit is eventually constant with `dvR ≠ 0`, so no round ever reports `ok`).
This section removes the *other* possible explanation of such a refutation — the `ℚ`/`ℝ` gate.  At
that point **both** readings of the body are inhabited: the real body by the banked
`Z₀ = !![1,-1;-1,1]` (`IsUnitDiagPSD`, `(wMatrix * Z₀).trace = -1`) and the *rational* body by the
same matrix over `ℚ` — a symmetric `RelaxMem` member at the loop's own `(t − eps, dqShallow)`.

Consequences (for d5/d2 and for the coordinator):

* the cheap repair "restate `hcomplete` at RATIONAL non-emptiness" does **not** help at
  `(G₀, −1/2)`; the failure there is the *program's* `ok` test, not the `ℚ`/`ℝ` boundary;
* by §1, if the bit is `false` there then `hcomplete` fails at an interior real-nonempty point, hence
  the residual pair is unsatisfiable there and the repair must be in the programme (`stepF_vec` /
  the normal's code length), not in the hypothesis. -/

/-- The campaign exemplar: two vertices, the single edge of weight `1/2`, `Rq = 1`. -/
abbrev G₀ : QuantumMaxCutEnergy.Input := QMCLeafB.ResidRefute.G₀

/-- The campaign's own run parameters at `G₀`. -/
abbrev P₀ : QMCLeafB.FinalStroke.RunParams G₀ := QMCLeafB.UnionShallow.paramsKbc2 G₀

/-- The exemplar threshold `−1/2`. -/
def t₀ : ℚ := -(1 / 2)

/-- The rational witness `!![1,-1;-1,1]`: symmetric, unit diagonal, `qf = (x₀ − x₁)²`. -/
def Q₀ : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; -1, 1]

theorem Q₀_symm : Q₀ᵀ = Q₀ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Q₀]

theorem qf_Q₀ (x : Fin 2 → ℚ) : QMCLeafB.SepOracle.qf Q₀ x = (x 0 - x 1) ^ 2 := by
  rw [QMCLeafB.SepOracle.qf_eq_sum, Fin.sum_univ_two]
  simp [Q₀, Fin.sum_univ_two]
  ring

theorem Q₀_diag (i : Fin 2) : Q₀ i i = 1 := by
  fin_cases i <;> simp [Q₀]

theorem frob_wMatrixQ_Q₀ :
    QMCLeafB.SepOracle.frob (QMCLeafB.Finalization.wMatrixQ G₀) Q₀ = -1 := by
  simp [QMCLeafB.SepOracle.frob, Fin.sum_univ_two, Q₀,
    QMCLeafB.Finalization.wMatrixQ_apply]
  norm_num

theorem frob_wMatrix_Z₀ :
    QMCLeafB.BallFloor.frob (QMCLeafB.wMatrix G₀) QMCLeafB.ResidRefute.Z₀ = -1 := by
  simp [QMCLeafB.BallFloor.frob, Fin.sum_univ_two, QMCLeafB.ResidRefute.Z₀,
    QMCLeafB.wMatrix_apply]
  norm_num

theorem interior_t₀ : AsmM8.Interior G₀ t₀ := by
  refine ⟨?_, ?_⟩
  · show (-(QMCLeafB.EngineRuntime.Rq G₀) : ℚ) ≤ -(1 / 2)
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num
  · show ((-(1 / 2) : ℚ) : ℝ) < -((((QMCLeafB.EngineRuntime.Rq G₀) / 40000 : ℚ)) : ℝ)
    rw [QMCLeafB.ResidRefute.Rq_G₀]; norm_num

/-- **The real body is nonempty at the refutation point.** -/
theorem not_emptyBody_t₀ : ¬ AsmM8.EmptyBody G₀ t₀ P₀ := by
  intro h
  have hbody := h QMCLeafB.ResidRefute.Z₀
  apply hbody
  have hZ := QMCLeafB.ResidRefute.Z₀_isUnitDiagPSD
  have hδ : (0 : ℝ) ≤ ((P₀.dq : ℚ) : ℝ) := by
    have hh := P₀.hdq
    exact_mod_cast le_of_lt hh
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h0 : (0 : ℝ) ≤ QMCLeafB.BallFloor.qfR QMCLeafB.ResidRefute.Z₀ x := by
      have hz := hZ.1.dotProduct_mulVec_nonneg x
      simpa [QMCLeafB.BallFloor.qfR] using hz
    have hS : (0 : ℝ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  · intro i
    have h1 : QMCLeafB.ResidRefute.Z₀ i i = 1 := hZ.2 i
    rw [h1]
    simp only [sub_self, abs_zero]
    linarith
  · rw [frob_wMatrix_Z₀]
    show (-(1 : ℝ)) ≤ (((-(1 / 2) : ℚ)) : ℝ) - ((((QMCLeafB.EngineRuntime.Rq G₀) / 40000 : ℚ)) : ℝ)
      + ((P₀.dq : ℚ) : ℝ) / 2
    rw [QMCLeafB.ResidRefute.Rq_G₀]
    push_cast
    nlinarith

/-- **The rational body is nonempty at the refutation point too.**  So the gate of §1 is *closed*
exactly where d5's refutation lives: no restatement of `hcomplete` at rational non-emptiness can
repair that point. -/
theorem rational_member_t₀ :
    ∃ cX : Matrix (Fin 2) (Fin 2) ℚ, cXᵀ = cX ∧
      QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) cX
        (t₀ - QMCLeafB.RundataCert.eps G₀) (QMCLeafB.RundataParams.dqShallow G₀) := by
  have hδq : (0 : ℚ) < QMCLeafB.RundataParams.dqShallow G₀ :=
    QMCLeafB.RundataParams.dqShallow_pos G₀
  refine ⟨Q₀, Q₀_symm, hδq, ?_, ?_, ?_⟩
  · intro x
    rw [qf_Q₀]
    have hsq : (0 : ℚ) ≤ (x 0 - x 1) ^ 2 := sq_nonneg _
    have hS : (0 : ℚ) ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  · intro i
    rw [Q₀_diag]
    simp only [sub_self, abs_zero]
    linarith
  · rw [frob_wMatrixQ_Q₀]
    have heps : QMCLeafB.RundataCert.eps G₀ = 1 / 40000 := by
      rw [QMCLeafB.RundataCert.eps, QMCLeafB.ResidRefute.Rq_G₀]
    rw [heps]
    unfold t₀
    nlinarith

/-- **The two readings of the body at the refutation point, in one statement.** -/
theorem gate_closed_at_t₀ :
    AsmM8.Interior G₀ t₀ ∧ ¬ AsmM8.EmptyBody G₀ t₀ P₀ ∧
      (∃ cX : Matrix (Fin 2) (Fin 2) ℚ, cXᵀ = cX ∧
        QMCLeafB.RelaxOracle.RelaxMem (QMCLeafB.Finalization.wMatrixQ G₀) cX
          (t₀ - QMCLeafB.RundataCert.eps G₀) (QMCLeafB.RundataParams.dqShallow G₀)) :=
  ⟨interior_t₀, not_emptyBody_t₀, rational_member_t₀⟩

/-- **If the bit reads `false` at the refutation point, `hcomplete` fails there** — at an interior,
REAL-nonempty and RATIONAL-nonempty point.  (The bit's value is d5/m4's computation; this is the
residual-side consequence.) -/
theorem hcomplete_false_of_bit_false (hbit : QMCLeafB.MechM6.bit0 G₀ t₀ = false) :
    ¬ (∀ (G : QuantumMaxCutEnergy.Input) (t : ℚ), 2 ≤ G.n → AsmM8.Interior G t →
        ¬ AsmM8.EmptyBody G t (QMCLeafB.UnionShallow.paramsKbc2 G) → QMCLeafB.MechM6.bit0 G t = true) := by
  intro hc
  have hn : 2 ≤ G₀.n := by decide
  have h1 := hc G₀ t₀ hn interior_t₀ not_emptyBody_t₀
  rw [hbit] at h1
  exact absurd h1 (by decide)

end Lvl32M8

/-! ## Axiom audit -/

#print axioms Lvl32M8.density_of_hok_complete
#print axioms Lvl32M8.residual_pair_refuted
#print axioms Lvl32M8.fam_symm
#print axioms Lvl32M8.qf_fam
#print axioms Lvl32M8.frob_fam
#print axioms Lvl32M8.psd_clause_fam
#print axioms Lvl32M8.exists_mem_of_level_ge
#print axioms Lvl32M8.level_ge_of_nonempty
#print axioms Lvl32M8.density_n2
#print axioms Lvl32M8.ellip_symm
#print axioms Lvl32M8.qf_ellip
#print axioms Lvl32M8.frob_ellip
#print axioms Lvl32M8.exists_mem_of_elliptope
#print axioms Lvl32M8.density_of_elliptope
#print axioms Lvl32M8.qf_Q₀
#print axioms Lvl32M8.frob_wMatrixQ_Q₀
#print axioms Lvl32M8.frob_wMatrix_Z₀
#print axioms Lvl32M8.not_emptyBody_t₀
#print axioms Lvl32M8.rational_member_t₀
#print axioms Lvl32M8.gate_closed_at_t₀
#print axioms Lvl32M8.hcomplete_false_of_bit_false
#print axioms Lvl32M8.density_of_hok_complete_generic



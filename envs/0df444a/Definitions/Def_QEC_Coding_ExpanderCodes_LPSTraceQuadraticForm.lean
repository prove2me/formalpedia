-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
-- name    : QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T21:35:02.554633+00:00
-- url     : https://prove2.me/theorems/af73a7c1-f3a2-4d66-9098-f9960b72bbfb
-- title:
--   LPSTrace Quadratic Form
-- statement:
--   Definitions and structural lemmas for LPSTrace Quadratic Form, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSTraceQuadraticForm.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionCount
import Mathlib.RingTheory.PowerSeries.Basic
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q


set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
def lpsTraceQuadraticForm (q : ℕ) (t : LPSQuaternion) : ℤ :=
  t.a ^ 2 + ((2 * q : ℕ) : ℤ) ^ 2 * t.b ^ 2 +
    ((2 * q : ℕ) : ℤ) ^ 2 * t.c ^ 2 +
      ((2 * q : ℕ) : ℤ) ^ 2 * t.d ^ 2
def lpsTraceQuaternion (q : ℕ) (t : LPSQuaternion) : LPSQuaternion where
  a := t.a
  b := (2 * q : ℕ) * t.b
  c := (2 * q : ℕ) * t.c
  d := (2 * q : ℕ) * t.d
@[simp] theorem lpsTraceQuaternion_a (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).a = t.a := rfl
@[simp] theorem lpsTraceQuaternion_b (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).b = (2 * q : ℕ) * t.b := rfl
@[simp] theorem lpsTraceQuaternion_c (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).c = (2 * q : ℕ) * t.c := rfl
@[simp] theorem lpsTraceQuaternion_d (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).d = (2 * q : ℕ) * t.d := rfl
@[simp] theorem norm_lpsTraceQuaternion (q : ℕ) (t : LPSQuaternion) :
    (lpsTraceQuaternion q t).norm = lpsTraceQuadraticForm q t := by
  simp [LPSQuaternion.norm, lpsTraceQuadraticForm]
  ring
theorem lpsTraceQuaternion_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (lpsTraceQuaternion q) := by
  intro t u h
  have hab := congrArg LPSQuaternion.a h
  have hbb := congrArg LPSQuaternion.b h
  have hcb := congrArg LPSQuaternion.c h
  have hdb := congrArg LPSQuaternion.d h
  simp only [lpsTraceQuaternion_a] at hab
  simp only [lpsTraceQuaternion_b] at hbb
  simp only [lpsTraceQuaternion_c] at hcb
  simp only [lpsTraceQuaternion_d] at hdb
  apply LPSQuaternion.ext hab
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hbb
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hcb
  · exact mul_left_cancel₀ (by positivity : ((2 * q : ℕ) : ℤ) ≠ 0) hdb
theorem exists_lpsTraceQuaternion_eq_iff (q : ℕ) (u : LPSQuaternion) :
    (∃ t, lpsTraceQuaternion q t = u) ↔
      ((2 * q : ℕ) : ℤ) ∣ u.b ∧
        ((2 * q : ℕ) : ℤ) ∣ u.c ∧
          ((2 * q : ℕ) : ℤ) ∣ u.d := by
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · rintro ⟨⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩
    refine ⟨⟨u.a, b, c, d⟩, ?_⟩
    apply LPSQuaternion.ext <;> simp [hb, hc, hd]
noncomputable def lpsTraceQuadraticShell (q n : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionBox n).filter fun t => lpsTraceQuadraticForm q t = n
theorem coordinate_bounds_of_traceQuadraticForm
    {q n : ℕ} (hq : 0 < q) (t : LPSQuaternion)
    (ht : lpsTraceQuadraticForm q t = n) :
    -(n : ℤ) ≤ t.a ∧ t.a ≤ n ∧
      -(n : ℤ) ≤ t.b ∧ t.b ≤ n ∧
      -(n : ℤ) ≤ t.c ∧ t.c ≤ n ∧
      -(n : ℤ) ≤ t.d ∧ t.d ≤ n := by
  let scale : ℤ := (2 * q : ℕ)
  have hscale : 1 ≤ scale ^ 2 := by
    have hscaleOne : (1 : ℤ) ≤ scale := by
      dsimp [scale]
      exact_mod_cast (show 1 ≤ 2 * q by omega)
    nlinarith [sq_nonneg (scale - 1)]
  have hform :
      t.a ^ 2 + scale ^ 2 * t.b ^ 2 + scale ^ 2 * t.c ^ 2 +
          scale ^ 2 * t.d ^ 2 = (n : ℤ) := by
    simpa [lpsTraceQuadraticForm, scale] using ht
  have ha : t.a ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.b, sq_nonneg t.c, sq_nonneg t.d]
  have hbScale : t.b ^ 2 ≤ scale ^ 2 * t.b ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.b)
  have hb : t.b ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.c, sq_nonneg t.d]
  have hcScale : t.c ^ 2 ≤ scale ^ 2 * t.c ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.c)
  have hc : t.c ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.d]
  have hdScale : t.d ^ 2 ≤ scale ^ 2 * t.d ^ 2 :=
    by simpa using mul_le_mul_of_nonneg_right hscale (sq_nonneg t.d)
  have hd : t.d ^ 2 ≤ (n : ℤ) := by
    nlinarith [sq_nonneg t.a, sq_nonneg t.b, sq_nonneg t.c]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.a - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.b - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c + n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.c - n)]
  constructor
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d + n)]
  · by_contra h
    push Not at h
    nlinarith [sq_nonneg (t.d - n)]
theorem mem_lpsTraceQuadraticShell_iff
    {q n : ℕ} (hq : 0 < q) (t : LPSQuaternion) :
    t ∈ lpsTraceQuadraticShell q n ↔
      lpsTraceQuadraticForm q t = n := by
  rw [lpsTraceQuadraticShell, Finset.mem_filter]
  exact and_iff_right_of_imp fun ht =>
    (mem_lpsQuaternionBox_iff n t).mpr
      (coordinate_bounds_of_traceQuadraticForm hq t ht)
noncomputable def lpsTraceCongruenceShell (q n : ℕ) : Finset LPSQuaternion :=
  (lpsQuaternionFullShell n).filter fun u =>
    ((2 * q : ℕ) : ℤ) ∣ u.b ∧
      ((2 * q : ℕ) : ℤ) ∣ u.c ∧
        ((2 * q : ℕ) : ℤ) ∣ u.d
theorem mem_lpsTraceCongruenceShell_iff
    {q n : ℕ} (hn : 0 < n) (u : LPSQuaternion) :
    u ∈ lpsTraceCongruenceShell q n ↔
      u.norm = n ∧
        ((2 * q : ℕ) : ℤ) ∣ u.b ∧
          ((2 * q : ℕ) : ℤ) ∣ u.c ∧
            ((2 * q : ℕ) : ℤ) ∣ u.d := by
  rw [lpsTraceCongruenceShell, Finset.mem_filter,
    mem_lpsQuaternionFullShell_iff hn]
noncomputable def lpsTraceQuadraticShellEquivCongruenceShell
    {q n : ℕ} (hq : 0 < q) (hn : 0 < n) :
    {t // t ∈ lpsTraceQuadraticShell q n} ≃
      {u // u ∈ lpsTraceCongruenceShell q n} :=
  Equiv.ofBijective
    (fun t => ⟨lpsTraceQuaternion q t.1,
      (mem_lpsTraceCongruenceShell_iff hn _).mpr ⟨by
        rw [norm_lpsTraceQuaternion]
        exact (mem_lpsTraceQuadraticShell_iff hq t.1).mp t.2,
      by simp⟩⟩) <| by
    constructor
    · intro t u h
      apply Subtype.ext
      apply lpsTraceQuaternion_injective hq
      exact congrArg Subtype.val h
    · intro u
      have hu := (mem_lpsTraceCongruenceShell_iff hn u.1).mp u.2
      obtain ⟨t, ht⟩ :=
        (exists_lpsTraceQuaternion_eq_iff q u.1).mpr hu.2
      refine ⟨⟨t, (mem_lpsTraceQuadraticShell_iff hq t).mpr ?_⟩, ?_⟩
      · rw [← norm_lpsTraceQuaternion, ht]
        exact hu.1
      · apply Subtype.ext
        exact ht
noncomputable def lpsTraceThetaSeries (q : ℕ) : PowerSeries ℕ :=
  PowerSeries.mk fun n => (lpsTraceQuadraticShell q n).card
end QEC.Coding.TannerLiftedProduct



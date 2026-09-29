-- Prove2me | solution 1 for AutomorphicForm.mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/71396693-2a8a-59e9-a3f5-3f3130d9d10f

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Pointwise

noncomputable section

namespace KcCartanNormR4

open AutomorphicForm

section Local

variable (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

local notation "Kv" => v.adicCompletion K
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion K)

theorem mem_integers_iff_norm (y : Kv) : y ∈ v.adicCompletionIntegers K ↔ ‖y‖ ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valued.toNormedField.norm_le_one_iff]

theorem norm_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) (i j : Fin 2) :
    ‖(g : M2) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).1 i j)

theorem norm_inv_entry_le_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) Kv) : M2) i j‖ ≤ 1 :=
  (mem_integers_iff_norm K v _).1 (((mem_localIntegralSet K v).1 hg).2 i j)

theorem norm_det_le_mul {M : M2} {C : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ C) : ‖M.det‖ ≤ C * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hM 0 0)
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]; exact mul_le_mul (hM 0 0) (hM 1 1) (norm_nonneg _) hC
  · rw [norm_neg, norm_mul]; exact mul_le_mul (hM 0 1) (hM 1 0) (norm_nonneg _) hC

theorem norm_det_le_one {M : M2} (hM : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by
  simpa using norm_det_le_mul K v hM

theorem norm_det_eq_one_of_mem {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) : ‖(g : M2).det‖ = 1 := by
  have h1 : ‖(g : M2).det‖ ≤ 1 := norm_det_le_one K v (norm_entry_le_one_of_mem K v hg)
  have h2 : ‖((g⁻¹ : GL (Fin 2) Kv) : M2).det‖ ≤ 1 := norm_det_le_one K v (norm_inv_entry_le_one_of_mem K v hg)
  have hprod : (g : M2).det * ((g⁻¹ : GL (Fin 2) Kv) : M2).det = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have hn : ‖(g : M2).det‖ * ‖((g⁻¹ : GL (Fin 2) Kv) : M2).det‖ = 1 := by rw [← norm_mul, hprod, norm_one]
  by_contra hne
  have hlt : ‖(g : M2).det‖ < 1 := lt_of_le_of_ne h1 hne
  exact (mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt h2).ne hn

theorem mem_localIntegralSet_of_norm {g : GL (Fin 2) Kv} (h1 : ∀ i j, ‖(g : M2) i j‖ ≤ 1)
    (h2 : ‖(g : M2).det‖ = 1) : g ∈ localIntegralSet K v := by
  refine (mem_localIntegralSet K v).2 ⟨fun i j => (mem_integers_iff_norm K v _).2 (h1 i j), fun i j => ?_⟩
  rw [mem_integers_iff_norm, Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv, h2, inv_one, one_mul]
  fin_cases i <;> fin_cases j
  · exact h1 1 1
  · simpa using h1 0 1
  · simpa using h1 1 0
  · exact h1 0 0

theorem mem_localIntegralSet_iff_norm (g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v ↔ (∀ i j, ‖(g : M2) i j‖ ≤ 1) ∧ ‖(g : M2).det‖ = 1 :=
  ⟨fun hg => ⟨norm_entry_le_one_of_mem K v hg, norm_det_eq_one_of_mem K v hg⟩,
    fun h => mem_localIntegralSet_of_norm K v h.1 h.2⟩

theorem norm_mul_entry_le_of_left {M N : M2} {C : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ 1) (hN : ∀ i j, ‖N i j‖ ≤ C)
    (i j : Fin 2) : ‖(M * N) i j‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hN 0 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖M i 0‖ * ‖N 0 j‖ ≤ 1 * C := mul_le_mul (hM i 0) (hN 0 j) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [norm_mul]
    calc ‖M i 1‖ * ‖N 1 j‖ ≤ 1 * C := mul_le_mul (hM i 1) (hN 1 j) (norm_nonneg _) zero_le_one
      _ = C := one_mul C

theorem norm_mul_entry_le_of_right {M N : M2} {C : ℝ} (hM : ∀ i j, ‖M i j‖ ≤ C) (hN : ∀ i j, ‖N i j‖ ≤ 1)
    (i j : Fin 2) : ‖(M * N) i j‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hM 0 0)
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖M i 0‖ * ‖N 0 j‖ ≤ C * 1 := mul_le_mul (hM i 0) (hN 0 j) (norm_nonneg _) hC
      _ = C := mul_one C
  · rw [norm_mul]
    calc ‖M i 1‖ * ‖N 1 j‖ ≤ C * 1 := mul_le_mul (hM i 1) (hN 1 j) (norm_nonneg _) hC
      _ = C := mul_one C

theorem mul_mem_localIntegralSet {g h : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v)
    (hh : h ∈ localIntegralSet K v) : g * h ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet_iff_norm] at hg hh ⊢
  refine ⟨fun i j => ?_, ?_⟩
  · rw [Units.val_mul]; exact norm_mul_entry_le_of_left K v hg.1 hh.1 i j
  · rw [Units.val_mul, Matrix.det_mul, norm_mul, hg.2, hh.2, one_mul]

theorem inv_mem_localIntegralSet {g : GL (Fin 2) Kv} (hg : g ∈ localIntegralSet K v) :
    g⁻¹ ∈ localIntegralSet K v := by
  rw [mem_localIntegralSet] at hg ⊢
  rw [inv_inv]
  exact ⟨hg.2, hg.1⟩

theorem mem_doubleCoset_iff (d g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v ↔
      ∃ a ∈ localIntegralSet K v, ∃ b ∈ localIntegralSet K v, a * d * b = g := by
  constructor
  · intro hg
    obtain ⟨p, hp, b, hb, rfl⟩ := Set.mem_mul.1 hg
    obtain ⟨a, ha, d', hd', rfl⟩ := Set.mem_mul.1 hp
    rw [Set.mem_singleton_iff] at hd'
    subst hd'
    exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Set.mem_mul.2 ⟨a * d, Set.mem_mul.2 ⟨a, ha, d, Set.mem_singleton d, rfl⟩, b, hb, rfl⟩

theorem norm_uniformiser_lt_one {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : ‖(ϖ : Kv)‖ < 1 := by
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : Valued.v (ϖ : Kv) ≤ 1 := ϖ.2
  refine lt_of_le_of_ne h1 fun h => hϖ.not_isUnit ?_
  exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h

theorem uniformiser_ne_zero {ϖ : v.adicCompletionIntegers K} (hϖ : Irreducible ϖ) : (ϖ : Kv) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  exact_mod_cast h

theorem invariants_of_mem {π : Kv} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) {m₁ m₂ : ℤ} (hm : m₂ ≤ m₁)
    {dl : GL (Fin 2) Kv} (hdl : (dl : M2) = !![π ^ m₁, 0; 0, π ^ m₂])
    {g : GL (Fin 2) Kv}
    (hg : g ∈ localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v) :
    ‖(g : M2).det‖ = ‖π‖ ^ (m₁ + m₂) ∧ (∀ i j, ‖(g : M2) i j‖ ≤ ‖π‖ ^ m₂) ∧
      ∃ i j, ‖(g : M2) i j‖ = ‖π‖ ^ m₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCoset_iff K v dl g).1 hg
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  obtain ⟨ha1, ha2⟩ := (mem_localIntegralSet_iff_norm K v a).1 ha
  obtain ⟨hb1, hb2⟩ := (mem_localIntegralSet_iff_norm K v b).1 hb
  have hai := norm_entry_le_one_of_mem K v (inv_mem_localIntegralSet K v ha)
  have hbi := norm_entry_le_one_of_mem K v (inv_mem_localIntegralSet K v hb)

  have hdle : ∀ i j, ‖(dl : M2) i j‖ ≤ ‖π‖ ^ m₂ := by
    intro i j
    rw [hdl]
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, norm_zpow]
      exact zpow_le_zpow_right_of_le_one₀ hπpos hπ1 hm
    · simp [zpow_nonneg (norm_nonneg π) m₂]
    · simp [zpow_nonneg (norm_nonneg π) m₂]
    · simp
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, ha2, hb2, one_mul,
      mul_one, hdl, Matrix.det_fin_two_of, mul_zero, sub_zero, ← zpow_add₀ hπ0, norm_zpow]
  · intro i j
    rw [Units.val_mul, Units.val_mul]
    exact norm_mul_entry_le_of_right K v (norm_mul_entry_le_of_left K v ha1 hdle) hb1 i j
  ·
    by_contra hne
    push Not at hne
    have hlt : ∀ i j, ‖((a * dl * b : GL (Fin 2) Kv) : M2) i j‖ < ‖π‖ ^ m₂ := fun i j =>
      lt_of_le_of_ne (by
        rw [Units.val_mul, Units.val_mul]
        exact norm_mul_entry_le_of_right K v (norm_mul_entry_le_of_left K v ha1 hdle) hb1 i j) (hne i j)

    obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 2 × Fin 2))
      (fun p => ‖((a * dl * b : GL (Fin 2) Kv) : M2) p.1 p.2‖) ⟨(0, 0), Finset.mem_univ _⟩
    set C := ‖((a * dl * b : GL (Fin 2) Kv) : M2) p.1 p.2‖ with hC
    have hgC : ∀ i j, ‖((a * dl * b : GL (Fin 2) Kv) : M2) i j‖ ≤ C := fun i j => hp (i, j) (Finset.mem_univ _)
    have hdlC : ∀ i j, ‖(dl : M2) i j‖ ≤ C := by
      have heq : (dl : M2) = ((a⁻¹ : GL (Fin 2) Kv) : M2) * ((a * dl * b : GL (Fin 2) Kv) : M2) *
          ((b⁻¹ : GL (Fin 2) Kv) : M2) := by
        rw [← Units.val_mul, ← Units.val_mul]
        congr 1
        group
      intro i j
      rw [heq]
      exact norm_mul_entry_le_of_right K v (norm_mul_entry_le_of_left K v hai hgC) hbi i j
    have h11 := hdlC 1 1
    rw [hdl] at h11
    simp only [Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_fin_one,
      norm_zpow] at h11
    exact absurd (h11.trans_lt (hlt p.1 p.2)) (lt_irrefl _)

theorem mem_doubleCoset_of_norm_apply_zero_zero {π : Kv} (hπ0 : π ≠ 0) {n : ℤ}
    {d : GL (Fin 2) Kv} (hd : (d : M2) = !![π ^ n, 0; 0, 1])
    {h : GL (Fin 2) Kv} (h1 : ∀ i j, ‖(h : M2) i j‖ ≤ 1) (h00 : ‖(h : M2) 0 0‖ = 1)
    (hdet : ‖(h : M2).det‖ = ‖π‖ ^ n) :
    h ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
  set x := (h : M2) 0 0 with hx
  set y := (h : M2) 0 1 with hy
  set z := (h : M2) 1 0 with hz
  set w := (h : M2) 1 1 with hw
  set δ := (h : M2).det with hδ
  have hx0 : x ≠ 0 := norm_pos_iff.1 (by rw [h00]; exact one_pos)
  have hπn0 : π ^ n ≠ 0 := zpow_ne_zero n hπ0
  have hδ0 : δ ≠ 0 := (Matrix.isUnits_det_units h).ne_zero
  have hδ' : δ = x * w - y * z := by rw [hδ, Matrix.det_fin_two]

  let A : M2 := !![0, x; δ / (x * π ^ n), z]
  let B : M2 := !![0, 1; 1, y / x]
  have hA_det : A.det = -(δ / π ^ n) := by
    simp only [A, Matrix.det_fin_two_of]
    field_simp
    ring
  have hB_det : B.det = -1 := by
    simp only [B, Matrix.det_fin_two_of]; ring
  have hA0 : A.det ≠ 0 := by
    rw [hA_det, neg_ne_zero]; exact div_ne_zero hδ0 hπn0
  have hB0 : B.det ≠ 0 := by rw [hB_det]; norm_num
  have hyx : ‖y / x‖ ≤ 1 := by rw [norm_div, h00, div_one]; exact h1 0 1
  have hzn : ‖z‖ ≤ 1 := h1 1 0
  have hδx : ‖δ / (x * π ^ n)‖ = 1 := by
    rw [norm_div, norm_mul, h00, one_mul, hdet, norm_zpow, div_self]
    exact zpow_ne_zero n (norm_ne_zero_iff.2 hπ0)
  have hAK : Matrix.GeneralLinearGroup.mkOfDetNeZero A hA0 ∈ localIntegralSet K v := by
    refine mem_localIntegralSet_of_norm K v (fun i j => ?_) ?_
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      fin_cases i <;> fin_cases j
      · simp [A]
      · simp only [A, Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val_zero]
        exact h00.le
      · simp only [A, Fin.mk_one, Fin.isValue, Fin.zero_eta, Matrix.of_apply, Matrix.cons_val',
          Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one]
        exact hδx.le
      · simp only [A, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact hzn
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hA_det, norm_neg, norm_div, hdet, norm_zpow, div_self]
      exact zpow_ne_zero n (norm_ne_zero_iff.2 hπ0)
  have hBK : Matrix.GeneralLinearGroup.mkOfDetNeZero B hB0 ∈ localIntegralSet K v := by
    refine mem_localIntegralSet_of_norm K v (fun i j => ?_) ?_
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      fin_cases i <;> fin_cases j
      · simp [B]
      · simp [B]
      · simp [B]
      · simp only [B, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
          Matrix.cons_val_fin_one]
        exact hyx
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hB_det, norm_neg, norm_one]
  refine (mem_doubleCoset_iff K v d h).2 ⟨_, hAK, _, hBK, ?_⟩
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hd]

  have hw' : w = (δ + y * z) / x := by rw [hδ']; field_simp; ring
  ext i j : 1
  fin_cases i <;> fin_cases j
  · simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, hx]
  · simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, hy]
    field_simp
  · simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, hz]
  · simp [A, B, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    rw [← hw, hw']
    field_simp

def swapGL : GL (Fin 2) Kv :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (!![0, 1; 1, 0] : M2) (by rw [Matrix.det_fin_two_of]; norm_num)

theorem swapGL_coe : ((swapGL K v : GL (Fin 2) Kv) : M2) = !![0, 1; 1, 0] :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

theorem swapGL_mem : swapGL K v ∈ localIntegralSet K v := by
  refine mem_localIntegralSet_of_norm K v (fun i j => ?_) ?_
  · rw [swapGL_coe]; fin_cases i <;> fin_cases j <;> simp
  · rw [swapGL_coe, Matrix.det_fin_two_of]; norm_num

theorem mul_mem_doubleCoset {d g k : GL (Fin 2) Kv}
    (hg : g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v)
    (hk : k ∈ localIntegralSet K v) :
    g * k ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCoset_iff K v d g).1 hg
  exact (mem_doubleCoset_iff K v d _).2 ⟨a, ha, b * k, mul_mem_localIntegralSet K v hb hk, by group⟩

theorem mem_doubleCoset_mul {d g k : GL (Fin 2) Kv}
    (hg : g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v)
    (hk : k ∈ localIntegralSet K v) :
    k * g ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_doubleCoset_iff K v d g).1 hg
  exact (mem_doubleCoset_iff K v d _).2 ⟨k * a, mul_mem_localIntegralSet K v hk ha, b, hb, by group⟩

theorem mem_doubleCoset_of_exists_norm_apply_eq_one {π : Kv} (hπ0 : π ≠ 0) {n : ℤ}
    {d : GL (Fin 2) Kv} (hd : (d : M2) = !![π ^ n, 0; 0, 1])
    {h : GL (Fin 2) Kv} (h1 : ∀ i j, ‖(h : M2) i j‖ ≤ 1) (hex : ∃ i j, ‖(h : M2) i j‖ = 1)
    (hdet : ‖(h : M2).det‖ = ‖π‖ ^ n) :
    h ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
  have hs := swapGL_mem K v
  have hs1 : ∀ i j, ‖((swapGL K v : GL (Fin 2) Kv) : M2) i j‖ ≤ 1 := norm_entry_le_one_of_mem K v hs
  have hsi : (swapGL K v)⁻¹ * swapGL K v = 1 := inv_mul_cancel _
  obtain ⟨i, j, hij⟩ := hex
  fin_cases i <;> fin_cases j
  · exact mem_doubleCoset_of_norm_apply_zero_zero K v hπ0 hd h1 hij hdet
  ·
    have hmem : h * swapGL K v ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
      refine mem_doubleCoset_of_norm_apply_zero_zero K v hπ0 hd (fun i j => ?_) ?_ ?_
      · rw [Units.val_mul]; exact norm_mul_entry_le_of_right K v h1 hs1 i j
      · rw [Units.val_mul, swapGL_coe]
        conv_lhs => rw [Matrix.eta_fin_two (h : M2)]
        simpa using hij
      · rw [Units.val_mul, Matrix.det_mul, norm_mul, norm_det_eq_one_of_mem K v hs, mul_one, hdet]
    have := mul_mem_doubleCoset K v hmem (inv_mem_localIntegralSet K v hs)
    rwa [mul_inv_cancel_right] at this
  ·
    have hmem : swapGL K v * h ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
      refine mem_doubleCoset_of_norm_apply_zero_zero K v hπ0 hd (fun i j => ?_) ?_ ?_
      · rw [Units.val_mul]; exact norm_mul_entry_le_of_left K v hs1 h1 i j
      · rw [Units.val_mul, swapGL_coe]
        conv_lhs => rw [Matrix.eta_fin_two (h : M2)]
        simpa using hij
      · rw [Units.val_mul, Matrix.det_mul, norm_mul, norm_det_eq_one_of_mem K v hs, one_mul, hdet]
    have := mem_doubleCoset_mul K v hmem (inv_mem_localIntegralSet K v hs)
    rwa [inv_mul_cancel_left] at this
  ·
    have hmem : swapGL K v * h * swapGL K v ∈
        localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v := by
      refine mem_doubleCoset_of_norm_apply_zero_zero K v hπ0 hd (fun i j => ?_) ?_ ?_
      · rw [Units.val_mul, Units.val_mul]
        exact norm_mul_entry_le_of_right K v (norm_mul_entry_le_of_left K v hs1 h1) hs1 i j
      · rw [Units.val_mul, Units.val_mul, swapGL_coe]
        conv_lhs => rw [Matrix.eta_fin_two (h : M2)]
        simpa using hij
      · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
          norm_det_eq_one_of_mem K v hs, one_mul, mul_one, hdet]
    have h' := mem_doubleCoset_mul K v (mul_mem_doubleCoset K v hmem (inv_mem_localIntegralSet K v hs))
      (inv_mem_localIntegralSet K v hs)
    have heq : (swapGL K v)⁻¹ * (swapGL K v * h * swapGL K v * (swapGL K v)⁻¹) = h := by group
    rwa [heq] at h'

theorem mem_doubleCoset_iff_norm {π : Kv} (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) {m₁ m₂ : ℤ} (hm : m₂ ≤ m₁)
    {dl : GL (Fin 2) Kv} (hdl : (dl : M2) = !![π ^ m₁, 0; 0, π ^ m₂]) (g : GL (Fin 2) Kv) :
    g ∈ localIntegralSet K v * ({dl} : Set (GL (Fin 2) Kv)) * localIntegralSet K v ↔
      ‖(g : M2).det‖ = ‖π‖ ^ (m₁ + m₂) ∧ (∀ i j, ‖(g : M2) i j‖ ≤ ‖π‖ ^ m₂) ∧
        ∃ i j, ‖(g : M2) i j‖ = ‖π‖ ^ m₂ := by
  refine ⟨invariants_of_mem K v hπ0 hπ1 hm hdl, fun ⟨hdet, hle, hex⟩ => ?_⟩
  have hπpos : 0 < ‖π‖ := norm_pos_iff.2 hπ0
  set c : Kv := π ^ m₂ with hc
  have hc0 : c ≠ 0 := zpow_ne_zero m₂ hπ0
  have hnc : ‖c‖ = ‖π‖ ^ m₂ := norm_zpow π m₂
  have hnc0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc0

  set z : GL (Fin 2) Kv := Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 c hc0) with hz
  have hz_coe : (z : M2) = c • (1 : M2) := by
    rw [hz]
    show Matrix.scalar (Fin 2) ((Units.mk0 c hc0 : (v.adicCompletion K)ˣ) : Kv) = _
    rw [Units.val_mk0, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  set h : GL (Fin 2) Kv := z⁻¹ * g with hh
  have hh_coe : (h : M2) = c⁻¹ • (g : M2) := by
    rw [hh, Units.val_mul, hz, ← map_inv]
    show Matrix.scalar (Fin 2) (((Units.mk0 c hc0)⁻¹ : (v.adicCompletion K)ˣ) : Kv) * (g : M2) = _
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  have hh_entry : ∀ i j, (h : M2) i j = c⁻¹ * (g : M2) i j := fun i j => by
    rw [hh_coe, Matrix.smul_apply, smul_eq_mul]
  have h1' : ∀ i j, ‖(h : M2) i j‖ ≤ 1 := fun i j => by
    rw [hh_entry, norm_mul, norm_inv, hnc, ← div_eq_inv_mul, div_le_one (zpow_pos hπpos m₂)]
    exact hle i j
  have hex' : ∃ i j, ‖(h : M2) i j‖ = 1 := by
    obtain ⟨i, j, hij⟩ := hex
    exact ⟨i, j, by rw [hh_entry, norm_mul, norm_inv, hnc, hij, inv_mul_cancel₀ (zpow_ne_zero m₂ hπpos.ne')]⟩
  have hdet' : ‖(h : M2).det‖ = ‖π‖ ^ (m₁ - m₂) := by
    rw [hh_coe, Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, norm_inv, hnc, hdet]
    rw [← zpow_neg, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hπpos.ne']
    congr 1
    push_cast
    ring

  have hd0 : (!![π ^ (m₁ - m₂), 0; 0, 1] : M2).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]; simp [zpow_ne_zero _ hπ0]
  set d : GL (Fin 2) Kv := Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd0 with hd
  have hd_coe : (d : M2) = !![π ^ (m₁ - m₂), 0; 0, 1] := Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hmem : h ∈ localIntegralSet K v * ({d} : Set (GL (Fin 2) Kv)) * localIntegralSet K v :=
    mem_doubleCoset_of_exists_norm_apply_eq_one K v hπ0 hd_coe h1' hex' hdet'
  obtain ⟨a, ha, b, hb, hab⟩ := (mem_doubleCoset_iff K v d h).1 hmem

  have hzd : z * d = dl := by
    refine Units.ext ?_
    rw [Units.val_mul, hz_coe, hd_coe, hdl, Matrix.smul_mul, Matrix.one_mul]
    ext i j : 1
    fin_cases i <;> fin_cases j
    · simp only [hc, Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_fin_one, smul_eq_mul, Fin.zero_eta, Fin.isValue]
      rw [← zpow_add₀ hπ0]; congr 1; ring
    · simp
    · simp
    · simp [hc]

  have hzc : ∀ x : GL (Fin 2) Kv, z * x = x * z := fun x => by
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, hz_coe, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  refine (mem_doubleCoset_iff K v dl g).2 ⟨a, ha, b, hb, ?_⟩
  have hg : g = z * h := by rw [hh, mul_inv_cancel_left]
  rw [hg, ← hab, ← hzd]
  calc a * (z * d) * b = (a * z) * d * b := by group
    _ = (z * a) * d * b := by rw [hzc a]
    _ = z * (a * d * b) := by group

end Local

end KcCartanNormR4

end

open NumberField IsDedekindDomain
open scoped Pointwise

theorem solution
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (π : v.adicCompletion K) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ ≤ 1) (m₁ m₂ : ℤ) (hm : m₂ ≤ m₁)
    (dl : GL (Fin 2) (v.adicCompletion K))
    (hdl : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = Matrix.diagonal ![π ^ m₁, π ^ m₂])
    (g : GL (Fin 2) (v.adicCompletion K)) :
    g ∈ AutomorphicForm.localIntegralSet K v * ({dl} : Set (GL (Fin 2) (v.adicCompletion K))) *
        AutomorphicForm.localIntegralSet K v ↔
      ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)).det‖ = ‖π‖ ^ (m₁ + m₂) ∧
      (∀ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ ≤ ‖π‖ ^ m₂) ∧
      ∃ i j, ‖(g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j‖ = ‖π‖ ^ m₂ := by
  have hdl' : (dl : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![π ^ m₁, 0; 0, π ^ m₂] := by
    rw [hdl]
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp
  exact KcCartanNormR4.mem_doubleCoset_iff_norm K v hπ0 hπ1 hm hdl' g

end S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm
end P2MW
export P2MW.S_AutomorphicForm_mem_localIntegralSet_mul_singleton_diagonal_mul_localIntegralSet_iff_norm (solution)

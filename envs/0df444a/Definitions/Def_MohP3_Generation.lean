-- Prove2me | Definitions.Def_MohP3_Generation
-- name    : MohP3_Generation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T22:27:49.075104+00:00
-- url     : https://prove2.me/theorems/a735ac73-e1e8-4f3a-9e02-b4628eb75c23
-- title:
--   Generation
-- statement:
--   Definitions and structural lemmas for Generation, from GrgAakash (GrgAakash/moh-p3-set-theoretic-complete-intersection; see pinned Apache-2.0 LICENSE and README.md)'s pinned Moh P3 curve is a global and formal-local set-theoretic complete intersection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Theorems.Thm_MohP3_Gen_key_xA
public import Theorems.Thm_MohP3_Gen_key_zA
public import Theorems.Thm_MohP3_Gen_qxD_wt
public import Theorems.Thm_MohP3_Gen_qzD_wt
public import Theorems.Thm_MohP3_Gen_wxD_wt
public import Theorems.Thm_MohP3_Gen_wzD_wt
public import Theorems.Thm_MohP3_Wt_dd_apply_one
public import Theorems.Thm_MohP3_Wt_dd_apply_two
public import Theorems.Thm_MohP3_Wt_dd_apply_zero
public import Theorems.Thm_MohP3_Wt_mem_En
public import Theorems.Thm_MohP3_Wt_monomial_dd
public import Theorems.Thm_MohP3_Wt_wOrd_X
public import Theorems.Thm_MohP3_Wt_wOrd_add
public import Theorems.Thm_MohP3_Wt_wOrd_mono
public import Theorems.Thm_MohP3_Wt_wOrd_of_zero
public import Theorems.Thm_MohP3_Wt_wOrd_pow
public import Theorems.Thm_MohP3_Wt_wOrd_sub_top_part
public import Theorems.Thm_MohP3_Wt_wOrd_sum
public import Theorems.Thm_MohP3_Wt_wOrd_zero
public import Theorems.Thm_MohP3_Wt_wt_dd
public import Theorems.Thm_MohP3_Wt_yOrd_X_pow
public import Theorems.Thm_MohP3_Wt_yOrd_add
public import Theorems.Thm_MohP3_Wt_yOrd_mono
public import Theorems.Thm_MohP3_Wt_yOrd_monomial
public import Theorems.Thm_MohP3_Wt_yOrd_of_zero
public import Theorems.Thm_MohP3_Wt_yOrd_sum
public import Theorems.Thm_MohP3_Wt_yOrd_zero
public import Theorems.Thm_P2M_MohP3_Wt_wOrd_mul__c4d0f86c750f
public import Theorems.Thm_P2M_MohP3_Wt_yOrd_mul__b3d090251f18
attribute [local simp] MohP3.Wt.dd_apply_one
attribute [local simp] MohP3.Wt.dd_apply_two
attribute [local simp] MohP3.Wt.dd_apply_zero
attribute [local simp] MohP3.Wt.wt_dd


set_option autoImplicit true
@[expose] public section
@[expose] public section
noncomputable section
open MvPowerSeries MohP3.Wt
namespace MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
def ffS (j : Fin 4) : Sk k := Gen.ff (xs k) (ys k) (zs k) j
omit [CharZero k] in
lemma wOrd_xs : WOrd (xs k) 6 := by
  have := wOrd_X (k := k) 0
  simpa [xs, wt, Finsupp.single_apply] using this
omit [CharZero k] in
lemma wOrd_ys : WOrd (ys k) 8 := by
  have := wOrd_X (k := k) 1
  simpa [ys, wt, Finsupp.single_apply] using this
omit [CharZero k] in
lemma wOrd_zs : WOrd (zs k) 10 := by
  have := wOrd_X (k := k) 2
  simpa [zs, wt, Finsupp.single_apply] using this
omit [CharZero k] in
/-- A monomial with integer coefficient has the expected weighted order. -/
lemma wOrd_intMonomial (c : ℤ) (a b e n : ℕ) (h : n ≤ 6 * a + 8 * b + 10 * e) :
    WOrd ((c : Sk k) * (xs k) ^ a * (ys k) ^ b * (zs k) ^ e) n := by
  refine wOrd_mul' (m := (0 + a * 6 + b * 8)) (n := e * 10) (by omega) ?_
    (wOrd_pow (wOrd_zs k) e)
  refine wOrd_mul' (m := (0 + a * 6)) (n := b * 8) (by omega) ?_ (wOrd_pow (wOrd_ys k) b)
  exact wOrd_mul' (m := 0) (n := a * 6) (by omega) (wOrd_zero _) (wOrd_pow (wOrd_xs k) a)
omit [CharZero k] in
@[simp] lemma iotaS_X : iotaS k PowerSeries.X = ys k := by
  rw [iotaS, PowerSeries.substAlgHom_X]
omit [CharZero k] in
@[simp] lemma iotaS_C (a : k) : iotaS k (PowerSeries.C a) = MvPowerSeries.C a := by
  rw [show (PowerSeries.C a) = algebraMap k (PowerSeries k) a from rfl, AlgHom.commutes]
  rfl
omit [CharZero k] in
lemma wOrd_iotaS {p : PowerSeries k} {n : ℕ} (hp : YOrd p n) : WOrd (iotaS k p) n := by
  set M := (n + 7) / 8 with hM
  have hdvd : (PowerSeries.X : PowerSeries k) ^ M ∣ p := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    exact hp m (by omega)
  obtain ⟨q, hq⟩ := hdvd
  rw [hq, map_mul, map_pow, iotaS_X]
  exact wOrd_mul' (m := M * 8) (n := 0) (by omega) (wOrd_pow (wOrd_ys k) M) (wOrd_zero _)
lemma C18_mul_18 : (MvPowerSeries.C ((18 : k)⁻¹)) * (18 : Sk k) = 1 := by
  have h18 : (18 : k) ≠ 0 := by norm_num
  rw [show (18 : Sk k) = MvPowerSeries.C (18 : k) from (map_ofNat MvPowerSeries.C 18).symm,
    ← map_mul, inv_mul_cancel₀ h18, map_one]
lemma key_x_div (i : Fin 8) :
    xs k * hhS k i = MvPowerSeries.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qxA (ys k) i j * hhS k j) +
        ∑ j, Gen.wxA (xs k) (ys k) (zs k) i j * ffS k j) := by
  have h : (18 : Sk k) * (xs k * hhS k i) =
      (∑ j, Gen.qxA (ys k) i j * hhS k j) +
        ∑ j, Gen.wxA (xs k) (ys k) (zs k) i j * ffS k j :=
    Gen.key_xA (xs k) (ys k) (zs k) i
  rw [← h, ← mul_assoc, C18_mul_18, one_mul]
lemma key_z_div (i : Fin 8) :
    zs k * hhS k i = MvPowerSeries.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qzA (ys k) i j * hhS k j) +
        ∑ j, Gen.wzA (xs k) (ys k) (zs k) i j * ffS k j) := by
  have h : (18 : Sk k) * (zs k * hhS k i) =
      (∑ j, Gen.qzA (ys k) i j * hhS k j) +
        ∑ j, Gen.wzA (xs k) (ys k) (zs k) i j * ffS k j :=
    Gen.key_zA (xs k) (ys k) (zs k) i
  rw [← h, ← mul_assoc, C18_mul_18, one_mul]
def qxP (i j : Fin 8) : PowerSeries k :=
  PowerSeries.C (((Gen.qxD i j).1 : k)) * PowerSeries.X ^ (Gen.qxD i j).2
def qzP (i j : Fin 8) : PowerSeries k :=
  PowerSeries.C (((Gen.qzD i j).1 : k)) * PowerSeries.X ^ (Gen.qzD i j).2
omit [CharZero k] in
lemma iotaS_qxP (i j : Fin 8) : iotaS k (qxP k i j) = Gen.qxA (ys k) i j := by
  rw [qxP, Gen.qxA, map_mul, map_pow, iotaS_C, iotaS_X]
  congr 1
  exact map_intCast (MvPowerSeries.C : k →+* Sk k) _
omit [CharZero k] in
lemma iotaS_qzP (i j : Fin 8) : iotaS k (qzP k i j) = Gen.qzA (ys k) i j := by
  rw [qzP, Gen.qzA, map_mul, map_pow, iotaS_C, iotaS_X]
  congr 1
  exact map_intCast (MvPowerSeries.C : k →+* Sk k) _
omit [CharZero k] in
lemma yOrd_qxP (i j : Fin 8) : YOrd (qxP k i j) (8 * (Gen.qxD i j).2) :=
  yOrd_monomial _ _ _ (le_refl _)
omit [CharZero k] in
lemma yOrd_qzP (i j : Fin 8) : YOrd (qzP k i j) (8 * (Gen.qzD i j).2) :=
  yOrd_monomial _ _ _ (le_refl _)
omit [CharZero k] in
lemma wOrd_wxA (i : Fin 8) (j : Fin 4) :
    WOrd (Gen.wxA (xs k) (ys k) (zs k) i j) (6 + Gen.sig i - Gen.tau j) := by
  rw [Gen.wxA]
  refine wOrd_sum ?_
  intro t _
  exact wOrd_intMonomial k _ _ _ _ _ (by have := Gen.wxD_wt i j t; omega)
omit [CharZero k] in
lemma wOrd_wzA (i : Fin 8) (j : Fin 4) :
    WOrd (Gen.wzA (xs k) (ys k) (zs k) i j) (10 + Gen.sig i - Gen.tau j) := by
  rw [Gen.wzA]
  refine wOrd_sum ?_
  intro t _
  exact wOrd_intMonomial k _ _ _ _ _ (by have := Gen.wzD_wt i j t; omega)
def Rep (F : Sk k) (N : ℕ) : Prop :=
  ∃ (q : Fin 8 → PowerSeries k) (c : Fin 4 → Sk k),
    F = (∑ i, iotaS k (q i) * hhS k i) + ∑ j, c j * ffS k j ∧
      (∀ i, YOrd (q i) (N - Gen.sig i)) ∧ (∀ j, WOrd (c j) (N - Gen.tau j))
omit [CharZero k] in
lemma Rep_mono {F : Sk k} {N N' : ℕ} (h : N' ≤ N) (hF : Rep k F N) : Rep k F N' := by
  obtain ⟨q, c, hq, h1, h2⟩ := hF
  exact ⟨q, c, hq, fun i => yOrd_mono (by omega) (h1 i), fun j => wOrd_mono (by omega) (h2 j)⟩
omit [CharZero k] in
lemma Rep_zero (N : ℕ) : Rep k 0 N := by
  refine ⟨0, 0, ?_, fun i => yOrd_of_zero, fun j => wOrd_of_zero⟩
  simp
omit [CharZero k] in
lemma Rep_add {F G : Sk k} {N : ℕ} (hF : Rep k F N) (hG : Rep k G N) : Rep k (F + G) N := by
  obtain ⟨q, c, hq, h1, h2⟩ := hF
  obtain ⟨q', c', hq', h1', h2'⟩ := hG
  refine ⟨q + q', c + c', ?_, fun i => yOrd_add (h1 i) (h1' i),
    fun j => wOrd_add (h2 j) (h2' j)⟩
  rw [hq, hq']
  simp only [Pi.add_apply, map_add, Fin.sum_univ_eight, Fin.sum_univ_four, add_mul]
  ring
omit [CharZero k] in
lemma Rep_smul {F : Sk k} {N : ℕ} (a : k) (hF : Rep k F N) :
    Rep k (MvPowerSeries.C a * F) N := by
  obtain ⟨q, c, hq, h1, h2⟩ := hF
  refine ⟨fun i => PowerSeries.C a * q i, fun j => MvPowerSeries.C a * c j, ?_,
    fun i => yOrd_mul' (by omega) (yOrd_zero _) (h1 i),
    fun j => wOrd_mul' (by omega) (wOrd_zero _) (h2 j)⟩
  rw [hq]
  simp only [map_mul, iotaS_C, Fin.sum_univ_eight, Fin.sum_univ_four]
  ring
omit [CharZero k] in
lemma Rep_sum {ι : Type*} {s : Finset ι} {F : ι → Sk k} {N : ℕ}
    (h : ∀ i ∈ s, Rep k (F i) N) : Rep k (∑ i ∈ s, F i) N := by
  classical
  induction s using Finset.induction with
  | empty => simpa using Rep_zero k N
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact Rep_add k (h a (Finset.mem_insert_self _ _))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
omit [CharZero k] in
lemma Rep_one : Rep k 1 0 := by
  refine ⟨![1, 0, 0, 0, 0, 0, 0, 0], 0, ?_,
    fun i => yOrd_mono (by omega) (yOrd_zero _), fun _ => wOrd_of_zero⟩
  simp [Fin.sum_univ_eight, hhS]
omit [CharZero k] in
lemma Rep_mul_ys {F : Sk k} {N : ℕ} (h : Rep k F N) : Rep k (ys k * F) (N + 8) := by
  obtain ⟨q, c, hq, h1, h2⟩ := h
  refine ⟨fun i => PowerSeries.X * q i, fun j => ys k * c j, ?_, ?_, ?_⟩
  · rw [hq]
    simp only [map_mul, iotaS_X, Fin.sum_univ_eight, Fin.sum_univ_four]
    ring
  · intro i
    exact yOrd_mul' (m := 8) (n := N - Gen.sig i) (by omega)
      (by simpa using yOrd_X_pow (k := k) 1) (h1 i)
  · intro j
    exact wOrd_mul' (by omega) (wOrd_ys k) (h2 j)
lemma Rep_mul_xs {F : Sk k} {N : ℕ} (h : Rep k F N) : Rep k (xs k * F) (N + 6) := by
  obtain ⟨q, c, hq, h1, h2⟩ := h
  refine ⟨fun j => PowerSeries.C ((18 : k)⁻¹) * ∑ i, q i * qxP k i j,
    fun j => xs k * c j + MvPowerSeries.C ((18 : k)⁻¹) *
      ∑ i, iotaS k (q i) * Gen.wxA (xs k) (ys k) (zs k) i j, ?_, ?_, ?_⟩
  · have hq' : ∀ j : Fin 8, iotaS k (PowerSeries.C ((18 : k)⁻¹) * ∑ i, q i * qxP k i j) =
        MvPowerSeries.C ((18 : k)⁻¹) * ∑ i, iotaS k (q i) * Gen.qxA (ys k) i j := by
      intro j
      rw [map_mul, iotaS_C, map_sum]
      simp only [map_mul, iotaS_qxP]
    simp only [hq']
    have e0 := key_x_div k 0
    have e1 := key_x_div k 1
    have e2 := key_x_div k 2
    have e3 := key_x_div k 3
    have e4 := key_x_div k 4
    have e5 := key_x_div k 5
    have e6 := key_x_div k 6
    have e7 := key_x_div k 7
    simp only [Fin.sum_univ_eight, Fin.sum_univ_four] at hq e0 e1 e2 e3 e4 e5 e6 e7 ⊢
    linear_combination (xs k) * hq + iotaS k (q 0) * e0 + iotaS k (q 1) * e1 +
      iotaS k (q 2) * e2 + iotaS k (q 3) * e3 + iotaS k (q 4) * e4 + iotaS k (q 5) * e5 +
      iotaS k (q 6) * e6 + iotaS k (q 7) * e7
  · intro j
    refine yOrd_mul' (m := 0) (n := (N + 6) - Gen.sig j) (by omega) (yOrd_zero _) ?_
    refine yOrd_sum ?_
    intro i _
    exact yOrd_mul' (by have := Gen.qxD_wt i j; omega) (h1 i) (yOrd_qxP k i j)
  · intro j
    refine wOrd_add (wOrd_mul' (by omega) (wOrd_xs k) (h2 j)) ?_
    refine wOrd_mul' (m := 0) (n := (N + 6) - Gen.tau j) (by omega) (wOrd_zero _) ?_
    refine wOrd_sum ?_
    intro i _
    exact wOrd_mul' (by omega) (wOrd_iotaS k (h1 i)) (wOrd_wxA k i j)
lemma Rep_mul_zs {F : Sk k} {N : ℕ} (h : Rep k F N) : Rep k (zs k * F) (N + 10) := by
  obtain ⟨q, c, hq, h1, h2⟩ := h
  refine ⟨fun j => PowerSeries.C ((18 : k)⁻¹) * ∑ i, q i * qzP k i j,
    fun j => zs k * c j + MvPowerSeries.C ((18 : k)⁻¹) *
      ∑ i, iotaS k (q i) * Gen.wzA (xs k) (ys k) (zs k) i j, ?_, ?_, ?_⟩
  · have hq' : ∀ j : Fin 8, iotaS k (PowerSeries.C ((18 : k)⁻¹) * ∑ i, q i * qzP k i j) =
        MvPowerSeries.C ((18 : k)⁻¹) * ∑ i, iotaS k (q i) * Gen.qzA (ys k) i j := by
      intro j
      rw [map_mul, iotaS_C, map_sum]
      simp only [map_mul, iotaS_qzP]
    simp only [hq']
    have e0 := key_z_div k 0
    have e1 := key_z_div k 1
    have e2 := key_z_div k 2
    have e3 := key_z_div k 3
    have e4 := key_z_div k 4
    have e5 := key_z_div k 5
    have e6 := key_z_div k 6
    have e7 := key_z_div k 7
    simp only [Fin.sum_univ_eight, Fin.sum_univ_four] at hq e0 e1 e2 e3 e4 e5 e6 e7 ⊢
    linear_combination (zs k) * hq + iotaS k (q 0) * e0 + iotaS k (q 1) * e1 +
      iotaS k (q 2) * e2 + iotaS k (q 3) * e3 + iotaS k (q 4) * e4 + iotaS k (q 5) * e5 +
      iotaS k (q 6) * e6 + iotaS k (q 7) * e7
  · intro j
    refine yOrd_mul' (m := 0) (n := (N + 10) - Gen.sig j) (by omega) (yOrd_zero _) ?_
    refine yOrd_sum ?_
    intro i _
    exact yOrd_mul' (by have := Gen.qzD_wt i j; omega) (h1 i) (yOrd_qzP k i j)
  · intro j
    refine wOrd_add (wOrd_mul' (by omega) (wOrd_zs k) (h2 j)) ?_
    refine wOrd_mul' (m := 0) (n := (N + 10) - Gen.tau j) (by omega) (wOrd_zero _) ?_
    refine wOrd_sum ?_
    intro i _
    exact wOrd_mul' (by omega) (wOrd_iotaS k (h1 i)) (wOrd_wzA k i j)
lemma Rep_pow_zs (c : ℕ) : Rep k (zs k ^ c) (10 * c) := by
  induction c with
  | zero => simpa using Rep_one k
  | succ c ih =>
      have h := Rep_mul_zs k ih
      rw [← pow_succ'] at h
      exact Rep_mono k (by omega) h
lemma Rep_pow_ys_zs (b c : ℕ) : Rep k (ys k ^ b * zs k ^ c) (8 * b + 10 * c) := by
  induction b with
  | zero => simpa using Rep_pow_zs k c
  | succ b ih =>
      have h := Rep_mul_ys k ih
      rw [← mul_assoc, ← pow_succ'] at h
      exact Rep_mono k (by omega) h
lemma Rep_monomial (a b c : ℕ) :
    Rep k (xs k ^ a * ys k ^ b * zs k ^ c) (6 * a + 8 * b + 10 * c) := by
  rw [mul_assoc]
  induction a with
  | zero => simpa using Rep_pow_ys_zs k b c
  | succ a ih =>
      have h := Rep_mul_xs k ih
      rw [← mul_assoc, ← pow_succ'] at h
      exact Rep_mono k (by omega) h
lemma Rep_monomial_coeff (d : Fin 3 →₀ ℕ) (a : k) :
    Rep k (MvPowerSeries.monomial (dd (d 0) (d 1) (d 2)) a) (wt d) := by
  have h1 : (xs k ^ (d 0) * ys k ^ (d 1) * zs k ^ (d 2) : Sk k)
      = MvPowerSeries.monomial (dd (d 0) (d 1) (d 2)) 1 := (monomial_dd _ _ _).symm
  have hmon : MvPowerSeries.monomial (dd (d 0) (d 1) (d 2)) a
      = MvPowerSeries.C a * (xs k ^ (d 0) * ys k ^ (d 1) * zs k ^ (d 2)) := by
    rw [h1, show (MvPowerSeries.C a : Sk k) = MvPowerSeries.monomial 0 a from rfl,
      MvPowerSeries.monomial_mul_monomial, zero_add, mul_one]
  rw [hmon]
  refine Rep_smul k a (Rep_mono k ?_ (Rep_monomial k (d 0) (d 1) (d 2)))
  simp [wt]
lemma Rep_step (F : Sk k) (n : ℕ) (hF : WOrd F n) :
    ∃ D : Sk k × (Fin 8 → PowerSeries k) × (Fin 4 → Sk k),
      WOrd D.1 (n + 1) ∧ (∀ i, YOrd (D.2.1 i) (n - Gen.sig i)) ∧
        (∀ j, WOrd (D.2.2 j) (n - Gen.tau j)) ∧
        F - D.1 = (∑ i, iotaS k (D.2.1 i) * hhS k i) + ∑ j, D.2.2 j * ffS k j := by
  classical
  set S := ∑ p ∈ En n, MvPowerSeries.monomial (dd p.1 p.2.1 p.2.2)
    (coeff (dd p.1 p.2.1 p.2.2) F) with hS
  have hrep : Rep k S n := by
    refine Rep_sum k ?_
    intro p hp
    have hw : 6 * p.1 + 8 * p.2.1 + 10 * p.2.2 = n := mem_En hp
    have hd : dd p.1 p.2.1 p.2.2 = dd (dd p.1 p.2.1 p.2.2 0) (dd p.1 p.2.1 p.2.2 1)
        (dd p.1 p.2.1 p.2.2 2) := by simp
    rw [hd]
    refine Rep_mono k ?_ (Rep_monomial_coeff k (dd p.1 p.2.1 p.2.2) _)
    simp [wt, hw]
  obtain ⟨q, c, heq, h1, h2⟩ := hrep
  refine ⟨⟨F - S, q, c⟩, wOrd_sub_top_part F n hF, h1, h2, ?_⟩
  simpa using heq
open Classical in
/-- One step of the division algorithm as a function of the remainder. -/
def stepFun (n : ℕ) (F : Sk k) : Sk k × (Fin 8 → PowerSeries k) × (Fin 4 → Sk k) :=
  if h : WOrd F n then (Rep_step k F n h).choose else (0, 0, 0)
def iter (F : Sk k) : ℕ → Sk k × (Fin 8 → PowerSeries k) × (Fin 4 → Sk k)
  | 0 => (F, 0, 0)
  | (s + 1) => stepFun k s (iter F s).1
end MohP3.FormalLocal



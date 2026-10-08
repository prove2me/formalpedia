-- Prove2me | solution 1 for AlgMechDesign.Randomized.randomly_biased_min_work
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T07:39:54.345592+00:00
-- url     : https://prove2.me/submissions/c8fec28c-875b-4d79-9713-84d20f80b38f

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork



namespace AlgMechDesign.Randomized
open Finset Classical

lemma rb_other_other (v : Fin 2) : other (other v) = v := by fin_cases v <;> decide
lemma rb_other0 : other 0 = 1 := by decide
lemma rb_other1 : other 1 = 0 := by decide
lemma rb_fin2 : ∀ v : Fin 2, v = 0 ∨ v = 1 := by decide

lemma rb_key (D0 E0 F0 G0 a00 a10 b00 b10 D1 E1 F1 G1 a01 a11 b01 b11 T : ℝ)
    (n1 : 0 ≤ D0) (n2 : 0 ≤ E0) (n3 : 0 ≤ F0) (n4 : 0 ≤ G0) (n5 : 0 ≤ a00) (n6 : 0 ≤ a10)
    (n7 : 0 ≤ b00) (n8 : 0 ≤ b10)
    (m1 : 0 ≤ D1) (m2 : 0 ≤ E1) (m3 : 0 ≤ F1) (m4 : 0 ≤ G1) (m5 : 0 ≤ a01) (m6 : 0 ≤ a11)
    (m7 : 0 ≤ b01) (m8 : 0 ≤ b11)
    (h1 : D0 + F0 + a00 + a10 ≤ T) (h2 : G1 + E1 + b01 + b11 ≤ T)
    (e0 : E0 ≤ 3/4 * F0) (d0 : D0 ≤ 3/4 * G0) (hb0 : b00 + b10 ≤ 4/3 * (a00 + a10))
    (ha0 : a00 + a10 ≤ 4/3 * (b00 + b10))
    (e1 : E1 ≤ 3/4 * F1) (d1 : D1 ≤ 3/4 * G1) (hb1 : b01 + b11 ≤ 4/3 * (a01 + a11))
    (ha1 : a01 + a11 ≤ 4/3 * (b01 + b11)) :
    max (D0 + a00 + (D1 + a01)) (E0 + b10 + (E1 + b11)) +
    max (D0 + a10 + (D1 + a01)) (E0 + b00 + (E1 + b11)) +
    max (D0 + a00 + (D1 + a11)) (E0 + b10 + (E1 + b01)) +
    max (D0 + a10 + (D1 + a11)) (E0 + b00 + (E1 + b01)) ≤ 7 * T := by
  rcases max_cases (D0 + a00 + (D1 + a01)) (E0 + b10 + (E1 + b11)) with ⟨q1, _⟩ | ⟨q1, _⟩ <;>
  rcases max_cases (D0 + a10 + (D1 + a01)) (E0 + b00 + (E1 + b11)) with ⟨q2, _⟩ | ⟨q2, _⟩ <;>
  rcases max_cases (D0 + a00 + (D1 + a11)) (E0 + b10 + (E1 + b01)) with ⟨q3, _⟩ | ⟨q3, _⟩ <;>
  rcases max_cases (D0 + a10 + (D1 + a11)) (E0 + b00 + (E1 + b01)) with ⟨q4, _⟩ | ⟨q4, _⟩ <;>
  rw [q1, q2, q3, q4] <;> linarith


noncomputable def rbX {k : ℕ} (t : Fin 2 → Fin k → ℝ) (j : Fin k) (v : Fin 2) : Fin 2 :=
  if t v j ≤ 4/3 * t (other v) j then v else other v

lemma rb_alloc_eq {k : ℕ} (t : Fin 2 → Fin k → ℝ) (s : Fin k → Fin 2) (j : Fin k) :
    rbmwAlloc s t j = rbX t j (s j) := rfl

noncomputable def rbP {k : ℕ} (t : Fin 2 → Fin k → ℝ) (v : Fin k → Fin 2) (j : Fin k) : ℝ :=
  if rbX t j (v j) = 0 then t 0 j else 0
noncomputable def rbQ {k : ℕ} (t : Fin 2 → Fin k → ℝ) (v : Fin k → Fin 2) (j : Fin k) : ℝ :=
  if rbX t j (v j) = 1 then t 1 j else 0
noncomputable def rbD {k : ℕ} (t : Fin 2 → Fin k → ℝ) (j : Fin k) : ℝ :=
  if t 1 j ≤ 4/3 * t 0 j then 0 else t 0 j
noncomputable def rbG {k : ℕ} (t : Fin 2 → Fin k → ℝ) (j : Fin k) : ℝ :=
  if t 1 j ≤ 4/3 * t 0 j then 0 else t 1 j
noncomputable def rbE {k : ℕ} (t : Fin 2 → Fin k → ℝ) (j : Fin k) : ℝ :=
  if t 0 j ≤ 4/3 * t 1 j then 0 else t 1 j
noncomputable def rbF {k : ℕ} (t : Fin 2 → Fin k → ℝ) (j : Fin k) : ℝ :=
  if t 0 j ≤ 4/3 * t 1 j then 0 else t 0 j
noncomputable def rbR {k : ℕ} (t : Fin 2 → Fin k → ℝ) (v : Fin k → Fin 2) (c i : Fin 2)
    (j : Fin k) : ℝ :=
  if t 0 j ≤ 4/3 * t 1 j ∧ t 1 j ≤ 4/3 * t 0 j ∧ v j = c then t i j else 0

lemma rb_task {k : ℕ} (t : Fin 2 → Fin k → ℝ) (v : Fin k → Fin 2) (j : Fin k)
    (ha : 0 < t 0 j) (hb : 0 < t 1 j) :
    rbP t v j = rbD t j + rbR t v 0 0 j ∧
    rbQ t v j = rbE t j + rbR t v 1 1 j ∧
    t 0 j = rbD t j + rbF t j + rbR t v 0 0 j + rbR t v 1 0 j ∧
    t 1 j = rbG t j + rbE t j + rbR t v 0 1 j + rbR t v 1 1 j ∧
    rbE t j ≤ 3/4 * rbF t j ∧ rbD t j ≤ 3/4 * rbG t j ∧
    rbR t v 0 1 j + rbR t v 1 1 j ≤ 4/3 * (rbR t v 0 0 j + rbR t v 1 0 j) ∧
    rbR t v 0 0 j + rbR t v 1 0 j ≤ 4/3 * (rbR t v 0 1 j + rbR t v 1 1 j) ∧
    0 ≤ rbD t j ∧ 0 ≤ rbE t j ∧ 0 ≤ rbF t j ∧ 0 ≤ rbG t j ∧
    0 ≤ rbR t v 0 0 j ∧ 0 ≤ rbR t v 1 0 j ∧ 0 ≤ rbR t v 0 1 j ∧ 0 ≤ rbR t v 1 1 j := by
  unfold rbP rbQ rbD rbE rbF rbG rbR rbX
  by_cases c1 : t 0 j ≤ 4/3 * t 1 j <;> by_cases c2 : t 1 j ≤ 4/3 * t 0 j
  all_goals first
    | (exfalso; push_neg at c1 c2; linarith)
    | (rcases rb_fin2 (v j) with h | h <;>
        simp [h, c1, c2, rb_other0, rb_other1] <;> (try refine ⟨?_, ?_, ?_⟩) <;> (try refine ⟨?_, ?_⟩) <;>
        (try push_neg at c1 c2) <;> linarith)


noncomputable def rbS {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f : Fin k → ℝ) : ℝ :=
  ∑ j, if y j = i then f j else 0

lemma rbS_eq2 {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f g h : Fin k → ℝ)
    (H : ∀ j, f j = g j + h j) : rbS y i f = rbS y i g + rbS y i h := by
  unfold rbS; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
  split_ifs <;> simp [H j]

lemma rbS_eq4 {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f g1 g2 g3 g4 : Fin k → ℝ)
    (H : ∀ j, f j = g1 j + g2 j + g3 j + g4 j) :
    rbS y i f = rbS y i g1 + rbS y i g2 + rbS y i g3 + rbS y i g4 := by
  unfold rbS; rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  split_ifs <;> simp [H j]

lemma rbS_le1 {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f g : Fin k → ℝ) (c : ℝ)
    (H : ∀ j, f j ≤ c * g j) : rbS y i f ≤ c * rbS y i g := by
  unfold rbS; rw [mul_sum]; apply sum_le_sum; intro j _
  split_ifs <;> simp [H j]

lemma rbS_le2 {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f1 f2 g1 g2 : Fin k → ℝ) (c : ℝ)
    (H : ∀ j, f1 j + f2 j ≤ c * (g1 j + g2 j)) :
    rbS y i f1 + rbS y i f2 ≤ c * (rbS y i g1 + rbS y i g2) := by
  unfold rbS; rw [← sum_add_distrib, ← sum_add_distrib, mul_sum]; apply sum_le_sum; intro j _
  split_ifs <;> simp [H j]

lemma rbS_nonneg {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (f : Fin k → ℝ)
    (H : ∀ j, 0 ≤ f j) : 0 ≤ rbS y i f := by
  unfold rbS; apply sum_nonneg; intro j _
  split_ifs <;> simp [H j]

lemma rb_makespan_two {k : ℕ} (t : Fin 2 → Fin k → ℝ) (x : Fin k → Fin 2) :
    makespan t x = max (load t x 0) (load t x 1) := by
  unfold makespan
  apply le_antisymm
  · apply Finset.sup'_le; intro i _
    rcases rb_fin2 i with h | h <;> subst h
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply max_le
    · exact Finset.le_sup' (load t x) (mem_univ 0)
    · exact Finset.le_sup' (load t x) (mem_univ 1)

lemma rb_load_eq {k : ℕ} (t : Fin 2 → Fin k → ℝ) (x : Fin k → Fin 2) (i : Fin 2) :
    load t x i = ∑ j, if x j = i then t i j else 0 := by
  unfold load; rw [Finset.sum_filter]

lemma rb_load_split {k : ℕ} (t : Fin 2 → Fin k → ℝ) (y w w0 w1 : Fin k → Fin 2)
    (hw : ∀ j, w j = if y j = 0 then w0 j else w1 j) :
    load t (rbmwAlloc w t) 0 = rbS y 0 (rbP t w0) + rbS y 1 (rbP t w1) ∧
    load t (rbmwAlloc w t) 1 = rbS y 0 (rbQ t w0) + rbS y 1 (rbQ t w1) := by
  constructor <;>
  · rw [rb_load_eq]; unfold rbS; rw [← sum_add_distrib]; apply sum_congr rfl; intro j _
    rcases rb_fin2 (y j) with h | h <;> simp [hw j, h, rbP, rbQ, rb_alloc_eq]

lemma rb_R_flip {k : ℕ} (t : Fin 2 → Fin k → ℝ) (s : Fin k → Fin 2) (c i : Fin 2) :
    rbR t (fun j => other (s j)) c i = rbR t s (other c) i := by
  funext j; unfold rbR
  rcases rb_fin2 (s j) with h | h <;> rcases rb_fin2 c with h' | h' <;>
    simp [h, h', rb_other0, rb_other1]

lemma rb_quad {k : ℕ} (t : Fin 2 → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin 2)
    (s w1 w2 w3 : Fin k → Fin 2)
    (h1 : ∀ j, w1 j = if y j = 0 then other (s j) else s j)
    (h2 : ∀ j, w2 j = if y j = 0 then s j else other (s j))
    (h3 : ∀ j, w3 j = if y j = 0 then other (s j) else other (s j)) :
    makespan t (rbmwAlloc s t) + makespan t (rbmwAlloc w1 t) + makespan t (rbmwAlloc w2 t) +
      makespan t (rbmwAlloc w3 t) ≤ 7 * makespan t y := by
  set sb : Fin k → Fin 2 := fun j => other (s j) with hsb
  obtain ⟨l0, l1⟩ := rb_load_split t y s s s (fun j => by split_ifs <;> rfl)
  obtain ⟨l10, l11⟩ := rb_load_split t y w1 sb s h1
  obtain ⟨l20, l21⟩ := rb_load_split t y w2 s sb h2
  obtain ⟨l30, l31⟩ := rb_load_split t y w3 sb sb h3
  simp only [rb_makespan_two, l0, l1, l10, l11, l20, l21, l30, l31]
  have hT0 : rbS y 0 (fun j => t 0 j) ≤ max (load t y 0) (load t y 1) := by
    rw [rb_load_eq]; exact le_max_left _ _
  have hT1 : rbS y 1 (fun j => t 1 j) ≤ max (load t y 0) (load t y 1) := by
    rw [rb_load_eq t y 1]; exact le_max_right _ _
  have P := fun v j => rb_task t v j (ht 0 j) (ht 1 j)
  have hRf := rb_R_flip t s
  have Pb : ∀ j, rbP t sb j = rbD t j + rbR t s 1 0 j := fun j => by
    rw [(P sb j).1, hRf]; rfl
  have Qb : ∀ j, rbQ t sb j = rbE t j + rbR t s 0 1 j := fun j => by
    rw [(P sb j).2.1, hRf]; rfl
  have key := fun i => And.intro
    (rbS_eq2 y i _ _ _ (fun j => (P s j).1)) <| And.intro
    (rbS_eq2 y i _ _ _ (fun j => (P s j).2.1)) <| And.intro
    (rbS_eq2 y i _ _ _ Pb) <| And.intro (rbS_eq2 y i _ _ _ Qb) <| And.intro
    (rbS_eq4 y i _ _ _ _ _ (fun j => (P s j).2.2.1)) <| And.intro
    (rbS_eq4 y i _ _ _ _ _ (fun j => (P s j).2.2.2.1)) <| And.intro
    (rbS_le1 y i _ _ _ (fun j => (P s j).2.2.2.2.1)) <| And.intro
    (rbS_le1 y i _ _ _ (fun j => (P s j).2.2.2.2.2.1)) <| And.intro
    (rbS_le2 y i _ _ _ _ _ (fun j => (P s j).2.2.2.2.2.2.1)) <| And.intro
    (rbS_le2 y i _ _ _ _ _ (fun j => (P s j).2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.2.2.2.1)) <| And.intro
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1))
    (rbS_nonneg y i _ (fun j => (P s j).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2))
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18⟩ := key 0
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18⟩ := key 1
  rw [a1, a2, a3, a4, b1, b2, b3, b4]
  rw [a5] at hT0; rw [b6] at hT1
  exact rb_key _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a11 a12 a13 a14 a15 a16 a17 a18
    b11 b12 b13 b14 b15 b16 b17 b18 hT0 hT1 a7 a8 a9 a10 b7 b8 b9 b10


def rbFlip {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) : Equiv.Perm (Fin k → Fin 2) :=
  Function.Involutive.toPerm (fun s j => if y j = i then other (s j) else s j) (by
    intro s; funext j; by_cases h : y j = i <;> simp [h, rb_other_other])

lemma rbFlip_apply {k : ℕ} (y : Fin k → Fin 2) (i : Fin 2) (s : Fin k → Fin 2) (j : Fin k) :
    rbFlip y i s j = if y j = i then other (s j) else s j := rfl

theorem rbmw_approx_core {k : ℕ} (t : Fin 2 → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin 2) :
    expMakespan t ≤ 7 / 4 * makespan t y := by
  set M : (Fin k → Fin 2) → ℝ := fun s => makespan t (rbmwAlloc s t) with hM
  have e0 : ∑ s, M s = ∑ s, M (rbFlip y 0 s) := (Equiv.sum_comp (rbFlip y 0) M).symm
  have e1 : ∑ s, M s = ∑ s, M (rbFlip y 1 s) := (Equiv.sum_comp (rbFlip y 1) M).symm
  have e2 : ∑ s, M s = ∑ s, M (rbFlip y 0 (rbFlip y 1 s)) :=
    (Equiv.sum_comp ((rbFlip y 1).trans (rbFlip y 0)) M).symm
  have hq : ∀ s, M s + M (rbFlip y 0 s) + M (rbFlip y 1 s) + M (rbFlip y 0 (rbFlip y 1 s))
      ≤ 7 * makespan t y := by
    intro s
    apply rb_quad t ht y s
    · intro j; simp [rbFlip_apply]
    · intro j; rcases rb_fin2 (y j) with h | h <;> simp [rbFlip_apply, h]
    · intro j; rcases rb_fin2 (y j) with h | h <;> simp [rbFlip_apply, h]
  have hsum : 4 * ∑ s, M s ≤ ∑ _s : Fin k → Fin 2, 7 * makespan t y := by
    calc 4 * ∑ s, M s = ∑ s, (M s + M (rbFlip y 0 s) + M (rbFlip y 1 s) +
          M (rbFlip y 0 (rbFlip y 1 s))) := by
          rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← e0, ← e1, ← e2]; ring
      _ ≤ _ := sum_le_sum (fun s _ => hq s)
  rw [sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul] at hsum
  unfold expMakespan
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [show ∑ s : Fin k → Fin 2, makespan t (rbmwAlloc s t) = ∑ s, M s from rfl]
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hp]
  push_cast at hsum
  nlinarith


noncomputable def rbU {k : ℕ} (s : Fin k → Fin 2) (d : Fin 2 → Fin k → ℝ) (i : Fin 2)
    (ti : Fin k → ℝ) (j : Fin k) : ℝ :=
  if rbmwAlloc s d j = i then
    ((if i = s j then 4/3 * d (other (s j)) j else (4/3)⁻¹ * d (s j) j) - ti j) else 0

lemma rb_util_eq {k : ℕ} (s : Fin k → Fin 2) (d : Fin 2 → Fin k → ℝ) (i : Fin 2)
    (ti : Fin k → ℝ) :
    utility (rbmwAlloc s) (rbmwPay s) d i ti = ∑ j, rbU s d i ti j := by
  unfold utility rbmwPay bmwPay rbU
  rw [Finset.sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl; intro j _
  simp only [rbmwAlloc]
  by_cases h : bmwAlloc (4 / 3) s d j = i <;> simp only [h, if_true, if_false] <;> ring

lemma rb_task_truth {k : ℕ} (s : Fin k → Fin 2) (d : Fin 2 → Fin k → ℝ) (i : Fin 2)
    (ti ti' : Fin k → ℝ) (j : Fin k) :
    rbU s (Function.update d i ti') i ti j ≤ rbU s (Function.update d i ti) i ti j := by
  unfold rbU rbmwAlloc bmwAlloc
  rcases rb_fin2 i with hi | hi <;> rcases rb_fin2 (s j) with h | h <;>
    simp [hi, h, Function.update_apply, rb_other0, rb_other1] <;> split_ifs <;> linarith

lemma rb_truthful {k : ℕ} (s : Fin k → Fin 2) : IsTruthful (rbmwAlloc s) (rbmwPay s) := by
  intro d _ i ti ti' _ _
  rw [rb_util_eq, rb_util_eq]
  exact sum_le_sum (fun j _ => rb_task_truth s d i ti ti' j)

theorem rb_strong_core {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay := by
  refine ⟨fun s => rb_truthful s, ?_⟩
  intro i ti ti' hti hti' hne
  obtain ⟨j, hj⟩ : ∃ j, ti' j ≠ ti j := by
    by_contra hc; push_neg at hc; exact hne (funext hc)
  set m : ℝ := (ti j + ti' j) / 2 with hm
  have hmpos : 0 < m := by have := hti j; have := hti' j; rw [hm]; linarith
  refine ⟨fun _ => i, fun _ _ => 3/4 * m, fun _ _ => by positivity, ?_⟩
  rw [rb_util_eq, rb_util_eq]
  apply Finset.sum_lt_sum (fun j' _ => rb_task_truth _ _ i ti ti' j')
  refine ⟨j, mem_univ _, ?_⟩
  unfold rbU rbmwAlloc bmwAlloc
  rcases lt_or_gt_of_ne hj with hlt | hlt <;>
  rcases rb_fin2 i with hi | hi <;>
    simp [hi, Function.update_apply, rb_other0, rb_other1] <;> split_ifs <;> linarith

end AlgMechDesign.Randomized

open AlgMechDesign.Randomized


theorem solution {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay ∧
      ∀ t : Fin 2 → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin 2,
        expMakespan t ≤ 7 / 4 * makespan t y := by
  exact ⟨rb_strong_core, fun t ht y => rbmw_approx_core t ht y⟩

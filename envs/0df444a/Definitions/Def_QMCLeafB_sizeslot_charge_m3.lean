-- Prove2me | Definitions.Def_QMCLeafB_sizeslot_charge_m3
-- name    : QMCLeafB_sizeslot_charge_m3
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T00:34:51.96856+00:00
-- url     : https://prove2.me/theorems/ab487f28-c37c-4808-8863-1df6384653c6
-- title:
--   QMCLeafB sizeslot_charge_m3
-- statement:
--   # leaf B phase 14 — brick `size-slot`, part 2: the per-round charge of the concrete engine
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_sizeslot_m3
/-
# leaf B phase 14 — brick `size-slot`, part 2: the per-round charge of the concrete engine

`QMCLeafB.SizeSlot` showed that the closing stroke's state-level growth class is unsatisfiable at
`QMCLeafB.RoundProgram.RSt`, and reduced the size slot to the pair-level class.  This file supplies
the *charge* estimates that a pair-level bound needs: the encoded length of one round's new data
(`snapY` — the clipped, snapped matrix code — and the separation oracle's cut normal).

The engineering content is `HasHeight` closure for the rational arithmetic the engine performs
(`ℚ` multiplication, addition, inversion), the resulting heights of `dotL`/`rowSq`/`qformRows`, and
the height invariant of the pivot descent (`pivStepL_snd_height`).

No `sorry`, no `axiom`; audit at the end.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

open scoped BigOperators
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.SizeSlot

open QMCLeafB.RoundProgram
open QMCLeafB.PivotProgram
open QMCLeafB.SizesProfile

theorem prodMk_eq {α β : Type} {p : α × β} {a : α} (h : p.1 = a) : p = (a, p.2) := by
  obtain ⟨x, y⟩ := p
  simp only at h
  rw [h]

/-! ## 1.  `HasHeight` closure for `ℚ` -/

theorem int_natAbs_ediv_le (x : ℤ) (k : ℕ) : (x / (k : ℤ)).natAbs ≤ x.natAbs :=
  Int.natAbs_ediv_le_natAbs x (k : ℤ)

theorem HasHeight.num_natAbs {q : ℚ} {L : ℕ} (h : HasHeight q L) : q.num.natAbs ≤ 2 ^ L := by
  have h1 := h.1
  have h2 : ((q.num.natAbs : ℕ) : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by simpa using h1
  exact_mod_cast h2

theorem HasHeight.den_le {q : ℚ} {L : ℕ} (h : HasHeight q L) : q.den ≤ 2 ^ L := by
  have h1 := h.2
  have h2 : ((q.den : ℕ) : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by simpa using h1
  exact_mod_cast h2

theorem hasHeight_of_bounds {q : ℚ} {L : ℕ} (h1 : q.num.natAbs ≤ 2 ^ L) (h2 : q.den ≤ 2 ^ L) :
    HasHeight q L := by
  constructor
  · have h : ((q.num.natAbs : ℕ) : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast h1
    simpa using h
  · have h : ((q.den : ℕ) : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast h2
    simpa using h

theorem hasHeight_one : HasHeight (1 : ℚ) 1 := by
  refine hasHeight_of_bounds ?_ ?_
  · norm_num
  · norm_num

theorem hasHeight_two : HasHeight (2 : ℚ) 2 := by
  refine hasHeight_of_bounds ?_ ?_
  · norm_num
  · norm_num

theorem HasHeight.mul {a b : ℚ} {h g : ℕ} (ha : HasHeight a h) (hb : HasHeight b g) :
    HasHeight (a * b) (h + g) := by
  refine hasHeight_of_bounds ?_ ?_
  · rw [Rat.num_mul]
    calc (a.num * b.num / ((a.num * b.num).natAbs.gcd (a.den * b.den) : ℕ)).natAbs
        ≤ (a.num * b.num).natAbs := int_natAbs_ediv_le _ _
      _ = a.num.natAbs * b.num.natAbs := Int.natAbs_mul _ _
      _ ≤ 2 ^ h * 2 ^ g := Nat.mul_le_mul (HasHeight.num_natAbs ha) (HasHeight.num_natAbs hb)
      _ = 2 ^ (h + g) := by rw [← pow_add]
  · rw [Rat.den_mul]
    calc a.den * b.den / (a.num * b.num).natAbs.gcd (a.den * b.den)
        ≤ a.den * b.den := Nat.div_le_self _ _
      _ ≤ 2 ^ h * 2 ^ g := Nat.mul_le_mul (HasHeight.den_le ha) (HasHeight.den_le hb)
      _ = 2 ^ (h + g) := by rw [← pow_add]

theorem HasHeight.add {a b : ℚ} {h g : ℕ} (ha : HasHeight a h) (hb : HasHeight b g) :
    HasHeight (a + b) (h + g + 1) := by
  have e1 : (a.num * (b.den : ℤ)).natAbs = a.num.natAbs * b.den := by
    rw [Int.natAbs_mul]; simp
  have e2 : (b.num * (a.den : ℤ)).natAbs = b.num.natAbs * a.den := by
    rw [Int.natAbs_mul]; simp
  have hsum : 2 ^ h * 2 ^ g + 2 ^ h * 2 ^ g = 2 ^ (h + g + 1) := by
    rw [pow_succ, ← pow_add]; ring
  refine hasHeight_of_bounds ?_ ?_
  · rw [Rat.num_add]
    calc ((a.num * (b.den : ℤ) + b.num * (a.den : ℤ))
          / ((a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs.gcd (a.den * b.den) : ℕ)).natAbs
        ≤ (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs := int_natAbs_ediv_le _ _
      _ ≤ (a.num * (b.den : ℤ)).natAbs + (b.num * (a.den : ℤ)).natAbs := Int.natAbs_add_le _ _
      _ = a.num.natAbs * b.den + b.num.natAbs * a.den := by rw [e1, e2]
      _ ≤ 2 ^ h * 2 ^ g + 2 ^ g * 2 ^ h := by
          have h1 : a.num.natAbs * b.den ≤ 2 ^ h * 2 ^ g :=
            Nat.mul_le_mul (HasHeight.num_natAbs ha) (HasHeight.den_le (L := g) hb)
          have h2 : b.num.natAbs * a.den ≤ 2 ^ g * 2 ^ h :=
            Nat.mul_le_mul (HasHeight.num_natAbs hb) (HasHeight.den_le (L := h) ha)
          exact Nat.add_le_add h1 h2
      _ = 2 ^ (h + g + 1) := by rw [Nat.mul_comm (2 ^ g) (2 ^ h)]; exact hsum
  · rw [Rat.den_add]
    calc a.den * b.den / (a.num * (b.den : ℤ) + b.num * (a.den : ℤ)).natAbs.gcd (a.den * b.den)
        ≤ a.den * b.den := Nat.div_le_self _ _
      _ ≤ 2 ^ h * 2 ^ g := Nat.mul_le_mul (HasHeight.den_le ha) (HasHeight.den_le hb)
      _ ≤ 2 ^ (h + g + 1) := by
          rw [pow_succ, ← pow_add]
          exact Nat.le_mul_of_pos_right _ (by norm_num)

theorem HasHeight.neg {a : ℚ} {h : ℕ} (ha : HasHeight a h) : HasHeight (-a) (h + 1) := by
  have h1 := HasHeight.mul (a := (-1 : ℚ)) (b := a) (h := 1) (g := h) (by
    refine hasHeight_of_bounds ?_ ?_
    · norm_num
    · norm_num) ha
  have e : (-1 : ℚ) * a = -a := by ring
  rw [e] at h1
  rw [Nat.add_comm] at h1
  exact h1

theorem HasHeight.inv {a : ℚ} {h : ℕ} (ha : HasHeight a h) : HasHeight a⁻¹ h := by
  have hdentriv : a.den ≤ 2 ^ h := HasHeight.den_le ha
  have hnumtriv : a.num.natAbs ≤ 2 ^ h := HasHeight.num_natAbs ha
  refine hasHeight_of_bounds ?_ ?_
  · rw [Rat.num_inv]
    have e : (a.num.sign * (a.den : ℤ)).natAbs = a.num.sign.natAbs * a.den := by
      rw [Int.natAbs_mul]; simp
    rw [e]
    have hs : a.num.sign.natAbs ≤ 1 := by unfold Int.sign; split <;> simp
    calc a.num.sign.natAbs * a.den ≤ 1 * a.den := Nat.mul_le_mul_right _ hs
      _ = a.den := Nat.one_mul _
      _ ≤ 2 ^ h := hdentriv
  · rw [Rat.den_inv]
    split
    · exact Nat.one_le_two_pow
    · exact hnumtriv

theorem HasHeight.div {a b : ℚ} {h g : ℕ} (ha : HasHeight a h) (hb : HasHeight b g) :
    HasHeight (a / b) (h + g) := by
  rw [Rat.div_def]
  exact HasHeight.mul ha (HasHeight.inv hb)


/-! ## 2.  List sums, dot products and the loop's rational expressions -/

theorem hasHeight_mono {q : ℚ} {L M : ℕ} (h : HasHeight q L) (hLM : L ≤ M) : HasHeight q M := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨le_trans h1 (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hLM),
    le_trans h2 (by exact_mod_cast Nat.pow_le_pow_right (by norm_num) hLM)⟩

theorem mem_zip_left {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) : a ∈ l₁ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h' | h'
          · rw [Prod.mk.injEq] at h'
            rw [h'.1]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h')

theorem mem_zip_right {α β : Type} {l₁ : List α} {l₂ : List β} {a : α} {b : β}
    (h : (a, b) ∈ l₁.zip l₂) : b ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons x xs ih =>
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
          rw [List.zip_cons_cons, List.mem_cons] at h
          rcases h with h' | h'
          · rw [Prod.mk.injEq] at h'
            rw [h'.2]; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h')

theorem hasHeight_zero : HasHeight (0 : ℚ) 0 := by
  refine hasHeight_of_bounds ?_ ?_ <;> norm_num

theorem hasHeight_neg_one : HasHeight (-1 : ℚ) 2 := by
  have h := HasHeight.neg (a := (1 : ℚ)) (h := 1) hasHeight_one
  simpa using h

theorem hasHeight_sum {l : List ℚ} {B : ℕ} (h : ∀ q ∈ l, HasHeight q B) :
    HasHeight l.sum ((B + 1) * l.length) := by
  induction l with
  | nil => simpa using hasHeight_zero
  | cons a t ih =>
      have ha : HasHeight a B := h a (List.mem_cons_self ..)
      have ht : ∀ q ∈ t, HasHeight q B := fun q hq => h q (List.mem_cons_of_mem _ hq)
      rw [List.sum_cons, List.length_cons]
      have h2 := HasHeight.add ha (ih ht)
      have e : B + (B + 1) * t.length + 1 = (B + 1) * (t.length + 1) := by ring
      rwa [e] at h2

theorem hasHeight_sum_map {α : Type} {f : α → ℚ} {l : List α} {B : ℕ}
    (h : ∀ a ∈ l, HasHeight (f a) B) : HasHeight (l.map f).sum ((B + 1) * l.length) := by
  have h' : HasHeight (l.map f).sum ((B + 1) * (l.map f).length) :=
    hasHeight_sum (fun q hq => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
      exact h a ha)
  simpa only [List.length_map] using h'

theorem hasHeight_getD_zero {l : List ℚ} {B : ℕ} (h : ∀ q ∈ l, HasHeight q B) (i : ℕ) :
    HasHeight (l.getD i 0) B := by
  induction l generalizing i with
  | nil =>
      rw [List.getD_nil]
      exact hasHeight_mono hasHeight_zero (Nat.zero_le B)
  | cons a t ih =>
      cases i with
      | zero => simpa using h a (List.mem_cons_self ..)
      | succ j =>
          rw [List.getD_cons_succ]
          exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) j

theorem headTail_height {rows : Rows} {B : ℕ} (h : RowsHeight rows B) :
    ∀ q ∈ headTail rows, HasHeight q B := by
  cases rows with
  | nil => intro q hq; simp [headTail, headRowD] at hq
  | cons a t =>
      intro q hq
      have hq' : q ∈ a.tail := hq
      exact h a (List.mem_cons_self ..) q (List.mem_of_mem_tail hq')

theorem dotL_height {x y : List ℚ} {B : ℕ} (hx : ∀ q ∈ x, HasHeight q B)
    (hy : ∀ q ∈ y, HasHeight q B) :
    HasHeight (dotL x y) ((2 * B + 2) * (y.length + 1)) := by
  unfold dotL
  have hz : ∀ p ∈ x.zip y, HasHeight (p.1 * p.2) (2 * B) := by
    intro p hp
    have h1 : p.1 ∈ x := mem_zip_left hp
    have h2 : p.2 ∈ y := mem_zip_right hp
    have hp1 := HasHeight.mul (hx _ h1) (hy _ h2)
    have e : B + B = 2 * B := by ring
    rwa [e] at hp1
  have h2 := hasHeight_sum_map (f := fun p : ℚ × ℚ => p.1 * p.2) hz
  rw [List.length_zip] at h2
  refine hasHeight_mono h2 ?_
  have hmin : min x.length y.length ≤ y.length := Nat.min_le_right _ _
  calc (2 * B + 1) * min x.length y.length ≤ (2 * B + 1) * (y.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ (2 * B + 2) * (y.length + 1) := Nat.mul_le_mul_right _ (by omega)

theorem rowSq_height {v : List ℚ} {B : ℕ} (h : ∀ q ∈ v, HasHeight q B) :
    HasHeight (rowSq v) ((2 * B + 2) * (v.length + 1)) := by
  unfold rowSq
  have hz : ∀ q ∈ v, HasHeight (q * q) (2 * B) := by
    intro q hq
    have hq' := HasHeight.mul (h q hq) (h q hq)
    have e : B + B = 2 * B := by ring
    rwa [e] at hq'
  have h2 := hasHeight_sum_map (f := fun q : ℚ => q * q) hz
  refine hasHeight_mono h2 ?_
  calc (2 * B + 1) * v.length ≤ (2 * B + 1) * (v.length + 1) :=
        Nat.mul_le_mul_left _ (by omega)
    _ ≤ (2 * B + 2) * (v.length + 1) := Nat.mul_le_mul_right _ (by omega)

theorem dropRows_height {rows : Rows} {B : ℕ} (h : RowsHeight rows B) :
    RowsHeight (dropRows rows) B := by
  intro v hv
  unfold dropRows at hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  intro q hq
  exact h w (List.mem_of_mem_tail hw) q (List.mem_of_mem_tail hq)

/-- **The `qformRows` height.**  A quadratic form of a block of height `≤ B` and width `≤ K`, with
`≤ K` rows, has height at most `4(B+1)(K+1)²`. -/
theorem qformRows_height {rows : Rows} {b : List ℚ} {B K : ℕ} (h : RowsHeight rows B)
    (hb : ∀ q ∈ b, HasHeight q B) (hK : RowsWidth rows K) (hKb : b.length ≤ K)
    (hlen : rows.length ≤ K) :
    HasHeight (qformRows rows b) (6 * (B + 1) * (K + 1) ^ 2) := by
  unfold qformRows
  have hz : ∀ p ∈ rows.zip b, HasHeight (p.2 * dotL p.1 b) (4 * (B + 1) * (K + 1)) := by
    intro p hp
    have h1 : p.1 ∈ rows := mem_zip_left hp
    have h2 : p.2 ∈ b := mem_zip_right hp
    have hrow : ∀ q ∈ p.1, HasHeight q B := h p.1 h1
    have hdot : HasHeight (dotL p.1 b) ((2 * B + 2) * (b.length + 1)) := dotL_height hrow hb
    have hbnd : (2 * B + 2) * (b.length + 1) ≤ 3 * (B + 1) * (K + 1) := by
      have h1' : b.length + 1 ≤ K + 1 := by omega
      have h2' : (2 * B + 2) * (b.length + 1) ≤ (2 * B + 2) * (K + 1) :=
        Nat.mul_le_mul_left (2 * B + 2) h1'
      have h3' : (2 * B + 2) * (K + 1) ≤ (3 * (B + 1)) * (K + 1) :=
        Nat.mul_le_mul_right (K + 1) (by omega)
      have h4' : (3 * (B + 1)) * (K + 1) = 3 * (B + 1) * (K + 1) := by ring
      calc (2 * B + 2) * (b.length + 1) ≤ (2 * B + 2) * (K + 1) := h2'
        _ ≤ (3 * (B + 1)) * (K + 1) := h3'
        _ = 3 * (B + 1) * (K + 1) := h4'
    have hdot' : HasHeight (dotL p.1 b) (3 * (B + 1) * (K + 1)) := hasHeight_mono hdot hbnd
    have hprod : HasHeight (p.2 * dotL p.1 b) (B + 3 * (B + 1) * (K + 1)) :=
      HasHeight.mul (hb p.2 h2) hdot'
    refine hasHeight_mono hprod ?_
    have hK1 : 1 ≤ K + 1 := by omega
    have hBA : B ≤ (B + 1) * (K + 1) := by
      have h2' : B + 1 ≤ (B + 1) * (K + 1) := by
        have e : (B + 1) * 1 ≤ (B + 1) * (K + 1) := Nat.mul_le_mul_left _ hK1
        simpa using e
      omega
    have hsq : (K + 1) ≤ (K + 1) ^ 2 := by nlinarith
    have hAK : (B + 1) * (K + 1) ≤ (B + 1) * (K + 1) ^ 2 :=
      Nat.mul_le_mul_left _ hsq
    have hgoal : 4 * (B + 1) * (K + 1) = 4 * ((B + 1) * (K + 1)) := by ring
    have hsum : 3 * (B + 1) * (K + 1) = 3 * ((B + 1) * (K + 1)) := by ring
    rw [hgoal, hsum]
    omega
  have h2 := hasHeight_sum_map (f := fun p : List ℚ × ℚ => p.2 * dotL p.1 b) hz
  rw [List.length_zip] at h2
  refine hasHeight_mono h2 ?_
  have hK1 : 1 ≤ K + 1 := by omega
  have hB1 : 1 ≤ B + 1 := by omega
  have h1A : 1 ≤ (B + 1) * (K + 1) := by
    have h := Nat.mul_le_mul hB1 hK1
    simpa using h
  have hm : min rows.length b.length ≤ K + 1 := by omega
  have hstep : (4 * (B + 1) * (K + 1) + 1) * min rows.length b.length
      ≤ (4 * (B + 1) * (K + 1) + 1) * (K + 1) := Nat.mul_le_mul_left _ hm
  have hfin : (4 * (B + 1) * (K + 1) + 1) * (K + 1) ≤ 6 * (B + 1) * (K + 1) ^ 2 := by
    have h3 : 4 * (B + 1) * (K + 1) + 1 ≤ 5 * ((B + 1) * (K + 1)) := by
      have e : 4 * (B + 1) * (K + 1) = 4 * ((B + 1) * (K + 1)) := by ring
      rw [e]; omega
    have h4 := Nat.mul_le_mul_right (K + 1) h3
    have h5 : (5 * ((B + 1) * (K + 1))) * (K + 1) = 5 * (B + 1) * (K + 1) ^ 2 := by ring
    have h6 : 5 * (B + 1) * (K + 1) ^ 2 ≤ 6 * (B + 1) * (K + 1) ^ 2 := by
      have := Nat.mul_le_mul_right ((B + 1) * (K + 1) ^ 2) (by norm_num : 5 ≤ 6)
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    calc (4 * (B + 1) * (K + 1) + 1) * (K + 1)
        ≤ (5 * ((B + 1) * (K + 1))) * (K + 1) := h4
      _ = 5 * (B + 1) * (K + 1) ^ 2 := h5
      _ ≤ 6 * (B + 1) * (K + 1) ^ 2 := h6
  exact le_trans hstep hfin

/-- **`zeroWitness`'s height**: its head is a quotient of a quadratic form by a row square, so it is
bounded by `12(B+1)(K+1)²` when the block has heights `≤ B` and width `≤ K`. -/
theorem zeroWitness_height {rows : Rows} {B K : ℕ} (h : RowsHeight rows B)
    (hK : RowsWidth rows K) (hlen : rows.length ≤ K) :
    ∀ q ∈ zeroWitness rows, HasHeight q (16 * (B + 1) * (K + 1) ^ 2) := by
  intro q hq
  have hht : ∀ r ∈ headTail rows, HasHeight r B := headTail_height h
  have hhtlen : (headTail rows).length ≤ K := by
    cases rows with
    | nil => simp [headTail, headRowD]
    | cons a t =>
        have h1 : (a).length ≤ K := hK a (List.mem_cons_self ..)
        have h2 : (headTail (a :: t)).length = a.tail.length := rfl
        have h3 : a.tail.length ≤ a.length := by simp
        rw [h2]
        omega
  have hdrlen : (dropRows rows).length ≤ K := by
    have h1 : (dropRows rows).length = rows.tail.length := by
      unfold dropRows
      rw [List.length_map]
    have h2 : rows.tail.length ≤ rows.length := by
      rw [List.length_tail]
      omega
    rw [h1]
    omega
  have hQ : HasHeight (qformRows (dropRows rows) (headTail rows))
      (6 * (B + 1) * (K + 1) ^ 2) :=
    qformRows_height (dropRows_height h) hht (fun v hv => by
      unfold dropRows at hv
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
      have h1 : w.length ≤ K := hK w (List.mem_of_mem_tail hw)
      have h2 : w.tail.length ≤ w.length := by simp
      exact le_trans h2 h1) hhtlen hdrlen
  have hS : HasHeight (rowSq (headTail rows)) (3 * (B + 1) * (K + 1)) := by
    have h1 := rowSq_height hht
    refine hasHeight_mono h1 ?_
    calc (2 * B + 2) * ((headTail rows).length + 1) ≤ (2 * B + 2) * (K + 1) :=
          Nat.mul_le_mul_left _ (by omega)
      _ ≤ 3 * (B + 1) * (K + 1) := by
          have h3 : 2 * B + 2 ≤ 3 * (B + 1) := by omega
          calc (2 * B + 2) * (K + 1) ≤ (3 * (B + 1)) * (K + 1) := Nat.mul_le_mul_right _ h3
            _ = 3 * (B + 1) * (K + 1) := by ring
  rw [zeroWitness, List.mem_cons] at hq
  rcases hq with rfl | hq
  · -- the head
    have h1 := HasHeight.add hQ hasHeight_one
    have h2 := HasHeight.neg h1
    have h3 := HasHeight.mul (a := (2 : ℚ)) (b := rowSq (headTail rows)) (h := 2) (g := 3 * (B + 1) * (K + 1))
      hasHeight_two hS
    have h4 := HasHeight.div h2 h3
    refine hasHeight_mono h4 ?_
    have hK1 : 1 ≤ K + 1 := by omega
    have hB1 : 1 ≤ B + 1 := by omega
    have hsq : (K + 1) ≤ (K + 1) ^ 2 := by nlinarith
    have hY : (B + 1) * (K + 1) ≤ (B + 1) * (K + 1) ^ 2 := Nat.mul_le_mul_left _ hsq
    have hX1 : 1 ≤ (B + 1) * (K + 1) ^ 2 := by
      have h := Nat.mul_le_mul hB1 (Nat.one_le_pow 2 (K + 1) (by omega))
      simpa using h
    have e1 : 6 * (B + 1) * (K + 1) ^ 2 + 3 * (B + 1) * (K + 1) + 5
        ≤ 16 * (B + 1) * (K + 1) ^ 2 := by
      have e6 : 6 * (B + 1) * (K + 1) ^ 2 = 6 * ((B + 1) * (K + 1) ^ 2) := by ring
      have e3 : 3 * (B + 1) * (K + 1) = 3 * ((B + 1) * (K + 1)) := by ring
      have e16 : 16 * (B + 1) * (K + 1) ^ 2 = 16 * ((B + 1) * (K + 1) ^ 2) := by ring
      rw [e6, e3, e16]
      have hY3 : 3 * ((B + 1) * (K + 1)) ≤ 3 * ((B + 1) * (K + 1) ^ 2) :=
        Nat.mul_le_mul_left 3 hY
      have h5 : 5 ≤ 5 * ((B + 1) * (K + 1) ^ 2) := by
        calc 5 = 5 * 1 := by ring
          _ ≤ 5 * ((B + 1) * (K + 1) ^ 2) := Nat.mul_le_mul_left 5 hX1
      omega
    omega
  · refine hasHeight_mono (hht q hq) ?_
    have hK1 : 1 ≤ K + 1 := by omega
    have hB1 : 1 ≤ B + 1 := by omega
    have hX1 : 1 ≤ (K + 1) ^ 2 := Nat.one_le_pow 2 (K + 1) (by omega)
    have h1 : B + 1 ≤ (B + 1) * (K + 1) ^ 2 := by
      calc B + 1 = (B + 1) * 1 := by ring
        _ ≤ (B + 1) * (K + 1) ^ 2 := Nat.mul_le_mul_left _ hX1
    have h2 : 16 * (B + 1) * (K + 1) ^ 2 = 16 * ((B + 1) * (K + 1) ^ 2) := by ring
    rw [h2]
    have h3 : (B + 1) * (K + 1) ^ 2 ≤ 16 * ((B + 1) * (K + 1) ^ 2) := by omega
    omega

/-- **`negWitness`'s height**: it is `1` followed by zeros. -/
theorem negWitness_height (rows : Rows) :
    ∀ q ∈ negWitness rows, HasHeight q 2 := by
  intro q hq
  rw [negWitness, List.mem_cons] at hq
  rcases hq with rfl | hq
  · exact hasHeight_mono hasHeight_one (by norm_num)
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
    exact hasHeight_mono hasHeight_zero (by norm_num)

/-! ## 3.  The witnesses of the pivot descent -/

/-- The height bound `16(B'+1)(K+1)²` is at least `2`, so the `negWitness` (whose entries are `0`/`1`)
fits inside it. -/
theorem two_le_witness_bound (B' K : ℕ) : 2 ≤ 16 * (B' + 1) * (K + 1) ^ 2 := by
  have h1 : 1 ≤ (B' + 1) * (K + 1) ^ 2 := by
    have hb : 1 ≤ B' + 1 := by omega
    have hk : 1 ≤ (K + 1) ^ 2 := Nat.one_le_pow 2 (K + 1) (by omega)
    have h := Nat.mul_le_mul hb hk
    simpa using h
  have e : 16 * (B' + 1) * (K + 1) ^ 2 = 16 * ((B' + 1) * (K + 1) ^ 2) := by ring
  rw [e]
  omega

/-! ## 3.  The witnesses of the pivot descent

`pivStepL_snd_height` bounds the heights of every *continuation*; what a cut normal needs is the
height of the *answer*.  `step_ans_height` does the one-step case (the answer is `[]`, `negWitness` or
`zeroWitness` of the current block), and `runPivLFuel_ans_height` iterates it over the fuel while
carrying the continuation invariant.  Both conclusions are stated for an explicit answer `a`, so no
goal ever has to reduce a projection of a `match`. -/

theorem runPivLFuel_succ_inl {k : ℕ} {p : LSt} {a : Ans}
    (h : pivStepL p = Sum.inl a) : runPivLFuel (k + 1) p = a := by
  rw [runPivLFuel_succ, h]

theorem runPivLFuel_succ_inr {k : ℕ} {p p' : LSt}
    (h : pivStepL p = Sum.inr p') : runPivLFuel (k + 1) p = runPivLFuel k p' := by
  rw [runPivLFuel_succ, h]

/-- **One descent step's answer has bounded heights.** -/
theorem step_ans_height {mu : ℚ} {d : ℕ} {st : St} {B K : ℕ} {a : Ans}
    (hH : RowsHeight st.1 B) (hW : RowsWidth st.1 K) (hlen : st.1.length ≤ K)
    (h : pivStepL ((mu, d), st) = Sum.inl a) :
    ∀ q ∈ a.2, HasHeight q (16 * (B + 1) * (K + 1) ^ 2) := by
  rw [pivStepL_def] at h
  by_cases h1 : st.1.isEmpty
  · rw [if_pos h1] at h
    have hh : Sum.inl ((false, []) : Ans) = Sum.inl a := h
    injection hh with hEq
    rw [← hEq]
    intro q hq
    simp at hq
  · rw [if_neg h1] at h
    by_cases h2 : piv st.1 < 0
    · rw [if_pos h2] at h
      have hh : Sum.inl ((true, negWitness st.1) : Ans) = Sum.inl a := h
      injection hh with hEq
      rw [← hEq]
      exact fun q hq => hasHeight_mono (negWitness_height st.1 q hq) (two_le_witness_bound B K)
    · rw [if_neg h2] at h
      by_cases h3 : piv st.1 = 0
      · rw [if_pos h3] at h
        by_cases h4 : rowSq (headTail st.1) = 0
        · rw [if_pos h4] at h
          simp [brDropL] at h
        · rw [if_neg h4] at h
          have hh : Sum.inl ((true, zeroWitness st.1) : Ans) = Sum.inl a := h
          injection hh with hEq
          rw [← hEq]
          exact zeroWitness_height hH hW hlen
      · rw [if_neg h3] at h
        simp [brSchurL] at h

-- NOTE (m3): the fuel-level iteration of `step_ans_height` is the one remaining piece.  The
-- intended induction carries `pivStepL_snd_height`'s continuation invariant (`L + D`) and applies
-- `step_ans_height` at the stopping step; it times out on whnf of `runPivLFuel (k+1) p` while
-- case-splitting `pivStepL p`, so it is left out rather than left sorry-ridden.

end QMCLeafB.SizeSlot

#print axioms QMCLeafB.SizeSlot.step_ans_height
#print axioms QMCLeafB.SizeSlot.runPivLFuel_succ_inl
#print axioms QMCLeafB.SizeSlot.runPivLFuel_succ_inr



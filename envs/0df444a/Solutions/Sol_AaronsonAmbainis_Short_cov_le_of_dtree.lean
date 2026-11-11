-- Prove2me | solution 1 for AaronsonAmbainis.Short.cov_le_of_dtree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:27:24.194969+00:00
-- url     : https://prove2.me/submissions/72dc6ed1-cd50-40a6-b823-3eb3937b66f4

import Mathlib
import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

namespace AASolCov

section
variable {ι : Type*}

theorem dtree_succ {α : Type*} {n : ℕ} {h : Cube ι → α} (hD : Short.DTree n h) :
    Short.DTree (n + 1) h := by
  induction hD with
  | const n c => exact Short.DTree.const _ c
  | query n j h0 h1 _ _ ih0 ih1 => exact Short.DTree.query _ j h0 h1 ih0 ih1

theorem dtree_inv {D : ℕ} {h : Cube ι → ℝ} (hD : Short.DTree D h) :
    (∃ c, h = fun _ => c) ∨ ∃ n i h0 h1, D = n + 1 ∧ Short.DTree n h0 ∧ Short.DTree n h1 ∧
      h = fun x => if x i then h1 x else h0 x := by
  cases hD with
  | const n c => exact Or.inl ⟨c, rfl⟩
  | query n i h0 h1 a b => exact Or.inr ⟨n, i, h0, h1, rfl, a, b, rfl⟩

variable [DecidableEq ι]

theorem flip_flip (x : Cube ι) (i : ι) : flipSet (flipSet x {i}) {i} = x := by
  funext k
  by_cases hk : k = i <;> simp [flipSet, hk]

theorem flip_comm (x : Cube ι) (i j : ι) :
    flipSet (flipSet x {j}) {i} = flipSet (flipSet x {i}) {j} := by
  funext k
  simp only [flipSet, Finset.mem_singleton]
  split_ifs <;> rfl

theorem flip_apply_self (x : Cube ι) (i : ι) : flipSet x {i} i = !x i := by
  simp [flipSet]

theorem update_flip (x : Cube ι) (i : ι) (b : Bool) :
    Function.update (flipSet x {i}) i b = Function.update x i b := by
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · simp [flipSet, hk]

theorem dtree_restrict {α : Type*} (i : ι) (b : Bool) {n : ℕ} {h : Cube ι → α}
    (hD : Short.DTree n h) : Short.DTree n (fun x => h (Function.update x i b)) := by
  induction hD with
  | const n c => exact Short.DTree.const _ c
  | query n j h0 h1 _ _ ih0 ih1 =>
    by_cases hj : j = i
    · subst hj
      cases b
      · have e : (fun x : Cube ι => if Function.update x j false j
            then h1 (Function.update x j false) else h0 (Function.update x j false))
            = fun x => h0 (Function.update x j false) := by
          funext x; simp
        exact (congrArg (Short.DTree (n + 1)) e).mpr (dtree_succ ih0)
      · have e : (fun x : Cube ι => if Function.update x j true j
            then h1 (Function.update x j true) else h0 (Function.update x j true))
            = fun x => h1 (Function.update x j true) := by
          funext x; simp
        exact (congrArg (Short.DTree (n + 1)) e).mpr (dtree_succ ih1)
    · have e : (fun x : Cube ι => if Function.update x i b j
          then h1 (Function.update x i b) else h0 (Function.update x i b))
          = fun x => if x j then h1 (Function.update x i b) else h0 (Function.update x i b) := by
        funext x; rw [Function.update_of_ne hj]
      exact (congrArg (Short.DTree (n + 1)) e).mpr (Short.DTree.query n j _ _ ih0 ih1)

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_flip (i : ι) (g : Cube ι → ℝ) : ∑ x, g (flipSet x {i}) = ∑ x, g x :=
  Equiv.sum_comp (Function.Involutive.toPerm (fun x : Cube ι => flipSet x {i})
    (fun x => flip_flip x i)) g

theorem sum_ite_half (i : ι) (u0 u1 : Cube ι → ℝ)
    (h0 : ∀ x, u0 (flipSet x {i}) = u0 x) (h1 : ∀ x, u1 (flipSet x {i}) = u1 x) :
    ∑ x : Cube ι, (if x i then u1 x else u0 x) = (∑ x, u1 x + ∑ x, u0 x) / 2 := by
  have e : ∑ x : Cube ι, (if (flipSet x {i}) i then u1 (flipSet x {i}) else u0 (flipSet x {i}))
      = ∑ x : Cube ι, (if x i then u1 x else u0 x) :=
    sum_flip i (fun x => if x i then u1 x else u0 x)
  have e2 : ∑ x : Cube ι, ((if x i then u1 x else u0 x) +
      (if (flipSet x {i}) i then u1 (flipSet x {i}) else u0 (flipSet x {i})))
      = ∑ x, (u1 x + u0 x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [flip_apply_self, h0, h1]
    rcases Bool.eq_false_or_eq_true (x i) with hx | hx <;> simp [hx, add_comm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at e2
  linarith

theorem card_cube : (Fintype.card (Cube ι) : ℝ) = 2 ^ Fintype.card ι := by
  show ((Fintype.card (ι → Bool) : ℕ) : ℝ) = _
  rw [Fintype.card_fun, Fintype.card_bool]; norm_num

theorem cov_const (p : Cube ι → ℝ) (c : ℝ) : mean (fun x => (p x - mean p) * c) = 0 := by
  have hN : (2 : ℝ) ^ Fintype.card ι ≠ 0 := by positivity
  have h0 : ∑ x, (p x - mean p) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_cube]
    unfold mean
    field_simp
    ring
  show (∑ x, (p x - mean p) * c) / 2 ^ Fintype.card ι = 0
  rw [← Finset.sum_mul, h0, zero_mul, zero_div]

/-- Average of `p` over the two values of coordinate `i`. -/
noncomputable def avg (i : ι) (p : Cube ι → ℝ) : Cube ι → ℝ :=
  fun x => (p x + p (flipSet x {i})) / 2

omit [Fintype ι] in
theorem avg_flip (i : ι) (p : Cube ι → ℝ) (x : Cube ι) : avg i p (flipSet x {i}) = avg i p x := by
  simp only [avg, flip_flip]; ring

theorem mean_avg (i : ι) (p : Cube ι → ℝ) : mean (avg i p) = mean p := by
  unfold mean
  congr 1
  simp only [avg]
  rw [← Finset.sum_div, Finset.sum_add_distrib, sum_flip i p]; ring

theorem incr_avg (i j : ι) (p : Cube ι → ℝ) : meanAbsIncr (avg i p) j ≤ meanAbsIncr p j := by
  unfold meanAbsIncr
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  refine div_le_div_of_nonneg_right ?_ hN.le
  calc ∑ x, |avg i p x - avg i p (flipSet x {j})|
      ≤ ∑ x, (|p x - p (flipSet x {j})| +
          |p (flipSet x {i}) - p (flipSet (flipSet x {i}) {j})|) / 2 := by
        refine Finset.sum_le_sum fun x _ => ?_
        have e : avg i p x - avg i p (flipSet x {j}) = ((p x - p (flipSet x {j})) +
            (p (flipSet x {i}) - p (flipSet (flipSet x {i}) {j}))) / 2 := by
          simp only [avg, flip_comm x i j]; ring
        rw [e, abs_div, abs_two]
        exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
    _ = ∑ x, |p x - p (flipSet x {j})| := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          sum_flip i (fun x => |p x - p (flipSet x {j})|)]; ring

theorem step (n : ℕ)
    (IH : ∀ (p h : Cube ι → ℝ), Short.DTree n h → (∀ x, |h x| ≤ 1) → ∀ M : ℝ, 0 ≤ M →
      (∀ j, meanAbsIncr p j ≤ M) → |mean (fun x => (p x - mean p) * h x)| ≤ (n : ℝ) / 2 * M)
    (p : Cube ι → ℝ) (i : ι) (h g0 g1 : Cube ι → ℝ)
    (hh : ∀ x, h x = if x i then g1 x else g0 x)
    (inv0 : ∀ x, g0 (flipSet x {i}) = g0 x) (inv1 : ∀ x, g1 (flipSet x {i}) = g1 x)
    (d0 : Short.DTree n g0) (d1 : Short.DTree n g1)
    (b0 : ∀ x, |g0 x| ≤ 1) (b1 : ∀ x, |g1 x| ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr p j ≤ M) :
    |mean (fun x => (p x - mean p) * h x)| ≤ ((n + 1 : ℕ) : ℝ) / 2 * M := by
  have hN : (0 : ℝ) < 2 ^ Fintype.card ι := by positivity
  have hb : ∀ x, |h x| ≤ 1 := by
    intro x; rw [hh x]; split_ifs
    · exact b1 x
    · exact b0 x
  have hA : |(∑ x, (p x - avg i p x) * h x) / 2 ^ Fintype.card ι| ≤ M / 2 := by
    rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
    calc |∑ x, (p x - avg i p x) * h x|
        ≤ ∑ x, |(p x - avg i p x) * h x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |p x - p (flipSet x {i})| / 2 := by
          refine Finset.sum_le_sum fun x _ => ?_
          have e : p x - avg i p x = (p x - p (flipSet x {i})) / 2 := by
            simp only [avg]; ring
          rw [abs_mul, e, abs_div, abs_two]
          calc |p x - p (flipSet x {i})| / 2 * |h x|
              ≤ |p x - p (flipSet x {i})| / 2 * 1 :=
                mul_le_mul_of_nonneg_left (hb x) (by positivity)
            _ = _ := mul_one _
      _ = (∑ x, |p x - p (flipSet x {i})|) / 2 := (Finset.sum_div _ _ _).symm
      _ ≤ M / 2 * 2 ^ Fintype.card ι := by
          have := hM i
          unfold meanAbsIncr at this
          rw [div_le_iff₀ hN] at this
          linarith
  have hB : ∑ x, (avg i p x - mean p) * h x =
      (∑ x, (avg i p x - mean p) * g1 x + ∑ x, (avg i p x - mean p) * g0 x) / 2 := by
    rw [← sum_ite_half i (fun x => (avg i p x - mean p) * g0 x)
      (fun x => (avg i p x - mean p) * g1 x)
      (fun x => by show (avg i p (flipSet x {i}) - mean p) * g0 (flipSet x {i}) = _
                   rw [avg_flip, inv0])
      (fun x => by show (avg i p (flipSet x {i}) - mean p) * g1 (flipSet x {i}) = _
                   rw [avg_flip, inv1])]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hh x]; split_ifs <;> rfl
  have hsplit : ∑ x, (p x - mean p) * h x =
      ∑ x, (p x - avg i p x) * h x + ∑ x, (avg i p x - mean p) * h x := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have I1 := IH (avg i p) g1 d1 b1 M hM0 (fun j => (incr_avg i j p).trans (hM j))
  have I0 := IH (avg i p) g0 d0 b0 M hM0 (fun j => (incr_avg i j p).trans (hM j))
  rw [mean_avg] at I1 I0
  have e1 : mean (fun x => (avg i p x - mean p) * g1 x)
      = (∑ x, (avg i p x - mean p) * g1 x) / 2 ^ Fintype.card ι := rfl
  have e0 : mean (fun x => (avg i p x - mean p) * g0 x)
      = (∑ x, (avg i p x - mean p) * g0 x) / 2 ^ Fintype.card ι := rfl
  rw [e1] at I1
  rw [e0] at I0
  show |(∑ x, (p x - mean p) * h x) / 2 ^ Fintype.card ι| ≤ _
  rw [hsplit, hB]
  have key : (∑ x, (p x - avg i p x) * h x +
      (∑ x, (avg i p x - mean p) * g1 x + ∑ x, (avg i p x - mean p) * g0 x) / 2)
        / 2 ^ Fintype.card ι
      = (∑ x, (p x - avg i p x) * h x) / 2 ^ Fintype.card ι +
        ((∑ x, (avg i p x - mean p) * g1 x) / 2 ^ Fintype.card ι +
         (∑ x, (avg i p x - mean p) * g0 x) / 2 ^ Fintype.card ι) / 2 := by ring
  have hR : ((n + 1 : ℕ) : ℝ) / 2 * M = (n : ℝ) / 2 * M + M / 2 := by push_cast; ring
  rw [key, hR]
  rw [abs_le] at hA I1 I0 ⊢
  constructor <;> linarith [hA.1, hA.2, I1.1, I1.2, I0.1, I0.2]

theorem main (D : ℕ) : ∀ (p h : Cube ι → ℝ), Short.DTree D h → (∀ x, |h x| ≤ 1) → ∀ M : ℝ,
    0 ≤ M → (∀ j, meanAbsIncr p j ≤ M) →
    |mean (fun x => (p x - mean p) * h x)| ≤ (D : ℝ) / 2 * M := by
  induction D with
  | zero =>
    intro p h hD hb M hM0 hM
    rcases dtree_inv hD with ⟨c, rfl⟩ | ⟨n, i, h0, h1, hn, _⟩
    · rw [cov_const, abs_zero]; exact mul_nonneg (by positivity) hM0
    · omega
  | succ n IH =>
    intro p h hD hb M hM0 hM
    rcases dtree_inv hD with ⟨c, rfl⟩ | ⟨m, i, h0, h1, hm, d0, d1, rfl⟩
    · rw [cov_const, abs_zero]; exact mul_nonneg (by positivity) hM0
    · obtain rfl : n = m := by omega
      refine step n IH p i _ (fun x => h0 (Function.update x i false))
        (fun x => h1 (Function.update x i true)) ?_ ?_ ?_
        (dtree_restrict i false d0) (dtree_restrict i true d1) ?_ ?_ M hM0 hM
      · intro x
        rcases Bool.eq_false_or_eq_true (x i) with hx | hx
        · have : Function.update x i true = x := by
            rw [← hx]; exact Function.update_eq_self i x
          simp only [hx, if_true, this]
        · have : Function.update x i false = x := by
            rw [← hx]; exact Function.update_eq_self i x
          simp [hx, this]
      · intro x; show h0 (Function.update (flipSet x {i}) i false) = _; rw [update_flip]
      · intro x; show h1 (Function.update (flipSet x {i}) i true) = _; rw [update_flip]
      · intro x; simpa using hb (Function.update x i false)
      · intro x; simpa using hb (Function.update x i true)

end AASolCov

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p h : Cube ι → ℝ) (D : ℕ) (hD : Short.DTree D h) (hb : ∀ x, |h x| ≤ 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr p j ≤ M) :
    |mean (fun x => (p x - mean p) * h x)| ≤ (D : ℝ) / 2 * M :=
  AASolCov.main D p h hD hb M hM0 hM

-- Prove2me | solution 1 for AdaptSubCover.Rounds.bsz19_theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:28:38.225114+00:00
-- url     : https://prove2.me/submissions/d5c959ea-5537-4b02-ad45-95b6d1bda12f

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Model

open AdaptSubCover.Rounds

namespace ASCBSZ

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem prob_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (ω : Fin m → U) :
    0 ≤ I.prob ω := Finset.prod_nonneg fun i _ => hp0 i (ω i)

theorem sum_prob (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) :
    ∑ ω, I.prob ω = 1 := by
  unfold Instance.prob
  rw [← Fintype.prod_sum (fun i u => I.p i u)]
  simp [hp1]

theorem E_const (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) (a : ℝ) :
    I.E (fun _ => a) = a := by
  unfold Instance.E; rw [← Finset.sum_mul, sum_prob I hp1, one_mul]

theorem E_add (I : Instance U m) (F G : (Fin m → U) → ℝ) :
    I.E (fun ω => F ω + G ω) = I.E F + I.E G := by
  unfold Instance.E
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem E_mono (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  exact Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (prob_nonneg I hp0 ω)

/-- The involution `(ω, u) ↦ (ω[e := u], ω e)`. -/
def swapE (e : Fin m) (x : (Fin m → U) × U) : (Fin m → U) × U :=
  (Function.update x.1 e x.2, x.1 e)

theorem swapE_invol (e : Fin m) : Function.Involutive (swapE (U := U) e) := by
  intro x
  obtain ⟨ω, u⟩ := x
  simp [swapE]

/-- Conditioning on one coordinate of the product distribution. -/
theorem E_split (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) (e : Fin m)
    (F : (Fin m → U) → ℝ) :
    I.E F = ∑ u, I.p e u * I.E (fun ω => F (Function.update ω e u)) := by
  set P' : (Fin m → U) → ℝ := fun ω => ∏ i ∈ Finset.univ.erase e, I.p i (ω i) with hP'
  have hprob : ∀ ω, I.prob ω = I.p e (ω e) * P' ω := by
    intro ω
    unfold Instance.prob
    rw [hP', Finset.mul_prod_erase Finset.univ (fun i => I.p i (ω i)) (Finset.mem_univ e)]
  have hP'u : ∀ ω u, P' (Function.update ω e u) = P' ω := by
    intro ω u
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  set Ψ : (Fin m → U) × U → ℝ := fun x =>
    I.p e x.2 * (I.p e (x.1 e) * P' x.1 * F (Function.update x.1 e x.2)) with hΨ
  have h1 : ∑ u, I.p e u * I.E (fun ω => F (Function.update ω e u)) = ∑ x, Ψ x := by
    rw [Fintype.sum_prod_type_right]
    apply Finset.sum_congr rfl; intro u _
    unfold Instance.E
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω _
    rw [hΨ, hprob]
  have h2 : ∑ x, Ψ x = ∑ x, Ψ (swapE e x) :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ (swapE_invol e)) Ψ).symm
  rw [h1, h2, Fintype.sum_prod_type]
  unfold Instance.E
  apply Finset.sum_congr rfl; intro ω _
  simp only [hΨ, swapE, Function.update_self, Function.update_idem, Function.update_eq_self, hP'u]
  have : ∑ y, I.p e (ω e) * (I.p e y * P' ω * F ω) = (∑ y, I.p e y) * (I.p e (ω e) * P' ω * F ω) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro y _; ring
  rw [this, hp1 e, hprob]
  ring

end ASCBSZ

namespace ASCBSZ

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-! ### Subtrees of a decision tree -/

/-- The subtree of `π` after its root probe `e` realized to `u` (re-probing `e` stops). -/
def sub (π : AdaptivePolicy m U) (e : Fin m) (u : U) : AdaptivePolicy m U := fun h =>
  match π ((e, u) :: h) with
  | some i => if i = e then none else some i
  | none => none

theorem items_cons (x : Fin m × U) (h : History m U) :
    History.items (x :: h) = insert x.1 h.items := by
  ext y; simp [History.items]

theorem realized_cons (x : Fin m × U) (h : History m U) :
    History.realized (x :: h) = insert x.2 h.realized := by
  ext y; simp [History.realized]

theorem items_nil : History.items ([] : History m U) = ∅ := by simp [History.items]

theorem realized_nil : History.realized ([] : History m U) = ∅ := by simp [History.realized]

theorem sub_ne (π : AdaptivePolicy m U) (e : Fin m) (u : U) (h : History m U) :
    sub π e u h ≠ some e := by
  unfold sub
  split
  · split_ifs with h1
    · simp
    · simpa using h1
  · simp

theorem step_cons (π : AdaptivePolicy m U) (e : Fin m) (ω : Fin m → U) (h : History m U) :
    π.step ω ((e, ω e) :: h) = (e, ω e) :: (sub π e (ω e)).step ω h := by
  unfold AdaptivePolicy.step sub
  rcases hπ : π ((e, ω e) :: h) with _ | i
  · simp
  · simp only
    by_cases hie : i = e
    · subst hie; simp [items_cons]
    · simp only [hie, if_false, items_cons, Finset.mem_insert]
      by_cases hi : i ∈ h.items
      · simp [hi]
      · simp [hi, hie]

theorem iterate_cons (π : AdaptivePolicy m U) (e : Fin m) (ω : Fin m → U) :
    ∀ (n : ℕ) (h : History m U), (π.step ω)^[n] ((e, ω e) :: h) =
      (e, ω e) :: ((sub π e (ω e)).step ω)^[n] h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, step_cons, ih]

theorem run_some (π : AdaptivePolicy m U) (e : Fin m) (he : π [] = some e) (ω : Fin m → U)
    (n : ℕ) : (π.step ω)^[n + 1] [] = (e, ω e) :: ((sub π e (ω e)).step ω)^[n] [] := by
  rw [Function.iterate_succ_apply]
  have : π.step ω [] = [(e, ω e)] := by
    unfold AdaptivePolicy.step; rw [he]; simp [items_nil]
  rw [this, iterate_cons π e ω n []]

theorem run_none (π : AdaptivePolicy m U) (he : π [] = none) (ω : Fin m → U) (n : ℕ) :
    (π.step ω)^[n] [] = [] := by
  apply Function.iterate_fixed
  unfold AdaptivePolicy.step; rw [he]

/-- A policy that never names `e` does not read coordinate `e`. -/
theorem iterate_indep (ρ : AdaptivePolicy m U) (e : Fin m) (hρ : ∀ h, ρ h ≠ some e)
    (ω : Fin m → U) (v : U) (n : ℕ) (h : History m U) :
    (ρ.step (Function.update ω e v))^[n] h = (ρ.step ω)^[n] h := by
  have : ρ.step (Function.update ω e v) = ρ.step ω := by
    funext h
    unfold AdaptivePolicy.step
    rcases hh : ρ h with _ | i
    · rfl
    · have hie : i ≠ e := fun hie => hρ h (by rw [hh, hie])
      simp [Function.update_of_ne hie]
  rw [this]

theorem iterate_noE (ρ : AdaptivePolicy m U) (e : Fin m) (hρ : ∀ h, ρ h ≠ some e)
    (ω : Fin m → U) : ∀ (n : ℕ) (h : History m U), e ∉ h.items →
      e ∉ ((ρ.step ω)^[n] h).items := by
  intro n
  induction n with
  | zero => intro h hh; exact hh
  | succ n ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    apply ih
    unfold AdaptivePolicy.step
    rcases hr : ρ h with _ | i
    · exact hh
    · have hie : i ≠ e := fun hie => hρ h (by rw [hr, hie])
      simp only
      split_ifs
      · exact hh
      · simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union,
          not_or] at hh ⊢
        exact ⟨hh, by simpa using hie.symm⟩

/-! ### Contractions -/

theorem contr_mono (g : Finset U → ℝ) (hgm : Monotone g) (C : Finset U) :
    Monotone (fun S => g (C ∪ S) - g C) := by
  intro A B hAB
  simp only
  have := hgm (Finset.union_subset_union (le_refl C) hAB)
  linarith

theorem contr_sub (g : Finset U → ℝ) (hgs : NonmonotoneSubmod.Shared.Submodular g)
    (C : Finset U) : NonmonotoneSubmod.Shared.Submodular (fun S => g (C ∪ S) - g C) := by
  intro S T
  simp only
  have := hgs (C ∪ S) (C ∪ T)
  have e1 : C ∪ S ∪ (C ∪ T) = C ∪ (S ∪ T) := by
    ext x; simp only [Finset.mem_union]; tauto
  have e2 : (C ∪ S) ∩ (C ∪ T) = C ∪ (S ∩ T) := (Finset.union_inter_distrib_left C S T).symm
  rw [e1, e2] at this
  linarith

end ASCBSZ

namespace ASCBSZ

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- Expected value of the adaptive strategy (first `n` steps). -/
noncomputable def adapN (I : Instance U m) (π : AdaptivePolicy m U) (n : ℕ)
    (g : Finset U → ℝ) : ℝ :=
  I.E (fun ω => g ((π.step ω)^[n] []).realized)

/-- Expected value of the random-walk non-adaptive strategy (first `n` steps). -/
noncomputable def algN (I : Instance U m) (π : AdaptivePolicy m U) (n : ℕ)
    (g : Finset U → ℝ) : ℝ :=
  I.E (fun ω' => I.E (fun ω => g ((((π.step ω')^[n] []).items).image ω)))

theorem E_congr (I : Instance U m) (F G : (Fin m → U) → ℝ) (h : ∀ ω, F ω = G ω) :
    I.E F = I.E G := by
  unfold Instance.E; exact Finset.sum_congr rfl fun ω _ => by rw [h ω]

theorem E_sum_mul (I : Instance U m) (w : U → ℝ) (F : U → (Fin m → U) → ℝ) :
    I.E (fun ω => ∑ u, w u * F u ω) = ∑ u, w u * I.E (F u) := by
  unfold Instance.E
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro ω _; ring

theorem dsum (p : U → ℝ) (hp : ∑ u, p u = 1) (c d : U → ℝ) (k : ℝ) (y : U → U → ℝ) :
    ∑ a, p a * ∑ b, p b * (c a + d b + k + y a b) =
      ∑ a, p a * c a + ∑ b, p b * d b + k + ∑ a, p a * ∑ b, p b * y a b := by
  have h1 : ∀ a, ∑ b, p b * (c a + d b + k + y a b) =
      c a + ∑ b, p b * d b + k + ∑ b, p b * y a b := by
    intro a
    have : ∑ b, p b * (c a + d b + k + y a b) =
        (∑ b, p b) * (c a + k) + ∑ b, p b * d b + ∑ b, p b * y a b := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _; ring
    rw [this, hp]; ring
  simp only [h1]
  have : ∑ a, p a * (c a + ∑ b, p b * d b + k + ∑ b, p b * y a b) =
      ∑ a, p a * c a + (∑ a, p a) * (∑ b, p b * d b + k) + ∑ a, p a * ∑ b, p b * y a b := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro a _; ring
  rw [this, hp]; ring

theorem main_ineq (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u)
    (hp1 : ∀ i, ∑ u, I.p i u = 1) :
    ∀ (n : ℕ) (π : AdaptivePolicy m U) (g : Finset U → ℝ), Monotone g →
      NonmonotoneSubmod.Shared.Submodular g →
      adapN I π n g - g ∅ ≤ 2 * (algN I π n g - g ∅) := by
  intro n
  induction n with
  | zero =>
    intro π g _ _
    simp [adapN, algN, realized_nil, items_nil, E_const I hp1]
  | succ n ih =>
    intro π g hgm hgs
    rcases hπ0 : π [] with _ | e
    · simp [adapN, algN, run_none π hπ0, realized_nil, items_nil, E_const I hp1]
    -- notation
    set p : U → ℝ := fun u => I.p e u with hp
    have hpsum : ∑ u, p u = 1 := hp1 e
    set hIR : U → U → Finset U → ℝ := fun a b S => g ({a, b} ∪ S) - g {a, b} with hhIR
    have hIRm : ∀ a b, Monotone (hIR a b) := fun a b => contr_mono g hgm _
    have hIRs : ∀ a b, NonmonotoneSubmod.Shared.Submodular (hIR a b) :=
      fun a b => contr_sub g hgs _
    have hIR0 : ∀ a b, hIR a b ∅ = 0 := by intro a b; simp [hhIR]
    set A : U → (Fin m → U) → Finset U := fun a ω =>
      (((sub π e a).step ω)^[n] []).realized with hA
    set Bf : U → (Fin m → U) → (Fin m → U) → Finset U := fun a ω' ω =>
      ((((sub π e a).step ω')^[n] []).items).image ω with hB
    -- the adaptive side
    have hadap : adapN I π (n + 1) g = ∑ a, p a * I.E (fun ω => g (insert a (A a ω))) := by
      unfold adapN
      rw [E_split I hp1 e]
      apply Finset.sum_congr rfl; intro a _
      congr 1
      apply E_congr; intro ω
      rw [run_some π e hπ0, realized_cons]
      simp only [Function.update_self, hA]
      rw [iterate_indep (sub π e a) e (sub_ne π e a) ω a n []]
    -- the non-adaptive side
    have halg : algN I π (n + 1) g =
        ∑ a, p a * I.E (fun ω' => ∑ b, p b * I.E (fun ω => g (insert b (Bf a ω' ω)))) := by
      unfold algN
      rw [E_split I hp1 e]
      apply Finset.sum_congr rfl; intro a _
      congr 1
      apply E_congr; intro ω'
      rw [E_split I hp1 e]
      apply Finset.sum_congr rfl; intro b _
      congr 1
      apply E_congr; intro ω
      rw [run_some π e hπ0, items_cons]
      simp only [Function.update_self, hB]
      rw [iterate_indep (sub π e a) e (sub_ne π e a) ω' a n [], Finset.image_insert,
        Function.update_self]
      congr 2
      apply Finset.image_congr
      intro i hi
      have hie : i ≠ e := by
        intro hie; rw [hie] at hi
        exact iterate_noE (sub π e a) e (sub_ne π e a) ω' n [] (by simp [items_nil]) hi
      simp [Function.update_of_ne hie]
    -- pointwise bounds
    have hsubadd : ∀ a b, g {a, b} ≤ g {a} + g {b} - g ∅ := by
      intro a b
      have := hgs {a} {b}
      have h1 : ({a} : Finset U) ∪ {b} = {a, b} := by ext; simp
      have h2 : g ∅ ≤ g ({a} ∩ {b}) := hgm (Finset.empty_subset _)
      rw [h1] at this; linarith
    have hadap_pt : ∀ a b ω, g (insert a (A a ω)) ≤ g {a} + g {b} - g ∅ + hIR a b (A a ω) := by
      intro a b ω
      have : g (insert a (A a ω)) ≤ g ({a, b} ∪ A a ω) := by
        apply hgm; intro x hx
        simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hx ⊢
        tauto
      simp only [hhIR]; linarith [hsubadd a b]
    have halg_pt : ∀ a b ω' ω, g {b} + hIR a b (Bf a ω' ω) ≤ g (insert b (Bf a ω' ω)) := by
      intro a b ω' ω
      have := hgs (insert b (Bf a ω' ω)) {a, b}
      have e1 : insert b (Bf a ω' ω) ∪ {a, b} = {a, b} ∪ Bf a ω' ω := by
        ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
      have h2 : g {b} ≤ g (insert b (Bf a ω' ω) ∩ {a, b}) := by
        apply hgm; intro x hx
        simp only [Finset.mem_singleton] at hx; subst hx
        simp
      rw [e1] at this
      simp only [hhIR]; linarith
    -- expectations
    have hadapE : ∀ a, I.E (fun ω => g (insert a (A a ω))) ≤
        ∑ b, p b * (g {a} + g {b} + (- g ∅) + adapN I (sub π e a) n (hIR a b)) := by
      intro a
      have : I.E (fun ω => g (insert a (A a ω))) =
          ∑ b, p b * I.E (fun ω => g (insert a (A a ω))) := by
        rw [← Finset.sum_mul, hpsum, one_mul]
      rw [this]
      apply Finset.sum_le_sum; intro b _
      apply mul_le_mul_of_nonneg_left _ (hp0 e b)
      have h := E_mono I hp0 _ _ (hadap_pt a b)
      have e2 : I.E (fun ω => g {a} + g {b} - g ∅ + hIR a b (A a ω)) =
          g {a} + g {b} + - g ∅ + adapN I (sub π e a) n (hIR a b) := by
        rw [E_add, E_const I hp1]; unfold adapN; ring
      linarith
    have halgE : ∀ a, ∑ b, p b * (g {b} + algN I (sub π e a) n (hIR a b)) ≤
        I.E (fun ω' => ∑ b, p b * I.E (fun ω => g (insert b (Bf a ω' ω)))) := by
      intro a
      rw [E_sum_mul]
      apply Finset.sum_le_sum; intro b _
      apply mul_le_mul_of_nonneg_left _ (hp0 e b)
      unfold algN
      have : g {b} + I.E (fun ω' => I.E (fun ω => hIR a b (Bf a ω' ω))) =
          I.E (fun ω' => I.E (fun ω => g {b} + hIR a b (Bf a ω' ω))) := by
        rw [← E_const I hp1 (g {b}), ← E_add]
        congr 1; funext ω'
        rw [E_add, E_const I hp1, E_const I hp1]
      rw [this]
      apply E_mono I hp0; intro ω'
      apply E_mono I hp0; intro ω
      exact halg_pt a b ω' ω
    have hIH : ∀ a b, adapN I (sub π e a) n (hIR a b) ≤ 2 * algN I (sub π e a) n (hIR a b) := by
      intro a b
      have := ih (sub π e a) (hIR a b) (hIRm a b) (hIRs a b)
      rw [hIR0] at this; linarith
    -- combine
    have hA1 : adapN I π (n + 1) g ≤
        ∑ a, p a * ∑ b, p b * (g {a} + g {b} + (- g ∅) + adapN I (sub π e a) n (hIR a b)) := by
      rw [hadap]
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hadapE a) (hp0 e a)
    have hA2 : ∑ a, p a * ∑ b, p b * (g {b} + algN I (sub π e a) n (hIR a b)) ≤
        algN I π (n + 1) g := by
      rw [halg]
      exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (halgE a) (hp0 e a)
    rw [dsum p hpsum] at hA1
    have hA2' := hA2
    have e3 : ∑ a, p a * ∑ b, p b * (g {b} + algN I (sub π e a) n (hIR a b)) =
        ∑ a, p a * ∑ b, p b * ((fun _ => (0 : ℝ)) a + g {b} + 0 + algN I (sub π e a) n (hIR a b)) := by
      apply Finset.sum_congr rfl; intro a _; congr 1
      apply Finset.sum_congr rfl; intro b _; ring
    rw [e3, dsum p hpsum] at hA2'
    have hyy : ∑ a, p a * ∑ b, p b * adapN I (sub π e a) n (hIR a b) ≤
        2 * ∑ a, p a * ∑ b, p b * algN I (sub π e a) n (hIR a b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro a _
      have : ∑ b, p b * adapN I (sub π e a) n (hIR a b) ≤
          2 * ∑ b, p b * algN I (sub π e a) n (hIR a b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum; intro b _
        have := mul_le_mul_of_nonneg_left (hIH a b) (hp0 e b)
        linarith
      have := mul_le_mul_of_nonneg_left this (hp0 e a)
      linarith
    simp only [mul_zero, Finset.sum_const_zero] at hA2'
    linarith

end ASCBSZ

open ASCBSZ in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m)
    (hp0 : ∀ i u, 0 ≤ I.p i u) (hp1 : ∀ i, ∑ u, I.p i u = 1)
    (g : Finset U → ℝ) (hg0 : ∀ A, 0 ≤ g A) (hgm : Monotone g)
    (hgs : NonmonotoneSubmod.Shared.Submodular g)
    (avail : Finset (Fin m)) (B : ℝ) (π : AdaptivePolicy m U)
    (hπ : ∀ ω, (π.run ω).items ⊆ avail ∧ (I.costOf (π.run ω) : ℝ) ≤ B) :
    ∃ T ⊆ avail, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ B ∧
      I.E (fun ω => g (π.run ω).realized) ≤ 2 * I.E (fun ω => g (T.image ω)) := by
  have hmain := main_ineq I hp0 hp1 m π g hgm hgs
  have hg0' := hg0 ∅
  set Φ : (Fin m → U) → ℝ := fun ω' => I.E (fun ω => g (((π.run ω').items).image ω)) with hΦ
  have hne : (Finset.univ : Finset (Fin m → U)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := sum_prob I hp1
    rw [h, Finset.sum_empty] at this
    norm_num at this
  obtain ⟨ω₀, -, hmax⟩ := Finset.exists_max_image Finset.univ Φ hne
  refine ⟨(π.run ω₀).items, (hπ ω₀).1, (hπ ω₀).2, ?_⟩
  have halg : algN I π m g ≤ Φ ω₀ := by
    unfold algN
    calc I.E (fun ω' => I.E (fun ω => g ((((π.step ω')^[m] []).items).image ω)))
        = ∑ ω', I.prob ω' * Φ ω' := rfl
      _ ≤ ∑ ω', I.prob ω' * Φ ω₀ :=
          Finset.sum_le_sum fun ω' _ => mul_le_mul_of_nonneg_left (hmax ω' (Finset.mem_univ _))
            (prob_nonneg I hp0 ω')
      _ = Φ ω₀ := by rw [← Finset.sum_mul, sum_prob I hp1, one_mul]
  have hadap : I.E (fun ω => g (π.run ω).realized) = adapN I π m g := rfl
  rw [hadap]
  show adapN I π m g ≤ 2 * Φ ω₀
  linarith

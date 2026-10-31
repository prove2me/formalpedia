-- Prove2me | solution 1 for AdaptSubCover.Rounds.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:21:30.416998+00:00
-- url     : https://prove2.me/submissions/8862deb9-3071-411e-a22f-a0dc7d5d6fc8

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_ParCA
import Theorems.Thm_AdaptSubCover_Rounds_theorem_3_1

open AdaptSubCover.Rounds

namespace ASCT32

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


theorem E_congr (I : Instance U m) (F G : (Fin m → U) → ℝ) (h : ∀ ω, F ω = G ω) :
    I.E F = I.E G := by
  unfold Instance.E; exact Finset.sum_congr rfl fun ω _ => by rw [h ω]

theorem E_smul (I : Instance U m) (a : ℝ) (F : (Fin m → U) → ℝ) :
    I.E (fun ω => a * F ω) = a * I.E F := by
  unfold Instance.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem E_sub (I : Instance U m) (F G : (Fin m → U) → ℝ) :
    I.E (fun ω => F ω - G ω) = I.E F - I.E G := by
  unfold Instance.E
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro ω _; ring

/-- Independence: the coordinates in `D` may be drawn from an independent copy. -/
theorem E_indep (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) (D : Finset (Fin m)) :
    ∀ F : (Fin m → U) → ℝ, I.E F = I.E (fun ω => I.E (fun ν => F (D.piecewise ω ν))) := by
  induction D using Finset.induction_on with
  | empty =>
    intro F
    simp only [Finset.piecewise_empty]
    rw [E_const I hp1]
  | insert e D he ih =>
    intro F
    have hpw : ∀ ω ν : Fin m → U, (insert e D).piecewise ω ν = Function.update (D.piecewise ω ν) e (ω e) := by
      intro ω ν
      ext x
      by_cases hx : x = e
      · subst hx; simp
      · simp [Finset.piecewise, Function.update_of_ne hx, hx]
    have hpw2 : ∀ (ω ν : Fin m → U) (a : U), D.piecewise (Function.update ω e a) ν = D.piecewise ω ν := by
      intro ω ν a
      ext x
      by_cases hx : x ∈ D
      · have : x ≠ e := fun h => he (h ▸ hx)
        simp [Finset.piecewise, hx, Function.update_of_ne this]
      · simp [Finset.piecewise, hx]
    rw [E_split I hp1 e F]
    rw [E_split I hp1 e (fun ω => I.E (fun ν => F ((insert e D).piecewise ω ν)))]
    apply Finset.sum_congr rfl; intro a _
    congr 1
    rw [ih (fun ω => F (Function.update ω e a))]
    apply E_congr; intro ω
    apply E_congr; intro ν
    simp only [hpw, hpw2, Function.update_self]

/-- Changing the law of one coordinate does not affect a function independent of it. -/
theorem E_change (I I' : Instance U m) (e : Fin m) (hp1 : ∑ u, I.p e u = 1)
    (hp1' : ∑ u, I'.p e u = 1) (hpe : ∀ i, i ≠ e → I'.p i = I.p i)
    (H : (Fin m → U) → ℝ) (hH : ∀ ν a, H (Function.update ν e a) = H ν) :
    I.E H = I'.E H := by
  set P' : (Fin m → U) → ℝ := fun ω => ∏ i ∈ Finset.univ.erase e, I.p i (ω i) with hP'
  have hprob : ∀ ω, I.prob ω = I.p e (ω e) * P' ω := by
    intro ω
    unfold Instance.prob
    rw [hP', Finset.mul_prod_erase Finset.univ (fun i => I.p i (ω i)) (Finset.mem_univ e)]
  have hprob' : ∀ ω, I'.prob ω = I'.p e (ω e) * P' ω := by
    intro ω
    unfold Instance.prob
    rw [← Finset.mul_prod_erase Finset.univ (fun i => I'.p i (ω i)) (Finset.mem_univ e)]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [hpe i (Finset.ne_of_mem_erase hi)]
  have hP'u : ∀ ω u, P' (Function.update ω e u) = P' ω := by
    intro ω u
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  set Ψ : (Fin m → U) × U → ℝ := fun x =>
    I'.p e x.2 * (I.p e (x.1 e) * P' x.1 * H x.1) with hΨ
  have h1 : I.E H = ∑ x, Ψ x := by
    rw [Fintype.sum_prod_type]
    unfold Instance.E
    apply Finset.sum_congr rfl; intro ω _
    rw [hΨ]; simp only
    rw [← Finset.sum_mul, hp1', one_mul, hprob]
  have h2 : ∑ x, Ψ x = ∑ x, Ψ (swapE e x) :=
    (Equiv.sum_comp (Function.Involutive.toPerm _ (swapE_invol e)) Ψ).symm
  rw [h1, h2, Fintype.sum_prod_type]
  unfold Instance.E
  apply Finset.sum_congr rfl; intro ω _
  simp only [hΨ, swapE, Function.update_self, hP'u, hH]
  have : ∑ y, I'.p e (ω e) * (I.p e y * P' ω * H ω) = (∑ y, I.p e y) * (I'.p e (ω e) * P' ω * H ω) := by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro y _; ring
  rw [this, hp1, hprob']
  ring

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem E_of_p_eq (I I' : Instance U m) (h : ∀ i, I'.p i = I.p i) (H : (Fin m → U) → ℝ) :
    I'.E H = I.E H := by
  unfold Instance.E Instance.prob
  simp [h]

/-- Changing the laws of the coordinates in `D` does not affect a function independent of them. -/
theorem E_lawchange (I I' : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) (D : Finset (Fin m))
    (hp1' : ∀ i ∈ D, ∑ u, I'.p i u = 1) (hout : ∀ i, i ∉ D → I'.p i = I.p i)
    (H : (Fin m → U) → ℝ) (hH : ∀ ν, ∀ e ∈ D, ∀ a, H (Function.update ν e a) = H ν) :
    I'.E H = I.E H := by
  classical
  -- interpolating instances
  let J : Finset (Fin m) → Instance U m := fun A =>
    ⟨fun i u => if i ∈ A then I'.p i u else I.p i u, I.c, I.f⟩
  have hJ : ∀ A ⊆ D, (J A).E H = I.E H := by
    intro A
    induction A using Finset.induction_on with
    | empty => intro _; exact E_of_p_eq I (J ∅) (fun i => by funext u; simp [J]) H
    | insert e A he ih =>
      intro hsub
      have heD : e ∈ D := hsub (Finset.mem_insert_self e A)
      rw [← ih ((Finset.subset_insert e A).trans hsub)]
      symm
      apply E_change (J A) (J (insert e A)) e
      · simp [J, he]; exact hp1 e
      · simp [J]; exact hp1' e heD
      · intro i hi; funext u; simp [J, hi]
      · intro ν a; exact hH ν e heD a
  rw [← hJ D le_rfl]
  apply E_of_p_eq
  intro i; funext u
  by_cases hi : i ∈ D
  · simp [J, hi]
  · simp [J, hi, hout i hi]

/-- The instance in which the items of `S` are fixed to their values under `ω` and are free. -/
def condInst (I : Instance U m) (S : Finset (Fin m)) (ω : Fin m → U) : Instance U m :=
  ⟨fun i u => if i ∈ S then (if u = ω i then 1 else 0) else I.p i u,
   fun i => if i ∈ S then 0 else I.c i, I.f⟩

theorem condInst_E (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (hp1 : ∀ i, ∑ u, I.p i u = 1)
    (S : Finset (Fin m)) (ω : Fin m → U) (G : (Fin m → U) → ℝ) :
    (condInst I S ω).E G = I.E (fun ν => G (S.piecewise ω ν)) := by
  have h1 : (condInst I S ω).E G = (condInst I S ω).E (fun ν => G (S.piecewise ω ν)) := by
    unfold Instance.E
    apply Finset.sum_congr rfl; intro ν _
    by_cases hν : ∀ i ∈ S, ν i = ω i
    · congr 2
      ext x
      by_cases hx : x ∈ S
      · simp [Finset.piecewise, hx, hν x hx]
      · simp [Finset.piecewise, hx]
    · push Not at hν
      obtain ⟨i, hiS, hne⟩ := hν
      have : (condInst I S ω).prob ν = 0 := by
        unfold Instance.prob
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [condInst, hiS, hne]
      rw [this]; simp
  rw [h1]
  apply E_lawchange I (condInst I S ω) hp1 S
  · intro i hi; simp [condInst, hi]
  · intro i hi; funext u; simp [condInst, hi]
  · intro ν e he a
    congr 1
    ext x
    by_cases hx : x ∈ S
    · simp [Finset.piecewise, hx]
    · have : x ≠ e := fun h => hx (h ▸ he)
      simp [Finset.piecewise, hx, Function.update_of_ne this]

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem items_append (h : History m U) (x : Fin m × U) :
    (h ++ [x]).items = insert x.1 h.items := by
  ext y; simp [History.items, or_comm]

theorem realized_append (h : History m U) (x : Fin m × U) :
    (h ++ [x]).realized = insert x.2 h.realized := by
  ext y; simp [History.realized, or_comm]

theorem costOf_append (I : Instance U m) (h : History m U) (x : Fin m × U) (hx : x.1 ∉ h.items) :
    I.costOf (h ++ [x]) = I.costOf h + I.c x.1 := by
  unfold Instance.costOf
  rw [items_append, Finset.sum_insert hx, add_comm]

theorem items_prefix {h h' : History m U} (hp : h <+: h') : h.items ⊆ h'.items := by
  obtain ⟨t, rfl⟩ := hp
  intro x hx
  simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union] at hx ⊢
  exact Or.inl hx

theorem step_prefix (π : AdaptivePolicy m U) (ω : Fin m → U) (h : History m U) :
    h <+: π.step ω h := by
  unfold AdaptivePolicy.step
  split
  · split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  · exact List.prefix_refl _

theorem iterate_prefix (π : AdaptivePolicy m U) (ω : Fin m → U) (h : History m U) :
    ∀ a b, a ≤ b → (π.step ω)^[a] h <+: (π.step ω)^[b] h := by
  intro a b hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine (ih (by omega)).trans ?_
    rw [← Nat.add_assoc, Function.iterate_succ_apply']
    exact step_prefix π ω _

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

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

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem dimret (f : Finset U → ℝ) (hfm : Monotone f) (hfs : NonmonotoneSubmod.Shared.Submodular f)
    (A A' B : Finset U) (h : A ⊆ A') : f (A' ∪ B) - f A' ≤ f (A ∪ B) - f A := by
  have := hfs (A ∪ B) A'
  have e1 : A ∪ B ∪ A' = A' ∪ B := by
    ext x; simp only [Finset.mem_union]; have := @h x; tauto
  have h2 : f A ≤ f ((A ∪ B) ∩ A') := hfm (fun x hx => Finset.mem_inter.mpr
    ⟨Finset.mem_union_left _ hx, h hx⟩)
  rw [e1] at this
  linarith

theorem ind_nonneg (p : Prop) {inst : Decidable p} : (0 : ℝ) ≤ if p then 1 else 0 := by
  split <;> norm_num

theorem E_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 ≤ F ω) : 0 ≤ I.E F :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (prob_nonneg I hp0 ω) (h ω)

theorem E_mul_const (I : Instance U m) (F : (Fin m → U) → ℝ) (c : ℝ) :
    I.E (fun ω => F ω * c) = I.E F * c := by
  unfold Instance.E; rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro ω _; ring

theorem cost_union (c : Fin m → ℕ) (A B : Finset (Fin m)) :
    ∑ e ∈ A ∪ B, c e ≤ ∑ e ∈ A, c e + ∑ e ∈ B, c e := by
  have := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := c)
  omega

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem go_prefix (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), h <+: Round.go stop ω L h
  | [], h => by simp [Round.go]
  | i :: L, h => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact List.prefix_refl _
    · exact go_prefix stop ω L h
    · exact (List.prefix_append h _).trans (go_prefix stop ω L _)

theorem go_append (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l1 l2 : List (Fin m)) (h : History m U),
      Round.go stop ω (l1 ++ l2) h = Round.go stop ω l2 (Round.go stop ω l1 h)
  | [], l2, h => by simp [Round.go]
  | i :: l1, l2, h => by
    simp only [List.cons_append, Round.go]
    split_ifs with h1 h2
    · cases l2 with
      | nil => rfl
      | cons j l2 => simp [Round.go, h1]
    · exact go_append stop ω l1 l2 _
    · exact go_append stop ω l1 l2 _

/-- Running from `h ++ x` is running from `x` with the shifted rule, then prefixing `h`. -/
theorem go_shift (stop stop' : History m U → Bool) (ω : Fin m → U) (h : History m U)
    (hst : ∀ x, stop (h ++ x) = stop' x) :
    ∀ (l : List (Fin m)) (x : History m U), (∀ i ∈ l, i ∉ h.items) →
      Round.go stop ω l (h ++ x) = h ++ Round.go stop' ω l x
  | [], x, _ => by simp [Round.go]
  | i :: l, x, hdis => by
    have hi : i ∉ h.items := hdis i (by simp)
    have hdis' : ∀ j ∈ l, j ∉ h.items := fun j hj => hdis j (by simp [hj])
    simp only [Round.go, hst]
    split_ifs with h1 h2 h3 h3
    · rfl
    · exact go_shift stop stop' ω h hst l x hdis'
    · exfalso; apply h3
      simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union] at h2
      rcases h2 with h2 | h2
      · exact absurd h2 hi
      · exact h2
    · exfalso; apply h2
      simp only [History.items, List.map_append, List.toFinset_append, Finset.mem_union]
      exact Or.inr h3
    · rw [List.append_assoc]; exact go_shift stop stop' ω h hst l _ hdis'

/-- A round reads the realization only at the items it probes. -/
theorem go_agree (stop : History m U → Bool) (ω ω' : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U),
      (∀ i ∈ (Round.go stop ω l h).items, ω' i = ω i) →
      Round.go stop ω' l h = Round.go stop ω l h
  | [], h, _ => rfl
  | i :: l, h, hag => by
    by_cases h1 : stop h = true
    · simp [Round.go, h1]
    · by_cases h2 : i ∈ h.items
      · have e : ∀ ω₀ : Fin m → U, Round.go stop ω₀ (i :: l) h = Round.go stop ω₀ l h :=
          fun ω₀ => by simp [Round.go, h1, h2]
        rw [e ω] at hag; rw [e ω, e ω']; exact go_agree stop ω ω' l h hag
      · have e : ∀ ω₀ : Fin m → U, Round.go stop ω₀ (i :: l) h =
            Round.go stop ω₀ l (h ++ [(i, ω₀ i)]) := fun ω₀ => by simp [Round.go, h1, h2]
        rw [e ω] at hag; rw [e ω, e ω']
        have hi : ω' i = ω i :=
          hag i (items_prefix (go_prefix stop ω l _) (by simp [History.items]))
        rw [hi]; exact go_agree stop ω ω' l _ hag

theorem go_items_sub (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U),
      (Round.go stop ω l h).items ⊆ h.items ∪ l.toFinset
  | [], h => by simp [Round.go]
  | i :: l, h => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact Finset.subset_union_left
    · refine (go_items_sub stop ω l h).trans ?_
      intro x hx; simp only [Finset.mem_union, List.mem_toFinset, List.mem_cons] at hx ⊢; tauto
    · refine (go_items_sub stop ω l _).trans ?_
      rw [items_append]
      intro x hx
      simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset, List.mem_cons] at hx ⊢
      tauto

/-- Histories produced by executions record true realizations. -/
def Honest (ω : Fin m → U) (h : History m U) : Prop := ∀ p ∈ h, p.2 = ω p.1

theorem go_honest (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (L : List (Fin m)) (h : History m U), Honest ω h → Honest ω (Round.go stop ω L h)
  | [], h, hh => by simpa [Round.go] using hh
  | i :: L, h, hh => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact hh
    · exact go_honest stop ω L h hh
    · apply go_honest stop ω L
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hh p hp
      · simp at hp; subst hp; rfl

theorem realized_eq (ω : Fin m → U) (h : History m U) (hh : Honest ω h) :
    h.realized = h.items.image ω := by
  ext u
  simp only [History.realized, History.items, List.mem_toFinset, List.mem_map, Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.1, ⟨p, hp, rfl⟩, (hh p hp).symm⟩
  · rintro ⟨i, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨p, hp, hh p hp⟩

/-! ### Round policies -/

theorem run_succ (σ : RoundPolicy m U) (ω : Fin m → U) (k : ℕ) :
    σ.run ω (k + 1) = (σ k (σ.run ω k)).run ω (σ.run ω k) := rfl

theorem run_prefix (σ : RoundPolicy m U) (ω : Fin m → U) :
    ∀ a b, a ≤ b → σ.run ω a <+: σ.run ω b := by
  intro a b hab
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact List.prefix_refl _
  | succ d ih =>
    refine (ih (by omega)).trans ?_
    rw [← Nat.add_assoc, run_succ]
    exact go_prefix _ _ _ _

theorem run_honest (σ : RoundPolicy m U) (ω : Fin m → U) : ∀ k, Honest ω (σ.run ω k) := by
  intro k
  induction k with
  | zero => intro p hp; simp [RoundPolicy.run] at hp
  | succ k ih => rw [run_succ]; exact go_honest _ _ _ _ ih

theorem run_agree (σ : RoundPolicy m U) (ω ω' : Fin m → U) (K : ℕ)
    (hag : ∀ i ∈ (σ.run ω K).items, ω' i = ω i) : ∀ k ≤ K, σ.run ω' k = σ.run ω k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    rw [run_succ, run_succ, ih (by omega)]
    apply go_agree
    intro i hi
    apply hag
    apply items_prefix (run_prefix σ ω (k + 1) K hk)
    rw [run_succ]; exact hi

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem E_sum {ι : Type} (I : Instance U m) (s : Finset ι) (F : ι → (Fin m → U) → ℝ) :
    I.E (fun ω => ∑ j ∈ s, F j ω) = ∑ j ∈ s, I.E (F j) := by
  unfold Instance.E
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The cylinder of realizations compatible with a history. -/
def cyl (h : History m U) (ω : Fin m → U) : Prop := ∀ p ∈ h, ω p.1 = p.2

theorem run_eq_iff_cyl (σ : RoundPolicy m U) (ω0 : Fin m → U) (k : ℕ) (ω : Fin m → U) :
    σ.run ω k = σ.run ω0 k ↔ cyl (σ.run ω0 k) ω := by
  constructor
  · intro h p hp
    rw [← h] at hp
    exact (run_honest σ ω k p hp).symm
  · intro hc
    apply run_agree σ ω0 ω k _ k le_rfl
    intro i hi
    simp only [History.items, List.mem_toFinset, List.mem_map] at hi
    obtain ⟨p, hp, rfl⟩ := hi
    rw [hc p hp, run_honest σ ω0 k p hp]

theorem cyl_pw (h : History m U) (ω ν : Fin m → U) :
    cyl h (h.items.piecewise ω ν) ↔ cyl h ω := by
  unfold cyl
  have : ∀ p ∈ h, (h.items.piecewise ω ν) p.1 = ω p.1 := by
    intro p hp
    have : p.1 ∈ h.items := by
      simp only [History.items, List.mem_toFinset, List.mem_map]; exact ⟨p, hp, rfl⟩
    simp [Finset.piecewise, this]
  constructor
  · intro hc p hp; rw [← this p hp]; exact hc p hp
  · intro hc p hp; rw [this p hp]; exact hc p hp

/-- Conditioning on a cylinder: the conditional law is the instance with `h` fixed. -/
theorem E_cyl (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (hp1 : ∀ i, ∑ u, I.p i u = 1)
    (h : History m U) (ωh : Fin m → U) (hh : Honest ωh h) (G : (Fin m → U) → ℝ) :
    I.E (fun ω => @ite ℝ (cyl h ω) (Classical.propDecidable _) 1 0 * G ω) =
      I.P (cyl h) * (condInst I h.items ωh).E G := by
  rw [E_indep I hp1 h.items, condInst_E I hp0 hp1]
  unfold Instance.P
  rw [← E_mul_const]
  apply E_congr; intro ω
  by_cases hc : cyl h ω
  · have hpw : ∀ ν, h.items.piecewise ω ν = h.items.piecewise ωh ν := by
      intro ν
      ext i
      by_cases hi : i ∈ h.items
      · simp only [Finset.piecewise, hi, if_true]
        simp only [History.items, List.mem_toFinset, List.mem_map] at hi
        obtain ⟨p, hp, rfl⟩ := hi
        rw [hc p hp, hh p hp]
      · simp [Finset.piecewise, hi]
    rw [if_pos hc, one_mul]
    apply E_congr; intro ν
    rw [if_pos ((cyl_pw h ω ν).mpr hc), one_mul, hpw]
  · rw [if_neg hc, zero_mul]
    unfold Instance.E
    apply Finset.sum_eq_zero; intro ν _
    beta_reduce
    rw [if_neg (fun h' => hc ((cyl_pw h ω ν).mp h')), zero_mul, mul_zero]

/-- Partition of the outcome space according to the history after `k` rounds. -/
theorem E_partition (I : Instance U m) (σ : RoundPolicy m U) (k : ℕ) (G : (Fin m → U) → ℝ) :
    I.E G = ∑ h ∈ Finset.univ.image (fun ω => σ.run ω k),
      I.E (fun ω => @ite ℝ (cyl h ω) (Classical.propDecidable _) 1 0 * G ω) := by
  rw [← E_sum]
  apply E_congr; intro ω
  rw [Finset.sum_eq_single_of_mem (σ.run ω k)
    (Finset.mem_image_of_mem (fun ω => σ.run ω k) (Finset.mem_univ ω))]
  · have hc : cyl (σ.run ω k) ω := fun p hp => (run_honest σ ω k p hp).symm
    rw [if_pos hc, one_mul]
  · intro h hh hne
    obtain ⟨ω0, -, rfl⟩ := Finset.mem_image.mp hh
    rw [if_neg, zero_mul]
    intro hc
    exact hne ((run_eq_iff_cyl σ ω0 k ω).mpr hc).symm

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- The residual instance after a history `h`: the items of `h` are fixed to their observed
values, and the function is the contraction `f_R(A) = f(R ∪ A) - f(R)`. -/
def resInst (I : Instance U m) (h : History m U) (ωh : Fin m → U) : Instance U m :=
  ⟨(condInst I h.items ωh).p, I.c, fun A => I.f (h.realized ∪ A) - I.f h.realized⟩

theorem condInst_p0 (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (S : Finset (Fin m))
    (ω : Fin m → U) : ∀ k u, 0 ≤ (condInst I S ω).p k u := by
  intro k u; simp only [condInst]
  split_ifs
  · norm_num
  · norm_num
  · exact hp0 k u

theorem condInst_p1 (I : Instance U m) (hp1 : ∀ i, ∑ u, I.p i u = 1) (S : Finset (Fin m))
    (ω : Fin m → U) : ∀ k, ∑ u, (condInst I S ω).p k u = 1 := by
  intro k; simp only [condInst]
  split_ifs with hk
  · simp
  · exact hp1 k

theorem resInst_f_real (I : Instance U m) (hmon : Monotone I.f) (h : History m U)
    (ωh : Fin m → U) (A : Finset U) :
    ((resInst I h ωh).f A : ℝ) = (I.f (h.realized ∪ A) : ℝ) - I.f h.realized := by
  simp only [resInst]
  rw [Nat.cast_sub (hmon Finset.subset_union_left)]

theorem union_univ' (A : Finset U) : A ∪ Finset.univ = Finset.univ :=
  Finset.union_eq_right.mpr (Finset.subset_univ _)

theorem factor_pos (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (ω : Fin m → U)
    (h : 0 < I.prob ω) (i : Fin m) : 0 < I.p i (ω i) := by
  rcases (hp0 i (ω i)).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have : I.prob ω = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h1.symm
    linarith

theorem resInst_Q (I : Instance U m) (hmon : Monotone I.f) (h : History m U) (ωh : Fin m → U) :
    ((resInst I h ωh).Q : ℝ) = (I.Q : ℝ) - I.f h.realized := by
  unfold Instance.Q
  rw [resInst_f_real I hmon, union_univ']

theorem resInst_standing (I : Instance U m) (hI : I.Standing) (h : History m U)
    (ωh : Fin m → U) : (resInst I h ωh).Standing := by
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI
  refine ⟨condInst_p0 I hp0 _ _, condInst_p1 I hp1 _ _, hc1, ?_, ?_⟩
  · intro A B hAB
    simp only [resInst]
    exact Nat.sub_le_sub_right (hmon (Finset.union_subset_union le_rfl hAB)) _
  · have : (fun S => ((resInst I h ωh).f S : ℝ)) =
        (fun S => (fun A => (I.f A : ℝ)) (h.realized ∪ S) - (fun A => (I.f A : ℝ)) h.realized) := by
      funext S; exact resInst_f_real I hmon h ωh S
    rw [this]
    exact contr_sub _ hsub _

/-- Outcomes of positive probability in the residual instance are compatible with `h` and have
positive probability in the original instance. -/
theorem resInst_support (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (h : History m U)
    (ωh : Fin m → U) (hh : Honest ωh h) (hpos : 0 < I.prob ωh) (ν : Fin m → U)
    (hν : 0 < (resInst I h ωh).prob ν) : 0 < I.prob ν ∧ cyl h ν := by
  have hagree : ∀ i ∈ h.items, ν i = ωh i := by
    intro i hi
    by_contra hne
    have : (resInst I h ωh).prob ν = 0 := by
      unfold Instance.prob
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [resInst, condInst, hi, hne]
    linarith
  constructor
  · unfold Instance.prob
    apply Finset.prod_pos
    intro i _
    by_cases hi : i ∈ h.items
    · rw [hagree i hi]
      exact factor_pos I hp0 ωh hpos i
    · have h1 : 0 < (resInst I h ωh).p i (ν i) :=
        factor_pos (resInst I h ωh) (condInst_p0 I hp0 _ _) ν hν i
      simpa [resInst, condInst, hi] using h1
  · intro p hp
    have : p.1 ∈ h.items := by
      simp only [History.items, List.mem_toFinset, List.mem_map]; exact ⟨p, hp, rfl⟩
    rw [hagree p.1 this, hh p hp]

theorem resInst_feasible (I : Instance U m) (hI : I.Standing) (h : History m U)
    (ωh : Fin m → U) (hh : Honest ωh h) (hpos : 0 < I.prob ωh) (π : AdaptivePolicy m U)
    (hπ : I.Feasible π) : (resInst I h ωh).Feasible π := by
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI
  intro ν hν
  obtain ⟨hνI, -⟩ := resInst_support I hp0 h ωh hh hpos ν hν
  have hc := hπ ν hνI
  unfold Instance.Covers at hc ⊢
  unfold Instance.Q at hc ⊢
  show I.f (h.realized ∪ (π.run ν).realized) - I.f h.realized =
    I.f (h.realized ∪ Finset.univ) - I.f h.realized
  rw [union_univ']
  congr 1
  apply le_antisymm
  · exact hmon (Finset.subset_univ _)
  · have : I.f (π.run ν).realized ≤ I.f (h.realized ∪ (π.run ν).realized) :=
      hmon Finset.subset_union_right
    omega

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem score_nonneg (I : Instance U m) (hI : I.Standing) (τ : ℝ) (S : Finset (Fin m))
    (e : Fin m) : 0 ≤ I.scoreG (fun A => (I.f A : ℝ)) I.Q τ S e := by
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI
  unfold Instance.scoreG
  apply mul_nonneg (by positivity)
  apply E_nonneg I hp0
  intro ω
  split
  · apply div_nonneg
    · have : (I.f (S.image ω) : ℝ) ≤ I.f (insert (ω e) (S.image ω)) := by
        exact_mod_cast hmon (Finset.subset_insert _ _)
      linarith
    · have : (I.f (S.image ω) : ℝ) ≤ I.Q := by
        unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ _)
      linarith
  · exact le_refl _

theorem honest_mem_realized (ωh : Fin m → U) (h : History m U) (hh : Honest ωh h) (e : Fin m)
    (he : e ∈ h.items) : ωh e ∈ h.realized := by
  simp only [History.items, List.mem_toFinset, List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  simp only [History.realized, List.mem_toFinset, List.mem_map]
  exact ⟨p, hp, hh p hp⟩

/-- Items already probed have score `0` in the residual instance. -/
theorem res_score_zero (I : Instance U m) (hI : I.Standing) (h : History m U) (ωh : Fin m → U)
    (hh : Honest ωh h) (τ : ℝ) (S : Finset (Fin m)) (e : Fin m) (he : e ∈ h.items) :
    (resInst I h ωh).scoreG (fun A => ((resInst I h ωh).f A : ℝ)) (resInst I h ωh).Q τ S e = 0 := by
  have hmon := hI.2.2.2.1
  unfold Instance.scoreG
  apply mul_eq_zero_of_right
  unfold Instance.E
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hω : ω e = ωh e
  · have hv : ω e ∈ h.realized := hω ▸ honest_mem_realized ωh h hh e he
    have hset : h.realized ∪ insert (ω e) (S.image ω) = h.realized ∪ S.image ω := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert]
      constructor
      · rintro (h1 | rfl | h1)
        · exact Or.inl h1
        · exact Or.inl hv
        · exact Or.inr h1
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inr h1)
    have : (resInst I h ωh).f (insert (ω e) (S.image ω)) = (resInst I h ωh).f (S.image ω) := by
      show I.f (h.realized ∪ insert (ω e) (S.image ω)) - _ = I.f (h.realized ∪ S.image ω) - _
      rw [hset]
    beta_reduce
    rw [this]; simp
  · have : (resInst I h ωh).prob ω = 0 := by
      unfold Instance.prob
      apply Finset.prod_eq_zero (Finset.mem_univ e)
      simp [resInst, condInst, he, hω]
    rw [this, zero_mul]

/-- Scores of fresh items are the same in the residual instance. -/
theorem res_score_eq (I : Instance U m) (hI : I.Standing) (h : History m U) (ωh : Fin m → U)
    (τ : ℝ) (S : Finset (Fin m)) (hS : S ⊆ Finset.univ \ h.items) (e : Fin m)
    (he : e ∉ h.items) :
    (resInst I h ωh).scoreG (fun A => ((resInst I h ωh).f A : ℝ)) (resInst I h ωh).Q τ S e =
      I.scoreG (fun A => (I.f (h.realized ∪ A) : ℝ) - I.f h.realized)
        ((I.Q : ℝ) - I.f h.realized) τ S e := by
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI
  unfold Instance.scoreG
  simp only [resInst_f_real I hmon, resInst_Q I hmon]
  congr 1
  apply E_lawchange I (resInst I h ωh) hp1 h.items
  · intro i hi; exact condInst_p1 I hp1 _ _ i
  · intro i hi; funext u; simp [resInst, condInst, hi]
  · intro ν d hd a
    have hSimg : S.image (Function.update ν d a) = S.image ν := by
      apply Finset.image_congr
      intro x hx
      have : x ≠ d := by
        intro hxd; subst hxd
        exact (Finset.mem_sdiff.mp (hS (Finset.mem_coe.mp hx))).2 hd
      simp [Function.update_of_ne this]
    have hed : e ≠ d := fun hed => he (hed ▸ hd)
    simp only [hSimg, Function.update_of_ne hed]

/-- The greedy list of a later round, completed by the already-probed items, is a greedy list of
the residual instance. -/
theorem greedy_transport (I : Instance U m) (hI : I.Standing) (h : History m U) (ωh : Fin m → U)
    (hh : Honest ωh h) (τ : ℝ) (order : List (Fin m))
    (hg : I.IsGreedyList (fun A => (I.f (h.realized ∪ A) : ℝ) - I.f h.realized)
      ((I.Q : ℝ) - I.f h.realized) τ (Finset.univ \ h.items) order) :
    (resInst I h ωh).IsGreedyList (fun A => ((resInst I h ωh).f A : ℝ)) (resInst I h ωh).Q τ
      Finset.univ (order ++ h.items.toList) := by
  obtain ⟨hnd, hset, hgr⟩ := hg
  have hordS : ∀ x ∈ order, x ∉ h.items := by
    intro x hx
    have : x ∈ order.toFinset := List.mem_toFinset.mpr hx
    rw [hset] at this
    exact (Finset.mem_sdiff.mp this).2
  have hIres := resInst_standing I hI h ωh
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hnd, Finset.nodup_toList _, ?_⟩
    intro a ha b hb hab
    subst hab
    exact hordS a ha (Finset.mem_toList.mp hb)
  · rw [List.toFinset_append, hset, Finset.toList_toFinset]
    ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]; tauto
  · intro k hk e he
    rcases Nat.lt_or_ge k order.length with hko | hko
    · have ht : (order ++ h.items.toList).take k = order.take k :=
        List.take_append_of_le_length hko.le
      have hget : (order ++ h.items.toList)[k]'hk = order[k]'hko := List.getElem_append_left hko
      rw [ht] at he
      rw [ht, hget]
      have hSsub : (order.take k).toFinset ⊆ Finset.univ \ h.items := by
        rw [← hset]; intro x hx
        simp only [List.mem_toFinset] at hx ⊢
        exact List.take_subset _ _ hx
      have hok : order[k]'hko ∉ h.items := hordS _ (List.getElem_mem hko)
      rw [res_score_eq I hI h ωh τ _ hSsub _ hok]
      by_cases heh : e ∈ h.items
      · rw [res_score_zero I hI h ωh hh τ _ e heh, ← res_score_eq I hI h ωh τ _ hSsub _ hok]
        exact score_nonneg _ hIres τ _ _
      · rw [res_score_eq I hI h ωh τ _ hSsub _ heh]
        apply hgr k hko e
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at he ⊢
        exact ⟨heh, he⟩
    · have hget : (order ++ h.items.toList)[k]'hk ∈ h.items := by
        rw [List.getElem_append_right hko]
        exact Finset.mem_toList.mp (List.getElem_mem _)
      rw [res_score_zero I hI h ωh hh τ _ _ hget]
      have heh : e ∈ h.items := by
        by_contra heh
        have : e ∈ order.toFinset := by
          rw [hset]; simp [heh]
        have h2 : e ∈ ((order ++ h.items.toList).take k).toFinset := by
          rw [List.take_append, List.take_of_length_le hko, List.toFinset_append]
          exact Finset.mem_union_left _ this
        exact (Finset.mem_sdiff.mp he).2 h2
      rw [res_score_zero I hI h ωh hh τ _ _ heh]

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem E_mono' (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 < I.prob ω → F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  apply Finset.sum_le_sum
  intro ω _
  rcases (prob_nonneg I hp0 ω).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h ω hp) hp.le
  · rw [← hp]; simp

/-- The statement of Theorem 3.1 with a fixed constant, for one ground set. -/
def T31 (C : ℝ) (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) : Prop :=
  ∀ (J : Instance U m), J.Standing → 0 < J.Q → (∃ π : AdaptivePolicy m U, J.Feasible π) →
    ∀ z : ℕ,
      (∃ L : List (Fin m), J.IsGreedyList (fun A => (J.f A : ℝ)) J.Q (J.tau z) Finset.univ L) ∧
      ∀ L : List (Fin m), J.IsGreedyList (fun A => (J.f A : ℝ)) J.Q (J.tau z) Finset.univ L →
        (∀ ω, 0 < J.prob ω → J.tau z < (J.f (J.NA (J.tau z) L ω).realized : ℝ)) ∧
        ∀ π : AdaptivePolicy m U, J.Feasible π →
          J.E (fun ω => (J.costOf (J.NA (J.tau z) L ω) : ℝ)) ≤
            C * ((1 + Real.log (1 / delta z)) / delta z) * J.expCost π

theorem realized_append' (h x : History m U) : (h ++ x).realized = h.realized ∪ x.realized := by
  ext u; simp [History.realized]

theorem items_append' (h x : History m U) : (h ++ x).items = h.items ∪ x.items := by
  ext u; simp [History.items]

theorem costOf_append' (I : Instance U m) (h x : History m U) (hd : Disjoint h.items x.items) :
    I.costOf (h ++ x) = I.costOf h + I.costOf x := by
  unfold Instance.costOf
  rw [items_append', Finset.sum_union hd]

theorem costOf_prefix (I : Instance U m) {h h' : History m U} (hp : h <+: h') :
    I.costOf h ≤ I.costOf h' :=
  Finset.sum_le_sum_of_subset_of_nonneg (items_prefix hp) (fun _ _ _ => Nat.zero_le _)

/-- Entries appended by a round have the form `(i, ω i)` with `i` from its list. -/
theorem go_realized_sub (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (x : History m U),
      (Round.go stop ω l x).realized ⊆ x.realized ∪ l.toFinset.image ω
  | [], x => by simp [Round.go]
  | i :: l, x => by
    simp only [Round.go]
    split_ifs with h1 h2
    · exact Finset.subset_union_left
    · refine (go_realized_sub stop ω l x).trans ?_
      intro u hu
      simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset, List.mem_cons] at hu ⊢
      rcases hu with hu | ⟨a, ha, rfl⟩
      · exact Or.inl hu
      · exact Or.inr ⟨a, Or.inr ha, rfl⟩
    · refine (go_realized_sub stop ω l _).trans ?_
      rw [realized_append]
      intro u hu
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_image, List.mem_toFinset,
        List.mem_cons] at hu ⊢
      rcases hu with (rfl | hu) | ⟨a, ha, rfl⟩
      · exact Or.inr ⟨i, Or.inl rfl, rfl⟩
      · exact Or.inl hu
      · exact Or.inr ⟨a, Or.inr ha, rfl⟩

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- One later round of Algorithm 2 (round `k ≥ 1`), analysed through the residual instance:
coverage on every compatible outcome, and Theorem 3.1's cost bound conditioned on the history. -/
theorem round_res (C31 : ℝ) (hT : T31 C31 U m) (I : Instance U m) (hI : I.Standing)
    (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k < r) (σ : RoundPolicy m U) (hSSC : I.IsSSC r σ)
    (ω0 : Fin m → U) (hpos0 : 0 < I.prob ω0) (π0 : AdaptivePolicy m U) (hπ0 : I.Feasible π0)
    (hq : 0 < (I.Q : ℝ) - I.f (σ.run ω0 k).realized) :
    (∀ ν, 0 < I.prob ν → cyl (σ.run ω0 k) ν →
      ((I.Q : ℝ) - I.f (σ.run ω0 k).realized) *
          (1 - delta ⌈Real.logb 2 ((I.Q : ℝ) - I.f (σ.run ω0 k).realized) / ((r : ℝ) - k)⌉₊) <
        (I.f (σ.run ν (k + 1)).realized : ℝ) - I.f (σ.run ω0 k).realized) ∧
    (∀ π : AdaptivePolicy m U, I.Feasible π →
      (condInst I (σ.run ω0 k).items ω0).E
          (fun ν => (I.costOf (σ.run ν (k + 1)) : ℝ) - I.costOf (σ.run ν k)) ≤
        C31 * ((1 + Real.log (1 / delta
          ⌈Real.logb 2 ((I.Q : ℝ) - I.f (σ.run ω0 k).realized) / ((r : ℝ) - k)⌉₊)) /
          delta ⌈Real.logb 2 ((I.Q : ℝ) - I.f (σ.run ω0 k).realized) / ((r : ℝ) - k)⌉₊) *
        (condInst I (σ.run ω0 k).items ω0).E (fun ν => (I.costOf (π.run ν) : ℝ))) := by
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  set h := σ.run ω0 k with hhdef
  set R := h.realized with hR
  set Q' : ℝ := (I.Q : ℝ) - I.f R with hQ'
  set z := ⌈Real.logb 2 Q' / ((r : ℝ) - k)⌉₊ with hz
  set τ' : ℝ := Q' * (1 - delta z) with hτ'
  have hh : Honest ω0 h := run_honest σ ω0 k
  have hk0 : k ≠ 0 := by omega
  have hSk := hSSC k hkr h
  simp only [if_neg hk0] at hSk
  rcases hSk with ⟨hQ0, -⟩ | ⟨-, hgreedy, hstop⟩
  · exfalso; rw [← hR] at hQ0; linarith
  rw [← hR] at hgreedy hstop
  set order := (σ k h).order with horder
  set J := resInst I h ω0 with hJ
  have hJs : J.Standing := resInst_standing I hI h ω0
  have hJQ : (J.Q : ℝ) = Q' := resInst_Q I hmon h ω0
  have hJQpos : 0 < J.Q := by exact_mod_cast (show (0 : ℝ) < J.Q by rw [hJQ]; exact hq)
  have hJfeas : ∀ π, I.Feasible π → J.Feasible π :=
    fun π hπ => resInst_feasible I hI h ω0 hh hpos0 π hπ
  have hJτ : J.tau z = τ' := by unfold Instance.tau; rw [hJQ]
  obtain ⟨-, hL⟩ := hT J hJs hJQpos ⟨π0, hJfeas π0 hπ0⟩ z
  set L' := order ++ h.items.toList with hL'
  have hgr' : J.IsGreedyList (fun A => (J.f A : ℝ)) J.Q (J.tau z) Finset.univ L' := by
    rw [hJτ]; exact greedy_transport I hI h ω0 hh τ' order hgreedy
  obtain ⟨hcov, hcost⟩ := hL L' hgr'
  -- the rule of NA in the residual instance
  set stop' := (J.parcaRound (J.tau z) L').stop with hstop'
  have hst : ∀ x : History m U, (σ k h).stop (h ++ x) = stop' x := by
    intro x
    rw [hstop (h ++ x), hstop']
    simp only [Instance.parcaRound]
    rw [hJτ, resInst_f_real I hmon, realized_append', ← Finset.union_assoc, Finset.union_self]
  have hordS : ∀ x ∈ order, x ∉ h.items := by
    intro x hx
    have : x ∈ order.toFinset := List.mem_toFinset.mpr hx
    rw [hgreedy.2.1] at this
    exact (Finset.mem_sdiff.mp this).2
  -- the round from `h` is the residual NA on the order list
  have hrel : ∀ ν, cyl h ν → σ.run ν (k + 1) = h ++ Round.go stop' ν order [] := by
    intro ν hc
    have hrun : σ.run ν k = h := (run_eq_iff_cyl σ ω0 k ν).mpr hc
    rw [run_succ, hrun]
    show Round.go (σ k h).stop ν order h = _
    have := go_shift (σ k h).stop stop' ν h hst order [] hordS
    simpa using this
  have hNA : ∀ ν, J.NA (J.tau z) L' ν = Round.go stop' ν h.items.toList (Round.go stop' ν order []) := by
    intro ν
    show Round.go stop' ν (order ++ h.items.toList) [] = _
    exact go_append stop' ν order h.items.toList []
  have hydisj : ∀ ν, Disjoint h.items (Round.go stop' ν order []).items := by
    intro ν
    rw [Finset.disjoint_left]
    intro i hi hi'
    have := go_items_sub stop' ν order [] hi'
    simp only [Finset.mem_union, List.mem_toFinset] at this
    rcases this with h1 | h1
    · simp [History.items] at h1
    · exact hordS i h1 hi
  refine ⟨?_, ?_⟩
  · intro ν hν hc
    have hJν : 0 < J.prob ν := by
      unfold Instance.prob
      apply Finset.prod_pos
      intro i _
      by_cases hi : i ∈ h.items
      · have : ν i = ω0 i := by
          simp only [History.items, List.mem_toFinset, List.mem_map] at hi
          obtain ⟨p, hp, rfl⟩ := hi
          rw [hc p hp, hh p hp]
        simp [hJ, resInst, condInst, hi, this]
      · simpa [hJ, resInst, condInst, hi] using factor_pos I hp0 ν hν i
    have h1 := hcov ν hJν
    rw [hNA, hJτ] at h1
    set y := Round.go stop' ν order [] with hy
    -- the tail over already-probed items adds no value
    have hsubR : (Round.go stop' ν h.items.toList y).realized ⊆ y.realized ∪ R := by
      refine (go_realized_sub stop' ν h.items.toList y).trans ?_
      intro u hu
      simp only [Finset.mem_union, Finset.mem_image, List.mem_toFinset, Finset.mem_toList] at hu ⊢
      rcases hu with hu | ⟨i, hi, rfl⟩
      · exact Or.inl hu
      · right
        simp only [History.items, List.mem_toFinset, List.mem_map] at hi
        obtain ⟨p, hp, rfl⟩ := hi
        rw [hc p hp]
        simp only [hR, History.realized, List.mem_toFinset, List.mem_map]
        exact ⟨p, hp, rfl⟩
    have h2 : (J.f (Round.go stop' ν h.items.toList y).realized : ℝ) ≤ J.f y.realized := by
      rw [resInst_f_real I hmon, resInst_f_real I hmon]
      have hss : R ∪ (Round.go stop' ν h.items.toList y).realized ⊆ R ∪ y.realized := by
        intro u hu
        simp only [Finset.mem_union] at hu ⊢
        rcases hu with hu | hu
        · exact Or.inl hu
        · have := hsubR hu
          simp only [Finset.mem_union] at this
          tauto
      have : (I.f (R ∪ (Round.go stop' ν h.items.toList y).realized) : ℝ) ≤ I.f (R ∪ y.realized) := by
        exact_mod_cast hmon hss
      linarith
    have h3 : (J.f y.realized : ℝ) = (I.f (R ∪ y.realized) : ℝ) - I.f R :=
      resInst_f_real I hmon h ω0 _
    rw [hrel ν hc, realized_append']
    linarith
  · intro π hπ
    have hb := hcost π (hJfeas π hπ)
    have hEJ : ∀ G, J.E G = (condInst I h.items ω0).E G := fun G => E_of_p_eq _ _ (fun i => rfl) G
    rw [hEJ] at hb
    unfold Instance.expCost at hb
    rw [hEJ] at hb
    refine le_trans ?_ hb
    rw [← hEJ, ← hEJ]
    apply E_mono' J hJs.1
    intro ν hν
    obtain ⟨-, hc⟩ := resInst_support I hp0 h ω0 hh hpos0 ν hν
    rw [hrel ν hc, (run_eq_iff_cyl σ ω0 k ν).mpr hc, hNA,
      costOf_append' I h _ (hydisj ν)]
    push_cast
    have := costOf_prefix J (go_prefix stop' ν h.items.toList (Round.go stop' ν order []))
    have e : J.costOf (Round.go stop' ν order []) = I.costOf (Round.go stop' ν order []) := rfl
    rw [e] at this
    have : (I.costOf (Round.go stop' ν order []) : ℝ) ≤
        (J.costOf (Round.go stop' ν h.items.toList (Round.go stop' ν order [])) : ℝ) := by
      exact_mod_cast this
    linarith

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- The first round of Algorithm 2 is ParCA on the whole instance (Theorem 3.1). -/
theorem round0 (C31 : ℝ) (hT : T31 C31 U m) (I : Instance U m) (hI : I.Standing)
    (r : ℕ) (hr : 1 ≤ r) (σ : RoundPolicy m U) (hSSC : I.IsSSC r σ)
    (π0 : AdaptivePolicy m U) (hπ0 : I.Feasible π0) (hQ : 0 < I.Q) :
    (∀ ν, 0 < I.prob ν →
      (I.Q : ℝ) * (1 - delta ⌈Real.logb 2 (I.Q : ℝ) / (r : ℝ)⌉₊) <
        (I.f (σ.run ν 1).realized : ℝ)) ∧
    (∀ π : AdaptivePolicy m U, I.Feasible π →
      I.E (fun ν => (I.costOf (σ.run ν 1) : ℝ)) ≤
        C31 * ((1 + Real.log (1 / delta ⌈Real.logb 2 (I.Q : ℝ) / (r : ℝ)⌉₊)) /
          delta ⌈Real.logb 2 (I.Q : ℝ) / (r : ℝ)⌉₊) * I.E (fun ν => (I.costOf (π.run ν) : ℝ))) := by
  have hS0 := hSSC 0 (by omega) []
  simp only [↓reduceIte, Nat.cast_zero, sub_zero] at hS0
  set z := ⌈Real.logb 2 (I.Q : ℝ) / (r : ℝ)⌉₊ with hz
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  rcases hS0 with ⟨hQ0, -⟩ | ⟨-, hgreedy, hstop⟩
  · exfalso; linarith
  have hitems : History.items ([] : History m U) = ∅ := by simp [History.items]
  rw [hitems, Finset.sdiff_empty] at hgreedy
  have hτ : (I.Q : ℝ) * (1 - delta z) = I.tau z := rfl
  rw [hτ] at hgreedy hstop
  obtain ⟨-, hL⟩ := hT I hI hQ ⟨π0, hπ0⟩ z
  obtain ⟨hcov, hcost⟩ := hL _ hgreedy
  have hrun : ∀ ν, σ.run ν 1 = I.NA (I.tau z) (σ 0 []).order ν := by
    intro ν
    show Round.go (σ 0 []).stop ν (σ 0 []).order [] = Round.go _ ν _ []
    congr 1
    funext h'
    rw [hstop h']
    rfl
  refine ⟨fun ν hν => ?_, fun π hπ => ?_⟩
  · rw [hrun ν, hτ]; exact hcov ν hν
  · have := hcost π hπ
    unfold Instance.expCost at this
    refine le_trans (le_of_eq ?_) this
    apply E_congr; intro ν; rw [hrun ν]

end ASCT32

namespace ASCT32

theorem logb2_mul_pow (x : ℝ) (hx : 0 < x) (z : ℕ) :
    Real.logb 2 (x * 2 ^ z) = Real.logb 2 x + z := by
  rw [Real.logb_mul hx.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

theorem delta_mul (z : ℕ) : delta z * 2 ^ z = 1 := by
  unfold delta; rw [inv_pow, inv_mul_cancel₀ (by positivity)]

/-- The residual values `q_k` of Algorithm 2 shrink fast enough. -/
theorem qseq (Q r : ℕ) (hr : 1 ≤ r) (q : ℕ → ℝ) (hq0 : q 0 = Q)
    (hnat : ∀ k, ∃ n : ℕ, q k = n)
    (hrec : ∀ k < r, (0 < q k → q (k + 1) < q k * delta ⌈Real.logb 2 (q k) / ((r : ℝ) - k)⌉₊) ∧
      (q k = 0 → q (k + 1) = 0)) :
    q r = 0 ∧
    (∀ k < r, 0 < q k → ⌈Real.logb 2 (q k) / ((r : ℝ) - k)⌉₊ ≤ ⌈Real.logb 2 Q / r⌉₊) ∧
    (∀ k ≤ r, 0 < q k → 2 ^ k ≤ Q) := by
  have hq0' : ∀ k, 0 ≤ q k := fun k => by obtain ⟨n, hn⟩ := hnat k; rw [hn]; positivity
  have hq1 : ∀ k, 0 < q k → 1 ≤ q k := by
    intro k hk; obtain ⟨n, hn⟩ := hnat k; rw [hn] at hk ⊢
    exact_mod_cast (show 1 ≤ n by exact_mod_cast hk)
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  -- positivity propagates backwards
  have hback : ∀ k < r, 0 < q (k + 1) → 0 < q k := by
    intro k hk h
    rcases (hq0' k).lt_or_eq with h1 | h1
    · exact h1
    · rw [(hrec k hk).2 h1.symm] at h; exact absurd h (lt_irrefl _)
  -- the logarithmic invariant
  have hinv : ∀ k ≤ r, 0 < q k → Real.logb 2 (q k) * r ≤ ((r : ℝ) - k) * Real.logb 2 Q ∧
      (1 ≤ k → Real.logb 2 (q k) * r < ((r : ℝ) - k) * Real.logb 2 Q) := by
    intro k
    induction k with
    | zero =>
      intro _ _; rw [hq0]
      refine ⟨by simp [mul_comm], fun h => absurd h (by omega)⟩
    | succ k ih =>
      intro hk hpos
      have hkr : k < r := by omega
      have hqk := hback k hkr hpos
      obtain ⟨ihle, -⟩ := ih (by omega) hqk
      set z := ⌈Real.logb 2 (q k) / ((r : ℝ) - k)⌉₊ with hz
      have hrk : (0 : ℝ) < (r : ℝ) - k := by
        have : (k : ℝ) < r := by exact_mod_cast hkr
        linarith
      have hzge : Real.logb 2 (q k) / ((r : ℝ) - k) ≤ z := Nat.le_ceil _
      have hlt := (hrec k hkr).1 hqk
      -- q_{k+1} * 2^z < q_k
      have hlt' : q (k + 1) * 2 ^ z < q k := by
        have := mul_lt_mul_of_pos_right hlt (show (0 : ℝ) < 2 ^ z by positivity)
        rwa [mul_assoc, delta_mul, mul_one] at this
      have hlog : Real.logb 2 (q (k + 1)) + z < Real.logb 2 (q k) := by
        rw [← logb2_mul_pow _ hpos]
        exact Real.logb_lt_logb (by norm_num) (by positivity) hlt'
      have hlqk : 0 ≤ Real.logb 2 (q k) := Real.logb_nonneg (by norm_num) (hq1 k hqk)
      have hz' : Real.logb 2 (q k) ≤ z * ((r : ℝ) - k) := by
        rwa [div_le_iff₀ hrk] at hzge
      have key : Real.logb 2 (q (k + 1)) * r < ((r : ℝ) - (k + 1 : ℕ)) * Real.logb 2 Q := by
        push_cast
        -- logb q_{k+1} < logb q_k - z ≤ logb q_k * (r-k-1)/(r-k)
        have h1 : Real.logb 2 (q (k + 1)) * ((r : ℝ) - k) <
            Real.logb 2 (q k) * ((r : ℝ) - k - 1) := by nlinarith
        have h2 : Real.logb 2 (q k) * ((r : ℝ) - k - 1) * r ≤
            ((r : ℝ) - k) * Real.logb 2 Q * ((r : ℝ) - k - 1) := by
          have hnn : (0 : ℝ) ≤ (r : ℝ) - k - 1 := by
            have : ((k + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hk
            push_cast at this; linarith
          nlinarith
        have h3 : Real.logb 2 (q (k + 1)) * r * ((r : ℝ) - k) <
            ((r : ℝ) - k - 1) * Real.logb 2 Q * ((r : ℝ) - k) := by nlinarith
        rw [show ((r : ℝ) - (k + 1)) = (r : ℝ) - k - 1 by ring]
        exact lt_of_mul_lt_mul_right h3 hrk.le
      exact ⟨key.le, fun _ => key⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the last round leaves nothing
    rcases (hq0' r).lt_or_eq with hpos | hzero
    · exfalso
      obtain ⟨-, hstrict⟩ := hinv r le_rfl hpos
      have := hstrict hr
      rw [sub_self, zero_mul] at this
      have hl : Real.logb 2 (q r) < 0 := by nlinarith
      have : q r < 1 := (Real.logb_neg_iff (by norm_num) hpos).mp hl
      linarith [hq1 r hpos]
    · exact hzero.symm
  · intro k hk hpos
    apply Nat.ceil_mono
    obtain ⟨hle, -⟩ := hinv k hk.le hpos
    have hrk : (0 : ℝ) < (r : ℝ) - k := by
      have : (k : ℝ) < r := by exact_mod_cast hk
      linarith
    rw [div_le_div_iff₀ hrk hrpos]
    linarith
  · -- halving
    have hhalf : ∀ k ≤ r, 0 < q k → q k * 2 ^ k ≤ Q := by
      intro k
      induction k with
      | zero => intro _ _; rw [hq0]; simp
      | succ k ih =>
        intro hk hpos
        have hkr : k < r := by omega
        have hqk := hback k hkr hpos
        have ihk := ih (by omega) hqk
        set z := ⌈Real.logb 2 (q k) / ((r : ℝ) - k)⌉₊ with hz
        have hlt := (hrec k hkr).1 hqk
        -- q_k ≥ 2, hence z ≥ 1
        have hq2 : 2 ≤ q k := by
          by_contra h2
          push Not at h2
          have h1 : q k = 1 := by
            obtain ⟨n, hn⟩ := hnat k
            have hn1 : (1 : ℝ) ≤ n := by rw [← hn]; exact hq1 k hqk
            have hn2 : (n : ℝ) < 2 := by rw [← hn]; exact h2
            have : n = 1 := by
              have a1 : 1 ≤ n := by exact_mod_cast hn1
              have a2 : n < 2 := by exact_mod_cast hn2
              omega
            rw [hn, this]; norm_num
          rw [h1] at hlt
          simp only [Real.logb_one, zero_div, Nat.ceil_zero, delta, pow_zero, one_mul] at hlt
          linarith [hq1 (k + 1) hpos]
        have hzpos : 1 ≤ z := by
          rw [hz, Nat.one_le_ceil_iff]
          apply div_pos
          · exact Real.logb_pos (by norm_num) (by linarith)
          · have : (k : ℝ) < r := by exact_mod_cast hkr
            linarith
        have hδ : delta z ≤ 1 / 2 := by
          unfold delta
          calc (2⁻¹ : ℝ) ^ z ≤ (2⁻¹ : ℝ) ^ 1 :=
                pow_le_pow_of_le_one (by norm_num) (by norm_num) hzpos
            _ = 1 / 2 := by norm_num
        have : q (k + 1) < q k / 2 := by
          calc q (k + 1) < q k * delta z := hlt
            _ ≤ q k * (1 / 2) := mul_le_mul_of_nonneg_left hδ (hq0' k)
            _ = q k / 2 := by ring
        rw [pow_succ]
        nlinarith
    intro k hk hpos
    have := hhalf k hk hpos
    have h1 := hq1 k hpos
    have : (2 : ℝ) ^ k ≤ Q := by nlinarith [show (0 : ℝ) < 2 ^ k by positivity]
    exact_mod_cast this

end ASCT32

namespace ASCT32

theorem final_ineq (Q r : ℕ) (hr : 1 ≤ r) (hQ : 1 ≤ Q) :
    (1 + Real.log (1 / delta ⌈Real.logb 2 Q / r⌉₊)) / delta ⌈Real.logb 2 Q / r⌉₊ *
        ((min r (Nat.log 2 Q + 1) : ℕ) : ℝ) ≤
      8 * (Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log Q) := by
  set z := ⌈Real.logb 2 Q / r⌉₊ with hz
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hrr : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlQ : 0 ≤ Real.log Q := Real.log_nonneg hQr
  have hlbQ : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQr
  have hinvδ : 1 / delta z = 2 ^ z := by unfold delta; rw [inv_pow, one_div, inv_inv]
  have hF : (1 + Real.log (1 / delta z)) / delta z = (1 + z * Real.log 2) * 2 ^ z := by
    rw [div_eq_mul_one_div, hinvδ, Real.log_pow]
  rw [hF]
  have hzlt : (z : ℝ) < Real.logb 2 Q / r + 1 := Nat.ceil_lt_add_one (by positivity)
  -- 2^z ≤ 2 Q^{1/r}
  have h2z : (2 : ℝ) ^ z ≤ 2 * (Q : ℝ) ^ ((1 : ℝ) / r) := by
    have e1 : (2 : ℝ) ^ z = (2 : ℝ) ^ ((z : ℕ) : ℝ) := (Real.rpow_natCast 2 z).symm
    have e2 : (2 : ℝ) ^ (Real.logb 2 Q / r + 1) = 2 * (Q : ℝ) ^ ((1 : ℝ) / r) := by
      rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]
      congr 1
      rw [div_eq_mul_one_div, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
        (by linarith)]
    rw [e1, ← e2]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hzlt.le
  -- the number of nonempty rounds
  set N := min r (Nat.log 2 Q + 1) with hN
  have hN1 : (N : ℝ) ≤ r := by exact_mod_cast Nat.min_le_left _ _
  have hN2 : (N : ℝ) ≤ Real.logb 2 Q + 1 := by
    have h1 : (N : ℝ) ≤ (Nat.log 2 Q : ℝ) + 1 := by exact_mod_cast Nat.min_le_right _ _
    have h2 : (Nat.log 2 Q : ℝ) ≤ Real.logb 2 Q := by
      have hp : ((2 ^ Nat.log 2 Q : ℕ) : ℝ) ≤ Q := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
      push_cast at hp
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hp
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hlogb : Real.logb 2 Q * Real.log 2 = Real.log Q := by
    unfold Real.logb; field_simp
  have hmain : (1 + z * Real.log 2) * N ≤ 4 * (1 + Real.log Q) := by
    have hz' : (z : ℝ) * Real.log 2 ≤ (Real.logb 2 Q / r + 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hzlt.le (by linarith)
    have hstep : (1 + z * Real.log 2) * N ≤ N * (1 + Real.log 2) + Real.log Q * (N / r) := by
      have : (Real.logb 2 Q / r + 1) * Real.log 2 = Real.log Q / r + Real.log 2 := by
        rw [add_mul, div_mul_eq_mul_div, hlogb, one_mul]
      rw [this] at hz'
      have := mul_le_mul_of_nonneg_right hz' hN0
      have e : Real.log Q / r * N = Real.log Q * (N / r) := by ring
      nlinarith
    have hNr : (N : ℝ) / r ≤ 1 := by rw [div_le_one (by linarith)]; exact hN1
    have h3 : Real.log Q * (N / r) ≤ Real.log Q := by
      calc Real.log Q * (N / r) ≤ Real.log Q * 1 := mul_le_mul_of_nonneg_left hNr hlQ
        _ = Real.log Q := mul_one _
    have h4 : N * (1 + Real.log 2) ≤ (Real.logb 2 Q + 1) * (1 + Real.log 2) :=
      mul_le_mul_of_nonneg_right hN2 (by linarith)
    have h5 : Real.logb 2 Q * (1 + Real.log 2) ≤ 3 * Real.log Q := by
      have : Real.logb 2 Q * (1 + Real.log 2) ≤ Real.logb 2 Q * (3 * Real.log 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hlbQ
      nlinarith
    nlinarith
  have h2z0 : (0 : ℝ) ≤ 2 ^ z := by positivity
  have hA : (0 : ℝ) ≤ 1 + z * Real.log 2 := by
    have : (0 : ℝ) ≤ z := by positivity
    have : 0 ≤ (z : ℝ) * Real.log 2 := mul_nonneg this (by linarith)
    linarith
  calc (1 + z * Real.log 2) * 2 ^ z * N = 2 ^ z * ((1 + z * Real.log 2) * N) := by ring
    _ ≤ (2 * (Q : ℝ) ^ ((1 : ℝ) / r)) * (4 * (1 + Real.log Q)) :=
        mul_le_mul h2z hmain (mul_nonneg hA hN0) (by positivity)
    _ = 8 * (Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log Q) := by ring

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem F_eq (z : ℕ) : (1 + Real.log (1 / delta z)) / delta z = (1 + z * Real.log 2) * 2 ^ z := by
  have hinvδ : 1 / delta z = 2 ^ z := by unfold delta; rw [inv_pow, one_div, inv_inv]
  rw [div_eq_mul_one_div, hinvδ, Real.log_pow]

theorem F_mono (z z' : ℕ) (h : z ≤ z') :
    (1 + Real.log (1 / delta z)) / delta z ≤ (1 + Real.log (1 / delta z')) / delta z' := by
  rw [F_eq, F_eq]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : (z : ℝ) ≤ z' := by exact_mod_cast h
  have h2 : (2 : ℝ) ^ z ≤ 2 ^ z' := pow_le_pow_right₀ (by norm_num) h
  have h3 : 0 ≤ 1 + (z : ℝ) * Real.log 2 := by positivity
  apply mul_le_mul _ h2 (by positivity) (by positivity)
  nlinarith

theorem F_nonneg (z : ℕ) : 0 ≤ (1 + Real.log (1 / delta z)) / delta z := by
  rw [F_eq]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

theorem greedy_exists_avail (sc : Finset (Fin m) → Fin m → ℝ) (avail : Finset (Fin m)) :
    ∀ n ≤ avail.card, ∃ l : List (Fin m), l.length = n ∧ l.Nodup ∧ l.toFinset ⊆ avail ∧
      ∀ k (hk : k < l.length), ∀ e ∈ avail \ (l.take k).toFinset,
        sc (l.take k).toFinset e ≤ sc (l.take k).toFinset (l[k]'hk) := by
  intro n
  induction n with
  | zero => intro _; exact ⟨[], rfl, List.nodup_nil, by simp, fun k hk => by simp at hk⟩
  | succ n ih =>
    intro hn
    obtain ⟨l, hlen, hnd, hsub, hgr⟩ := ih (by omega)
    have hcard : l.toFinset.card = n := by rw [List.toFinset_card_of_nodup hnd, hlen]
    have hR : (avail \ l.toFinset).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub, hcard]
      omega
    obtain ⟨e, he, hemax⟩ := Finset.exists_max_image _ (sc l.toFinset) hR
    have hel : e ∉ l := by
      intro h; exact (Finset.mem_sdiff.mp he).2 (List.mem_toFinset.mpr h)
    refine ⟨l ++ [e], by simp [hlen], ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd, List.nodup_singleton e, ?_⟩
      intro a ha b hb; simp at hb; subst hb; rintro rfl; exact hel ha
    · rw [List.toFinset_append]
      apply Finset.union_subset hsub
      intro x hx; simp at hx; subst hx; exact (Finset.mem_sdiff.mp he).1
    · intro k hk e' he'
      simp only [List.length_append, List.length_singleton] at hk
      rcases Nat.lt_or_ge k l.length with hkl | hkl
      · have ht : (l ++ [e]).take k = l.take k := List.take_append_of_le_length hkl.le
        rw [ht] at he' ⊢
        rw [List.getElem_append_left hkl]
        exact hgr k hkl e' he'
      · have hk' : k = l.length := by omega
        subst hk'
        have ht : (l ++ [e]).take l.length = l := by simp
        rw [ht] at he' ⊢
        rw [List.getElem_append_right (le_refl _)]
        simpa using hemax e' he'

theorem greedy_exists_avail' (sc : Finset (Fin m) → Fin m → ℝ) (avail : Finset (Fin m)) :
    ∃ l : List (Fin m), l.Nodup ∧ l.toFinset = avail ∧
      ∀ k (hk : k < l.length), ∀ e ∈ avail \ (l.take k).toFinset,
        sc (l.take k).toFinset e ≤ sc (l.take k).toFinset (l[k]'hk) := by
  obtain ⟨l, hlen, hnd, hsub, hgr⟩ := greedy_exists_avail sc avail avail.card le_rfl
  refine ⟨l, hnd, ?_, hgr⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [List.toFinset_card_of_nodup hnd, hlen]

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- The rounds of Algorithm 2 `SSC(r, X, f)`. -/
noncomputable def sscRound (I : Instance U m) (r k : ℕ) (h : History m U) : Round m U :=
  let R := h.realized
  let g : Finset U → ℝ :=
    if k = 0 then (fun A => (I.f A : ℝ)) else (fun A => (I.f (R ∪ A) : ℝ) - I.f R)
  let Q' : ℝ := if k = 0 then (I.Q : ℝ) else (I.Q : ℝ) - I.f R
  let z : ℕ := ⌈Real.logb 2 Q' / ((r : ℝ) - k)⌉₊
  let τ' : ℝ := Q' * (1 - delta z)
  if 0 < Q' then
    ⟨Classical.choose (greedy_exists_avail' (I.scoreG g Q' τ') (Finset.univ \ h.items)),
      fun h' => decide (τ' < g h'.realized)⟩
  else ⟨[], fun _ => false⟩

theorem ssc_exists (I : Instance U m) (hI : I.Standing) (r : ℕ) :
    I.IsSSC r (fun k h => sscRound I r k h) := by
  intro k _ h
  have hmon := hI.2.2.2.1
  have hfR : (I.f h.realized : ℝ) ≤ I.Q := by
    unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ _)
  by_cases hk0 : k = 0
  · subst hk0
    simp only [sscRound, ↓reduceIte]
    by_cases hpos : (0 : ℝ) < I.Q
    · rw [if_pos hpos]
      right
      refine ⟨hpos, ?_, fun h' => rfl⟩
      exact Classical.choose_spec (greedy_exists_avail' _ _)
    · rw [if_neg hpos]
      left
      exact ⟨le_antisymm (not_lt.mp hpos) (by positivity), rfl⟩
  · simp only [sscRound, hk0, ↓reduceIte]
    by_cases hpos : (0 : ℝ) < (I.Q : ℝ) - I.f h.realized
    · rw [if_pos hpos]
      right
      refine ⟨hpos, ?_, fun h' => rfl⟩
      exact Classical.choose_spec (greedy_exists_avail' _ _)
    · rw [if_neg hpos]
      left
      exact ⟨le_antisymm (not_lt.mp hpos) (by linarith), rfl⟩

end ASCT32

namespace ASCT32

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- The expected cost of round `k ≥ 1`, through the partition by the history after `k` rounds. -/
theorem roundk_bound (C31 : ℝ) (hC31 : 0 < C31) (hT : T31 C31 U m) (I : Instance U m)
    (hI : I.Standing) (r k : ℕ) (hk1 : 1 ≤ k) (hkr : k < r) (σ : RoundPolicy m U)
    (hSSC : I.IsSSC r σ) (π0 : AdaptivePolicy m U) (hπ0 : I.Feasible π0)
    (π : AdaptivePolicy m U) (hπ : I.Feasible π) (zbar : ℕ)
    (hzb : ∀ ω, 0 < I.prob ω → 0 < (I.Q : ℝ) - I.f (σ.run ω k).realized →
      ⌈Real.logb 2 ((I.Q : ℝ) - I.f (σ.run ω k).realized) / ((r : ℝ) - k)⌉₊ ≤ zbar) :
    I.E (fun ω => (I.costOf (σ.run ω (k + 1)) : ℝ) - I.costOf (σ.run ω k)) ≤
      C31 * ((1 + Real.log (1 / delta zbar)) / delta zbar) *
        I.E (fun ω => @ite ℝ (0 < (I.Q : ℝ) - I.f (σ.run ω k).realized)
          (Classical.propDecidable _) (I.costOf (π.run ω) : ℝ) 0) := by
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  set Fz := (1 + Real.log (1 / delta zbar)) / delta zbar with hFz
  have hFz0 : 0 ≤ Fz := F_nonneg zbar
  set RC : (Fin m → U) → ℝ := fun ω => (I.costOf (σ.run ω (k + 1)) : ℝ) - I.costOf (σ.run ω k)
    with hRC
  set G : (Fin m → U) → ℝ := fun ω => @ite ℝ (0 < (I.Q : ℝ) - I.f (σ.run ω k).realized)
    (Classical.propDecidable _) (I.costOf (π.run ω) : ℝ) 0 with hG
  rw [E_partition I σ k RC, E_partition I σ k G, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro hh hmem
  obtain ⟨ω0, -, rfl⟩ := Finset.mem_image.mp hmem
  have hRHS0 : 0 ≤ C31 * Fz * I.E (fun ω => @ite ℝ (cyl (σ.run ω0 k) ω)
      (Classical.propDecidable _) 1 0 * G ω) := by
    apply mul_nonneg (mul_nonneg hC31.le hFz0)
    apply E_nonneg I hp0
    intro ω
    apply mul_nonneg (ind_nonneg _)
    simp only [hG]; split
    · positivity
    · exact le_refl _
  by_cases hex : ∃ ω1, 0 < I.prob ω1 ∧ cyl (σ.run ω0 k) ω1
  · obtain ⟨ω1, hω1, hc1'⟩ := hex
    have e : σ.run ω0 k = σ.run ω1 k := ((run_eq_iff_cyl σ ω0 k ω1).mpr hc1').symm
    rw [e] at hRHS0 ⊢
    set h := σ.run ω1 k with hhdef
    have hh1 : Honest ω1 h := run_honest σ ω1 k
    by_cases hq : 0 < (I.Q : ℝ) - I.f h.realized
    · obtain ⟨-, hb⟩ := round_res C31 hT I hI r k hk1 hkr σ hSSC ω1 hω1 π0 hπ0 hq
      have hb' := hb π hπ
      rw [E_cyl I hp0 hp1 h ω1 hh1 RC]
      have hG' : I.E (fun ω => @ite ℝ (cyl h ω) (Classical.propDecidable _) 1 0 * G ω) =
          I.E (fun ω => @ite ℝ (cyl h ω) (Classical.propDecidable _) 1 0 *
            (I.costOf (π.run ω) : ℝ)) := by
        apply E_congr; intro ω
        by_cases hc : cyl h ω
        · have hrun : σ.run ω k = h := (run_eq_iff_cyl σ ω1 k ω).mpr hc
          simp only [hG, if_pos hc, hrun, if_pos hq]
        · simp only [if_neg hc, zero_mul]
      rw [hG', E_cyl I hp0 hp1 h ω1 hh1 (fun ω => (I.costOf (π.run ω) : ℝ))]
      have hP0 : 0 ≤ I.P (cyl h) := E_nonneg I hp0 _ (fun ω => ind_nonneg _)
      have hE0 : 0 ≤ (condInst I h.items ω1).E (fun ω => (I.costOf (π.run ω) : ℝ)) :=
        E_nonneg _ (condInst_p0 I hp0 _ _) _ (fun ω => by positivity)
      have hFle := F_mono _ _ (hzb ω1 hω1 hq)
      have : (condInst I h.items ω1).E RC ≤ C31 * Fz *
          (condInst I h.items ω1).E (fun ω => (I.costOf (π.run ω) : ℝ)) := by
        refine le_trans hb' ?_
        apply mul_le_mul_of_nonneg_right _ hE0
        exact mul_le_mul_of_nonneg_left hFle hC31.le
      calc I.P (cyl h) * (condInst I h.items ω1).E RC
          ≤ I.P (cyl h) * (C31 * Fz * (condInst I h.items ω1).E
              (fun ω => (I.costOf (π.run ω) : ℝ))) := mul_le_mul_of_nonneg_left this hP0
        _ = _ := by ring
    · -- the residual is already covered: the round is empty
      have hzero : I.E (fun ω => @ite ℝ (cyl h ω) (Classical.propDecidable _) 1 0 * RC ω) = 0 := by
        unfold Instance.E
        apply Finset.sum_eq_zero; intro ω _
        by_cases hc : cyl h ω
        · have hrun : σ.run ω k = h := (run_eq_iff_cyl σ ω1 k ω).mpr hc
          have hSk := hSSC k hkr h
          simp only [if_neg (show k ≠ 0 by omega)] at hSk
          rcases hSk with ⟨-, hord⟩ | ⟨hpos, -⟩
          · have : σ.run ω (k + 1) = h := by
              rw [run_succ, hrun]
              show Round.go (σ k h).stop ω (σ k h).order h = h
              rw [hord]; rfl
            simp only [hRC, this, hrun, sub_self, mul_zero]
          · exact absurd hpos hq
        · simp only [if_neg hc, zero_mul, mul_zero]
      rw [hzero]; exact hRHS0
  · push Not at hex
    have hzero : I.E (fun ω => @ite ℝ (cyl (σ.run ω0 k) ω) (Classical.propDecidable _) 1 0 * RC ω) = 0 := by
      unfold Instance.E
      apply Finset.sum_eq_zero; intro ω _
      by_cases hc : cyl (σ.run ω0 k) ω
      · have : I.prob ω = 0 := by
          rcases (prob_nonneg I hp0 ω).lt_or_eq with h1 | h1
          · exact absurd hc (hex ω h1)
          · exact h1.symm
        rw [this, zero_mul]
      · simp only [if_neg hc, zero_mul, mul_zero]
    rw [hzero]; exact hRHS0

end ASCT32

open ASCT32 in
theorem solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → (∃ π : AdaptivePolicy m U, I.Feasible π) → ∀ r : ℕ, 1 ≤ r →
          (∃ σ : RoundPolicy m U, I.IsSSC r σ) ∧
          ∀ σ : RoundPolicy m U, I.IsSSC r σ →
            I.FeasibleR r σ ∧
            ∀ π : AdaptivePolicy m U, I.Feasible π →
              I.expCostR r σ ≤
                C * (I.Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log I.Q) * I.expCost π := by
  obtain ⟨C31, hC31, h31⟩ := AdaptSubCover.Rounds.theorem_3_1
  refine ⟨8 * C31, by positivity, ?_⟩
  intro U _ _ m I hI hfeas r hr
  have hT : T31 C31 U m := fun J => h31 U m J
  obtain ⟨π0, hπ0⟩ := hfeas
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  refine ⟨⟨_, ssc_exists I hI r⟩, ?_⟩
  intro σ hSSC
  have hfR : ∀ ω k, (I.f (σ.run ω k).realized : ℝ) ≤ I.Q := by
    intro ω k; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ _)
  have hRmono : ∀ ω k, (I.f (σ.run ω k).realized : ℝ) ≤ I.f (σ.run ω (k + 1)).realized := by
    intro ω k
    have hp := run_prefix σ ω k (k + 1) (by omega)
    obtain ⟨t, ht⟩ := hp
    have : (σ.run ω k).realized ⊆ (σ.run ω (k + 1)).realized := by
      rw [← ht, realized_append']; exact Finset.subset_union_left
    exact_mod_cast hmon this
  set q : (Fin m → U) → ℕ → ℝ := fun ω k =>
    if k = 0 then (I.Q : ℝ) else (I.Q : ℝ) - I.f (σ.run ω k).realized with hqdef
  have hqk : ∀ ω k, k ≠ 0 → q ω k = (I.Q : ℝ) - I.f (σ.run ω k).realized := by
    intro ω k hk; simp only [hqdef, if_neg hk]
  have hnat : ∀ ω k, ∃ n : ℕ, q ω k = n := by
    intro ω k
    by_cases hk : k = 0
    · exact ⟨I.Q, by simp [hqdef, hk]⟩
    · refine ⟨I.Q - I.f (σ.run ω k).realized, ?_⟩
      rw [hqk ω k hk]
      have : I.f (σ.run ω k).realized ≤ I.Q := by
        unfold Instance.Q; exact hmon (Finset.subset_univ _)
      push_cast [this]; ring
  have hq0' : ∀ ω k, 0 ≤ q ω k := fun ω k => by
    obtain ⟨n, hn⟩ := hnat ω k; rw [hn]; positivity
  have hrec : ∀ ω, 0 < I.prob ω → ∀ k < r,
      (0 < q ω k → q ω (k + 1) < q ω k * delta ⌈Real.logb 2 (q ω k) / ((r : ℝ) - k)⌉₊) ∧
      (q ω k = 0 → q ω (k + 1) = 0) := by
    intro ω hω k hk
    have hq1 : q ω (k + 1) = (I.Q : ℝ) - I.f (σ.run ω (k + 1)).realized := hqk ω (k + 1) (by omega)
    refine ⟨fun hpos => ?_, fun hzero => ?_⟩
    · by_cases hk0 : k = 0
      · subst hk0
        have hQpos : 0 < I.Q := by
          have : (0 : ℝ) < I.Q := by simpa [hqdef] using hpos
          exact_mod_cast this
        obtain ⟨hcov, -⟩ := round0 C31 hT I hI r hr σ hSSC π0 hπ0 hQpos
        have := hcov ω hω
        rw [hq1]
        simp only [hqdef, ↓reduceIte, Nat.cast_zero, sub_zero]
        unfold delta at this ⊢
        nlinarith
      · rw [hqk ω k hk0] at hpos ⊢
        have hhon : cyl (σ.run ω k) ω := fun p hp => (run_honest σ ω k p hp).symm
        obtain ⟨hcov, -⟩ := round_res C31 hT I hI r k (by omega) hk σ hSSC ω hω π0 hπ0 hpos
        have := hcov ω hω hhon
        rw [hq1]
        nlinarith
    · have h1 : q ω (k + 1) ≤ q ω k := by
        rw [hq1]
        by_cases hk0 : k = 0
        · subst hk0; simp only [hqdef, ↓reduceIte]
          have : (0 : ℝ) ≤ I.f (σ.run ω (0 + 1)).realized := by positivity
          linarith
        · rw [hqk ω k hk0]; linarith [hRmono ω k]
      linarith [hq0' ω (k + 1)]
  have hQS := fun ω (hω : 0 < I.prob ω) =>
    qseq I.Q r hr (q ω) (by simp [hqdef]) (hnat ω) (hrec ω hω)
  refine ⟨?_, ?_⟩
  · -- coverage after `r` rounds
    intro ω hω
    obtain ⟨h0, -, -⟩ := hQS ω hω
    rw [hqk ω r (by omega)] at h0
    unfold Instance.Covers
    have : (I.f (σ.run ω r).realized : ℝ) = I.Q := by linarith
    exact_mod_cast this
  · intro π hπ
    set zbar := ⌈Real.logb 2 (I.Q : ℝ) / (r : ℝ)⌉₊ with hzbar
    set Fz := (1 + Real.log (1 / delta zbar)) / delta zbar with hFz
    have hFz0 : 0 ≤ Fz := F_nonneg zbar
    set G : ℕ → (Fin m → U) → ℝ := fun k ω =>
      @ite ℝ (0 < q ω k) (Classical.propDecidable _) (I.costOf (π.run ω) : ℝ) 0 with hG
    -- per-round bounds
    have hround : ∀ k < r, I.E (fun ω => (I.costOf (σ.run ω (k + 1)) : ℝ) -
        I.costOf (σ.run ω k)) ≤ C31 * Fz * I.E (G k) := by
      intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        have hrun0 : ∀ ω, σ.run ω 0 = [] := fun ω => rfl
        by_cases hQ0 : I.Q = 0
        · -- nothing to cover
          have hS0 := hSSC 0 (by omega) []
          simp only [↓reduceIte] at hS0
          have hord : (σ 0 []).order = [] := by
            rcases hS0 with ⟨-, h1⟩ | ⟨h1, -⟩
            · exact h1
            · exfalso; rw [hQ0] at h1; simp at h1
          have : ∀ ω, (I.costOf (σ.run ω (0 + 1)) : ℝ) - I.costOf (σ.run ω 0) = 0 := by
            intro ω
            have : σ.run ω (0 + 1) = [] := by
              rw [run_succ, hrun0]
              show Round.go (σ 0 []).stop ω (σ 0 []).order [] = []
              rw [hord]; rfl
            rw [this, hrun0]; simp
          rw [E_congr I _ _ this]
          have : I.E (fun _ => (0 : ℝ)) = 0 := by unfold Instance.E; simp
          rw [this]
          apply mul_nonneg (mul_nonneg hC31.le hFz0)
          apply E_nonneg I hp0; intro ω; simp only [hG]; split
          · positivity
          · exact le_refl _
        · have hQpos : 0 < I.Q := Nat.pos_of_ne_zero hQ0
          obtain ⟨-, hb⟩ := round0 C31 hT I hI r hr σ hSSC π0 hπ0 hQpos
          have hb' := hb π hπ
          have e1 : I.E (fun ω => (I.costOf (σ.run ω (0 + 1)) : ℝ) - I.costOf (σ.run ω 0)) =
              I.E (fun ν => (I.costOf (σ.run ν 1) : ℝ)) := by
            apply E_congr; intro ω; rw [hrun0]; simp [Instance.costOf, History.items]
          have e2 : I.E (G 0) = I.E (fun ν => (I.costOf (π.run ν) : ℝ)) := by
            apply E_congr; intro ω
            have : 0 < q ω 0 := by simp only [hqdef, ↓reduceIte]; exact_mod_cast hQpos
            simp only [hG, if_pos this]
          rw [e1, e2]
          exact hb'
      · have hzb : ∀ ω, 0 < I.prob ω → 0 < (I.Q : ℝ) - I.f (σ.run ω k).realized →
            ⌈Real.logb 2 ((I.Q : ℝ) - I.f (σ.run ω k).realized) / ((r : ℝ) - k)⌉₊ ≤ zbar := by
          intro ω hω hpos
          obtain ⟨-, hz, -⟩ := hQS ω hω
          have := hz k hk (by rw [hqk ω k hk0]; exact hpos)
          rwa [hqk ω k hk0] at this
        have := roundk_bound C31 hC31 hT I hI r k (by omega) hk σ hSSC π0 hπ0 π hπ zbar hzb
        refine le_trans this (le_of_eq ?_)
        congr 1
        apply E_congr; intro ω
        simp only [hG, hqk ω k hk0]
    -- telescoping over rounds
    have htel : I.expCostR r σ = ∑ k ∈ Finset.range r,
        I.E (fun ω => (I.costOf (σ.run ω (k + 1)) : ℝ) - I.costOf (σ.run ω k)) := by
      unfold Instance.expCostR
      rw [← E_sum]
      apply E_congr; intro ω
      rw [Finset.sum_range_sub (fun k => (I.costOf (σ.run ω k) : ℝ)) r]
      simp [RoundPolicy.run, Instance.costOf, History.items]
    rw [htel]
    have hsum1 : ∑ k ∈ Finset.range r,
        I.E (fun ω => (I.costOf (σ.run ω (k + 1)) : ℝ) - I.costOf (σ.run ω k)) ≤
        C31 * Fz * I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) := by
      rw [E_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => hround k (Finset.mem_range.mp hk)
    refine le_trans hsum1 ?_
    -- counting the nonempty rounds
    set N := min r (Nat.log 2 I.Q + 1) with hN
    have hcount : ∀ ω, 0 < I.prob ω →
        ∑ k ∈ Finset.range r, G k ω ≤ (N : ℝ) * (I.costOf (π.run ω) : ℝ) := by
      intro ω hω
      obtain ⟨-, -, hpow⟩ := hQS ω hω
      have e : ∑ k ∈ Finset.range r, G k ω =
          (((Finset.range r).filter (fun k => 0 < q ω k)).card : ℝ) * (I.costOf (π.run ω) : ℝ) := by
        simp only [hG]
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hsubset : (Finset.range r).filter (fun k => 0 < q ω k) ⊆ Finset.range N := by
        intro k hk
        rw [Finset.mem_filter, Finset.mem_range] at hk
        rw [Finset.mem_range, hN, lt_min_iff]
        refine ⟨hk.1, ?_⟩
        have h2 := hpow k hk.1.le hk.2
        have hQ1 : I.Q ≠ 0 := by
          intro h0; rw [h0] at h2; have := Nat.one_le_two_pow (n := k); omega
        have := Nat.le_log_of_pow_le (by norm_num : 1 < 2) h2
        omega
      have := Finset.card_le_card hsubset
      rw [Finset.card_range] at this
      exact_mod_cast this
    have hE1 : I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) ≤ (N : ℝ) * I.expCost π := by
      unfold Instance.expCost
      rw [← E_smul]
      exact E_mono' I hp0 _ _ hcount
    have hEπ : 0 ≤ I.expCost π := E_nonneg I hp0 _ (fun ω => by positivity)
    by_cases hQ0 : I.Q = 0
    · -- then no round is ever nonempty
      have hall : ∀ ω, 0 < I.prob ω → ∑ k ∈ Finset.range r, G k ω ≤ 0 := by
        intro ω hω
        obtain ⟨-, -, hpow⟩ := hQS ω hω
        apply le_of_eq
        apply Finset.sum_eq_zero
        intro k hk
        simp only [hG]
        rw [if_neg]
        intro hpos
        have := hpow k (Finset.mem_range.mp hk).le hpos
        rw [hQ0] at this
        have := Nat.one_le_two_pow (n := k); omega
      have h0 : I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) ≤ 0 := by
        calc I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) ≤ I.E (fun _ => (0 : ℝ)) :=
              E_mono' I hp0 _ _ hall
          _ = 0 := by unfold Instance.E; simp
      have hRHS : 0 ≤ 8 * C31 * (I.Q : ℝ) ^ ((1 : ℝ) / r) * (1 + Real.log I.Q) * I.expCost π := by
        rw [hQ0, Nat.cast_zero, Real.zero_rpow (by positivity)]; simp
      have : C31 * Fz * I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC31.le hFz0) h0
      linarith
    · have hstep : C31 * Fz * I.E (fun ω => ∑ k ∈ Finset.range r, G k ω) ≤
          C31 * Fz * ((N : ℝ) * I.expCost π) :=
        mul_le_mul_of_nonneg_left hE1 (mul_nonneg hC31.le hFz0)
      refine le_trans hstep ?_
      have hQ1 : 1 ≤ I.Q := Nat.one_le_iff_ne_zero.mpr hQ0
      have hfin := final_ineq I.Q r hr hQ1
      rw [← hzbar, ← hFz, ← hN] at hfin
      have := mul_le_mul_of_nonneg_left hfin (mul_nonneg hC31.le hEπ)
      nlinarith

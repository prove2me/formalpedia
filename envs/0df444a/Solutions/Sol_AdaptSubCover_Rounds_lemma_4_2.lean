-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:39:47.186556+00:00
-- url     : https://prove2.me/submissions/6d6a2e78-3f14-42e5-9b9f-0dcffcfb5965

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis
import Theorems.Thm_AdaptSubCover_Rounds_bsz19_theorem_1

open AdaptSubCover.Rounds

namespace ASCL42

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

end ASCL42

namespace ASCL42

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

end ASCL42

namespace ASCL42

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

/-- `OPT` truncated at time `2^i`, measured with the costs `c'` of an instance `J`. -/
noncomputable def trunc (J : Instance U m) (π : AdaptivePolicy m U) (i : ℕ) : AdaptivePolicy m U := fun h =>
  match π h with
  | some k => if ((J.costOf h : ℕ) : ℝ) + (J.c k : ℝ) ≤ 2 ^ i then some k else none
  | none => none

theorem trunc_cost (J : Instance U m) (π : AdaptivePolicy m U) (i : ℕ) (ν : Fin m → U) :
    ((J.costOf ((trunc J π i).run ν) : ℕ) : ℝ) ≤ 2 ^ i := by
  unfold AdaptivePolicy.run
  suffices ∀ n (h : History m U), ((J.costOf h : ℕ) : ℝ) ≤ 2 ^ i →
      ((J.costOf (((trunc J π i).step ν)^[n] h) : ℕ) : ℝ) ≤ 2 ^ i from
    this m [] (by simp [Instance.costOf, History.items])
  intro n
  induction n with
  | zero => intro h hh; exact hh
  | succ n ih =>
    intro h hh
    rw [Function.iterate_succ_apply]
    apply ih
    have hguard : ∀ k, trunc J π i h = some k →
        ((J.costOf h : ℕ) : ℝ) + (J.c k : ℝ) ≤ 2 ^ i := by
      intro k hk
      unfold trunc at hk
      rcases hπ : π h with _ | k'
      · rw [hπ] at hk; simp at hk
      · rw [hπ] at hk
        simp only at hk
        split_ifs at hk with hg
        · cases hk; exact hg
    unfold AdaptivePolicy.step
    rcases ht : trunc J π i h with _ | k
    · exact hh
    · simp only
      split_ifs with h2
      · exact hh
      · rw [costOf_append J h (k, ν k) h2]; push_cast; exact hguard k ht

theorem trunc_run (I J : Instance U m) (hc : ∀ k, J.c k ≤ I.c k) (π : AdaptivePolicy m U)
    (i : ℕ) (ν : Fin m → U) (hcost : ((I.costOf (π.run ν) : ℕ) : ℝ) ≤ 2 ^ i) :
    (trunc J π i).run ν = π.run ν := by
  unfold AdaptivePolicy.run at hcost ⊢
  have hJI : ∀ h : History m U, J.costOf h ≤ I.costOf h := fun h =>
    Finset.sum_le_sum fun k _ => hc k
  suffices ∀ n, n ≤ m → ((trunc J π i).step ν)^[n] [] = (π.step ν)^[n] [] from this m le_rfl
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
    set h := (π.step ν)^[n] [] with hh
    unfold AdaptivePolicy.step trunc
    rcases hπ : π h with _ | k
    · rfl
    · simp only
      by_cases hk : k ∈ h.items
      · split_ifs <;> simp [hk]
      · have hpre : h ++ [(k, ν k)] <+: (π.step ν)^[m] [] := by
          have := iterate_prefix π ν [] (n + 1) m hn
          rw [Function.iterate_succ_apply'] at this
          have e : π.step ν h = h ++ [(k, ν k)] := by
            unfold AdaptivePolicy.step; rw [hπ]; simp [hk]
          rw [← hh, e] at this
          exact this
        have h1 : I.costOf (h ++ [(k, ν k)]) ≤ I.costOf ((π.step ν)^[m] []) :=
          Finset.sum_le_sum_of_subset_of_nonneg (items_prefix hpre) (fun _ _ _ => Nat.zero_le _)
        rw [costOf_append I h (k, ν k) hk] at h1
        have h1' : I.costOf h + I.c k ≤ I.costOf ((π.step ν)^[m] []) := h1
        have h2 : ((J.costOf h : ℕ) : ℝ) + (J.c k : ℝ) ≤ 2 ^ i := by
          have := hJI h
          have := hc k
          have h3 : ((J.costOf h + J.c k : ℕ) : ℝ) ≤ ((I.costOf ((π.step ν)^[m] []) : ℕ) : ℝ) := by
            exact_mod_cast (by omega : J.costOf h + J.c k ≤ I.costOf ((π.step ν)^[m] []))
          push_cast at h3
          linarith
        rw [if_pos h2]

end ASCL42

namespace ASCL42

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

/-- Steps 2 and the adaptivity-gap bound of the proof of Lemma 4.2, for one realization `ω`
of the items `S`: a non-adaptive set `T_S` of cost at most `2^i` whose expected marginal value
is at least half of what `OPT` (truncated at time `2^i`) obtains. -/
theorem perContext (I : Instance U m) (hI : I.Standing) (π : AdaptivePolicy m U) (i : ℕ)
    (S : Finset (Fin m)) (ω : Fin m → U) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 2 ^ i ∧
      ((I.Q : ℝ) - I.f (S.image ω)) *
          I.E (fun ν => @ite ℝ (I.Covers (π.run (S.piecewise ω ν)) ∧
            (I.costOf (π.run (S.piecewise ω ν)) : ℝ) ≤ 2 ^ i) (Classical.propDecidable _) 1 0) ≤
        2 * I.E (fun ν => (I.f (S.image ω ∪ T.image ν) : ℝ) - I.f (S.image ω)) := by
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI
  set J := condInst I S ω with hJ
  have hp0' : ∀ k u, 0 ≤ J.p k u := by
    intro k u; simp only [hJ, condInst]
    split_ifs
    · norm_num
    · norm_num
    · exact hp0 k u
  have hp1' : ∀ k, ∑ u, J.p k u = 1 := by
    intro k; simp only [hJ, condInst]
    split_ifs with hk
    · simp
    · exact hp1 k
  set g : Finset U → ℝ := fun A => (I.f (S.image ω ∪ A) : ℝ) - I.f (S.image ω) with hg
  have hfm : Monotone (fun A : Finset U => (I.f A : ℝ)) := fun A B h => by
    simp only; exact_mod_cast hmon h
  have hgm : Monotone g := contr_mono _ hfm _
  have hgs : NonmonotoneSubmod.Shared.Submodular g := contr_sub _ hsub _
  have hg0 : ∀ A, 0 ≤ g A := by
    intro A; simp only [hg]
    linarith [hfm (Finset.subset_union_left (s₁ := S.image ω) (s₂ := A))]
  obtain ⟨T0, -, hcost, hbsz⟩ := AdaptSubCover.Rounds.bsz19_theorem_1 J hp0' hp1' g hg0 hgm hgs
    Finset.univ (2 ^ i) (trunc J π i)
    (fun ν => ⟨Finset.subset_univ _, trunc_cost J π i ν⟩)
  refine ⟨T0 \ S, Finset.sdiff_subset_sdiff (Finset.subset_univ _) le_rfl, ?_, ?_⟩
  · have : (∑ e ∈ T0, J.c e) = ∑ e ∈ T0 \ S, I.c e := by
      simp only [hJ, condInst]
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_not,
        Finset.sdiff_eq_filter]
      congr 1
      ext x; simp only [Finset.mem_filter, Finset.mem_sdiff]; tauto
    rw [← this]; exact hcost
  · rw [condInst_E I hp0 hp1, condInst_E I hp0 hp1] at hbsz
    have hR : I.E (fun ν => g (T0.image (S.piecewise ω ν))) =
        I.E (fun ν => (I.f (S.image ω ∪ (T0 \ S).image ν) : ℝ) - I.f (S.image ω)) := by
      apply E_congr; intro ν
      simp only [hg]
      congr 3
      ext u
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_sdiff, Finset.piecewise]
      constructor
      · rintro (h | ⟨e, he, rfl⟩)
        · exact Or.inl h
        · by_cases heS : e ∈ S
          · left; exact ⟨e, heS, by simp [heS]⟩
          · right; exact ⟨e, ⟨he, heS⟩, by simp [heS]⟩
      · rintro (h | ⟨e, ⟨he, heS⟩, rfl⟩)
        · exact Or.inl h
        · right; exact ⟨e, he, by simp [heS]⟩
    rw [hR] at hbsz
    refine le_trans ?_ hbsz
    rw [← E_smul]
    apply E_mono I hp0
    intro ν
    set ν' := S.piecewise ω ν
    by_cases hc : I.Covers (π.run ν') ∧ (I.costOf (π.run ν') : ℝ) ≤ 2 ^ i
    · rw [if_pos hc, mul_one]
      have hJc : ∀ k, J.c k ≤ I.c k := by
        intro k; simp only [hJ, condInst]; split_ifs <;> omega
      rw [trunc_run I J hJc π i ν' hc.2]
      simp only [hg]
      have hcov := hc.1
      unfold Instance.Covers at hcov
      have : (I.Q : ℝ) ≤ I.f (S.image ω ∪ (π.run ν').realized) := by
        rw [← hcov]
        exact_mod_cast hmon (Finset.subset_union_right)
      linarith
    · rw [if_neg hc, mul_zero]
      exact hg0 _

end ASCL42

namespace ASCL42

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem image_pw_S (S : Finset (Fin m)) (ω ν : Fin m → U) :
    S.image (S.piecewise ω ν) = S.image ω := by
  apply Finset.image_congr
  intro e he; simp [Finset.piecewise, Finset.mem_coe.mp he]

theorem image_pw_T (S T : Finset (Fin m)) (hT : T ⊆ Finset.univ \ S) (ω ν : Fin m → U) :
    T.image (S.piecewise ω ν) = T.image ν := by
  apply Finset.image_congr
  intro e he
  have : e ∉ S := (Finset.mem_sdiff.mp (hT (Finset.mem_coe.mp he))).2
  simp [Finset.piecewise, this]

theorem inScale_pw (I : Instance U m) (j : ℕ) (S : Finset (Fin m)) (ω ν : Fin m → U) :
    I.InScale j S (S.piecewise ω ν) ↔ I.InScale j S ω := by
  unfold Instance.InScale; rw [image_pw_S]

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

end ASCL42

open ASCL42 in
theorem solution {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (π : AdaptivePolicy m U) (i j : ℕ) (S : Finset (Fin m)) (hgood : I.Good π i j S) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 / (2⁻¹ : ℝ) ^ j * 2 ^ i ∧
      I.condE (I.InScale j S)
          (fun ω => (I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) ≥
        (2⁻¹ : ℝ) ^ j * I.Q / 6 * (I.rStar π i j S / I.P (I.InScale j S)) := by
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  set f : Finset U → ℝ := fun A => (I.f A : ℝ) with hf
  have hfm : Monotone f := fun A B h => by simp only [hf]; exact_mod_cast hmon h
  have hfQ : ∀ A, f A ≤ I.Q := fun A => by
    simp only [hf]; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ A)
  have hf0 : ∀ A, 0 ≤ f A := fun A => by simp only [hf]; positivity
  set θ : ℝ := (2⁻¹ : ℝ) ^ j with hθ
  have hθpos : 0 < θ := by positivity
  have hθK : θ * 2 ^ j = 1 := by rw [hθ, inv_pow, inv_mul_cancel₀ (by positivity)]
  set PE := I.P (I.InScale j S) with hPE
  set rs := I.rStar π i j S with hrs
  have hPE0 : 0 ≤ PE := E_nonneg I hp0 _ (fun ω => ind_nonneg _)
  have hPEpos : 0 < PE := by
    rcases hPE0.lt_or_eq with h | h
    · exact h
    · exfalso; unfold Instance.Good at hgood; rw [← hPE, ← h, div_zero] at hgood; norm_num at hgood
  have hrsPE : PE / 6 ≤ rs := by
    unfold Instance.Good at hgood; rw [← hPE, ← hrs, le_div_iff₀ hPEpos] at hgood; linarith
  -- indicator of the scale event
  set eind : (Fin m → U) → ℝ := fun ω =>
    @ite ℝ (I.InScale j S ω) (Classical.propDecidable _) 1 0 with heind
  have heind01 : ∀ ω, 0 ≤ eind ω ∧ eind ω ≤ 1 := by
    intro ω; simp only [heind]; split <;> norm_num
  have hPEeq : PE = I.E eind := rfl
  -- per-realization sets T_S
  set w : (Fin m → U) → ℝ := fun ω => I.E (fun ν => @ite ℝ (I.Covers (π.run (S.piecewise ω ν)) ∧
      (I.costOf (π.run (S.piecewise ω ν)) : ℝ) ≤ 2 ^ i) (Classical.propDecidable _) 1 0) with hw
  have hw0 : ∀ ω, 0 ≤ w ω := fun ω => E_nonneg I hp0 _ (fun ν => ind_nonneg _)
  set V : (Fin m → U) → Finset (Fin m) → ℝ := fun ω T =>
    I.E (fun ν => f (S.image ω ∪ T.image ν) - f (S.image ω)) with hV
  have hex := fun ω => perContext I hI π i S ω
  choose Tc hTcS hTccost hTcval using hex
  -- (K1) r* through the conditional coverage probabilities
  have hK1 : rs = I.E (fun ω => eind ω * w ω) := by
    rw [hrs]
    unfold Instance.rStar Instance.P
    rw [E_indep I hp1 S]
    apply E_congr; intro ω
    rw [← E_smul]
    apply E_congr; intro ν
    simp only [heind]
    by_cases hE : I.InScale j S ω
    · have hE' : I.InScale j S (S.piecewise ω ν) := (inScale_pw I j S ω ν).mpr hE
      rw [if_pos hE, one_mul]
      by_cases hc : I.Covers (π.run (S.piecewise ω ν)) ∧
          (I.costOf (π.run (S.piecewise ω ν)) : ℝ) ≤ 2 ^ i
      · rw [if_pos ⟨hc.1, hc.2, hE'⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]
    · have hE' : ¬ I.InScale j S (S.piecewise ω ν) := fun h => hE ((inScale_pw I j S ω ν).mp h)
      rw [if_neg hE, zero_mul, if_neg (fun h => hE' h.2.2)]
  -- (K2) numerators of conditional expectations
  have hK2 : ∀ T, T ⊆ Finset.univ \ S →
      I.E (fun ω => @ite ℝ (I.InScale j S ω) (Classical.propDecidable _)
        (f (S.image ω ∪ T.image ω) - f (S.image ω)) 0) = I.E (fun ω => eind ω * V ω T) := by
    intro T hT
    rw [E_indep I hp1 S]
    apply E_congr; intro ω
    simp only [hV]
    rw [← E_smul]
    apply E_congr; intro ν
    simp only [heind]
    by_cases hE : I.InScale j S ω
    · rw [if_pos ((inScale_pw I j S ω ν).mpr hE), if_pos hE, one_mul, image_pw_S,
        image_pw_T S T hT]
    · rw [if_neg (fun h => hE ((inScale_pw I j S ω ν).mp h)), if_neg hE, zero_mul]
  -- (K3) the bound (7)
  have hK3 : θ * I.Q / 4 * rs ≤ I.E (fun ω => eind ω * V ω (Tc ω)) := by
    rw [hK1, ← E_smul]
    apply E_mono I hp0
    intro ω
    simp only [heind]
    by_cases hE : I.InScale j S ω
    · rw [if_pos hE, one_mul, one_mul]
      obtain ⟨-, h1, -⟩ := hE
      have hgap : θ * I.Q / 2 ≤ (I.Q : ℝ) - I.f (S.image ω) := by
        rw [lt_div_iff₀ hQr] at h1; rw [hθ]; linarith
      have := hTcval ω
      have := hw0 ω
      simp only [hV, hf]
      nlinarith
    · rw [if_neg hE]; simp
  -- the iteration
  set D : Finset (Fin m) → (Fin m → U) → ℝ := fun A ω =>
    I.E (fun ν => f (A.image ν ∪ (Tc ω).image ν) - f (A.image ν)) with hD
  set Ef : Finset (Fin m) → ℝ := fun A => I.E (fun ν => f (A.image ν)) with hEf
  have hDEf : ∀ A ω, D A ω = Ef (A ∪ Tc ω) - Ef A := by
    intro A ω; simp only [hD, hEf]; rw [← E_sub]
    apply E_congr; intro ν; rw [Finset.image_union]
  classical
  set Eset := Finset.univ.filter (fun ω => I.InScale j S ω) with hEset
  have hne : Eset.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : PE = 0 := by
      rw [hPEeq]; unfold Instance.E
      apply Finset.sum_eq_zero; intro ω _
      have : ¬ I.InScale j S ω := by
        intro h
        have : ω ∈ Eset := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
        rw [hne] at this; simp at this
      simp [heind, this]
    linarith
  have hmax := fun A => Finset.exists_max_image Eset (D A) hne
  choose nxt hnxtE hnxt using hmax
  let Tseq : ℕ → Finset (Fin m) := fun k => Nat.rec ∅ (fun _ A => A ∪ Tc (nxt A)) k
  have hTseq0 : Tseq 0 = ∅ := rfl
  have hTseqS : ∀ k, Tseq (k + 1) = Tseq k ∪ Tc (nxt (Tseq k)) := fun k => rfl
  set K := 144 * 2 ^ j with hK
  set Tθ := Tseq K with hTθ
  have hTseq_sub : ∀ k, Tseq k ⊆ Finset.univ \ S := by
    intro k
    induction k with
    | zero => rw [hTseq0]; exact Finset.empty_subset _
    | succ k ih => rw [hTseqS]; exact Finset.union_subset ih (hTcS _)
  have hTseq_cost : ∀ k, ((∑ e ∈ Tseq k, I.c e : ℕ) : ℝ) ≤ k * 2 ^ i := by
    intro k
    induction k with
    | zero => rw [hTseq0]; simp
    | succ k ih =>
      rw [hTseqS]
      have h1 := cost_union I.c (Tseq k) (Tc (nxt (Tseq k)))
      have h2 := hTccost (nxt (Tseq k))
      have h3 : ((∑ e ∈ Tseq k ∪ Tc (nxt (Tseq k)), I.c e : ℕ) : ℝ) ≤
          ((∑ e ∈ Tseq k, I.c e : ℕ) : ℝ) + ((∑ e ∈ Tc (nxt (Tseq k)), I.c e : ℕ) : ℝ) := by
        exact_mod_cast h1
      have e : ((k + 1 : ℕ) : ℝ) * 2 ^ i = (k : ℝ) * 2 ^ i + 2 ^ i := by push_cast; ring
      rw [e]
      linarith
  have hTseq_mono : ∀ k, k ≤ K → Tseq k ⊆ Tθ := by
    intro k hk
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    rw [hTθ, hd]
    clear hd hk
    induction d with
    | zero => exact le_rfl
    | succ d ih => rw [← Nat.add_assoc, hTseqS]; exact ih.trans Finset.subset_union_left
  refine ⟨Tθ, hTseq_sub K, ?_, ?_⟩
  · have := hTseq_cost K
    have e : (144 : ℝ) / (2⁻¹ : ℝ) ^ j * 2 ^ i = (K : ℝ) * 2 ^ i := by
      rw [hK]; push_cast; rw [inv_pow, div_inv_eq_mul]
    rw [e]; exact this
  -- the value bound, by contradiction
  by_contra hcon
  push Not at hcon
  unfold Instance.condE at hcon
  beta_reduce at hcon
  rw [hK2 Tθ (hTseq_sub K), div_lt_iff₀ hPEpos] at hcon
  have hnum : I.E (fun ω => eind ω * V ω Tθ) < θ * I.Q / 6 * rs := by
    have : θ * I.Q / 6 * (rs / PE) * PE = θ * I.Q / 6 * rs := by field_simp
    linarith
  -- each increment is large
  have hinc : ∀ k < K, θ * I.Q * rs / 12 < PE * D (Tseq k) (nxt (Tseq k)) := by
    intro k hk
    -- average ≤ max
    have hav : I.E (fun ω => eind ω * D (Tseq k) ω) ≤ PE * D (Tseq k) (nxt (Tseq k)) := by
      rw [hPEeq, ← E_mul_const]
      apply E_mono I hp0; intro ω
      simp only [heind]
      by_cases hE : I.InScale j S ω
      · rw [if_pos hE, one_mul, one_mul]
        exact hnxt (Tseq k) ω (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hE⟩)
      · rw [if_neg hE]; simp
    -- monotonicity in the base set
    have hdr : I.E (fun ω => eind ω * D Tθ ω) ≤ I.E (fun ω => eind ω * D (Tseq k) ω) := by
      apply E_mono I hp0; intro ω
      apply mul_le_mul_of_nonneg_left _ (heind01 ω).1
      simp only [hD]
      apply E_mono I hp0; intro ν
      apply dimret f hfm hsub
      exact Finset.image_subset_image (hTseq_mono k hk.le)
    -- comparison with the per-realization sets
    have hcmp : I.E (fun ω => eind ω * V ω (Tc ω)) - I.E (fun ω => eind ω * V ω Tθ) ≤
        I.E (fun ω => eind ω * D Tθ ω) := by
      rw [← E_sub]
      apply E_mono I hp0; intro ω
      rw [← mul_sub]
      apply mul_le_mul_of_nonneg_left _ (heind01 ω).1
      simp only [hV, hD]
      rw [← E_sub]
      apply E_mono I hp0; intro ν
      have h1 := dimret f hfm hsub (Tθ.image ν) (S.image ω ∪ Tθ.image ν) ((Tc ω).image ν)
        Finset.subset_union_right
      have h2 : f (S.image ω ∪ (Tc ω).image ν) ≤ f (S.image ω ∪ Tθ.image ν ∪ (Tc ω).image ν) := by
        apply hfm; intro x hx
        simp only [Finset.mem_union] at hx ⊢; tauto
      linarith
    nlinarith
  -- telescoping
  have htel : ∑ k ∈ Finset.range K, D (Tseq k) (nxt (Tseq k)) = Ef Tθ - Ef ∅ := by
    have : ∀ k, D (Tseq k) (nxt (Tseq k)) = Ef (Tseq (k + 1)) - Ef (Tseq k) := by
      intro k; rw [hDEf, hTseqS]
    simp only [this]
    rw [Finset.sum_range_sub (fun k => Ef (Tseq k)) K, hTseq0]
  have hEfle : Ef Tθ ≤ I.Q := by
    simp only [hEf]
    calc I.E (fun ν => f (Tθ.image ν)) ≤ I.E (fun _ => (I.Q : ℝ)) :=
          E_mono I hp0 _ _ (fun ν => hfQ _)
      _ = I.Q := E_const I hp1 _
  have hEf0 : 0 ≤ Ef ∅ := by
    simp only [hEf]
    calc (0 : ℝ) = I.E (fun _ => (0 : ℝ)) := (E_const I hp1 0).symm
      _ ≤ _ := E_mono I hp0 _ _ (fun ν => hf0 _)
  have hsum : (K : ℝ) * (θ * I.Q * rs / 12) < PE * ∑ k ∈ Finset.range K, D (Tseq k) (nxt (Tseq k)) := by
    rw [Finset.mul_sum]
    have hKpos : 0 < K := by rw [hK]; positivity
    have := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hKpos.ne')
      (fun k hk => hinc k (Finset.mem_range.mp hk))
    simpa using this
  rw [htel] at hsum
  have hKθ : (K : ℝ) * θ = 144 := by
    rw [hK]; push_cast
    rw [show (144 : ℝ) * 2 ^ j * θ = 144 * (θ * 2 ^ j) by ring, hθK]; ring
  have : (K : ℝ) * (θ * I.Q * rs / 12) = 12 * I.Q * rs := by
    have : (K : ℝ) * (θ * I.Q * rs / 12) = (K * θ) * I.Q * rs / 12 := by ring
    rw [this, hKθ]; ring
  rw [this] at hsum
  have h1 : PE * (Ef Tθ - Ef ∅) ≤ PE * I.Q := by
    apply mul_le_mul_of_nonneg_left _ hPE0; linarith
  nlinarith

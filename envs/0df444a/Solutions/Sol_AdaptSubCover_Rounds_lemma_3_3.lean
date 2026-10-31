-- Prove2me | solution 1 for AdaptSubCover.Rounds.lemma_3_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T22:56:23.83903+00:00
-- url     : https://prove2.me/submissions/ddbe18c8-ec5b-4bf4-b7d8-ead45642aab5

import Mathlib
import Definitions.Def_AdaptSubCover_Rounds_Analysis
import Theorems.Thm_AdaptSubCover_Rounds_bsz19_theorem_1
import Theorems.Thm_AdaptSubCover_Rounds_lemma_4_5

open AdaptSubCover.Rounds

namespace ASCL33

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

end ASCL33

namespace ASCL33

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

end ASCL33

namespace ASCL33

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

end ASCL33

namespace ASCL33

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

end ASCL33

namespace ASCL33

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

end ASCL33

namespace ASCL33

/-- Lemma 4.2 for an arbitrary event `Cs` of the realization of `S` whose relative gap is
at least `θ/2` (the proof of Lemma 4.2 uses nothing else about the scale `E_θ`). -/
theorem G42 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (π : AdaptivePolicy m U) (i j : ℕ) (S : Finset (Fin m)) (Cs : Finset U → Prop)
    (hgap : ∀ A, Cs A → (2⁻¹ : ℝ) ^ j * I.Q / 2 ≤ (I.Q : ℝ) - I.f A)
    (hgood : 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
        Cs (S.image ω)) / I.P (fun ω => Cs (S.image ω))) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 * 2 ^ j * 2 ^ i ∧
      (2⁻¹ : ℝ) ^ j * I.Q / 6 * I.P (fun ω => I.Covers (π.run ω) ∧
          (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cs (S.image ω)) ≤
        I.E (fun ω => @ite ℝ (Cs (S.image ω)) (Classical.propDecidable _)
          ((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) 0) := by
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
  set PE := I.P (fun ω => Cs (S.image ω)) with hPE
  set rs := I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
        Cs (S.image ω)) with hrs
  have hPE0 : 0 ≤ PE := E_nonneg I hp0 _ (fun ω => ind_nonneg _)
  have hPEpos : 0 < PE := by
    rcases hPE0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h, div_zero] at hgood; norm_num at hgood
  have hrsPE : PE / 6 ≤ rs := by
    rw [le_div_iff₀ hPEpos] at hgood; linarith
  -- indicator of the scale event
  set eind : (Fin m → U) → ℝ := fun ω =>
    @ite ℝ (Cs (S.image ω)) (Classical.propDecidable _) 1 0 with heind
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
    unfold Instance.P
    rw [E_indep I hp1 S]
    apply E_congr; intro ω
    rw [← E_smul]
    apply E_congr; intro ν
    simp only [heind]
    by_cases hE : Cs (S.image ω)
    · have hE' : Cs (S.image (S.piecewise ω ν)) := by rw [image_pw_S]; exact hE
      rw [if_pos hE, one_mul]
      by_cases hc : I.Covers (π.run (S.piecewise ω ν)) ∧
          (I.costOf (π.run (S.piecewise ω ν)) : ℝ) ≤ 2 ^ i
      · rw [if_pos ⟨hc.1, hc.2, hE'⟩, if_pos hc]
      · rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩), if_neg hc]
    · have hE' : ¬ Cs (S.image (S.piecewise ω ν)) := by rw [image_pw_S]; exact hE
      rw [if_neg hE, zero_mul, if_neg (fun h => hE' h.2.2)]
  -- (K2) numerators of conditional expectations
  have hK2 : ∀ T, T ⊆ Finset.univ \ S →
      I.E (fun ω => @ite ℝ (Cs (S.image ω)) (Classical.propDecidable _)
        (f (S.image ω ∪ T.image ω) - f (S.image ω)) 0) = I.E (fun ω => eind ω * V ω T) := by
    intro T hT
    rw [E_indep I hp1 S]
    apply E_congr; intro ω
    simp only [hV]
    rw [← E_smul]
    apply E_congr; intro ν
    simp only [heind]
    by_cases hE : Cs (S.image ω)
    · rw [image_pw_S, if_pos hE, if_pos hE, one_mul, image_pw_T S T hT]
    · rw [image_pw_S, if_neg hE, if_neg hE, zero_mul]
  -- (K3) the bound (7)
  have hK3 : θ * I.Q / 4 * rs ≤ I.E (fun ω => eind ω * V ω (Tc ω)) := by
    rw [hK1, ← E_smul]
    apply E_mono I hp0
    intro ω
    simp only [heind]
    by_cases hE : Cs (S.image ω)
    · rw [if_pos hE, one_mul, one_mul]
      have hgap2 : θ * I.Q / 2 ≤ (I.Q : ℝ) - I.f (S.image ω) := hgap _ hE
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
  set Eset := Finset.univ.filter (fun ω => Cs (S.image ω)) with hEset
  have hne : Eset.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have : PE = 0 := by
      rw [hPEeq]; unfold Instance.E
      apply Finset.sum_eq_zero; intro ω _
      have : ¬ Cs (S.image ω) := by
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
    have e : (144 : ℝ) * 2 ^ j * 2 ^ i = (K : ℝ) * 2 ^ i := by
      rw [hK]; push_cast; ring
    rw [e]; exact this
  -- the value bound, by contradiction
  by_contra hcon
  push Not at hcon
  rw [hK2 Tθ (hTseq_sub K)] at hcon
  have hnum : I.E (fun ω => eind ω * V ω Tθ) < θ * I.Q / 6 * rs := hcon
  -- each increment is large
  have hinc : ∀ k < K, θ * I.Q * rs / 12 < PE * D (Tseq k) (nxt (Tseq k)) := by
    intro k hk
    -- average ≤ max
    have hav : I.E (fun ω => eind ω * D (Tseq k) ω) ≤ PE * D (Tseq k) (nxt (Tseq k)) := by
      rw [hPEeq, ← E_mul_const]
      apply E_mono I hp0; intro ω
      simp only [heind]
      by_cases hE : Cs (S.image ω)
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

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem scale_unique (x : ℝ) (j j' : ℕ)
    (h1 : (2⁻¹ : ℝ) ^ j / 2 < x) (h2 : x ≤ (2⁻¹ : ℝ) ^ j)
    (h1' : (2⁻¹ : ℝ) ^ j' / 2 < x) (h2' : x ≤ (2⁻¹ : ℝ) ^ j') : j = j' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (2⁻¹ : ℝ) ^ j' ≤ (2⁻¹ : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith
  · have : (2⁻¹ : ℝ) ^ j ≤ (2⁻¹ : ℝ) ^ (j' + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    rw [pow_succ] at this
    linarith

theorem scale_exists (Q F : ℕ) (hFQ : F < Q) :
    ∃ j : ℕ, j ≤ Nat.log 2 Q ∧ (2⁻¹ : ℝ) ^ j / 2 < ((Q : ℝ) - F) / Q ∧
        ((Q : ℝ) - F) / Q ≤ (2⁻¹ : ℝ) ^ j := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hinv : ∀ j : ℕ, (2⁻¹ : ℝ) ^ j = 1 / 2 ^ j := by intro j; rw [inv_pow, one_div]
  set d := Q - F with hd
  have hd1 : 1 ≤ d := by omega
  have hdQ : d ≤ Q := by omega
  set j := Nat.log 2 (Q / d)
  have hqd : Q / d ≠ 0 := by
    have : 1 ≤ Q / d := (Nat.one_le_div_iff (by omega)).mpr hdQ
    omega
  have h1 : 2 ^ j * d ≤ Q := by
    have := Nat.pow_log_le_self 2 hqd
    calc 2 ^ j * d ≤ Q / d * d := Nat.mul_le_mul_right _ this
      _ ≤ Q := Nat.div_mul_le_self Q d
  have h2 : Q < 2 ^ (j + 1) * d := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Q / d)
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp this
  have hdr : ((Q : ℝ) - F) = (d : ℝ) := by
    rw [hd, Nat.cast_sub hFQ.le]
  have h1r : (2 : ℝ) ^ j * d ≤ Q := by exact_mod_cast h1
  have h2r : (Q : ℝ) < 2 ^ (j + 1) * d := by exact_mod_cast h2
  refine ⟨j, ?_, ?_, ?_⟩
  · apply Nat.log_mono_right
    exact Nat.div_le_self Q d
  · rw [hdr, hinv, lt_div_iff₀ hQr]
    rw [pow_succ] at h2r
    rw [div_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    linarith
  · rw [hdr, hinv, div_le_iff₀ hQr]
    have h2j : (0 : ℝ) < 2 ^ j := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ h2j]
    linarith

theorem E_sum {ι : Type} (I : Instance U m) (s : Finset ι) (F : ι → (Fin m → U) → ℝ) :
    I.E (fun ω => ∑ j ∈ s, F j ω) = ∑ j ∈ s, I.E (F j) := by
  unfold Instance.E
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- The (extended) scale classes used in the proof of Lemma 3.3: scale `2^{-j}` intersected
with `f(S) ≤ τ`. For `j < z` this is the scale itself; the class `j = z` is nonempty only when
`τ` is an integer (it is `{f(S) = τ}`). -/
def Cls (I : Instance U m) (τ : ℝ) (j : ℕ) (A : Finset U) : Prop :=
  (j ≤ Nat.log 2 I.Q ∧ (2⁻¹ : ℝ) ^ j / 2 < ((I.Q : ℝ) - I.f A) / I.Q ∧
    ((I.Q : ℝ) - I.f A) / I.Q ≤ (2⁻¹ : ℝ) ^ j) ∧ (I.f A : ℝ) ≤ τ

theorem Cls_unique (I : Instance U m) (τ : ℝ) (j j' : ℕ) (A : Finset U)
    (h : Cls I τ j A) (h' : Cls I τ j' A) : j = j' :=
  scale_unique _ j j' h.1.2.1 h.1.2.2 h'.1.2.1 h'.1.2.2

theorem geom_two (N : ℕ) : ∑ i ∈ Finset.range N, (2 : ℝ) ^ i = 2 ^ N - 1 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem sum_biUnion_le' {ι κ : Type} [DecidableEq κ] (G : Finset ι) (T : ι → Finset κ)
    (c : κ → ℕ) : ∑ e ∈ G.biUnion T, c e ≤ ∑ j ∈ G, ∑ e ∈ T j, c e := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert a G ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have := Finset.sum_union_inter (s₁ := T a) (s₂ := G.biUnion T) (f := c)
    omega

/-- Lemma 4.3 for the extended classes `j ≤ z`, with the function `g` built on `f(S) ≤ τ`. -/
theorem G43 (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q) (τ : ℝ) (z : ℕ)
    (π : AdaptivePolicy m U) (i : ℕ) (S : Finset (Fin m)) :
    ∃ T ⊆ Finset.univ \ S, ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 288 * 2 ^ z * 2 ^ i ∧
      1 / 6 * ∑ j ∈ (Finset.range (z + 1)).filter (fun j =>
          1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I τ j (S.image ω)) / I.P (fun ω => Cls I τ j (S.image ω))),
        I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I τ j (S.image ω)) ≤
      I.E (fun ω => @ite ℝ ((I.f (S.image ω) : ℝ) ≤ τ) (Classical.propDecidable _)
        (((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))) 0) := by
  classical
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI'
  have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
  have hfQ : ∀ A : Finset U, (I.f A : ℝ) ≤ I.Q := by
    intro A; unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ A)
  have hfmono : ∀ A B : Finset U, A ⊆ B → (I.f A : ℝ) ≤ I.f B := by
    intro A B h; exact_mod_cast hmon h
  set r : ℕ → ℝ := fun j => I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
      Cls I τ j (S.image ω)) with hr
  set good : ℕ → Prop := fun j => 1 / 6 ≤ r j / I.P (fun ω => Cls I τ j (S.image ω)) with hgood
  have hex : ∀ j : ℕ, ∃ T : Finset (Fin m), T ⊆ Finset.univ \ S ∧ (good j →
      ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ 144 * 2 ^ j * 2 ^ i ∧
      (2⁻¹ : ℝ) ^ j * I.Q / 6 * r j ≤
        I.E (fun ω => @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _)
          ((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) 0)) := by
    intro j
    by_cases hg : good j
    · have hgap : ∀ A, Cls I τ j A → (2⁻¹ : ℝ) ^ j * I.Q / 2 ≤ (I.Q : ℝ) - I.f A := by
        intro A hA
        have := hA.1.2.1
        rw [lt_div_iff₀ hQr] at this; linarith
      obtain ⟨T, hT, h1, h2⟩ := G42 I hI hQ π i j S (Cls I τ j) hgap hg
      exact ⟨T, hT, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨∅, Finset.empty_subset _, fun h => absurd h hg⟩
  choose Tj hTsub hTj using hex
  set G := (Finset.range (z + 1)).filter good with hG
  set T := G.biUnion Tj with hT
  have hTS : T ⊆ Finset.univ \ S := by
    intro e he
    rw [hT, Finset.mem_biUnion] at he
    obtain ⟨j, _, hj⟩ := he
    exact hTsub j hj
  refine ⟨T, hTS, ?_, ?_⟩
  · have h1 := sum_biUnion_le' G Tj I.c
    have h1r : ((∑ e ∈ T, I.c e : ℕ) : ℝ) ≤ ∑ j ∈ G, ((∑ e ∈ Tj j, I.c e : ℕ) : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h1
    refine h1r.trans ?_
    have h2 : ∑ j ∈ G, ((∑ e ∈ Tj j, I.c e : ℕ) : ℝ) ≤ ∑ j ∈ G, 144 * 2 ^ i * (2 : ℝ) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      have := (hTj j (Finset.mem_filter.mp hj).2).1
      linarith
    refine h2.trans ?_
    have h3 : ∑ j ∈ G, 144 * 2 ^ i * (2 : ℝ) ^ j ≤
        ∑ j ∈ Finset.range (z + 1), 144 * 2 ^ i * (2 : ℝ) ^ j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    refine h3.trans ?_
    rw [← Finset.mul_sum, geom_two, pow_succ]
    have : (0 : ℝ) ≤ 144 * 2 ^ i := by positivity
    nlinarith
  · set ratio : (Fin m → U) → ℝ := fun ω =>
      ((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))
      with hratio
    have hratio0 : ∀ ω, 0 ≤ ratio ω := by
      intro ω
      apply div_nonneg
      · linarith [hfmono _ _ (Finset.subset_union_left (s₁ := S.image ω) (s₂ := T.image ω))]
      · linarith [hfQ (S.image ω)]
    have hA : ∑ j ∈ G, I.E (fun ω => @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _)
        (ratio ω) 0) ≤ I.E (fun ω => @ite ℝ ((I.f (S.image ω) : ℝ) ≤ τ)
          (Classical.propDecidable _) (ratio ω) 0) := by
      rw [← E_sum]
      apply E_mono I hp0
      intro ω
      by_cases hex : ∃ j ∈ G, Cls I τ j (S.image ω)
      · obtain ⟨j0, hj0, hE0⟩ := hex
        rw [Finset.sum_eq_single_of_mem j0 hj0 (fun j hj hne => by
          rw [if_neg]
          intro hE
          exact hne (Cls_unique I τ j j0 _ hE hE0))]
        rw [if_pos hE0, if_pos hE0.2]
      · push Not at hex
        rw [Finset.sum_eq_zero (fun j hj => if_neg (hex j hj))]
        split
        · exact hratio0 ω
        · exact le_refl _
    have hB : ∀ j ∈ G, 1 / 6 * r j ≤
        I.E (fun ω => @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _) (ratio ω) 0) := by
      intro j hj
      have hg := (Finset.mem_filter.mp hj).2
      obtain ⟨-, hcond⟩ := hTj j hg
      have hθ : (0 : ℝ) < (2⁻¹ : ℝ) ^ j := by positivity
      have hpt : ∀ ω, @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _)
          ((I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω)) 0 / ((2⁻¹ : ℝ) ^ j * I.Q) ≤
          @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _) (ratio ω) 0 := by
        intro ω
        by_cases hE : Cls I τ j (S.image ω)
        · rw [if_pos hE, if_pos hE]
          obtain ⟨⟨-, h1, h2⟩, -⟩ := hE
          have hden : 0 < (I.Q : ℝ) - I.f (S.image ω) := by
            have : 0 < ((I.Q : ℝ) - I.f (S.image ω)) / I.Q := lt_of_le_of_lt (by positivity) h1
            rwa [div_pos_iff_of_pos_right hQr] at this
          have hden2 : (I.Q : ℝ) - I.f (S.image ω) ≤ (2⁻¹ : ℝ) ^ j * I.Q := by
            rwa [div_le_iff₀ hQr] at h2
          have hDmono : (I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω) ≤
              (I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω) := by
            have : (Tj j).image ω ⊆ T.image ω := by
              apply Finset.image_subset_image
              intro e he; rw [hT, Finset.mem_biUnion]; exact ⟨j, hj, he⟩
            linarith [hfmono _ _ (Finset.union_subset_union (le_refl (S.image ω)) this)]
          have hD0 : 0 ≤ (I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω) := by
            linarith [hfmono _ _ (Finset.subset_union_left (s₁ := S.image ω) (s₂ := (Tj j).image ω))]
          simp only [hratio]
          calc _ ≤ ((I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω)) /
                ((I.Q : ℝ) - I.f (S.image ω)) := div_le_div_of_nonneg_left hD0 hden hden2
            _ ≤ _ := div_le_div_of_nonneg_right hDmono hden.le
        · rw [if_neg hE, if_neg hE, zero_div]
      have hEle := E_mono I hp0 _ _ hpt
      have e1 : I.E (fun ω => @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _)
          ((I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω)) 0 / ((2⁻¹ : ℝ) ^ j * I.Q)) =
          I.E (fun ω => @ite ℝ (Cls I τ j (S.image ω)) (Classical.propDecidable _)
          ((I.f (S.image ω ∪ (Tj j).image ω) : ℝ) - I.f (S.image ω)) 0) / ((2⁻¹ : ℝ) ^ j * I.Q) := by
        rw [div_eq_mul_inv, ← E_mul_const]
        apply E_congr; intro ω; rw [div_eq_mul_inv]
      rw [e1] at hEle
      refine le_trans ?_ hEle
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    rw [Finset.mul_sum]
    exact le_trans (Finset.sum_le_sum hB) hA

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem E_mono' (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (F G : (Fin m → U) → ℝ)
    (h : ∀ ω, 0 < I.prob ω → F ω ≤ G ω) : I.E F ≤ I.E G := by
  unfold Instance.E
  apply Finset.sum_le_sum
  intro ω _
  rcases (prob_nonneg I hp0 ω).lt_or_eq with hp | hp
  · exact mul_le_mul_of_nonneg_left (h ω hp) hp.le
  · rw [← hp]; simp

theorem P_nonneg (I : Instance U m) (hp0 : ∀ i u, 0 ≤ I.p i u) (A : (Fin m → U) → Prop) :
    0 ≤ I.P A := E_nonneg I hp0 _ (fun ω => ind_nonneg _)

theorem ind_sum_le_one {ι : Type} (s : Finset ι) (A : ι → Prop) {inst : ∀ j, Decidable (A j)}
    (h : ∀ j ∈ s, ∀ j' ∈ s, A j → A j' → j = j') :
    ∑ j ∈ s, (if A j then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hex : ∃ j ∈ s, A j
  · obtain ⟨j0, hj0, hA0⟩ := hex
    rw [Finset.sum_eq_single_of_mem j0 hj0 (fun j hj hne => if_neg (fun hA => hne (h j hj j0 hj0 hA hA0)))]
    simp [hA0]
  · push Not at hex
    rw [Finset.sum_eq_zero (fun j hj => if_neg (hex j hj))]
    norm_num

/-- If the stopping rule fires after the first `k` entries, only those entries are probed. -/
theorem go_items_sub (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U) (k : ℕ), l.Nodup → (∀ x ∈ l, x ∉ h.items) →
      stop (h ++ (l.take k).map (fun i => (i, ω i))) = true →
      (Round.go stop ω l h).items ⊆ h.items ∪ (l.take k).toFinset
  | [], h, k, _, _, _ => by simp [Round.go]
  | i :: l, h, k, hnd, hdis, hs => by
    by_cases hsh : stop h = true
    · simp [Round.go, hsh]
    · have hs' : stop h = false := by simpa using hsh
      have hi : i ∉ h.items := hdis i (by simp)
      have e : Round.go stop ω (i :: l) h = Round.go stop ω l (h ++ [(i, ω i)]) := by
        simp [Round.go, hs', hi]
      rw [e]
      cases k with
      | zero => simp at hs; exact absurd hs hsh
      | succ k =>
        have hnd' := (List.nodup_cons.mp hnd)
        have hdis' : ∀ x ∈ l, x ∉ (h ++ [(i, ω i)]).items := by
          intro x hx
          rw [items_append, Finset.mem_insert, not_or]
          exact ⟨fun hxi => hnd'.1 (by simp only at hxi; exact hxi ▸ hx), hdis x (by simp [hx])⟩
        have hs2 : stop ((h ++ [(i, ω i)]) ++ (l.take k).map (fun i => (i, ω i))) = true := by
          simpa using hs
        have := go_items_sub stop ω l _ k hnd'.2 hdis' hs2
        refine this.trans ?_
        rw [items_append]
        intro y hy
        simp only [Finset.mem_union, Finset.mem_insert, List.mem_toFinset] at hy ⊢
        rcases hy with (rfl | hy) | hy
        · right; simp
        · left; exact hy
        · right; simp [hy]

end ASCL33
namespace ASCL33

/-- Lemma 4.4 for the extended classes `j ≤ z` (no integrality assumption on `τ`). -/
theorem G44 {U : Type} [Fintype U] [DecidableEq U] {m : ℕ} (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q)
    (z : ℕ) (L : List (Fin m)) (hnd : L.Nodup) (hLuniv : L.toFinset = Finset.univ)
    (π : AdaptivePolicy m U) (hπ : I.Feasible π)
    (α : ℝ) (hα : 0 < α) (i : ℕ)
    (t : ℝ) (ht1 : α * 2 ^ (i - 1) ≤ t) (ht2 : t < α * 2 ^ i) :
    I.uPhase (I.tau z) α L i - 6 / 5 * I.uStar π i ≤
      ∑ j ∈ (Finset.range (z + 1)).filter (fun j =>
          1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I (I.tau z) j ((I.prefixAt L t).image ω)) /
            I.P (fun ω => Cls I (I.tau z) j ((I.prefixAt L t).image ω))),
        I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I (I.tau z) j ((I.prefixAt L t).image ω)) := by
  classical
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, -⟩ := hI'
  set S := I.prefixAt L t with hSdef
  set X : (Fin m → U) → ℝ := fun ω => (I.costOf (I.NA (I.tau z) L ω) : ℝ) with hXdef
  set Y : (Fin m → U) → ℝ := fun ω => (I.costOf (π.run ω) : ℝ) with hYdef
  have ht0 : 0 ≤ t := le_trans (by positivity) ht1
  -- the prefix index
  set k := Nat.findGreatest (fun j => (I.cumCost L j : ℝ) ≤ t) L.length with hk
  have hpre : S = (L.take k).toFinset := rfl
  have hPk : (I.cumCost L k : ℝ) ≤ t := by
    have := Nat.findGreatest_spec (P := fun j => (I.cumCost L j : ℝ) ≤ t) (m := 0)
      (n := L.length) (Nat.zero_le _) (by simp [Instance.cumCost, ht0])
    exact this
  have hcum : ∀ j, (I.cumCost L j : ℝ) = ∑ e ∈ (L.take j).toFinset, (I.c e : ℝ) := by
    intro j
    unfold Instance.cumCost
    rw [List.sum_toFinset _ ((List.take_sublist j L).nodup hnd)]
    push_cast
    rw [List.map_map]
    rfl
  have hcostle : ∀ (h : History m U) (A : Finset (Fin m)), h.items ⊆ A →
      (I.costOf h : ℝ) ≤ ∑ e ∈ A, (I.c e : ℝ) := by
    intro h A hA
    unfold Instance.costOf; push_cast
    exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun _ _ _ => by positivity)
  -- stopping by time t bounds the cost of NA by t
  have hstopcost : ∀ ω, I.NAStoppedBy (I.tau z) L t ω → X ω ≤ t := by
    intro ω hs
    have := hcostle _ (L.take k).toFinset hs
    rw [← hcum k] at this
    exact this.trans hPk
  have htot : ∀ ω, X ω ≤ I.cumCost L L.length := by
    intro ω
    rw [hcum, List.take_length, hLuniv]
    exact hcostle _ _ (Finset.subset_univ _)
  -- Step 1: non-good scales
  have hstep1 : ∀ j, ¬ 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) / I.P (fun ω => Cls I (I.tau z) j (S.image ω)) →
      I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) ≤ 1 / 5 * I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) := by
    intro j hng
    have hr0 : 0 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) := P_nonneg I hp0 _
    have hp20 := P_nonneg I hp0 (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω))
    have hrE : I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) ≤ I.P (fun ω => Cls I (I.tau z) j (S.image ω)) := by
      unfold Instance.P
      apply E_mono' I hp0
      intro ω _
      by_cases h : I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)
      · rw [if_pos h, if_pos h.2.2]
      · rw [if_neg h]; exact ind_nonneg _
    have hEr : I.P (fun ω => Cls I (I.tau z) j (S.image ω)) ≤
        I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) + I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) := by
      unfold Instance.P
      rw [← E_add]
      apply E_mono' I hp0
      intro ω hω
      by_cases hE : Cls I (I.tau z) j (S.image ω)
      · rw [if_pos hE]
        by_cases hY : (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i
        · rw [if_pos ⟨hπ ω hω, hY, hE⟩]
          linarith [@ind_nonneg ((2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) (Classical.propDecidable _)]
        · push Not at hY
          rw [if_pos (⟨hY.le, hE⟩ : (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω))]
          linarith [@ind_nonneg (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I (I.tau z) j (S.image ω)) (Classical.propDecidable _)]
      · rw [if_neg hE]
        exact add_nonneg (ind_nonneg _) (ind_nonneg _)
    push Not at hng
    rcases (P_nonneg I hp0 (fun ω => Cls I (I.tau z) j (S.image ω))).lt_or_eq with hpos | hzero
    · rw [div_lt_iff₀ hpos] at hng
      linarith
    · rw [← hzero] at hrE
      linarith
  -- Step 2: the sum over all scales above δ
  have hstep2 : I.uPhase (I.tau z) α L i - I.uStar π i ≤
      ∑ j ∈ Finset.range (z + 1), I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) := by
    unfold Instance.uPhase Instance.uStar Instance.P
    rw [← E_sub, ← E_sum]
    apply E_mono' I hp0
    intro ω hω
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (z + 1),
        @ite ℝ (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω))
          (Classical.propDecidable _) 1 0 :=
      Finset.sum_nonneg fun j _ => ind_nonneg _
    by_cases hu : α * 2 ^ i ≤ X ω
    · by_cases hus : (2 : ℝ) ^ i ≤ Y ω
      · rw [if_pos hu, if_pos hus, sub_self]
        exact Finset.sum_nonneg fun j _ => ind_nonneg _
      · rw [if_pos hu, if_neg hus]
        push Not at hus
        -- NA is not stopped by time t, so `f(S) ≤ τ`
        have hfle : (I.f (S.image ω) : ℝ) ≤ I.tau z := by
          by_contra hlt
          push Not at hlt
          have hsub := go_items_sub (I.parcaRound (I.tau z) L).stop ω L [] k hnd
            (by simp [History.items])
            (by
              have : History.realized (([] : History m U) ++ (L.take k).map (fun i => (i, ω i))) =
                  S.image ω := by
                rw [hpre]; ext u
                simp only [History.realized, List.nil_append, List.map_map, List.mem_toFinset,
                  Finset.mem_image]
                rw [List.mem_map]; simp
              simp only [Instance.parcaRound, this]
              simpa using hlt)
          have : I.NAStoppedBy (I.tau z) L t ω := by
            unfold Instance.NAStoppedBy
            rw [show History.items ([] : History m U) = ∅ by simp [History.items],
              Finset.empty_union] at hsub
            exact hsub
          have := hstopcost ω this; linarith
        have hτQ : I.tau z < I.Q := by
          unfold Instance.tau
          have : 0 < delta z := by unfold delta; positivity
          have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
          nlinarith
        have hFQ : I.f (S.image ω) < I.Q := by
          have : (I.f (S.image ω) : ℝ) < I.Q := lt_of_le_of_lt hfle hτQ
          exact_mod_cast this
        obtain ⟨j, hjlog, hj1, hj2⟩ := scale_exists I.Q (I.f (S.image ω)) hFQ
        have hjE : Cls I (I.tau z) j (S.image ω) := ⟨⟨hjlog, hj1, hj2⟩, hfle⟩
        have hjz : j < z + 1 := by
          by_contra hjz; push Not at hjz
          have hQr : (0 : ℝ) < I.Q := by exact_mod_cast hQ
          have h1 : (2⁻¹ : ℝ) ^ j ≤ (2⁻¹ : ℝ) ^ (z + 1) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hjz
          have h3 : delta z ≤ ((I.Q : ℝ) - I.f (S.image ω)) / I.Q := by
            rw [le_div_iff₀ hQr]; unfold Instance.tau at hfle; linarith
          unfold delta at h3
          rw [pow_succ] at h1
          have : (0 : ℝ) < (2⁻¹ : ℝ) ^ z := by positivity
          linarith
        have hterm : @ite ℝ (I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧
            Cls I (I.tau z) j (S.image ω)) (Classical.propDecidable _) 1 0 = 1 :=
          if_pos ⟨hπ ω hω, hus.le, hjE⟩
        have := Finset.single_le_sum (f := fun j => @ite ℝ (I.Covers (π.run ω) ∧
            (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) (Classical.propDecidable _) 1 0)
          (fun j _ => ind_nonneg _) (Finset.mem_range.mpr hjz)
        rw [hterm] at this
        linarith
    · rw [if_neg hu, zero_sub]
      refine le_trans ?_ (Finset.sum_nonneg fun j _ => ind_nonneg _)
      rw [neg_nonpos]
      exact ind_nonneg _
  -- Step 3: the OPT-tail mass over disjoint scales
  have hstep3 : ∀ B : Finset ℕ,
      ∑ j ∈ B, I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) ≤ I.uStar π i := by
    intro B
    unfold Instance.uStar Instance.P
    rw [← E_sum]
    apply E_mono' I hp0
    intro ω _
    by_cases hus : (2 : ℝ) ^ i ≤ Y ω
    · rw [if_pos hus]
      apply ind_sum_le_one
      intro j _ j' _ h h'
      exact Cls_unique I (I.tau z) j j' _ h.2 h'.2
    · rw [if_neg hus]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro j _
      exact if_neg (fun h => hus h.1)
  -- combine
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (z + 1))
    (fun j => 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) / I.P (fun ω => Cls I (I.tau z) j (S.image ω))) (fun j => I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)))
  have hbad : ∑ j ∈ (Finset.range (z + 1)).filter (fun j => ¬ 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) / I.P (fun ω => Cls I (I.tau z) j (S.image ω))), I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) ≤
      1 / 5 * I.uStar π i := by
    calc _ ≤ ∑ j ∈ (Finset.range (z + 1)).filter (fun j => ¬ 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) / I.P (fun ω => Cls I (I.tau z) j (S.image ω))),
          1 / 5 * I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact hstep1 j (Finset.mem_filter.mp hj).2
      _ = 1 / 5 * ∑ j ∈ (Finset.range (z + 1)).filter (fun j => ¬ 1 / 6 ≤ I.P (fun ω => I.Covers (π.run ω) ∧ (I.costOf (π.run ω) : ℝ) ≤ 2 ^ i ∧ Cls I (I.tau z) j (S.image ω)) / I.P (fun ω => Cls I (I.tau z) j (S.image ω))),
          I.P (fun ω => (2 : ℝ) ^ i ≤ Y ω ∧ Cls I (I.tau z) j (S.image ω)) := by rw [Finset.mul_sum]
      _ ≤ 1 / 5 * I.uStar π i := by
          apply mul_le_mul_of_nonneg_left (hstep3 _) (by norm_num)
  linarith

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- Structure of a round: it probes a prefix of its list, exactly until the rule fires. -/
theorem go_struct (stop : History m U → Bool) (ω : Fin m → U) :
    ∀ (l : List (Fin m)) (h : History m U), l.Nodup → (∀ x ∈ l, x ∉ h.items) →
      ∃ n ≤ l.length, Round.go stop ω l h = h ++ (l.take n).map (fun i => (i, ω i)) ∧
        (∀ j < n, stop (h ++ (l.take j).map (fun i => (i, ω i))) = false) ∧
        (n < l.length → stop (h ++ (l.take n).map (fun i => (i, ω i))) = true)
  | [], h, _, _ => ⟨0, le_rfl, by simp [Round.go], fun j hj => by omega, fun h => by simp at h⟩
  | i :: l, h, hnd, hdis => by
    by_cases hs : stop h = true
    · exact ⟨0, Nat.zero_le _, by simp [Round.go, hs], fun j hj => by omega, fun _ => by simpa using hs⟩
    · have hs' : stop h = false := by simpa using hs
      have hi : i ∉ h.items := hdis i (by simp)
      have e : Round.go stop ω (i :: l) h = Round.go stop ω l (h ++ [(i, ω i)]) := by
        simp [Round.go, hs', hi]
      have hnd' := (List.nodup_cons.mp hnd)
      have hdis' : ∀ x ∈ l, x ∉ (h ++ [(i, ω i)]).items := by
        intro x hx
        rw [items_append, Finset.mem_insert, not_or]
        exact ⟨fun hxi => hnd'.1 (by simp only at hxi; exact hxi ▸ hx), hdis x (by simp [hx])⟩
      obtain ⟨n, hn, hgo, hpre, hpost⟩ := go_struct stop ω l (h ++ [(i, ω i)]) hnd'.2 hdis'
      refine ⟨n + 1, by simp; omega, ?_, ?_, ?_⟩
      · rw [e, hgo]; simp
      · intro j hj
        cases j with
        | zero => simpa using hs'
        | succ j =>
          have := hpre j (by omega)
          simpa using this
      · intro hlt
        have := hpost (by simp at hlt; omega)
        simpa using this

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem items_take_map (L : List (Fin m)) (ω : Fin m → U) (j : ℕ) :
    History.items ((L.take j).map (fun i => (i, ω i))) = (L.take j).toFinset := by
  simp [History.items, List.map_map, Function.comp_def]

theorem realized_take_map (L : List (Fin m)) (ω : Fin m → U) (j : ℕ) :
    History.realized ((L.take j).map (fun i => (i, ω i))) = (L.take j).toFinset.image ω := by
  ext u
  simp only [History.realized, List.map_map, List.mem_toFinset, Finset.mem_image]
  rw [List.mem_map]; simp

theorem cost_take_map (I : Instance U m) (L : List (Fin m)) (hnd : L.Nodup) (ω : Fin m → U)
    (j : ℕ) : I.costOf ((L.take j).map (fun i => (i, ω i))) = I.cumCost L j := by
  unfold Instance.costOf Instance.cumCost
  rw [items_take_map, List.sum_toFinset _ ((List.take_sublist j L).nodup hnd)]

/-- The decision-path gain `G(Π)` of (14) written as a sum over the positions of the list. -/
theorem Gpath_formula (I : Instance U m) (hmon : Monotone I.f) (τ α : ℝ) (L : List (Fin m))
    (hnd : L.Nodup) (i : ℕ) (ω : Fin m → U) :
    I.Gpath τ α L i ω = ∑ j ∈ Finset.range L.length,
      max 0 (min (I.cumCost L (j + 1) : ℝ) (α * 2 ^ i) - max (I.cumCost L j : ℝ) (α * 2 ^ (i - 1))) /
        ((I.cumCost L (j + 1) : ℝ) - I.cumCost L j) *
      (if (I.f ((L.take j).toFinset.image ω) : ℝ) ≤ τ then
        ((I.f ((L.take (j + 1)).toFinset.image ω) : ℝ) - I.f ((L.take j).toFinset.image ω)) /
          ((I.Q : ℝ) - I.f ((L.take j).toFinset.image ω)) else 0) := by
  set stop := (I.parcaRound τ L).stop with hstop
  obtain ⟨n, hn, hgo, hpre, hpost⟩ := go_struct stop ω L [] hnd (by simp [History.items])
  have hNA : I.NA τ L ω = (L.take n).map (fun i => (i, ω i)) := by
    show Round.go stop ω L [] = _
    rw [hgo]; simp
  have hstopv : ∀ j, stop ((L.take j).map (fun i => (i, ω i))) =
      decide (τ < (I.f ((L.take j).toFinset.image ω) : ℝ)) := by
    intro j; simp only [hstop, Instance.parcaRound]; rw [realized_take_map]
  have hle : ∀ j < n, (I.f ((L.take j).toFinset.image ω) : ℝ) ≤ τ := by
    intro j hj
    have := hpre j hj
    simp only [List.nil_append] at this
    rw [hstopv] at this
    simpa using this
  have hgt : ∀ j, n ≤ j → j < L.length → ¬ (I.f ((L.take j).toFinset.image ω) : ℝ) ≤ τ := by
    intro j hj hjl
    have := hpost (by omega)
    simp only [List.nil_append] at this
    rw [hstopv] at this
    simp only [decide_eq_true_eq] at this
    have hsub : (L.take n).toFinset.image ω ⊆ (L.take j).toFinset.image ω := by
      apply Finset.image_subset_image
      intro x hx
      simp only [List.mem_toFinset] at hx ⊢
      exact List.take_subset_take_left L hj hx
    have : (I.f ((L.take n).toFinset.image ω) : ℝ) ≤ I.f ((L.take j).toFinset.image ω) := by
      exact_mod_cast hmon hsub
    push Not; linarith
  unfold Instance.Gpath
  rw [hNA]
  simp only [List.length_map, List.length_take, min_eq_left hn]
  have htk : ∀ j, j ≤ n → ((L.take n).map (fun i => (i, ω i))).take j =
      (L.take j).map (fun i => (i, ω i)) := by
    intro j hj
    rw [← List.map_take, List.take_take, min_eq_left hj]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hn) (fun j hj hjn => by
    simp only [Finset.mem_range] at hj hjn
    rw [if_neg (hgt j (by omega) hj), mul_zero])]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [htk x hx.le, htk (x + 1) hx, cost_take_map I L hnd, cost_take_map I L hnd,
    realized_take_map, realized_take_map, if_pos (hle x hx)]

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem subadd_image (f : Finset U → ℝ) (hfm : Monotone f)
    (hfs : NonmonotoneSubmod.Shared.Submodular f) (A : Finset U) (ω : Fin m → U) :
    ∀ T : Finset (Fin m), f (A ∪ T.image ω) - f A ≤ ∑ e ∈ T, (f (insert (ω e) A) - f A) := by
  intro T
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.image_insert]
    have h1 := dimret f hfm hfs A (A ∪ T.image ω) {ω a} Finset.subset_union_left
    have e1 : A ∪ insert (ω a) (T.image ω) = A ∪ T.image ω ∪ {ω a} := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    have e2 : A ∪ {ω a} = insert (ω a) A := by
      ext x; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
    rw [e1]; rw [e2] at h1
    linarith

theorem score_eq (I : Instance U m) (hc1 : ∀ i, 1 ≤ I.c i) (τ : ℝ) (S : Finset (Fin m))
    (e : Fin m) : (I.c e : ℝ) * I.scoreG (fun A => (I.f A : ℝ)) I.Q τ S e =
      I.E (fun ω => if (I.f (S.image ω) : ℝ) ≤ τ then
        ((I.f (insert (ω e) (S.image ω)) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))
        else 0) := by
  unfold Instance.scoreG
  have : (0 : ℝ) < I.c e := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hc1 e))
  field_simp

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

/-- The score lower bound (10) combined with Lemma 4.4, at a time `t` of phase `i`. -/
theorem SB (I : Instance U m) (hI : I.Standing) (hQ : 0 < I.Q) (z : ℕ) (L : List (Fin m))
    (hL : I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L)
    (π : AdaptivePolicy m U) (hπ : I.Feasible π) (α : ℝ) (hα : 0 < α) (i : ℕ)
    (t : ℝ) (ht1 : α * 2 ^ (i - 1) ≤ t) (ht2 : t < α * 2 ^ i) (k : ℕ) (hkl : k < L.length)
    (hk : Nat.findGreatest (fun j => (I.cumCost L j : ℝ) ≤ t) L.length = k) :
    delta z / (1728 * 2 ^ i) * (I.uPhase (I.tau z) α L i - 6 / 5 * I.uStar π i) ≤
      I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) (L.take k).toFinset (L[k]'hkl) := by
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  obtain ⟨hnd, hLuniv, hgr⟩ := hL
  set S := I.prefixAt L t with hS
  have hSk : S = (L.take k).toFinset := by rw [hS]; unfold Instance.prefixAt; rw [hk]
  set Δ := I.uPhase (I.tau z) α L i - 6 / 5 * I.uStar π i with hΔ
  have hsc0 := score_nonneg I hI (I.tau z) (L.take k).toFinset (L[k]'hkl)
  have hδ : 0 < delta z := by unfold delta; positivity
  rcases le_or_gt Δ 0 with hΔ0 | hΔ0
  · have : delta z / (1728 * 2 ^ i) * Δ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hΔ0
    linarith
  have h44 := G44 I hI hQ z L hnd hLuniv π hπ α hα i t ht1 ht2
  obtain ⟨T, hTS, hTcost, h43⟩ := G43 I hI hQ (I.tau z) z π i S
  rw [← hS] at h44
  -- subadditivity and the greedy choice
  have hfm : Monotone (fun A : Finset U => (I.f A : ℝ)) := fun A B h => by
    simp only; exact_mod_cast hmon h
  have hsubadd : I.E (fun ω => @ite ℝ ((I.f (S.image ω) : ℝ) ≤ I.tau z) (Classical.propDecidable _)
        (((I.f (S.image ω ∪ T.image ω) : ℝ) - I.f (S.image ω)) / ((I.Q : ℝ) - I.f (S.image ω))) 0) ≤
      ∑ e ∈ T, (I.c e : ℝ) * I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) S e := by
    simp only [score_eq I hc1]
    rw [← E_sum]
    apply E_mono I hp0
    intro ω
    by_cases hle : (I.f (S.image ω) : ℝ) ≤ I.tau z
    · rw [if_pos hle]
      simp only [if_pos hle]
      have hden : 0 ≤ (I.Q : ℝ) - I.f (S.image ω) := by
        have : (I.f (S.image ω) : ℝ) ≤ I.Q := by
          unfold Instance.Q; exact_mod_cast hmon (Finset.subset_univ _)
        linarith
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ hden
      exact subadd_image _ hfm hsub (S.image ω) ω T
    · rw [if_neg hle]; simp only [if_neg hle, Finset.sum_const_zero]; exact le_refl _
  have hgreedy : ∑ e ∈ T, (I.c e : ℝ) * I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) S e ≤
      ((∑ e ∈ T, I.c e : ℕ) : ℝ) * I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z)
        (L.take k).toFinset (L[k]'hkl) := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e he
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hSk]
    apply hgr k hkl e
    have := hTS he
    rw [hSk] at this
    exact this
  -- combine
  have hcost0 : (0 : ℝ) ≤ ((∑ e ∈ T, I.c e : ℕ) : ℝ) := by positivity
  have hchain : Δ / 6 ≤ 288 * 2 ^ z * 2 ^ i *
      I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) (L.take k).toFinset (L[k]'hkl) := by
    have := mul_le_mul_of_nonneg_right hTcost hsc0
    nlinarith
  have hz : delta z * 2 ^ z = 1 := by
    unfold delta; rw [inv_pow, inv_mul_cancel₀ (by positivity)]
  have h2i : (0 : ℝ) < 2 ^ i := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  set sc := I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) (L.take k).toFinset (L[k]'hkl)
  have h := mul_le_mul_of_nonneg_left hchain (by positivity : (0 : ℝ) ≤ 6 * delta z)
  have e : 6 * delta z * (288 * 2 ^ z * 2 ^ i * sc) = sc * (1728 * 2 ^ i) := by
    have : 6 * delta z * (288 * 2 ^ z * 2 ^ i * sc) = 1728 * (delta z * 2 ^ z) * 2 ^ i * sc := by
      ring
    rw [this, hz]; ring
  have e2 : 6 * delta z * (Δ / 6) = delta z * Δ := by ring
  linarith

end ASCL33

namespace ASCL33

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

theorem w_phi (a b X Y : ℝ) (hab : a ≤ b) (hYX : Y ≤ X) :
    max 0 (min b X - max a Y) = min (max b Y) X - min (max a Y) X := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem cum_succ (I : Instance U m) (L : List (Fin m)) (j : ℕ) (hj : j < L.length) :
    (I.cumCost L (j + 1) : ℝ) = I.cumCost L j + I.c (L[j]'hj) := by
  have : I.cumCost L (j + 1) = I.cumCost L j + I.c (L[j]'hj) := by
    unfold Instance.cumCost
    rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
      List.sum_append]
    simp
  exact_mod_cast this

theorem cum_mono (I : Instance U m) (L : List (Fin m)) (a b : ℕ) (hab : a ≤ b) :
    (I.cumCost L a : ℝ) ≤ I.cumCost L b := by
  have : I.cumCost L a ≤ I.cumCost L b := by
    unfold Instance.cumCost
    obtain ⟨t, ht⟩ := List.take_prefix_take_left (l := L) hab
    rw [← ht, List.map_append, List.sum_append]
    exact Nat.le_add_right _ _
  exact_mod_cast this

theorem take_succ_image (L : List (Fin m)) (j : ℕ) (hj : j < L.length) (ω : Fin m → U) :
    (L.take (j + 1)).toFinset.image ω = insert (ω (L[j]'hj)) ((L.take j).toFinset.image ω) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj]
  ext u
  simp only [Option.toList_some, List.toFinset_append, Finset.mem_image, Finset.mem_union,
    List.mem_toFinset, List.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨a, ha | rfl, rfl⟩
    · right; exact ⟨a, ha, rfl⟩
    · left; rfl
  · rintro (rfl | ⟨a, ha, rfl⟩)
    · exact ⟨L[j], Or.inr rfl, rfl⟩
    · exact ⟨a, Or.inl ha, rfl⟩

/-- `G(Π) = 0` if NA ends before phase `i`. -/
theorem Gpath_zero (I : Instance U m) (τ α : ℝ) (L : List (Fin m)) (i : ℕ) (ω : Fin m → U)
    (h : (I.costOf (I.NA τ L ω) : ℝ) < α * 2 ^ (i - 1)) : I.Gpath τ α L i ω = 0 := by
  unfold Instance.Gpath
  apply Finset.sum_eq_zero
  intro j _
  simp only
  have hb : (I.costOf ((I.NA τ L ω).take (j + 1)) : ℝ) ≤ I.costOf (I.NA τ L ω) := by
    unfold Instance.costOf
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => by positivity)
    intro x hx
    simp only [History.items, List.mem_toFinset, List.mem_map] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, List.take_subset _ _ hp, rfl⟩
  have hw : max 0 (min (I.costOf ((I.NA τ L ω).take (j + 1)) : ℝ) (α * 2 ^ i) -
      max (I.costOf ((I.NA τ L ω).take j) : ℝ) (α * 2 ^ (i - 1))) = 0 := by
    apply max_eq_left
    have := min_le_left (I.costOf ((I.NA τ L ω).take (j + 1)) : ℝ) (α * 2 ^ i)
    have := le_max_right (I.costOf ((I.NA τ L ω).take j) : ℝ) (α * 2 ^ (i - 1))
    linarith
  rw [hw, zero_div, zero_mul]

end ASCL33

open ASCL33 in
theorem solution :
    ∃ β : ℝ, 0 < β ∧
      ∀ (U : Type) [Fintype U] [DecidableEq U] (m : ℕ) (I : Instance U m),
        I.Standing → 0 < I.Q →
        ∀ (z : ℕ) (L : List (Fin m)), I.IsGreedyList (fun A => (I.f A : ℝ)) I.Q (I.tau z) Finset.univ L →
        ∀ π : AdaptivePolicy m U, I.Feasible π → ∀ i : ℕ, 1 ≤ i →
          I.uPhase (I.tau z) (8 * β / delta z * (1 + Real.log (1 / delta z))) L i ≤
            I.uPhase (I.tau z) (8 * β / delta z * (1 + Real.log (1 / delta z))) L (i - 1) / 4 +
              6 / 5 * I.uStar π i := by
  refine ⟨1728, by norm_num, ?_⟩
  intro U _ _ m I hI hQ z L hL π hπ i hi
  have hI' := hI
  obtain ⟨hp0, hp1, hc1, hmon, hsub⟩ := hI'
  have hL' := hL
  obtain ⟨hnd, hLuniv, hgr⟩ := hL'
  have hδ : 0 < delta z := by unfold delta; positivity
  have hδ1 : delta z ≤ 1 := by unfold delta; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.log (1 / delta z) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  set Λ := 1 + Real.log (1 / delta z) with hΛ
  have hΛpos : 0 < Λ := by linarith
  set α := 8 * 1728 / delta z * Λ with hαdef
  have hα : 0 < α := by positivity
  set u := I.uPhase (I.tau z) α L i with hu
  set u' := I.uPhase (I.tau z) α L (i - 1) with hu'
  set us := I.uStar π i with hus
  have hu'0 : 0 ≤ u' := P_nonneg I hp0 _
  have hus0 : 0 ≤ us := P_nonneg I hp0 _
  set Δ := u - 6 / 5 * us with hΔ
  rcases le_or_gt Δ 0 with hΔ0 | hΔ0
  · linarith
  set Xc := α * 2 ^ i with hXc
  set Yc := α * 2 ^ (i - 1) with hYc
  have hpow : (2 : ℝ) ^ i = 2 * 2 ^ (i - 1) := by
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    simp [pow_succ]; ring
  have hYpos : 0 < Yc := by positivity
  have hXY : Xc = 2 * Yc := by rw [hXc, hYc, hpow]; ring
  set C : ℕ → ℝ := fun j => (I.cumCost L j : ℝ) with hC
  have hC0 : C 0 = 0 := by simp [hC, Instance.cumCost]
  -- NA never costs more than the whole list
  have hXle : ∀ ω, (I.costOf (I.NA (I.tau z) L ω) : ℝ) ≤ C L.length := by
    intro ω
    have : I.costOf (I.NA (I.tau z) L ω) ≤ I.cumCost L L.length := by
      unfold Instance.costOf Instance.cumCost
      rw [List.take_length, ← List.sum_toFinset _ hnd, hLuniv]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
    simp only [hC]; exact_mod_cast this
  have htot : Xc ≤ C L.length := by
    by_contra h
    push Not at h
    have hu0 : u = 0 := by
      rw [hu]; unfold Instance.uPhase Instance.P Instance.E
      apply Finset.sum_eq_zero; intro ω _
      beta_reduce
      rw [if_neg (by have := hXle ω; linarith), mul_zero]
    linarith
  -- the gain G as a sum over list positions
  set w : ℕ → ℝ := fun j => max 0 (min (C (j + 1)) Xc - max (C j) Yc) with hw
  set sc : ∀ j, j < L.length → ℝ := fun j hj =>
    I.scoreG (fun A => (I.f A : ℝ)) I.Q (I.tau z) (L.take j).toFinset (L[j]'hj) with hsc
  have hEG : I.E (fun ω => I.Gpath (I.tau z) α L i ω) =
      ∑ j ∈ Finset.range L.length, (if hj : j < L.length then w j * sc j hj else 0) := by
    rw [E_congr I _ _ (fun ω => Gpath_formula I hmon (I.tau z) α L hnd i ω), E_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjl : j < L.length := Finset.mem_range.mp hj
    rw [dif_pos hjl, E_smul]
    have hcj : (0 : ℝ) < I.c (L[j]'hjl) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (hc1 _))
    have e1 := score_eq I hc1 (I.tau z) (L.take j).toFinset (L[j]'hjl)
    have e2 : I.E (fun ω => if (I.f ((L.take j).toFinset.image ω) : ℝ) ≤ I.tau z then
        ((I.f ((L.take (j + 1)).toFinset.image ω) : ℝ) - I.f ((L.take j).toFinset.image ω)) /
          ((I.Q : ℝ) - I.f ((L.take j).toFinset.image ω)) else 0) =
        (I.c (L[j]'hjl) : ℝ) * sc j hjl := by
      rw [hsc, e1]
      apply E_congr; intro ω
      rw [take_succ_image L j hjl ω]
    rw [e2, show (I.cumCost L (j + 1) : ℝ) - I.cumCost L j = I.c (L[j]'hjl) by
      rw [cum_succ I L j hjl]; ring]
    simp only [hw, hC]
    field_simp
    rw [hXc, hYc]; ring
  -- lower bound on G
  set B := delta z / (1728 * 2 ^ i) * Δ with hB
  have hlow : ∀ j (hj : j < L.length), w j * B ≤ w j * sc j hj := by
    intro j hj
    have hw0 : 0 ≤ w j := le_max_left _ _
    rcases hw0.lt_or_eq with hwpos | hw0'
    · apply mul_le_mul_of_nonneg_left _ hw0
      have hw' : max (C j) Yc < min (C (j + 1)) Xc := by
        simp only [hw] at hwpos
        by_contra hcon; push Not at hcon
        have : max 0 (min (C (j + 1)) Xc - max (C j) Yc) = 0 := max_eq_left (by linarith)
        linarith
      set t := max (C j) Yc with ht
      have ht2 : t < Xc := lt_of_lt_of_le hw' (min_le_right _ _)
      have hCt : t < C (j + 1) := lt_of_lt_of_le hw' (min_le_left _ _)
      have hk : Nat.findGreatest (fun j' => (I.cumCost L j' : ℝ) ≤ t) L.length = j := by
        rw [Nat.findGreatest_eq_iff]
        refine ⟨hj.le, fun _ => le_max_left _ _, ?_⟩
        intro n' hn' hn'l
        have := cum_mono I L (j + 1) n' hn'
        simp only [hC] at hCt
        push Not
        linarith
      exact SB I hI hQ z L hL π hπ α hα i t (le_max_right _ _) ht2 j hj hk
    · rw [← hw0']; simp
  have hsumw : ∑ j ∈ Finset.range L.length, w j = Xc - Yc := by
    have hφ : ∀ j, w j = min (max (C (j + 1)) Yc) Xc - min (max (C j) Yc) Xc := by
      intro j
      exact w_phi _ _ _ _ (cum_mono I L j (j + 1) (by omega)) (by rw [hXY]; linarith)
    simp only [hφ]
    rw [Finset.sum_range_sub (fun j => min (max (C j) Yc) Xc)]
    have hYX : Yc ≤ Xc := by rw [hXY]; linarith
    have e1 : min (max (C L.length) Yc) Xc = Xc := by
      rw [max_eq_left (le_trans hYX htot)]; exact min_eq_right htot
    have e2 : min (max (C 0) Yc) Xc = Yc := by
      rw [hC0, max_eq_right hYpos.le]; exact min_eq_left hYX
    simp only [e1, e2]
  have hGlow : (Xc - Yc) * B ≤ I.E (fun ω => I.Gpath (I.tau z) α L i ω) := by
    rw [hEG, ← hsumw, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    have hjl : j < L.length := Finset.mem_range.mp hj
    rw [dif_pos hjl]
    exact hlow j hjl
  -- upper bound on G (Lemma 4.5)
  have hGup : I.E (fun ω => I.Gpath (I.tau z) α L i ω) ≤ Λ * u' := by
    rw [hu']
    unfold Instance.uPhase Instance.P
    rw [← E_smul]
    apply E_mono I hp0
    intro ω
    by_cases hY : α * 2 ^ (i - 1) ≤ (I.costOf (I.NA (I.tau z) L ω) : ℝ)
    · rw [if_pos hY, mul_one]
      exact AdaptSubCover.Rounds.lemma_4_5 I hI hQ z L hL α hα i hi ω
    · rw [if_neg hY, mul_zero]
      push Not at hY
      rw [Gpath_zero I (I.tau z) α L i ω hY]
  -- combine
  have hkey : (Xc - Yc) * B = 4 * Λ * Δ := by
    rw [hXY, hB, hYc, hαdef, hpow]
    field_simp
    ring
  have : 4 * Λ * Δ ≤ Λ * u' := by linarith
  have : 4 * Δ ≤ u' := by nlinarith
  linarith

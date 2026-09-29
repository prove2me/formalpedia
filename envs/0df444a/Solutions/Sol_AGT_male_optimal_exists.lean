-- Prove2me | solution 1 for AGT.male_optimal_exists
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T09:56:38.573826+00:00
-- url     : https://prove2.me/submissions/c22e77b8-9bae-4a8e-814b-2a3a1b75cc97

import Definitions.Def_agt_matching
import Mathlib.Data.Fintype.Order
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Common

/-!
# Existence of a male-optimal stable matching (Gale–Shapley)

Adachi's fixed-point route: the deferred-acceptance operator is a monotone map on a
finite complete lattice of "aspiration levels", and its least fixed point is the
male-optimal stable matching.
-/



namespace GaleShapley

open Finset

/-! ## Ranks -/

/-- The number of alternatives strictly better than `a` in the strict total order `r`. -/
noncomputable def rk {α : Type*} (r : α → α → Prop) (a : α) : ℕ := {b | r b a}.ncard

section Rank

variable {α : Type*} [Fintype α] {r : α → α → Prop}

theorem rk_lt_rk (h : IsStrictTotalOrder α r) {a b : α} (hab : r a b) : rk r a < rk r b := by
  have := h
  apply Set.ncard_lt_ncard
  · constructor
    · intro x hx; exact trans_of r hx hab
    · intro hsub
      have : a ∈ {x : α | r x a} := hsub hab
      exact absurd this (by simpa using irrefl_of r a)
  · exact Set.toFinite _

theorem rk_lt_card (h : IsStrictTotalOrder α r) (a : α) : rk r a < Fintype.card α := by
  have := h
  have h2 : ({b : α | r b a}).ncard < (Set.univ : Set α).ncard := by
    apply Set.ncard_lt_ncard _ Set.finite_univ
    constructor
    · exact Set.subset_univ _
    · intro hsub
      have : a ∈ {x : α | r x a} := hsub (Set.mem_univ a)
      exact absurd this (by simpa using irrefl_of r a)
  simpa [rk, Set.ncard_univ, Nat.card_eq_fintype_card] using h2

theorem rk_lt_iff (h : IsStrictTotalOrder α r) (a b : α) : rk r a < rk r b ↔ r a b := by
  have := h
  constructor
  · intro hlt
    rcases trichotomous_of r a b with h1 | h1 | h1
    · exact h1
    · subst h1; omega
    · have := rk_lt_rk h h1; omega
  · exact rk_lt_rk h

theorem rk_inj (h : IsStrictTotalOrder α r) : Function.Injective (rk r) := by
  have := h
  intro a b hab
  rcases trichotomous_of r a b with h1 | h1 | h1
  · have := rk_lt_rk h h1; omega
  · exact h1
  · have := rk_lt_rk h h1; omega

end Rank

/-! ## The deferred acceptance operator -/

section Operator

variable {M W : Type*} [Fintype M] [Fintype W]

/-- The `Fin`-valued rank of woman `w` in man `m`'s list (`n` is a cap that is never
attained under the standing hypotheses: smaller means better). -/
noncomputable def rkF (PM : M → W → W → Prop) (n : ℕ) (m : M) (w : W) : Fin (n + 1) :=
  ⟨min (rk (PM m) w) n, by omega⟩

/-- The `Fin`-valued *co-rank* of man `m` in woman `w`'s list: `n` minus his rank, so that
bigger means better and `0` is reserved for "no man at all". -/
noncomputable def coF (PW : W → M → M → Prop) (n : ℕ) (w : W) (m : M) : Fin (n + 1) :=
  ⟨n - rk (PW w) m, by omega⟩

/-- One round of deferred acceptance in terms of aspiration levels: each man aims at his
best woman who would not reject him, each woman keeps the best man aiming at her. -/
noncomputable def step (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ)
    (x : (M → Fin (n + 1)) × (W → Fin (n + 1))) :
    (M → Fin (n + 1)) × (W → Fin (n + 1)) :=
  (fun m => (univ.filter fun w => x.2 w ≤ coF PW n w m).inf (rkF PM n m),
   fun w => (univ.filter fun m => rkF PM n m w ≤ x.1 m).sup (coF PW n w))

theorem step_mono (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    Monotone (step PM PW n) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · intro m
    refine Finset.inf_mono ?_
    intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw ⊢
    exact le_trans (h2 w) hw
  · intro w
    refine Finset.sup_mono ?_
    intro m hm
    simp only [mem_filter, mem_univ, true_and] at hm ⊢
    exact le_trans hm (h1 m)

/-- The deferred-acceptance operator as a bundled monotone map. -/
noncomputable def stepHom (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    ((M → Fin (n + 1)) × (W → Fin (n + 1))) →o ((M → Fin (n + 1)) × (W → Fin (n + 1))) :=
  ⟨step PM PW n, step_mono PM PW n⟩

end Operator

/-! ## Rank arithmetic in `Fin (n+1)` -/

section FinRank

variable {M W : Type*} [Fintype M] [Fintype W] {n : ℕ}
  {PM : M → W → W → Prop} {PW : W → M → M → Prop}

omit [Fintype M] in
theorem rkF_val (hM : AGT.IsPrefProfile PM) (hnW : Fintype.card W = n) (m : M) (w : W) :
    (rkF PM n m w).val = rk (PM m) w := by
  have := rk_lt_card (hM m) w
  simp only [rkF]
  omega

omit [Fintype M] in
theorem rkF_lt_iff (hM : AGT.IsPrefProfile PM) (hnW : Fintype.card W = n) (m : M) (w₁ w₂ : W) :
    rkF PM n m w₁ < rkF PM n m w₂ ↔ PM m w₁ w₂ := by
  rw [Fin.lt_def, rkF_val hM hnW, rkF_val hM hnW]
  exact rk_lt_iff (hM m) w₁ w₂

omit [Fintype M] in
theorem rkF_inj (hM : AGT.IsPrefProfile PM) (hnW : Fintype.card W = n) (m : M) :
    Function.Injective (rkF PM n m) := by
  intro w₁ w₂ h
  apply rk_inj (hM m)
  rw [← rkF_val hM hnW m w₁, ← rkF_val hM hnW m w₂, h]

omit [Fintype M] in
theorem rkF_le_iff (hM : AGT.IsPrefProfile PM) (hnW : Fintype.card W = n) (m : M) (w₁ w₂ : W) :
    rkF PM n m w₁ ≤ rkF PM n m w₂ ↔ (w₁ = w₂ ∨ PM m w₁ w₂) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inr ((rkF_lt_iff hM hnW m w₁ w₂).1 h)
    · exact Or.inl (rkF_inj hM hnW m h)
  · rintro (rfl | h)
    · exact le_rfl
    · exact le_of_lt ((rkF_lt_iff hM hnW m w₁ w₂).2 h)

omit [Fintype W] in
theorem coF_pos (hW : AGT.IsPrefProfile PW) (hnM : Fintype.card M = n) (w : W) (m : M) :
    0 < (coF PW n w m).val := by
  have := rk_lt_card (hW w) m
  simp only [coF]
  omega

omit [Fintype W] in
theorem coF_lt_iff (hW : AGT.IsPrefProfile PW) (hnM : Fintype.card M = n) (w : W) (m₁ m₂ : M) :
    coF PW n w m₁ < coF PW n w m₂ ↔ PW w m₂ m₁ := by
  have h1 := rk_lt_card (hW w) m₁
  have h2 := rk_lt_card (hW w) m₂
  rw [Fin.lt_def]
  simp only [coF]
  rw [← rk_lt_iff (hW w) m₂ m₁]
  omega

omit [Fintype W] in
theorem coF_inj (hW : AGT.IsPrefProfile PW) (hnM : Fintype.card M = n) (w : W) :
    Function.Injective (coF PW n w) := by
  have := hW w
  intro m₁ m₂ h
  by_contra hne
  rcases trichotomous_of (PW w) m₁ m₂ with h1 | h1 | h1
  · have := (coF_lt_iff hW hnM w m₂ m₁).2 h1
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact hne h1
  · have := (coF_lt_iff hW hnM w m₁ m₂).2 h1
    rw [h] at this; exact absurd this (lt_irrefl _)

omit [Fintype W] in
theorem coF_le_iff (hW : AGT.IsPrefProfile PW) (hnM : Fintype.card M = n) (w : W) (m₁ m₂ : M) :
    coF PW n w m₁ ≤ coF PW n w m₂ ↔ (m₁ = m₂ ∨ PW w m₂ m₁) := by
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inr ((coF_lt_iff hW hnM w m₁ m₂).1 h)
    · exact Or.inl (coF_inj hW hnM w h)
  · rintro (rfl | h)
    · exact le_rfl
    · exact le_of_lt ((coF_lt_iff hW hnM w m₁ m₂).2 h)

end FinRank

/-! ## Properties of a fixed point -/

section Fixed

variable {M W : Type*} [Fintype M] [Fintype W] {n : ℕ}
  {PM : M → W → W → Prop} {PW : W → M → M → Prop}
  {a : M → Fin (n + 1)} {b : W → Fin (n + 1)}

/-- At a fixed point, a man's aspiration level is at least as good as any woman who
would not reject him. -/
theorem inf_le_of_fixed (hfix : step PM PW n (a, b) = (a, b)) {m : M} {w : W}
    (h : b w ≤ coF PW n w m) : a m ≤ rkF PM n m w := by
  have h1 : (univ.filter fun w => b w ≤ coF PW n w m).inf (rkF PM n m) = a m := by
    have := congrArg (fun p => p.1 m) hfix
    simpa [step] using this
  rw [← h1]
  exact Finset.inf_le (by simp [h])

/-- At a fixed point, a woman's level is at least as good as any man aiming at her. -/
theorem le_sup_of_fixed (hfix : step PM PW n (a, b) = (a, b)) {m : M} {w : W}
    (h : rkF PM n m w ≤ a m) : coF PW n w m ≤ b w := by
  have h1 : (univ.filter fun m => rkF PM n m w ≤ a m).sup (coF PW n w) = b w := by
    have := congrArg (fun p => p.2 w) hfix
    simpa [step] using this
  rw [← h1]
  exact Finset.le_sup (by simp [h])

/-- At a fixed point, a woman holding somebody holds an actual man. -/
theorem sup_attained (hfix : step PM PW n (a, b) = (a, b)) {w : W} (h : 0 < b w) :
    ∃ m : M, rkF PM n m w ≤ a m ∧ b w = coF PW n w m := by
  have h1 : (univ.filter fun m => rkF PM n m w ≤ a m).sup (coF PW n w) = b w := by
    have := congrArg (fun p => p.2 w) hfix
    simpa [step] using this
  rcases Finset.eq_empty_or_nonempty (univ.filter fun m => rkF PM n m w ≤ a m) with he | hne
  · rw [he, Finset.sup_empty] at h1
    rw [← h1] at h
    exact absurd h (lt_irrefl _)
  · obtain ⟨m, hm, hsup⟩ := Finset.exists_mem_eq_sup _ hne (coF PW n w)
    refine ⟨m, by simpa using hm, ?_⟩
    rw [← h1, hsup]

/-- At a fixed point, every man has a woman who would not reject him. -/
theorem filter_nonempty (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hnM : Fintype.card M = n) (hnW : Fintype.card W = n)
    (hfix : step PM PW n (a, b) = (a, b)) (m : M) :
    (univ.filter fun w => b w ≤ coF PW n w m).Nonempty := by
  by_contra hemp
  rw [Finset.not_nonempty_iff_eq_empty] at hemp
  have hall : ∀ w : W, coF PW n w m < b w := by
    intro w
    have hw : w ∉ univ.filter (fun w => b w ≤ coF PW n w m) := by rw [hemp]; simp
    simp only [mem_filter, mem_univ, true_and, not_le] at hw
    exact hw
  have hpos : ∀ w : W, 0 < b w := by
    intro w
    have h1 := coF_pos hW hnM w m
    have h2 := hall w
    rw [Fin.lt_def] at h2 ⊢
    simp only [Fin.val_zero]
    omega
  choose g hg1 hg2 using fun w => sup_attained hfix (hpos w)
  have hkey : ∀ w : W, a (g w) = rkF PM n (g w) w := fun w =>
    le_antisymm (inf_le_of_fixed hfix (le_of_eq (hg2 w))) (hg1 w)
  have hginj : Function.Injective g := by
    intro w₁ w₂ hgg
    apply rkF_inj hM hnW (g w₁)
    have e1 : rkF PM n (g w₁) w₁ = a (g w₁) := (hkey w₁).symm
    have e2 : rkF PM n (g w₁) w₂ = a (g w₁) := by rw [hgg]; exact (hkey w₂).symm
    rw [e1, e2]
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).2 ⟨hginj, by rw [hnW, hnM]⟩
  obtain ⟨w, hw⟩ := hgbij.2 m
  have : b w ≤ coF PW n w m := by rw [hg2 w, hw]
  have hmem : w ∈ univ.filter (fun w => b w ≤ coF PW n w m) := by simp [this]
  rw [hemp] at hmem
  simp at hmem

/-- At a fixed point, every man's aspiration level is realized by an actual woman who
would not reject him. -/
theorem inf_attained (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hnM : Fintype.card M = n) (hnW : Fintype.card W = n)
    (hfix : step PM PW n (a, b) = (a, b)) (m : M) :
    ∃ w : W, b w ≤ coF PW n w m ∧ a m = rkF PM n m w := by
  have h1 : (univ.filter fun w => b w ≤ coF PW n w m).inf (rkF PM n m) = a m := by
    have := congrArg (fun p => p.1 m) hfix
    simpa [step] using this
  obtain ⟨w, hw, hinf⟩ :=
    Finset.exists_mem_eq_inf _ (filter_nonempty hM hW hnM hnW hfix m) (rkF PM n m)
  simp only [mem_filter, mem_univ, true_and] at hw
  exact ⟨w, hw, by rw [← h1, hinf]⟩

end Fixed

end GaleShapley

/-! ## The theorem -/

theorem solution {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hcard : Nonempty (M ≃ W)) :
    ∃ μ : M ≃ W, AGT.IsMaleOptimal PM PW μ := by
  classical
  open GaleShapley Finset in
  obtain ⟨e⟩ := hcard
  set n := Fintype.card M with hn
  have hnM : Fintype.card M = n := rfl
  have hnW : Fintype.card W = n := (Fintype.card_congr e).symm
  have hmap := OrderHom.map_lfp (stepHom PM PW n)
  set x := OrderHom.lfp (stepHom PM PW n) with hx
  set a := x.1 with ha
  set b := x.2 with hb
  have hfix : step PM PW n (a, b) = (a, b) := by
    rw [ha, hb, Prod.mk.eta]
    exact hmap
  choose v hv1 hv2 using inf_attained hM hW hnM hnW hfix
  have hbv : ∀ m, b (v m) = coF PW n (v m) m := fun m =>
    le_antisymm (hv1 m) (le_sup_of_fixed hfix (le_of_eq (hv2 m).symm))
  have hvinj : Function.Injective v := by
    intro m₁ m₂ h
    apply coF_inj hW hnM (v m₁)
    have e1 : coF PW n (v m₁) m₁ = b (v m₁) := (hbv m₁).symm
    have e2 : coF PW n (v m₁) m₂ = b (v m₁) := by rw [h]; exact (hbv m₂).symm
    rw [e1, e2]
  have hvbij : Function.Bijective v :=
    (Fintype.bijective_iff_injective_and_card v).2 ⟨hvinj, by rw [hnM, hnW]⟩
  refine ⟨Equiv.ofBijective v hvbij, ?_, ?_⟩
  · -- stability
    rintro m w ⟨hb1, hb2⟩
    set μ := Equiv.ofBijective v hvbij with hμ
    have hsymm : v (μ.symm w) = w := μ.apply_symm_apply w
    have h1 : b w = coF PW n w (μ.symm w) := by
      have := hbv (μ.symm w); rwa [hsymm] at this
    have h2 : coF PW n w (μ.symm w) < coF PW n w m := (coF_lt_iff hW hnM w _ m).2 hb2
    have h3 : b w ≤ coF PW n w m := le_of_lt (h1 ▸ h2)
    have h4 : a m ≤ rkF PM n m w := inf_le_of_fixed hfix h3
    have h5 : rkF PM n m w < rkF PM n m (v m) := (rkF_lt_iff hM hnW m w (v m)).2 hb1
    rw [← hv2 m] at h5
    exact absurd h4 (not_le.2 h5)
  · -- male optimality
    intro ν hν m
    set y : (M → Fin (n + 1)) × (W → Fin (n + 1)) :=
      (fun m => rkF PM n m (ν m), fun w => coF PW n w (ν.symm w)) with hy
    have hstep : step PM PW n y ≤ y := by
      refine ⟨?_, ?_⟩
      · intro m'
        have hmem : ν m' ∈ univ.filter (fun w => y.2 w ≤ coF PW n w m') := by
          simp only [mem_filter, mem_univ, true_and, hy]
          rw [ν.symm_apply_apply]
        exact Finset.inf_le hmem
      · intro w
        refine Finset.sup_le ?_
        intro m' hm'
        simp only [mem_filter, mem_univ, true_and, hy] at hm' ⊢
        rcases (rkF_le_iff hM hnW m' w (ν m')).1 hm' with heq | hpref
        · subst heq
          rw [ν.symm_apply_apply]
        · refine (coF_le_iff hW hnM w m' (ν.symm w)).2 ?_
          by_contra hcon
          rw [not_or] at hcon
          obtain ⟨hne, hnp⟩ := hcon
          have := hW w
          rcases trichotomous_of (PW w) m' (ν.symm w) with h1 | h1 | h1
          · exact hν m' w ⟨hpref, h1⟩
          · exact hne h1
          · exact hnp h1
    have hle : x ≤ y := OrderHom.lfp_le (stepHom PM PW n) hstep
    have hm : a m ≤ rkF PM n m (ν m) := hle.1 m
    rw [hv2 m] at hm
    exact (rkF_le_iff hM hnW m (v m) (ν m)).1 hm

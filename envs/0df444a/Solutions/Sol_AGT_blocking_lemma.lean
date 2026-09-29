-- Prove2me | solution 1 for AGT.blocking_lemma
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-13T11:22:13.229643+00:00
-- url     : https://prove2.me/submissions/bd728ef2-09e0-468c-a5a5-9214f3616505

import Definitions.Def_agt_matching
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Card
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Common
import Mathlib.Tactic.Push

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

/-! ## The deferred-acceptance state and its matching -/

section DA

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] {n : ℕ}
  {PM : M → W → W → Prop} {PW : W → M → M → Prop}

/-- The men's component of the least fixed point: `daA m` is the rank of the best woman
man `m` can still hope for. -/
noncomputable def daA (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    M → Fin (n + 1) := (OrderHom.lfp (stepHom PM PW n)).1

/-- The women's component of the least fixed point: `daB w` is the co-rank of the best man
woman `w` is holding. -/
noncomputable def daB (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    W → Fin (n + 1) := (OrderHom.lfp (stepHom PM PW n)).2

theorem da_fix (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    step PM PW n (daA PM PW n, daB PM PW n) = (daA PM PW n, daB PM PW n) := by
  have hmap := OrderHom.map_lfp (stepHom PM PW n)
  have h : (daA PM PW n, daB PM PW n) = OrderHom.lfp (stepHom PM PW n) := rfl
  rw [h]
  exact hmap

/-- The least fixed point of the deferred-acceptance operator is a matching, and it is the
male-optimal stable matching. -/
theorem exists_da_matching (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hnM : Fintype.card M = n) (hnW : Fintype.card W = n) :
    ∃ μ : M ≃ W, (∀ m, daA PM PW n m = rkF PM n m (μ m)) ∧
      (∀ w, daB PM PW n w = coF PW n w (μ.symm w)) ∧ AGT.IsMaleOptimal PM PW μ := by
  classical
  set a := daA PM PW n with ha
  set b := daB PM PW n with hb
  have hfix : step PM PW n (a, b) = (a, b) := da_fix PM PW n
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
  set μ := Equiv.ofBijective v hvbij with hμ
  have hvμ : ∀ m, v m = μ m := fun _ => rfl
  have hbw : ∀ w, b w = coF PW n w (μ.symm w) := by
    intro w
    have hsymm : v (μ.symm w) = w := μ.apply_symm_apply w
    have := hbv (μ.symm w)
    rwa [hsymm] at this
  refine ⟨μ, fun m => by rw [hv2 m, hvμ], hbw, ?_, ?_⟩
  · -- stability
    rintro m w ⟨hb1, hb2⟩
    have h1 : b w = coF PW n w (μ.symm w) := hbw w
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
    have hle : OrderHom.lfp (stepHom PM PW n) ≤ y := OrderHom.lfp_le (stepHom PM PW n) hstep
    have hm : a m ≤ rkF PM n m (ν m) := hle.1 m
    rw [hv2 m] at hm
    exact (rkF_le_iff hM hnW m (v m) (ν m)).1 hm

end DA

end GaleShapley

/-! ## The theorem -/

theorem male_optimal_exists {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hcard : Nonempty (M ≃ W)) :
    ∃ μ : M ≃ W, AGT.IsMaleOptimal PM PW μ := by
  obtain ⟨e⟩ := hcard
  obtain ⟨μ, -, -, hopt⟩ :=
    GaleShapley.exists_da_matching (n := Fintype.card M) hM hW rfl (Fintype.card_congr e).symm
  exact ⟨μ, hopt⟩

/-!
# The Blocking Lemma (Gale–Sotomayor)

Let `mu` be the male-optimal stable matching for strict profiles `PM`, `PW`, let `nu` be an
arbitrary matching, and let `R` be the set of men who strictly prefer `nu` to `mu`.  If `R`
is nonempty then `nu` is blocked by a pair `(m, nu m')` with `m' ∈ R` and `m ∉ R`.

The proof follows Gale–Sotomayor.  If some woman of `nu '' R` is not in `mu '' R`, her
`mu`-partner lies outside `R` and blocks `nu` with her, using only stability of `mu`.
Otherwise `nu '' R = mu '' R`, and the blocking pair is extracted from the
deferred-acceptance run producing `mu` — here the Kleene iteration of the monotone operator
`step` whose least fixed point is `mu` — by looking at the last stage at which a man of `R`
is rejected by a woman of `nu '' R`.
-/

namespace GaleShapley

open Finset

/-! ## Kleene iterates of a monotone map on a finite lattice -/

section Iterate

variable {α : Type*} [CompleteLattice α]

theorem iterate_bot_mono (f : α →o α) : Monotone fun k : ℕ => f^[k] (⊥ : α) := by
  refine monotone_nat_of_le_succ fun k => ?_
  induction k with
  | zero => simp
  | succ j ih =>
      have h1 : (⇑f)^[j + 1] (⊥ : α) = f ((⇑f)^[j] ⊥) := Function.iterate_succ_apply' f j ⊥
      have h2 : (⇑f)^[j + 2] (⊥ : α) = f ((⇑f)^[j + 1] ⊥) := Function.iterate_succ_apply' f (j + 1) ⊥
      rw [h1, h2]
      exact f.monotone ih

theorem iterate_bot_le_lfp (f : α →o α) (k : ℕ) : f^[k] ⊥ ≤ OrderHom.lfp f := by
  induction k with
  | zero => simp
  | succ j ih =>
      have h1 : (⇑f)^[j + 1] (⊥ : α) = f ((⇑f)^[j] ⊥) := Function.iterate_succ_apply' f j ⊥
      rw [h1]
      calc f ((⇑f)^[j] ⊥) ≤ f (OrderHom.lfp f) := f.monotone ih
        _ = OrderHom.lfp f := OrderHom.map_lfp f

theorem exists_iterate_eq_lfp [Finite α] (f : α →o α) :
    ∃ k : ℕ, f^[k] ⊥ = OrderHom.lfp f := by
  obtain ⟨i, j, hij, hEq⟩ : ∃ i j : ℕ, i ≠ j ∧ f^[i] (⊥ : α) = f^[j] ⊥ :=
    Finite.exists_ne_map_eq_of_infinite fun k : ℕ => f^[k] (⊥ : α)
  have key : ∀ i j : ℕ, i < j → f^[i] (⊥ : α) = f^[j] ⊥ → f^[i + 1] (⊥ : α) = f^[i] ⊥ := by
    intro i j hlt heq
    refine le_antisymm ?_ (iterate_bot_mono f (Nat.le_succ i))
    calc f^[i + 1] (⊥ : α) ≤ f^[j] ⊥ := iterate_bot_mono f hlt
      _ = f^[i] ⊥ := heq.symm
  have hstall : ∃ i : ℕ, f^[i + 1] (⊥ : α) = f^[i] ⊥ := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i, key i j h hEq⟩
    · exact ⟨j, key j i h hEq.symm⟩
  obtain ⟨i, hi⟩ := hstall
  refine ⟨i, le_antisymm (iterate_bot_le_lfp f i) ?_⟩
  refine OrderHom.lfp_le f (le_of_eq ?_)
  rw [← Function.iterate_succ_apply' f i, hi]

end Iterate

/-! ## The stages of the deferred-acceptance iteration -/

section Stages

variable {M W : Type*} [Fintype M] [Fintype W] {n : ℕ}
  {PM : M → W → W → Prop} {PW : W → M → M → Prop}

/-- The state of deferred acceptance after `k` rounds: the `k`-th Kleene iterate of `step`
started from the bottom element. -/
noncomputable def daIter (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) (k : ℕ) :
    (M → Fin (n + 1)) × (W → Fin (n + 1)) := (stepHom PM PW n)^[k] ⊥

theorem daIter_zero (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    daIter PM PW n 0 = ⊥ := rfl

theorem daIter_succ (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) :
    daIter PM PW n (k + 1) = step PM PW n (daIter PM PW n k) :=
  Function.iterate_succ_apply' (stepHom PM PW n) k ⊥

theorem daIter_mono (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    Monotone (daIter PM PW n) := iterate_bot_mono (stepHom PM PW n)

theorem daIter_le (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) :
    daIter PM PW n k ≤ (daA PM PW n, daB PM PW n) :=
  iterate_bot_le_lfp (stepHom PM PW n) k

theorem daIter_fst_le (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) (m : M) :
    (daIter PM PW n k).1 m ≤ daA PM PW n m := (daIter_le PM PW n k).1 m

theorem daIter_snd_le (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) (w : W) :
    (daIter PM PW n k).2 w ≤ daB PM PW n w := (daIter_le PM PW n k).2 w

theorem exists_daIter_eq (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ) :
    ∃ k : ℕ, daIter PM PW n k = (daA PM PW n, daB PM PW n) :=
  exists_iterate_eq_lfp (stepHom PM PW n)

theorem daIter_fst_succ (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) (m : M) :
    (daIter PM PW n (k + 1)).1 m =
      (univ.filter fun w => (daIter PM PW n k).2 w ≤ coF PW n w m).inf (rkF PM n m) := by
  rw [daIter_succ]
  rfl

theorem daIter_snd_succ (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n k : ℕ) (w : W) :
    (daIter PM PW n (k + 1)).2 w =
      (univ.filter fun m => rkF PM n m w ≤ (daIter PM PW n k).1 m).sup (coF PW n w) := by
  rw [daIter_succ]
  rfl

/-- The round at which woman `w` starts holding somebody she prefers to `m`. -/
noncomputable def daReject (PM : M → W → W → Prop) (PW : W → M → M → Prop) (n : ℕ)
    (m : M) (w : W) : ℕ := sInf {k | coF PW n w m < (daIter PM PW n k).2 w}

theorem daReject_spec {m : M} {w : W} (h : coF PW n w m < daB PM PW n w) :
    coF PW n w m < (daIter PM PW n (daReject PM PW n m w)).2 w := by
  obtain ⟨N, hN⟩ := exists_daIter_eq PM PW n
  have hNmem : coF PW n w m < (daIter PM PW n N).2 w := by rw [hN]; exact h
  have hne : {k | coF PW n w m < (daIter PM PW n k).2 w}.Nonempty := ⟨N, hNmem⟩
  exact Nat.sInf_mem hne

theorem le_of_lt_daReject {m : M} {w : W} {k : ℕ} (hk : k < daReject PM PW n m w) :
    (daIter PM PW n k).2 w ≤ coF PW n w m := by
  have := Nat.notMem_of_lt_sInf hk
  simpa [not_lt] using this

attribute [irreducible] daIter daReject

end Stages

/-! ## Uniqueness of the male-optimal stable matching -/

theorem male_optimal_unique {M W : Type*} {PM : M → W → W → Prop} {PW : W → M → M → Prop}
    (hM : AGT.IsPrefProfile PM) {mu mu' : M ≃ W}
    (h : AGT.IsMaleOptimal PM PW mu) (h' : AGT.IsMaleOptimal PM PW mu') : mu = mu' := by
  refine Equiv.ext fun m => ?_
  have := hM m
  rcases h.2 mu' h'.1 m with h1 | h1
  · exact h1
  · rcases h'.2 mu h.1 m with h2 | h2
    · exact h2.symm
    · exact absurd h2 (asymm_of (PM m) h1)

/-- If every woman matched by `nu` to a man of `R` is matched by `mu` to a man of `R`, then
the reverse inclusion holds as well, both sets having `R` as a common preimage. -/
theorem swap_image_of_subset {M W : Type*} [Fintype M] (R : M → Prop) (mu nu : M ≃ W)
    (h : ∀ m, R m → ∃ m₃, R m₃ ∧ mu m₃ = nu m) :
    ∀ m, R m → ∃ m₃, R m₃ ∧ nu m₃ = mu m := by
  classical
  intro m hm
  have hmemS : ∀ x : M, x ∈ univ.filter R ↔ R x := by
    intro x; simp
  have hsub : (univ.filter R).image nu ⊆ (univ.filter R).image mu := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hw
    obtain ⟨m₃, hm₃, h₃⟩ := h x ((hmemS x).1 hx)
    exact mem_image.2 ⟨m₃, (hmemS m₃).2 hm₃, h₃⟩
  have hcard : ((univ.filter R).image mu).card ≤ ((univ.filter R).image nu).card := by
    rw [card_image_of_injective _ mu.injective, card_image_of_injective _ nu.injective]
  have heq : (univ.filter R).image nu = (univ.filter R).image mu :=
    eq_of_subset_of_card_le hsub hcard
  have hmem : mu m ∈ (univ.filter R).image nu := by
    rw [heq]
    exact mem_image_of_mem mu ((hmemS m).2 hm)
  obtain ⟨m₃, hm₃, h₃⟩ := mem_image.1 hmem
  exact ⟨m₃, (hmemS m₃).1 hm₃, h₃⟩

/-! ## The two cases of the lemma -/

section Cases

variable {M W : Type*} [Fintype M] [Fintype W] {n : ℕ}
  {PM : M → W → W → Prop} {PW : W → M → M → Prop}

omit [Fintype M] [Fintype W] in
/-- Easy case: some woman matched by `nu` to a man of `R` is not matched by `mu` to a man
of `R`.  Her `mu`-partner is outside `R` and blocks `nu` with her. -/
theorem blocking_lemma_case1 (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (mu nu : M ≃ W) (hstable : AGT.IsStableMatching PM PW mu)
    (m' : M) (hm' : PM m' (nu m') (mu m'))
    (hout : ∀ m₃, PM m₃ (nu m₃) (mu m₃) → mu m₃ ≠ nu m') :
    ∃ m m' : M, PM m' (nu m') (mu m') ∧ ¬ PM m (nu m) (mu m) ∧
      AGT.IsBlockingPair PM PW nu m (nu m') := by
  classical
  have hmuw : mu (mu.symm (nu m')) = nu m' := mu.apply_symm_apply _
  have hRm : ¬ PM (mu.symm (nu m')) (nu (mu.symm (nu m'))) (mu (mu.symm (nu m'))) := by
    intro hR
    exact hout _ hR hmuw
  have hne : mu.symm (nu m') ≠ m' := by
    intro h
    rw [h] at hRm
    exact hRm hm'
  refine ⟨mu.symm (nu m'), m', hm', hRm, ?_, ?_⟩
  · have := hM (mu.symm (nu m'))
    rcases trichotomous_of (PM (mu.symm (nu m'))) (nu (mu.symm (nu m'))) (mu (mu.symm (nu m')))
      with h | h | h
    · exact absurd h hRm
    · exact absurd (nu.injective (by rw [h, hmuw])) hne
    · rwa [hmuw] at h
  · have hsym : nu.symm (nu m') = m' := nu.symm_apply_apply m'
    rw [hsym]
    have h2 : ¬ PW (nu m') m' (mu.symm (nu m')) := fun h2 => hstable m' (nu m') ⟨hm', h2⟩
    have := hW (nu m')
    rcases trichotomous_of (PW (nu m')) (mu.symm (nu m')) m' with h | h | h
    · exact h
    · exact absurd h hne
    · exact absurd h h2

/-- Hard case: every woman matched by `mu` to a man of `R` is matched by `nu` to a man of
`R`.  The blocking pair is read off the last stage of the deferred-acceptance iteration at
which a man of `R` is rejected by a woman of `nu '' R`. -/
theorem blocking_lemma_case2 (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (hnM : Fintype.card M = n) (hnW : Fintype.card W = n) (mu nu : M ≃ W)
    (ha : ∀ m, daA PM PW n m = rkF PM n m (mu m))
    (m₀ : M) (hm₀ : PM m₀ (nu m₀) (mu m₀))
    (hcase : ∀ m', PM m' (nu m') (mu m') → ∃ m₃, PM m₃ (nu m₃) (mu m₃) ∧ nu m₃ = mu m') :
    ∃ m m' : M, PM m' (nu m') (mu m') ∧ ¬ PM m (nu m) (mu m) ∧
      AGT.IsBlockingPair PM PW nu m (nu m') := by
  classical
  have hfix : step PM PW n (daA PM PW n, daB PM PW n) = (daA PM PW n, daB PM PW n) :=
    da_fix PM PW n
  -- a man is rejected, at the limit, by every woman he ranks above his own partner
  have hrej : ∀ (m : M) (w : W), rkF PM n m w < daA PM PW n m → coF PW n w m < daB PM PW n w := by
    intro m w h
    by_contra hcon
    rw [not_lt] at hcon
    exact absurd (inf_le_of_fixed hfix hcon) (not_le.2 h)
  -- the rejection events of men of `R` by women of `nu '' R`
  set E : Finset (M × W) :=
    univ.filter (fun p : M × W => PM p.1 (nu p.1) (mu p.1) ∧
      (∃ m₃, PM m₃ (nu m₃) (mu m₃) ∧ nu m₃ = p.2) ∧ rkF PM n p.1 p.2 < daA PM PW n p.1) with hEdef
  have hEmem : ∀ p : M × W, p ∈ E ↔ (PM p.1 (nu p.1) (mu p.1) ∧
      (∃ m₃, PM m₃ (nu m₃) (mu m₃) ∧ nu m₃ = p.2) ∧ rkF PM n p.1 p.2 < daA PM PW n p.1) := by
    intro p
    rw [hEdef, mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ p, h⟩⟩
  have hEne : E.Nonempty := by
    refine ⟨(m₀, nu m₀), (hEmem _).2 ⟨hm₀, ⟨m₀, hm₀, rfl⟩, ?_⟩⟩
    rw [ha m₀]
    exact (rkF_lt_iff hM hnW m₀ (nu m₀) (mu m₀)).2 hm₀
  obtain ⟨p₁, hp₁E, hp₁sup⟩ :=
    Finset.exists_mem_eq_sup E hEne (fun p : M × W => daReject PM PW n p.1 p.2)
  obtain ⟨m₁, w₁⟩ := p₁
  obtain ⟨hRm₁, -, hrk₁⟩ := (hEmem (m₁, w₁)).1 hp₁E
  simp only at hRm₁ hrk₁ hp₁sup
  -- up to the last stage, `m₁` still aspires to `w₁` or better
  have hasp : ∀ k, k ≤ E.sup (fun p : M × W => daReject PM PW n p.1 p.2) →
      (daIter PM PW n k).1 m₁ ≤ rkF PM n m₁ w₁ := by
    intro k hk
    match k with
    | 0 =>
        rw [daIter_zero]
        exact bot_le
    | (j + 1) =>
        have hj : j < daReject PM PW n m₁ w₁ := by
          rw [hp₁sup] at hk
          omega
        rw [daIter_fst_succ]
        refine Finset.inf_le ?_
        simp only [mem_filter, mem_univ, true_and]
        exact le_of_lt_daReject hj
  -- he strictly prefers `w₁` to his own partner, so he never aspires to her before the end
  have hw₁w₂ : rkF PM n m₁ w₁ < rkF PM n m₁ (mu m₁) := by
    rw [← ha m₁]
    exact hrk₁
  have hnotm₁ : ∀ k, k ≤ E.sup (fun p : M × W => daReject PM PW n p.1 p.2) →
      ¬ rkF PM n m₁ (mu m₁) ≤ (daIter PM PW n k).1 m₁ := by
    intro k hk hle
    exact absurd (lt_of_le_of_lt (le_trans hle (hasp k hk)) hw₁w₂) (lt_irrefl _)
  -- his partner is matched by `nu` to a man `m₃` of `R`
  obtain ⟨m₃, hRm₃, hm₃⟩ := hcase m₁ hRm₁
  have hrk₃ : rkF PM n m₃ (mu m₁) < daA PM PW n m₃ := by
    rw [ha m₃, ← hm₃]
    exact (rkF_lt_iff hM hnW m₃ (nu m₃) (mu m₃)).2 hRm₃
  have hT₃ : daReject PM PW n m₃ (mu m₁) ≤ E.sup (fun p : M × W => daReject PM PW n p.1 p.2) :=
    Finset.le_sup (f := fun p : M × W => daReject PM PW n p.1 p.2)
      ((hEmem (m₃, mu m₁)).2 ⟨hRm₃, ⟨m₃, hRm₃, hm₃⟩, hrk₃⟩)
  -- so by the next stage she holds somebody she prefers to `m₃`
  have hrej₃ : coF PW n (mu m₁) m₃ <
      (daIter PM PW n (E.sup (fun p : M × W => daReject PM PW n p.1 p.2) + 1)).2 (mu m₁) := by
    have h1 := daReject_spec (PM := PM) (PW := PW) (n := n) (hrej m₃ (mu m₁) hrk₃)
    exact lt_of_lt_of_le h1
      ((daIter_mono PM PW n (le_trans hT₃ (Nat.le_succ _))).2 (mu m₁))
  -- the man she is holding then
  have hfilter : (univ.filter fun m => rkF PM n m (mu m₁) ≤
      (daIter PM PW n (E.sup (fun p : M × W => daReject PM PW n p.1 p.2))).1 m).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (univ.filter fun m => rkF PM n m (mu m₁) ≤
      (daIter PM PW n (E.sup (fun p : M × W => daReject PM PW n p.1 p.2))).1 m) with he | hne
    · exfalso
      rw [daIter_snd_succ, he, Finset.sup_empty] at hrej₃
      exact absurd hrej₃ (not_lt.2 bot_le)
    · exact hne
  obtain ⟨m₆, hm₆mem, hm₆sup⟩ := Finset.exists_mem_eq_sup _ hfilter (coF PW n (mu m₁))
  simp only [mem_filter, mem_univ, true_and] at hm₆mem
  have hm₆val : (daIter PM PW n (E.sup (fun p : M × W => daReject PM PW n p.1 p.2) + 1)).2 (mu m₁)
      = coF PW n (mu m₁) m₆ := by
    rw [daIter_snd_succ, hm₆sup]
  have hm₆ne : m₆ ≠ m₁ := by
    rintro rfl
    exact hnotm₁ _ le_rfl hm₆mem
  have hm₆rk : rkF PM n m₆ (mu m₁) < daA PM PW n m₆ := by
    rcases lt_or_eq_of_le (le_trans hm₆mem (daIter_fst_le PM PW n _ m₆)) with h | h
    · exact h
    · exfalso
      refine hm₆ne (mu.injective (rkF_inj hM hnW m₆ ?_))
      rw [← ha m₆, ← h]
  -- he is outside `R`, else she would reject him after the last stage
  have hm₆R : ¬ PM m₆ (nu m₆) (mu m₆) := by
    intro hR
    have hT₆ : daReject PM PW n m₆ (mu m₁) ≤
        E.sup (fun p : M × W => daReject PM PW n p.1 p.2) :=
      Finset.le_sup (f := fun p : M × W => daReject PM PW n p.1 p.2)
        ((hEmem (m₆, mu m₁)).2 ⟨hR, ⟨m₃, hRm₃, hm₃⟩, hm₆rk⟩)
    have h1 := daReject_spec (PM := PM) (PW := PW) (n := n) (hrej m₆ (mu m₁) hm₆rk)
    have h2 := (daIter_mono PM PW n (le_trans hT₆ (Nat.le_succ _))).2 (mu m₁)
    rw [hm₆val] at h2
    exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
  -- and he blocks `nu` with her
  refine ⟨m₆, m₃, hRm₃, hm₆R, ?_, ?_⟩
  · rw [hm₃]
    refine (rkF_lt_iff hM hnW m₆ (mu m₁) (nu m₆)).1 ?_
    have hge : rkF PM n m₆ (mu m₆) ≤ rkF PM n m₆ (nu m₆) := by
      have := hM m₆
      rcases trichotomous_of (PM m₆) (nu m₆) (mu m₆) with h | h | h
      · exact absurd h hm₆R
      · rw [h]
      · exact le_of_lt ((rkF_lt_iff hM hnW m₆ (mu m₆) (nu m₆)).2 h)
    have hlt := hm₆rk
    rw [ha m₆] at hlt
    exact lt_of_lt_of_le hlt hge
  · rw [nu.symm_apply_apply, hm₃]
    refine (coF_lt_iff hW hnM (mu m₁) m₃ m₆).1 ?_
    rw [← hm₆val]
    exact hrej₃

end Cases

/-! ## The Blocking Lemma -/

theorem blocking_lemma {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (mu nu : M ≃ W) (hmu : AGT.IsMaleOptimal PM PW mu)
    (m₀ : M) (hm₀ : PM m₀ (nu m₀) (mu m₀)) :
    ∃ m m' : M, PM m' (nu m') (mu m') ∧ ¬ PM m (nu m) (mu m) ∧
      AGT.IsBlockingPair PM PW nu m (nu m') := by
  classical
  obtain ⟨mu', ha, -, hopt⟩ :=
    exists_da_matching (n := Fintype.card M) hM hW rfl (Fintype.card_congr mu).symm
  have hmm : mu = mu' := male_optimal_unique hM hmu hopt
  subst hmm
  by_cases hc : ∀ m, PM m (nu m) (mu m) → ∃ m₃, PM m₃ (nu m₃) (mu m₃) ∧ mu m₃ = nu m
  · exact blocking_lemma_case2 hM hW rfl (Fintype.card_congr mu).symm mu nu ha m₀ hm₀
      (swap_image_of_subset (fun m => PM m (nu m) (mu m)) mu nu hc)
  · push_neg at hc
    obtain ⟨m', hm', hout⟩ := hc
    exact blocking_lemma_case1 hM hW mu nu hmu.1 m' hm' hout

end GaleShapley


/-- The Blocking Lemma of Gale–Sotomayor. -/
theorem solution {M W : Type*} [Fintype M] [Fintype W]
    (PM : M → W → W → Prop) (PW : W → M → M → Prop)
    (hM : AGT.IsPrefProfile PM) (hW : AGT.IsPrefProfile PW)
    (mu nu : M ≃ W) (hmu : AGT.IsMaleOptimal PM PW mu)
    (m₀ : M) (hm₀ : PM m₀ (nu m₀) (mu m₀)) :
    ∃ m m' : M, PM m' (nu m') (mu m') ∧ ¬ PM m (nu m) (mu m) ∧
      AGT.IsBlockingPair PM PW nu m (nu m') :=
  GaleShapley.blocking_lemma PM PW hM hW mu nu hmu m₀ hm₀

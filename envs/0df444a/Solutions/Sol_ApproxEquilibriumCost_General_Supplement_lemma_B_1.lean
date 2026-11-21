-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:33.930363+00:00
-- url     : https://prove2.me/submissions/681cfd42-13ed-418e-9f11-f2b78ddb5057

import Mathlib
import Definitions.Def_ApproxEquilibriumCost_General_FlowCosts
import Definitions.Def_ApproxEquilibriumCost_General_Supplement_RoutingGame

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.SP
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement

set_option allowUnsafeReducibility true in
attribute [local reducible] edgeCount

def comb {a b : ℕ} (P : Finset (Fin a)) (Q : Finset (Fin b)) : Finset (Fin (a + b)) :=
  P.image (Fin.castAdd b) ∪ Q.image (Fin.natAdd a)

def loads (N : SPNetwork) (φ : Finset (Fin (edgeCount N)) → ℝ) (e : Fin (edgeCount N)) : ℝ :=
  ∑ S ∈ paths N, if e ∈ S then φ S else 0

def tot (N : SPNetwork) (φ : Finset (Fin (edgeCount N)) → ℝ) : ℝ := ∑ S ∈ paths N, φ S

def plat {m : ℕ} (l : Fin m → ℝ → ℝ) (x : Fin m → ℝ) (S : Finset (Fin m)) : ℝ :=
  ∑ e ∈ S, l e (x e)

def Nonneg (N : SPNetwork) (φ : Finset (Fin (edgeCount N)) → ℝ) : Prop :=
  ∀ S ∈ paths N, 0 ≤ φ S

def PNash (N : SPNetwork) (l : Fin (edgeCount N) → ℝ → ℝ)
    (φ : Finset (Fin (edgeCount N)) → ℝ) : Prop :=
  Nonneg N φ ∧ ∀ S ∈ paths N, 0 < φ S → ∀ S' ∈ paths N,
    plat l (loads N φ) S ≤ plat l (loads N φ) S'

def margA (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (P : Finset (Fin (edgeCount A))) : ℝ := ∑ Q ∈ paths B, φ (comb P Q)

def margB (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (Q : Finset (Fin (edgeCount B))) : ℝ := ∑ P ∈ paths A, φ (comb P Q)

def splA (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (P : Finset (Fin (edgeCount A))) : ℝ := φ (P.image (Fin.castAdd (edgeCount B)))

def splB (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (Q : Finset (Fin (edgeCount B))) : ℝ := φ (Q.image (Fin.natAdd (edgeCount A)))

theorem paths_series_eq (A B : SPNetwork) : paths (.series A B) =
    (paths A).biUnion fun P => (paths B).image fun Q => comb P Q := rfl

theorem paths_par_eq (A B : SPNetwork) : paths (.par A B) =
    ((paths A).image fun P => P.image (Fin.castAdd (edgeCount B))) ∪
      ((paths B).image fun Q => Q.image (Fin.natAdd (edgeCount A))) := rfl

theorem mem_paths_nonempty (N : SPNetwork) : ∀ S ∈ paths N, S.Nonempty := by
  induction N with
  | arc => intro S hS; simp [paths] at hS; subst hS; simp
  | series A B ihA ihB =>
    intro S hS
    rw [paths_series_eq] at hS
    simp only [Finset.mem_biUnion, Finset.mem_image] at hS
    obtain ⟨P, hP, Q, hQ, rfl⟩ := hS
    obtain ⟨e, he⟩ := ihA P hP
    exact ⟨Fin.castAdd _ e, Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)⟩
  | par A B ihA ihB =>
    intro S hS
    rw [paths_par_eq] at hS
    simp only [Finset.mem_union, Finset.mem_image] at hS
    rcases hS with ⟨P, hP, rfl⟩ | ⟨Q, hQ, rfl⟩
    · obtain ⟨e, he⟩ := ihA P hP
      exact ⟨Fin.castAdd _ e, by simp [he]⟩
    · obtain ⟨e, he⟩ := ihB Q hQ
      exact ⟨Fin.natAdd _ e, by simp [he]⟩

theorem castAdd_ne_natAdd {a b : ℕ} (e : Fin a) (f : Fin b) :
    Fin.castAdd b e ≠ Fin.natAdd a f := by
  intro h; have := congrArg Fin.val h; simp at this; omega

theorem mem_comb_castAdd {a b : ℕ} (P : Finset (Fin a)) (Q : Finset (Fin b)) (e : Fin a) :
    Fin.castAdd b e ∈ comb P Q ↔ e ∈ P := by
  have h1 := e.isLt
  simp only [comb, Finset.mem_union, Finset.mem_image, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨x, _, h⟩)
    · have : x = e := Fin.ext h
      subst this; exact hx
    · exfalso; omega
  · intro h; exact Or.inl ⟨e, h, rfl⟩

theorem mem_comb_natAdd {a b : ℕ} (P : Finset (Fin a)) (Q : Finset (Fin b)) (e : Fin b) :
    Fin.natAdd a e ∈ comb P Q ↔ e ∈ Q := by
  have h1 := e.isLt
  simp only [comb, Finset.mem_union, Finset.mem_image, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
  constructor
  · rintro (⟨x, hx, h⟩ | ⟨x, hx, h⟩)
    · exfalso; have := x.isLt; omega
    · have : x = e := Fin.ext (by omega)
      subst this; exact hx
  · intro h; exact Or.inr ⟨e, h, rfl⟩

theorem comb_inj {a b : ℕ} {P P' : Finset (Fin a)} {Q Q' : Finset (Fin b)}
    (h : comb P Q = comb P' Q') : P = P' ∧ Q = Q' := by
  constructor
  · ext e
    have := congrArg (fun S => Fin.castAdd b e ∈ S) h
    simpa [mem_comb_castAdd] using this
  · ext e
    have := congrArg (fun S => Fin.natAdd a e ∈ S) h
    simpa [mem_comb_natAdd] using this

theorem paths_series (A B : SPNetwork) :
    paths (.series A B) = (paths A ×ˢ paths B).image (fun pq => comb pq.1 pq.2) := by
  ext S
  rw [paths_series_eq]
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨P, hP, Q, hQ, rfl⟩; exact ⟨(P, Q), ⟨hP, hQ⟩, rfl⟩
  · rintro ⟨⟨P, Q⟩, ⟨hP, hQ⟩, rfl⟩; exact ⟨P, hP, Q, hQ, rfl⟩

theorem comb_mem (A B : SPNetwork) {P Q} (hP : P ∈ paths A) (hQ : Q ∈ paths B) :
    comb P Q ∈ paths (.series A B) := by
  rw [paths_series]; exact Finset.mem_image.2 ⟨(P, Q), Finset.mem_product.2 ⟨hP, hQ⟩, rfl⟩

theorem mem_paths_series (A B : SPNetwork) {S} (hS : S ∈ paths (.series A B)) :
    ∃ P ∈ paths A, ∃ Q ∈ paths B, S = comb P Q := by
  rw [paths_series] at hS
  obtain ⟨⟨P, Q⟩, hm, rfl⟩ := Finset.mem_image.1 hS
  exact ⟨P, (Finset.mem_product.1 hm).1, Q, (Finset.mem_product.1 hm).2, rfl⟩

theorem sum_paths_series (A B : SPNetwork) (g : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    ∑ S ∈ paths (.series A B), g S = ∑ P ∈ paths A, ∑ Q ∈ paths B, g (comb P Q) := by
  rw [paths_series, Finset.sum_image, Finset.sum_product]
  intro x _ y _ h
  have := comb_inj h
  exact Prod.ext this.1 this.2

theorem sum_paths_series' (A B : SPNetwork) (g : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    ∑ S ∈ paths (.series A B), g S = ∑ Q ∈ paths B, ∑ P ∈ paths A, g (comb P Q) := by
  rw [sum_paths_series, Finset.sum_comm]

theorem loads_series_left (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (e : Fin (edgeCount A)) :
    loads (.series A B) φ (Fin.castAdd _ e) = loads A (margA A B φ) e := by
  unfold loads
  rw [sum_paths_series]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [mem_comb_castAdd, margA]
  split_ifs <;> simp

theorem loads_series_right (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (e : Fin (edgeCount B)) :
    loads (.series A B) φ (Fin.natAdd _ e) = loads B (margB A B φ) e := by
  unfold loads
  rw [sum_paths_series']
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [mem_comb_natAdd, margB]
  split_ifs <;> simp

theorem tot_series_left (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    tot (.series A B) φ = tot A (margA A B φ) := by
  unfold tot margA; rw [sum_paths_series]

theorem tot_series_right (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    tot (.series A B) φ = tot B (margB A B φ) := by
  unfold tot margB; rw [sum_paths_series']

theorem plat_comb {a b : ℕ} (l : Fin (a + b) → ℝ → ℝ) (x : Fin (a + b) → ℝ)
    (P : Finset (Fin a)) (Q : Finset (Fin b)) :
    plat l x (comb P Q) = plat (fun e => l (Fin.castAdd b e)) (fun e => x (Fin.castAdd b e)) P
      + plat (fun e => l (Fin.natAdd a e)) (fun e => x (Fin.natAdd a e)) Q := by
  unfold plat comb
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro x _ y _ h; exact Fin.natAdd_injective _ _ h
  · intro x _ y _ h; exact Fin.castAdd_injective _ _ h
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨x1, _, rfl⟩ := h1
    obtain ⟨x2, _, h⟩ := h2
    exact castAdd_ne_natAdd _ _ h.symm

theorem plat_series_comb (A B : SPNetwork) (l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ)
    (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (P : Finset (Fin (edgeCount A))) (Q : Finset (Fin (edgeCount B))) :
    plat l (loads (.series A B) φ) (comb P Q) =
      plat (fun e => l (Fin.castAdd _ e)) (loads A (margA A B φ)) P
      + plat (fun e => l (Fin.natAdd _ e)) (loads B (margB A B φ)) Q := by
  rw [plat_comb]
  congr 2
  · funext e; exact loads_series_left A B φ e
  · funext e; exact loads_series_right A B φ e

theorem nonneg_margA (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) : Nonneg A (margA A B φ) := by
  intro P hP
  exact Finset.sum_nonneg fun Q hQ => h _ (comb_mem A B hP hQ)

theorem nonneg_margB (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) : Nonneg B (margB A B φ) := by
  intro Q hQ
  exact Finset.sum_nonneg fun P hP => h _ (comb_mem A B hP hQ)

theorem exists_pos_margA (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) {P} (hP : 0 < margA A B φ P) :
    ∃ Q ∈ paths B, 0 < φ (comb P Q) := by
  by_contra hc
  push Not at hc
  exact absurd hP (not_lt.2 (Finset.sum_nonpos hc))

theorem exists_pos_margB (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) {Q} (hQ : 0 < margB A B φ Q) :
    ∃ P ∈ paths A, 0 < φ (comb P Q) := by
  by_contra hc
  push Not at hc
  exact absurd hQ (not_lt.2 (Finset.sum_nonpos hc))

theorem pos_margA (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) {P Q} (hP : P ∈ paths A) (hQ : Q ∈ paths B)
    (hpos : 0 < φ (comb P Q)) : 0 < margA A B φ P :=
  lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun Q => φ (comb P Q))
    (fun Q hQ => h _ (comb_mem A B hP hQ)) hQ)

theorem pos_margB (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.series A B) φ) {P Q} (hP : P ∈ paths A) (hQ : Q ∈ paths B)
    (hpos : 0 < φ (comb P Q)) : 0 < margB A B φ Q :=
  lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun P => φ (comb P Q))
    (fun P hP => h _ (comb_mem A B hP hQ)) hP)

theorem pnash_margA (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.series A B) l φ) :
    PNash A (fun e => l (Fin.castAdd _ e)) (margA A B φ) := by
  refine ⟨nonneg_margA A B h.1, fun P hP hpos P' hP' => ?_⟩
  obtain ⟨Q, hQ, hφ⟩ := exists_pos_margA A B h.1 hpos
  have := h.2 _ (comb_mem A B hP hQ) hφ _ (comb_mem A B hP' hQ)
  rw [plat_series_comb, plat_series_comb] at this
  linarith

theorem pnash_margB (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.series A B) l φ) :
    PNash B (fun e => l (Fin.natAdd _ e)) (margB A B φ) := by
  refine ⟨nonneg_margB A B h.1, fun Q hQ hpos Q' hQ' => ?_⟩
  obtain ⟨P, hP, hφ⟩ := exists_pos_margB A B h.1 hpos
  have := h.2 _ (comb_mem A B hP hQ) hφ _ (comb_mem A B hP hQ')
  rw [plat_series_comb, plat_series_comb] at this
  linarith

/-! Parallel -/

theorem imageA_mem (A B : SPNetwork) {P} (hP : P ∈ paths A) :
    P.image (Fin.castAdd (edgeCount B)) ∈ paths (.par A B) := by
  rw [paths_par_eq]; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl ⟨P, hP, rfl⟩

theorem imageB_mem (A B : SPNetwork) {Q} (hQ : Q ∈ paths B) :
    Q.image (Fin.natAdd (edgeCount A)) ∈ paths (.par A B) := by
  rw [paths_par_eq]; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inr ⟨Q, hQ, rfl⟩

theorem sum_paths_par (A B : SPNetwork) (g : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    ∑ S ∈ paths (.par A B), g S =
      ∑ P ∈ paths A, g (P.image (Fin.castAdd (edgeCount B)))
      + ∑ Q ∈ paths B, g (Q.image (Fin.natAdd (edgeCount A))) := by
  rw [paths_par_eq]
  rw [Finset.sum_union, Finset.sum_image, Finset.sum_image]
  · intro x _ y _ h
    exact Finset.image_injective (Fin.natAdd_injective _ _) h
  · intro x _ y _ h
    exact Finset.image_injective (Fin.castAdd_injective _ _) h
  · rw [Finset.disjoint_left]
    intro S h1 h2
    simp only [Finset.mem_image] at h1 h2
    obtain ⟨P, hP, rfl⟩ := h1
    obtain ⟨Q, hQ, h⟩ := h2
    obtain ⟨e, he⟩ := mem_paths_nonempty A P hP
    have : Fin.castAdd _ e ∈ Q.image (Fin.natAdd (edgeCount A)) := by
      rw [h]; exact Finset.mem_image_of_mem _ he
    simp only [Finset.mem_image] at this
    obtain ⟨y, _, hy⟩ := this
    exact castAdd_ne_natAdd _ _ hy.symm

theorem loads_par_left (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (e : Fin (edgeCount A)) :
    loads (.par A B) φ (Fin.castAdd _ e) = loads A (splA A B φ) e := by
  unfold loads
  rw [sum_paths_par]
  have h2 : ∀ Q ∈ paths B, (if Fin.castAdd (edgeCount B) e ∈ Q.image (Fin.natAdd (edgeCount A))
      then φ (Q.image (Fin.natAdd (edgeCount A))) else 0) = 0 := by
    intro Q _
    rw [if_neg]
    simp only [Finset.mem_image, not_exists, not_and]
    intro y _ hy; exact castAdd_ne_natAdd _ _ hy.symm
  rw [Finset.sum_eq_zero h2, add_zero]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [splA, (Fin.castAdd_injective _ _).mem_finset_image]

theorem loads_par_right (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ)
    (e : Fin (edgeCount B)) :
    loads (.par A B) φ (Fin.natAdd _ e) = loads B (splB A B φ) e := by
  unfold loads
  rw [sum_paths_par]
  have h2 : ∀ P ∈ paths A, (if Fin.natAdd (edgeCount A) e ∈ P.image (Fin.castAdd (edgeCount B))
      then φ (P.image (Fin.castAdd (edgeCount B))) else 0) = 0 := by
    intro P _
    rw [if_neg]
    simp only [Finset.mem_image, not_exists, not_and]
    intro y _ hy; exact castAdd_ne_natAdd _ _ hy
  rw [Finset.sum_eq_zero h2, zero_add]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [splB, (Fin.natAdd_injective _ _).mem_finset_image]

theorem tot_par (A B : SPNetwork) (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) :
    tot (.par A B) φ = tot A (splA A B φ) + tot B (splB A B φ) := by
  unfold tot splA splB; rw [sum_paths_par]

theorem plat_par_left (A B : SPNetwork) (l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ)
    (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) (P : Finset (Fin (edgeCount A))) :
    plat l (loads (.par A B) φ) (P.image (Fin.castAdd (edgeCount B))) =
      plat (fun e => l (Fin.castAdd _ e)) (loads A (splA A B φ)) P := by
  unfold plat
  rw [Finset.sum_image (fun x _ y _ h => Fin.castAdd_injective _ _ h)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [loads_par_left]

theorem plat_par_right (A B : SPNetwork) (l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ)
    (φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) (Q : Finset (Fin (edgeCount B))) :
    plat l (loads (.par A B) φ) (Q.image (Fin.natAdd (edgeCount A))) =
      plat (fun e => l (Fin.natAdd _ e)) (loads B (splB A B φ)) Q := by
  unfold plat
  rw [Finset.sum_image (fun x _ y _ h => Fin.natAdd_injective _ _ h)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [loads_par_right]

theorem nonneg_splA (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.par A B) φ) : Nonneg A (splA A B φ) :=
  fun P hP => h _ (imageA_mem A B hP)

theorem nonneg_splB (A B : SPNetwork) {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ}
    (h : Nonneg (.par A B) φ) : Nonneg B (splB A B φ) :=
  fun Q hQ => h _ (imageB_mem A B hQ)

theorem pnash_splA (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.par A B) l φ) :
    PNash A (fun e => l (Fin.castAdd _ e)) (splA A B φ) := by
  refine ⟨nonneg_splA A B h.1, fun P hP hpos P' hP' => ?_⟩
  have := h.2 _ (imageA_mem A B hP) hpos _ (imageA_mem A B hP')
  rwa [plat_par_left, plat_par_left] at this

theorem pnash_splB (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.par A B) l φ) :
    PNash B (fun e => l (Fin.natAdd _ e)) (splB A B φ) := by
  refine ⟨nonneg_splB A B h.1, fun Q hQ hpos Q' hQ' => ?_⟩
  have := h.2 _ (imageB_mem A B hQ) hpos _ (imageB_mem A B hQ')
  rwa [plat_par_right, plat_par_right] at this

theorem exists_pos_of_tot (N : SPNetwork) {φ : Finset (Fin (edgeCount N)) → ℝ}
    (h : 0 < tot N φ) : ∃ S ∈ paths N, 0 < φ S := by
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.2 (Finset.sum_nonpos hc))

theorem tot_nonneg (N : SPNetwork) {φ : Finset (Fin (edgeCount N)) → ℝ}
    (h : Nonneg N φ) : 0 ≤ tot N φ := Finset.sum_nonneg h

/-! Arc -/

theorem paths_arc : paths .arc = {{⟨0, by decide⟩}} := rfl

theorem loads_arc (φ : Finset (Fin (edgeCount .arc)) → ℝ) (e : Fin (edgeCount .arc)) :
    loads .arc φ e = φ {⟨0, by decide⟩} := by
  have : e = ⟨0, by decide⟩ := Subsingleton.elim _ _
  subst this
  simp [loads, paths_arc]

theorem tot_arc (φ : Finset (Fin (edgeCount .arc)) → ℝ) :
    tot .arc φ = φ {⟨0, by decide⟩} := by
  simp [tot, paths_arc]

theorem plat_arc (l : Fin (edgeCount .arc) → ℝ → ℝ) (x : Fin (edgeCount .arc) → ℝ) :
    plat l x {⟨0, by decide⟩} = l ⟨0, by decide⟩ (x ⟨0, by decide⟩) := by
  simp [plat]

theorem mem_paths_arc {S : Finset (Fin (edgeCount .arc))} (h : S ∈ paths .arc) :
    S = {⟨0, by decide⟩} := by
  simpa [paths_arc] using h

/-! Reduction from the game model to path flows -/

noncomputable def idx {n : ℕ} (G : Game n 1) (s : StrategyIndex G) : Fin (routeCount G) :=
  Fintype.equivFin (StrategyIndex G) s

theorem route_idx {n : ℕ} (G : Game n 1) (s : StrategyIndex G) : route G (idx G s) = s := by
  unfold route idx; rw [Equiv.symm_apply_apply]

theorem idx_route {n : ℕ} (G : Game n 1) (r : Fin (routeCount G)) : idx G (route G r) = r := by
  unfold route idx; exact Equiv.apply_symm_apply _ _

noncomputable def pf {n : ℕ} (G : Game n 1) (f : Flow G) (S : Finset (Fin n)) : ℝ :=
  if h : S ∈ G.strategies 0 then f (idx G ⟨0, ⟨S, h⟩⟩) else 0

theorem route_mem0 {n : ℕ} (G : Game n 1) (r : Fin (routeCount G)) :
    (route G r).2.val ∈ G.strategies 0 := by
  obtain ⟨i, S, hS⟩ := route G r
  have : i = 0 := Subsingleton.elim _ _
  subst this; exact hS

theorem sidx_eq {n : ℕ} (G : Game n 1) (s : StrategyIndex G) (hm : s.2.val ∈ G.strategies 0) :
    s = ⟨0, ⟨s.2.val, hm⟩⟩ := by
  obtain ⟨i, S, hS⟩ := s
  have : i = 0 := Subsingleton.elim _ _
  subst this; rfl

theorem pf_route {n : ℕ} (G : Game n 1) (f : Flow G) (r : Fin (routeCount G)) :
    pf G f (route G r).2.val = f r := by
  unfold pf
  rw [dif_pos (route_mem0 G r)]
  congr 1
  rw [← sidx_eq G (route G r) (route_mem0 G r)]
  exact idx_route G r

theorem exists_route {n : ℕ} (G : Game n 1) {S : Finset (Fin n)} (h : S ∈ G.strategies 0) :
    ∃ r : Fin (routeCount G), (route G r).2.val = S :=
  ⟨idx G ⟨0, ⟨S, h⟩⟩, by rw [route_idx]⟩

theorem sum_route {n : ℕ} (G : Game n 1) (g : Finset (Fin n) → ℝ) :
    ∑ r : Fin (routeCount G), g (route G r).2.val = ∑ S ∈ G.strategies 0, g S := by
  have h1 : ∑ r : Fin (routeCount G), g (route G r).2.val
      = ∑ s : StrategyIndex G, g s.2.val :=
    Equiv.sum_comp (Fintype.equivFin (StrategyIndex G)).symm (fun s : StrategyIndex G => g s.2.val)
  rw [h1, Fintype.sum_sigma, Fintype.sum_unique]
  exact Finset.sum_coe_sort (G.strategies default) g

theorem load_eq {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) (e : Fin (edgeCount N)) :
    load G f e = loads N (pf G f) e := by
  have h1 : load G f e = ∑ r : Fin (routeCount G),
      (fun S => if e ∈ S then pf G f S else 0) (route G r).2.val := by
    unfold load KellyStochasticNetworks.linkFlow
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [incidence, pf_route]
    split_ifs <;> simp
  have h2 := sum_route G (fun S => if e ∈ S then pf G f S else 0)
  rw [h1]
  refine h2.trans ?_
  unfold IsRoutingGame at hG
  rw [hG]; rfl

theorem route_mem {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (r : Fin (routeCount G)) : (route G r).2.val ∈ paths N := by
  have := route_mem0 G r
  unfold IsRoutingGame at hG
  rwa [hG] at this

theorem strategyLatency_eq {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) (r : Fin (routeCount G)) :
    strategyLatency G f r = plat G.latency (loads N (pf G f)) (route G r).2.val := by
  unfold strategyLatency plat
  simp only [incidence, load_eq G hG, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem]
  simp

theorem feas_facts {n : ℕ} (G : Game n 1) {f : Flow G} (h : IsFeasible G f) :
    (∀ r, 0 ≤ f r) ∧ ∑ r, f r = G.demand 0 := by
  refine ⟨h.1, ?_⟩
  have := h.2 0
  rwa [Finset.filter_true_of_mem (fun r _ => Subsingleton.elim _ _)] at this

theorem nonneg_pf {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) (hf : ∀ r, 0 ≤ f r) : Nonneg N (pf G f) := by
  intro S hS
  unfold pf
  split_ifs with h
  · exact hf _
  · exact le_rfl

theorem tot_pf {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) : tot N (pf G f) = ∑ r, f r := by
  unfold tot
  have : paths N = G.strategies 0 := hG.symm
  rw [this, ← sum_route]
  exact Finset.sum_congr rfl fun r _ => pf_route G f r

theorem pf_pos {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) {S : Finset (Fin (edgeCount N))} (h : 0 < pf G f S) :
    ∃ r, (route G r).2.val = S ∧ 0 < f r := by
  have hS : S ∈ G.strategies 0 := by
    by_contra hc; unfold pf at h; rw [dif_neg hc] at h; exact lt_irrefl _ h
  obtain ⟨r, hr⟩ := exists_route G hS
  refine ⟨r, hr, ?_⟩
  rw [← pf_route G f r, hr]; exact h

theorem pos_pf {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    (f : Flow G) {r : Fin (routeCount G)} (h : 0 < f r) : 0 < pf G f (route G r).2.val := by
  rw [pf_route]; exact h

theorem exists_route_paths {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    {S : Finset (Fin (edgeCount N))} (h : S ∈ paths N) :
    ∃ r : Fin (routeCount G), (route G r).2.val = S := by
  apply exists_route
  unfold IsRoutingGame at hG; rwa [hG]

theorem pnash_of_nash {N : SPNetwork} (G : Game (edgeCount N) 1) (hG : IsRoutingGame N G)
    {f : Flow G} (hf : IsNash G f) : PNash N G.latency (pf G f) := by
  refine ⟨nonneg_pf G hG f (feas_facts G hf.1).1, fun S hS hpos S' hS' => ?_⟩
  obtain ⟨r, hr, hfr⟩ := pf_pos G hG f hpos
  obtain ⟨r', hr'⟩ := exists_route_paths G hG hS'
  have := hf.2 r r' (Subsingleton.elim _ _) hfr
  have h2 : strategyLatency G f r ≤ strategyLatency G f r' := this
  rw [strategyLatency_eq G hG, strategyLatency_eq G hG, hr, hr'] at h2
  exact h2

end ApproxEquilibriumCost.Dev.SP
end

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.B1
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement ApproxEquilibriumCost.Dev.SP

theorem choose_i (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : a' + b' ≤ a + b) (hp : 0 < a + b) : (0 < a ∧ a' ≤ a) ∨ (0 < b ∧ b' ≤ b) := by
  by_contra hc
  simp only [not_or, not_and, not_le] at hc
  obtain ⟨h1, h2⟩ := hc
  by_cases hA : 0 < a
  · have := h1 hA
    by_cases hB : 0 < b
    · have := h2 hB; linarith
    · have : b = 0 := le_antisymm (not_lt.1 hB) hb
      linarith
  · have : a = 0 := le_antisymm (not_lt.1 hA) ha
    have hB : 0 < b := by linarith
    have := h2 hB
    linarith

theorem par_child_A (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.par A B) l φ)
    {S0} (hS0 : S0 ∈ paths (.par A B)) (hpos : 0 < φ S0) (ht : 0 < tot A (splA A B φ)) :
    ∃ P ∈ paths A, 0 < splA A B φ P ∧
      plat (fun e => l (Fin.castAdd _ e)) (loads A (splA A B φ)) P =
        plat l (loads (.par A B) φ) S0 := by
  obtain ⟨P, hP, hPpos⟩ := exists_pos_of_tot A ht
  refine ⟨P, hP, hPpos, ?_⟩
  rw [← plat_par_left]
  exact le_antisymm (h.2 _ (imageA_mem A B hP) hPpos _ hS0)
    (h.2 _ hS0 hpos _ (imageA_mem A B hP))

theorem par_child_B (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} (h : PNash (.par A B) l φ)
    {S0} (hS0 : S0 ∈ paths (.par A B)) (hpos : 0 < φ S0) (ht : 0 < tot B (splB A B φ)) :
    ∃ P ∈ paths B, 0 < splB A B φ P ∧
      plat (fun e => l (Fin.natAdd _ e)) (loads B (splB A B φ)) P =
        plat l (loads (.par A B) φ) S0 := by
  obtain ⟨P, hP, hPpos⟩ := exists_pos_of_tot B ht
  refine ⟨P, hP, hPpos, ?_⟩
  rw [← plat_par_right]
  exact le_antisymm (h.2 _ (imageB_mem A B hP) hPpos _ hS0)
    (h.2 _ hS0 hpos _ (imageB_mem A B hP))

theorem claim (N : SPNetwork) : ∀ (l : Fin (edgeCount N) → ℝ → ℝ),
    (∀ e, MonotoneOn (l e) (Set.Ici 0)) →
    ∀ (φ φ' : Finset (Fin (edgeCount N)) → ℝ), PNash N l φ → Nonneg N φ' →
    0 < tot N φ → tot N φ' ≤ tot N φ →
    ∀ S0 ∈ paths N, 0 < φ S0 →
      ∃ S ∈ paths N, plat l (loads N φ') S ≤ plat l (loads N φ) S0 := by
  induction N with
  | arc =>
    intro l hl φ φ' hφ hφ' htot hle S0 hS0 hpos
    have h0 := mem_paths_arc hS0
    subst h0
    refine ⟨_, hS0, ?_⟩
    rw [tot_arc, tot_arc] at hle
    rw [plat_arc, plat_arc, loads_arc, loads_arc]
    exact hl _ (Set.mem_Ici.2 (hφ' _ hS0)) (Set.mem_Ici.2 (hφ.1 _ hS0)) hle
  | series A B ihA ihB =>
    intro l hl φ φ' hφ hφ' htot hle S0 hS0 hpos
    obtain ⟨PA, hPA, PB, hPB, rfl⟩ := mem_paths_series A B hS0
    have hposA : 0 < margA A B φ PA := pos_margA A B hφ.1 hPA hPB hpos
    have hposB : 0 < margB A B φ PB := pos_margB A B hφ.1 hPA hPB hpos
    obtain ⟨QA, hQA, hlA⟩ := ihA (fun e => l (Fin.castAdd _ e)) (fun e => hl _)
      (margA A B φ) (margA A B φ') (pnash_margA A B hφ) (nonneg_margA A B hφ')
      (by have := tot_series_left A B φ; linarith)
      (by have := tot_series_left A B φ; have := tot_series_left A B φ'; linarith) PA hPA hposA
    obtain ⟨QB, hQB, hlB⟩ := ihB (fun e => l (Fin.natAdd _ e)) (fun e => hl _)
      (margB A B φ) (margB A B φ') (pnash_margB A B hφ) (nonneg_margB A B hφ')
      (by have := tot_series_right A B φ; linarith)
      (by have := tot_series_right A B φ; have := tot_series_right A B φ'; linarith) PB hPB hposB
    refine ⟨comb QA QB, comb_mem A B hQA hQB, ?_⟩
    have e1 := plat_series_comb A B l φ' QA QB
    have e2 := plat_series_comb A B l φ PA PB
    exact e1.trans_le ((add_le_add hlA hlB).trans_eq e2.symm)
  | par A B ihA ihB =>
    intro l hl φ φ' hφ hφ' htot hle S0 hS0 hpos
    have t1 := tot_par A B φ
    have t2 := tot_par A B φ'
    replace htot : 0 < tot A (splA A B φ) + tot B (splB A B φ) := by linarith
    replace hle : tot A (splA A B φ') + tot B (splB A B φ') ≤ tot A (splA A B φ) + tot B (splB A B φ) := by linarith
    have hnA := nonneg_splA A B hφ.1
    have hnB := nonneg_splB A B hφ.1
    have hnA' := nonneg_splA A B hφ'
    have hnB' := nonneg_splB A B hφ'
    rcases choose_i _ _ _ _ (tot_nonneg A hnA) (tot_nonneg B hnB) (tot_nonneg A hnA')
      (tot_nonneg B hnB') hle htot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨P, hP, hPpos, hPeq⟩ := par_child_A A B hφ hS0 hpos h1
      obtain ⟨Q, hQ, hlQ⟩ := ihA (fun e => l (Fin.castAdd _ e)) (fun e => hl _)
        (splA A B φ) (splA A B φ') (pnash_splA A B hφ) hnA' h1 h2 P hP hPpos
      refine ⟨Q.image (Fin.castAdd _), imageA_mem A B hQ, ?_⟩
      have e := plat_par_left A B l φ' Q; exact e.trans_le (hlQ.trans_eq hPeq)
    · obtain ⟨P, hP, hPpos, hPeq⟩ := par_child_B A B hφ hS0 hpos h1
      obtain ⟨Q, hQ, hlQ⟩ := ihB (fun e => l (Fin.natAdd _ e)) (fun e => hl _)
        (splB A B φ) (splB A B φ') (pnash_splB A B hφ) hnB' h1 h2 P hP hPpos
      refine ⟨Q.image (Fin.natAdd _), imageB_mem A B hQ, ?_⟩
      have e := plat_par_right A B l φ' Q; exact e.trans_le (hlQ.trans_eq hPeq)

theorem main (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (f' : Flow G) (hf' : IsFeasible G f')
    (P : Fin (routeCount G)) (hP : 0 < f P) :
    ∃ Q : Fin (routeCount G), strategyLatency G f' Q ≤ strategyLatency G f P := by
  have hfe := feas_facts G hf.1
  have hfe' := feas_facts G hf'
  have ht : tot N (pf G f) = G.demand 0 := by rw [tot_pf G hG, hfe.2]
  have ht' : tot N (pf G f') = G.demand 0 := by rw [tot_pf G hG, hfe'.2]
  obtain ⟨S, hS, hle⟩ := claim N G.latency G.latency_monotone (pf G f) (pf G f')
    (pnash_of_nash G hG hf) (nonneg_pf G hG f' hfe'.1)
    (by rw [ht]; exact G.demand_pos 0) (by rw [ht, ht'])
    (route G P).2.val (route_mem G hG P) (pos_pf G hG f hP)
  obtain ⟨Q, hQ⟩ := exists_route_paths G hG hS
  refine ⟨Q, ?_⟩
  rw [strategyLatency_eq G hG, strategyLatency_eq G hG, hQ]
  exact hle

end ApproxEquilibriumCost.Dev.B1

namespace ApproxEquilibriumCost.General.Supplement
theorem chk_lemma_B_1 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (f' : Flow G) (hf' : IsFeasible G f')
    (P : Fin (routeCount G)) (hP : 0 < f P) :
    ∃ Q : Fin (routeCount G), strategyLatency G f' Q ≤ strategyLatency G f P :=
  ApproxEquilibriumCost.Dev.B1.main N G hG f hf f' hf' P hP
end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_lemma_B_1 := @ApproxEquilibriumCost.General.Supplement.chk_lemma_B_1

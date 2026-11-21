-- Prove2me | solution 1 for ApproxEquilibriumCost.General.Supplement.lemma_3_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T10:11:33.83424+00:00
-- url     : https://prove2.me/submissions/65c5ddd9-9bf3-4fdb-a47d-7f92f2a67720

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

theorem paths_nonempty (N : SPNetwork) : (paths N).Nonempty := by
  induction N with
  | arc => simp [paths]
  | series A B ihA ihB =>
    obtain ⟨P, hP⟩ := ihA
    obtain ⟨Q, hQ⟩ := ihB
    exact ⟨comb P Q, by rw [paths_series_eq]; simp only [Finset.mem_biUnion, Finset.mem_image]; exact ⟨P, hP, Q, hQ, rfl⟩⟩
  | par A B ihA ihB =>
    obtain ⟨P, hP⟩ := ihA
    exact ⟨P.image (Fin.castAdd (edgeCount B)), by
      rw [paths_par_eq]; simp only [Finset.mem_union, Finset.mem_image]; exact Or.inl ⟨P, hP, rfl⟩⟩

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

theorem tot_nonneg (N : SPNetwork) {φ : Finset (Fin (edgeCount N)) → ℝ}
    (h : Nonneg N φ) : 0 ≤ tot N φ := Finset.sum_nonneg h

theorem loads_nonneg (N : SPNetwork) {φ : Finset (Fin (edgeCount N)) → ℝ}
    (h : Nonneg N φ) (e : Fin (edgeCount N)) : 0 ≤ loads N φ e :=
  Finset.sum_nonneg fun S hS => by split_ifs <;> [exact h S hS; exact le_rfl]

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

theorem plat_nonneg {N : SPNetwork} (G : Game (edgeCount N) 1) {φ : Finset (Fin (edgeCount N)) → ℝ}
    (hφ : Nonneg N φ) (S : Finset (Fin (edgeCount N))) :
    0 ≤ plat G.latency (loads N φ) S :=
  Finset.sum_nonneg fun e _ => G.latency_nonnegative e _ (loads_nonneg N hφ e)

end ApproxEquilibriumCost.Dev.SP
end

section
set_option autoImplicit false
namespace ApproxEquilibriumCost.Dev.L38
open ApproxEquilibriumCost.General ApproxEquilibriumCost.General.Supplement ApproxEquilibriumCost.Dev.SP

/-- every used path is within `δ` of every path -/
def UD (N : SPNetwork) (l : Fin (edgeCount N) → ℝ → ℝ)
    (φ : Finset (Fin (edgeCount N)) → ℝ) (δ : ℝ) : Prop :=
  ∀ S ∈ paths N, 0 < φ S → ∀ S' ∈ paths N,
    plat l (loads N φ) S ≤ plat l (loads N φ) S' + δ

def Claim (N : SPNetwork) : Prop :=
  ∀ (l : Fin (edgeCount N) → ℝ → ℝ), (∀ e, MonotoneOn (l e) (Set.Ici 0)) →
  ∀ (φ φ' : Finset (Fin (edgeCount N)) → ℝ) (δ : ℝ), 0 ≤ δ → Nonneg N φ → Nonneg N φ' →
  tot N φ ≤ tot N φ' → 0 < tot N φ' → UD N l φ' δ →
  ∀ S0 ∈ paths N, (∀ S ∈ paths N, plat l (loads N φ) S0 ≤ plat l (loads N φ) S) →
  ∃ S ∈ paths N, 0 < φ' S ∧
    plat l (loads N φ) S0 - ((depth N : ℝ) - 1) * δ ≤ plat l (loads N φ') S

theorem choose_i (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (h : a + b ≤ a' + b') (hp : 0 < a' + b') : (a ≤ a' ∧ 0 < a') ∨ (b ≤ b' ∧ 0 < b') := by
  by_contra hc
  simp only [not_or, not_and, not_lt] at hc
  obtain ⟨h1, h2⟩ := hc
  by_cases hA : a ≤ a'
  · have h3 := h1 hA
    by_cases hB : b ≤ b'
    · have := h2 hB; linarith
    · push Not at hB; linarith
  · push Not at hA
    by_cases hB : b ≤ b'
    · have := h2 hB; linarith
    · push Not at hB; linarith

theorem ud_margA (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} {δ : ℝ}
    (hφ : Nonneg (.series A B) φ) (h : UD (.series A B) l φ δ) :
    UD A (fun e => l (Fin.castAdd _ e)) (margA A B φ) δ := by
  intro P hP hpos P' hP'
  obtain ⟨Q, hQ, hq⟩ := exists_pos_margA A B hφ hpos
  have h3 : plat l (loads (.series A B) φ) (comb P Q) ≤
      plat l (loads (.series A B) φ) (comb P' Q) + δ :=
    h _ (comb_mem A B hP hQ) hq _ (comb_mem A B hP' hQ)
  rw [plat_series_comb, plat_series_comb] at h3
  linarith

theorem ud_margB (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} {δ : ℝ}
    (hφ : Nonneg (.series A B) φ) (h : UD (.series A B) l φ δ) :
    UD B (fun e => l (Fin.natAdd _ e)) (margB A B φ) δ := by
  intro Q hQ hpos Q' hQ'
  obtain ⟨P, hP, hq⟩ := exists_pos_margB A B hφ hpos
  have h3 : plat l (loads (.series A B) φ) (comb P Q) ≤
      plat l (loads (.series A B) φ) (comb P Q') + δ :=
    h _ (comb_mem A B hP hQ) hq _ (comb_mem A B hP hQ')
  rw [plat_series_comb, plat_series_comb] at h3
  linarith

theorem ud_splA (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} {δ : ℝ}
    (h : UD (.par A B) l φ δ) :
    UD A (fun e => l (Fin.castAdd _ e)) (splA A B φ) δ := by
  intro P hP hpos P' hP'
  have h3 : plat l (loads (.par A B) φ) (P.image (Fin.castAdd (edgeCount B))) ≤
      plat l (loads (.par A B) φ) (P'.image (Fin.castAdd (edgeCount B))) + δ :=
    h _ (imageA_mem A B hP) hpos _ (imageA_mem A B hP')
  rw [plat_par_left, plat_par_left] at h3
  exact h3

theorem ud_splB (A B : SPNetwork) {l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ}
    {φ : Finset (Fin (edgeCount A + edgeCount B)) → ℝ} {δ : ℝ}
    (h : UD (.par A B) l φ δ) :
    UD B (fun e => l (Fin.natAdd _ e)) (splB A B φ) δ := by
  intro P hP hpos P' hP'
  have h3 : plat l (loads (.par A B) φ) (P.image (Fin.natAdd (edgeCount A))) ≤
      plat l (loads (.par A B) φ) (P'.image (Fin.natAdd (edgeCount A))) + δ :=
    h _ (imageB_mem A B hP) hpos _ (imageB_mem A B hP')
  rw [plat_par_right, plat_par_right] at h3
  exact h3

theorem series_step (A B : SPNetwork) (IHA : Claim A) (IHB : Claim B)
    (l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ) (hl : ∀ e, MonotoneOn (l e) (Set.Ici 0))
    (φ φ' : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hφ : Nonneg (.series A B) φ) (hφ' : Nonneg (.series A B) φ')
    (h1 : tot (.series A B) φ ≤ tot (.series A B) φ') (h2 : 0 < tot (.series A B) φ')
    (hud : UD (.series A B) l φ' δ) (S0 : Finset (Fin (edgeCount A + edgeCount B)))
    (hS0 : S0 ∈ paths (.series A B))
    (hmin : ∀ S ∈ paths (.series A B),
      plat l (loads (.series A B) φ) S0 ≤ plat l (loads (.series A B) φ) S) :
    ∃ S ∈ paths (.series A B), 0 < φ' S ∧
      plat l (loads (.series A B) φ) S0 - ((depth (.series A B) : ℝ) - 1) * δ ≤
        plat l (loads (.series A B) φ') S := by
  obtain ⟨PA0, hPA0, hminA⟩ := Finset.exists_min_image (paths A)
    (plat (fun e => l (Fin.castAdd _ e)) (loads A (margA A B φ))) (paths_nonempty A)
  obtain ⟨PB0, hPB0, hminB⟩ := Finset.exists_min_image (paths B)
    (plat (fun e => l (Fin.natAdd _ e)) (loads B (margB A B φ))) (paths_nonempty B)
  have h4 : plat l (loads (.series A B) φ) S0 ≤ plat l (loads (.series A B) φ) (comb PA0 PB0) :=
    hmin _ (comb_mem A B hPA0 hPB0)
  rw [plat_series_comb] at h4
  have ta := tot_series_left A B φ
  have ta' := tot_series_left A B φ'
  have tb := tot_series_right A B φ
  have tb' := tot_series_right A B φ'
  obtain ⟨PA', hPA', hposA', hlA⟩ := IHA (fun e => l (Fin.castAdd _ e)) (fun e => hl _)
    (margA A B φ) (margA A B φ') δ hδ (nonneg_margA A B hφ) (nonneg_margA A B hφ')
    (by linarith) (by linarith) (ud_margA A B hφ' hud) PA0 hPA0 hminA
  obtain ⟨PB', hPB', hposB', hlB⟩ := IHB (fun e => l (Fin.natAdd _ e)) (fun e => hl _)
    (margB A B φ) (margB A B φ') δ hδ (nonneg_margB A B hφ) (nonneg_margB A B hφ')
    (by linarith) (by linarith) (ud_margB A B hφ' hud) PB0 hPB0 hminB
  obtain ⟨QB, hQB, hφQ⟩ := exists_pos_margA A B hφ' hposA'
  have h5 := ud_margB A B hφ' hud PB' hPB' hposB' QB hQB
  have e1 := plat_series_comb A B l φ' PA' QB
  have hd : ((depth (.series A B) : ℕ) : ℝ) = depth A + depth B := by simp [depth]
  refine ⟨comb PA' QB, comb_mem A B hPA' hQB, hφQ, ?_⟩
  rw [hd]
  have key : plat l (loads (.series A B) φ) S0 - (((depth A : ℝ) + depth B) - 1) * δ ≤
      plat l (loads (.series A B) φ') (comb PA' QB) := by
    rw [e1]
    nlinarith
  exact key

theorem par_step (A B : SPNetwork) (IHA : Claim A) (IHB : Claim B)
    (l : Fin (edgeCount A + edgeCount B) → ℝ → ℝ) (hl : ∀ e, MonotoneOn (l e) (Set.Ici 0))
    (φ φ' : Finset (Fin (edgeCount A + edgeCount B)) → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hφ : Nonneg (.par A B) φ) (hφ' : Nonneg (.par A B) φ')
    (h1 : tot (.par A B) φ ≤ tot (.par A B) φ') (h2 : 0 < tot (.par A B) φ')
    (hud : UD (.par A B) l φ' δ) (S0 : Finset (Fin (edgeCount A + edgeCount B)))
    (hS0 : S0 ∈ paths (.par A B))
    (hmin : ∀ S ∈ paths (.par A B),
      plat l (loads (.par A B) φ) S0 ≤ plat l (loads (.par A B) φ) S) :
    ∃ S ∈ paths (.par A B), 0 < φ' S ∧
      plat l (loads (.par A B) φ) S0 - ((depth (.par A B) : ℝ) - 1) * δ ≤
        plat l (loads (.par A B) φ') S := by
  have t1 := tot_par A B φ
  have t2 := tot_par A B φ'
  have hnA := nonneg_splA A B hφ
  have hnB := nonneg_splB A B hφ
  have hnA' := nonneg_splA A B hφ'
  have hnB' := nonneg_splB A B hφ'
  have hdA : ((depth A : ℕ) : ℝ) ≤ ((depth (.par A B) : ℕ) : ℝ) :=
    Nat.cast_le.2 (le_max_left _ _)
  have hdB : ((depth B : ℕ) : ℝ) ≤ ((depth (.par A B) : ℕ) : ℝ) :=
    Nat.cast_le.2 (le_max_right _ _)
  rcases choose_i _ _ _ _ (tot_nonneg A hnA) (tot_nonneg B hnB) (tot_nonneg A hnA')
    (tot_nonneg B hnB') (by linarith) (by linarith) with ⟨c1, c2⟩ | ⟨c1, c2⟩
  · obtain ⟨P0, hP0, hminA⟩ := Finset.exists_min_image (paths A)
      (plat (fun e => l (Fin.castAdd _ e)) (loads A (splA A B φ))) (paths_nonempty A)
    have h4 : plat l (loads (.par A B) φ) S0 ≤
        plat l (loads (.par A B) φ) (P0.image (Fin.castAdd (edgeCount B))) :=
      hmin _ (imageA_mem A B hP0)
    rw [plat_par_left] at h4
    obtain ⟨P', hP', hpos', hl'⟩ := IHA (fun e => l (Fin.castAdd _ e)) (fun e => hl _)
      (splA A B φ) (splA A B φ') δ hδ hnA hnA' c1 c2 (ud_splA A B hud) P0 hP0 hminA
    refine ⟨P'.image (Fin.castAdd _), imageA_mem A B hP', hpos', ?_⟩
    have e := plat_par_left A B l φ' P'
    have := mul_le_mul_of_nonneg_right (sub_le_sub_right hdA 1) hδ
    have key : plat l (loads (.par A B) φ) S0 - (((depth (.par A B) : ℕ) : ℝ) - 1) * δ ≤
        plat l (loads (.par A B) φ') (P'.image (Fin.castAdd (edgeCount B))) := by
      rw [e]; linarith
    exact key
  · obtain ⟨P0, hP0, hminB⟩ := Finset.exists_min_image (paths B)
      (plat (fun e => l (Fin.natAdd _ e)) (loads B (splB A B φ))) (paths_nonempty B)
    have h4 : plat l (loads (.par A B) φ) S0 ≤
        plat l (loads (.par A B) φ) (P0.image (Fin.natAdd (edgeCount A))) :=
      hmin _ (imageB_mem A B hP0)
    rw [plat_par_right] at h4
    obtain ⟨P', hP', hpos', hl'⟩ := IHB (fun e => l (Fin.natAdd _ e)) (fun e => hl _)
      (splB A B φ) (splB A B φ') δ hδ hnB hnB' c1 c2 (ud_splB A B hud) P0 hP0 hminB
    refine ⟨P'.image (Fin.natAdd _), imageB_mem A B hP', hpos', ?_⟩
    have e := plat_par_right A B l φ' P'
    have := mul_le_mul_of_nonneg_right (sub_le_sub_right hdB 1) hδ
    have key : plat l (loads (.par A B) φ) S0 - (((depth (.par A B) : ℕ) : ℝ) - 1) * δ ≤
        plat l (loads (.par A B) φ') (P'.image (Fin.natAdd (edgeCount A))) := by
      rw [e]; linarith
    exact key

theorem claim (N : SPNetwork) : Claim N := by
  induction N with
  | arc =>
    intro l hl φ φ' δ hδ hφ hφ' h1 h2 hud S0 hS0 hmin
    have h0 := mem_paths_arc hS0
    subst h0
    refine ⟨_, hS0, ?_, ?_⟩
    · rw [tot_arc] at h2; exact h2
    · rw [tot_arc, tot_arc] at h1
      rw [plat_arc, plat_arc, loads_arc, loads_arc]
      have : ((depth .arc : ℕ) : ℝ) = 1 := by simp [depth]
      rw [this]
      have := hl ⟨0, by decide⟩ (Set.mem_Ici.2 (hφ _ hS0)) (Set.mem_Ici.2 (hφ' _ hS0)) h1
      linarith
  | series A B ihA ihB =>
    intro l hl φ φ' δ hδ hφ hφ' h1 h2 hud S0 hS0 hmin
    exact series_step A B ihA ihB l hl φ φ' δ hδ hφ hφ' h1 h2 hud S0 hS0 hmin
  | par A B ihA ihB =>
    intro l hl φ φ' δ hδ hφ hφ' h1 h2 hud S0 hS0 hmin
    exact par_step A B ihA ihB l hl φ φ' δ hδ hφ hφ' h1 h2 hud S0 hS0 hmin

theorem main (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (ε : ℝ) (hε : 0 ≤ ε) (f' : Flow G) (hf' : IsApproxNash G ε f')
    (P Q : Fin (routeCount G)) (hP : 0 < f P) :
    strategyLatency G f P / (1 + (depth N : ℝ) * ε) ≤ strategyLatency G f' Q := by
  have hfe := feas_facts G hf.1
  have hfe' := feas_facts G hf'.1
  have hn' := nonneg_pf G hG f' hfe'.1
  have ht : tot N (pf G f) = G.demand 0 := by rw [tot_pf G hG, hfe.2]
  have ht' : tot N (pf G f') = G.demand 0 := by rw [tot_pf G hG, hfe'.2]
  obtain ⟨S1, hS1, hmin1⟩ := Finset.exists_min_image (paths N)
    (plat G.latency (loads N (pf G f'))) (paths_nonempty N)
  obtain ⟨r1, hr1⟩ := exists_route_paths G hG hS1
  have hL : 0 ≤ plat G.latency (loads N (pf G f')) S1 := plat_nonneg G hn' S1
  have hused : ∀ S ∈ paths N, 0 < pf G f' S →
      plat G.latency (loads N (pf G f')) S ≤
        plat G.latency (loads N (pf G f')) S1 + ε * plat G.latency (loads N (pf G f')) S1 := by
    intro S _ hpos
    obtain ⟨r, hr, hfr⟩ := pf_pos G hG f' hpos
    have h := hf'.2 r r1 (Subsingleton.elim _ _) hfr
    rw [strategyLatency_eq G hG, strategyLatency_eq G hG, hr, hr1] at h
    linarith
  have hδ : 0 ≤ ε * plat G.latency (loads N (pf G f')) S1 := mul_nonneg hε hL
  have hud : UD N G.latency (pf G f') (ε * plat G.latency (loads N (pf G f')) S1) := by
    intro S hS hpos S' hS'
    have := hused S hS hpos
    have := hmin1 S' hS'
    linarith
  have hnash := pnash_of_nash G hG hf
  obtain ⟨S, hS, hposS, hb⟩ := claim N G.latency G.latency_monotone (pf G f) (pf G f')
    (ε * plat G.latency (loads N (pf G f')) S1) hδ hnash.1 hn'
    (by rw [ht, ht']) (by rw [ht']; exact G.demand_pos 0) hud
    (route G P).2.val (route_mem G hG P)
    (fun S hS => hnash.2 _ (route_mem G hG P) (pos_pf G hG f hP) S hS)
  have hu := hused S hS hposS
  rw [strategyLatency_eq G hG, strategyLatency_eq G hG]
  have hQ := hmin1 _ (route_mem G hG Q)
  have hpos : 0 < 1 + (depth N : ℝ) * ε := by positivity
  rw [div_le_iff₀ hpos]
  set L := plat G.latency (loads N (pf G f')) S1
  have : plat G.latency (loads N (pf G f)) (route G P).2.val ≤ L * (1 + (depth N : ℝ) * ε) := by
    nlinarith
  have h2 : L * (1 + (depth N : ℝ) * ε) ≤
      plat G.latency (loads N (pf G f')) (route G Q).2.val * (1 + (depth N : ℝ) * ε) :=
    mul_le_mul_of_nonneg_right hQ hpos.le
  linarith

end ApproxEquilibriumCost.Dev.L38

namespace ApproxEquilibriumCost.General.Supplement
theorem chk_lemma_3_8 (N : SPNetwork) (G : Game (edgeCount N) 1)
    (hG : IsRoutingGame N G) (f : Flow G) (hf : IsNash G f)
    (ε : ℝ) (hε : 0 ≤ ε) (f' : Flow G) (hf' : IsApproxNash G ε f')
    (P Q : Fin (routeCount G)) (hP : 0 < f P) :
    strategyLatency G f P / (1 + (depth N : ℝ) * ε) ≤
      strategyLatency G f' Q :=
  ApproxEquilibriumCost.Dev.L38.main N G hG f hf ε hε f' hf' P Q hP
end ApproxEquilibriumCost.General.Supplement
end

theorem solution : type_of% @ApproxEquilibriumCost.General.Supplement.chk_lemma_3_8 := @ApproxEquilibriumCost.General.Supplement.chk_lemma_3_8

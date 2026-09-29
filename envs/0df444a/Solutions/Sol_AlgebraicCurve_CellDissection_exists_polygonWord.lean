-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_polygonWord
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/5fa8651b-a4b5-5ec0-bc42-c99ee7cd141b

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_polygonWord

open AlgebraicCurve
open scoped Real

namespace SolWORD

section CycList

variable {α : Type*}

private def Cyc (P : α → α → Prop) (l : List α) : Prop :=
  l.IsChain P ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, P x y

private lemma cyc_imp {P P' : α → α → Prop} (hPP' : ∀ x y, P x y → P' x y) {l : List α}
    (h : Cyc P l) : Cyc P' l :=
  ⟨h.1.imp (fun _ _ hxy => hPP' _ _ hxy), fun x hx y hy => hPP' x y (h.2 x hx y hy)⟩

private lemma cyc_shift {P : α → α → Prop} {a : α} {l : List α} (h : Cyc P (a :: l)) :
    Cyc P (l ++ [a]) := by
  obtain ⟨hchain, hwrap⟩ := h
  rw [List.isChain_cons] at hchain
  refine ⟨List.isChain_append.2 ⟨hchain.2, List.isChain_singleton _, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    subst hy
    cases l with
    | nil => simp at hx
    | cons b l' =>
      exact hwrap x (by simpa using hx) _ (by simp)
  · intro x hx y hy
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.mem_def,
      Option.some.injEq] at hx
    subst hx
    cases l with
    | nil =>
      simp only [List.nil_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hwrap _ (by simp) _ (by simp)
    | cons b l' =>
      simp only [List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hchain.1 _ (by simp)

private lemma cyc_rotate {P : α → α → Prop} : ∀ (n : ℕ) {l : List α}, Cyc P l → Cyc P (l.rotate n)
  | 0, l, h => by simpa using h
  | n + 1, [], h => by simpa using h
  | n + 1, a :: l, h => by
    rw [List.rotate_cons_succ]
    exact cyc_rotate n (cyc_shift h)

private lemma cyc_getElem {P : α → α → Prop} {l : List α} (h : Cyc P l) (k : ℕ)
    (hk : k < l.length) :
    P (l[k]) (l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk))) := by
  obtain ⟨hchain, hwrap⟩ := h
  by_cases hk1 : k + 1 < l.length
  · have := List.isChain_iff_getElem.1 hchain k hk1
    simpa [Nat.mod_eq_of_lt hk1] using this
  · have hk2 : k + 1 = l.length := by omega
    have hmod : (k + 1) % l.length = 0 := by rw [hk2, Nat.mod_self]
    have hne : l ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hx : l[k] ∈ l.getLast? := by
      rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq,
        List.getLast_eq_getElem]
      congr 1; omega
    have hy : l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)) ∈
        l.head? := by
      rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq, List.head_eq_getElem]
      congr 1; omega
    exact hwrap _ hx _ hy

private lemma cyc_of_getElem {P : α → α → Prop} {l : List α}
    (h : ∀ (k : ℕ) (hk : k < l.length),
      P (l[k]) (l[(k + 1) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)))) :
    Cyc P l := by
  refine ⟨List.isChain_iff_getElem.2 (fun i hi => ?_), fun x hx y hy => ?_⟩
  · have := h i (by omega)
    simpa [Nat.mod_eq_of_lt hi] using this
  · have hne : l ≠ [] := by rintro rfl; simp at hx
    have hpos : 0 < l.length := List.length_pos_of_ne_nil hne
    rw [List.getLast?_eq_some_getLast hne, Option.mem_def, Option.some.injEq] at hx
    rw [List.head?_eq_some_head hne, Option.mem_def, Option.some.injEq] at hy
    subst hx; subst hy
    have := h (l.length - 1) (by omega)
    have hmod : (l.length - 1 + 1) % l.length = 0 := by
      rw [Nat.sub_add_cancel hpos, Nat.mod_self]
    rw [List.getLast_eq_getElem, List.head_eq_getElem]
    simpa [hmod] using this

private lemma cyc_splice {P P' : α → α → Prop} {a b : α} {l₁ l₂ : List α}
    (h₁ : Cyc P (a :: l₁)) (h₂ : Cyc P (b :: l₂))
    (hmono : ∀ x y, P x y → P' x y)
    (hja : ∀ x y, P' x a → P b y → P' x y)
    (hjb : ∀ x y, P' x b → P a y → P' x y) :
    Cyc P' (l₁ ++ l₂) := by
  obtain ⟨hc₁, hw₁⟩ := h₁
  obtain ⟨hc₂, hw₂⟩ := h₂
  rw [List.isChain_cons] at hc₁ hc₂

  have hlast₁ : ∀ x ∈ l₁.getLast?, P x a := fun x hx =>
    hw₁ x (by cases l₁ with | nil => simp at hx | cons c l => simpa using hx) a (by simp)
  have hlast₂ : ∀ x ∈ l₂.getLast?, P x b := fun x hx =>
    hw₂ x (by cases l₂ with | nil => simp at hx | cons c l => simpa using hx) b (by simp)
  have haa : l₁ = [] → P a a := fun h => by subst h; exact hw₁ a (by simp) a (by simp)
  have hbb : l₂ = [] → P b b := fun h => by subst h; exact hw₂ b (by simp) b (by simp)
  refine ⟨List.isChain_append.2 ⟨hc₁.2.imp (fun _ _ h => hmono _ _ h),
    hc₂.2.imp (fun _ _ h => hmono _ _ h), fun x hx y hy => hja x y (hmono _ _ (hlast₁ x hx))
      (hc₂.1 y hy)⟩, ?_⟩
  intro x hx y hy
  rw [List.getLast?_append] at hx
  rw [List.head?_append] at hy
  cases l₂ with
  | nil =>
    cases l₁ with
    | nil => simp at hx
    | cons c l =>
      simp only [List.getLast?_nil, Option.none_or, List.head?_nil, Option.or_none] at hx hy

      have h1 : P' x b := hja x b (hmono _ _ (hlast₁ x hx)) (hbb rfl)
      exact hjb x y h1 (hc₁.1 y hy)
  | cons d l =>
    have hx' : x ∈ (d :: l).getLast? := by
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil d l)] at hx ⊢
      simpa using hx
    have hxb : P x b := hlast₂ x hx'
    cases l₁ with
    | nil =>
      simp only [List.head?_nil, Option.none_or] at hy

      have h1 : P' x a := hjb x a (hmono _ _ hxb) (haa rfl)
      exact hja x y h1 (hc₂.1 y hy)
    | cons c l' =>
      simp only [List.head?_cons, Option.or_some, Option.mem_def, Option.some.injEq] at hy
      subst hy
      exact hjb x c (hmono _ _ hxb) (hc₁.1 c (by simp))

private lemma exists_rotate_cons {l : List α} {a : α} (ha : a ∈ l) :
    ∃ (n : ℕ) (l' : List α), l.rotate n = a :: l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
  refine ⟨i, (l.rotate i).tail, ?_⟩
  have hlen : 0 < (l.rotate i).length := by rw [List.length_rotate]; omega
  have hne : l.rotate i ≠ [] := List.ne_nil_of_length_pos hlen
  conv_lhs => rw [← List.cons_head_tail hne]
  congr 1
  rw [List.head_eq_getElem, List.getElem_rotate]
  congr 1
  simp [Nat.mod_eq_of_lt hi]

private lemma exists_list_of_rtg {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ cs : List α, cs.head? = some a ∧ cs.getLast? = some b ∧ cs.IsChain r := by
  induction h with
  | refl => exact ⟨[a], by simp, by simp, List.isChain_singleton _⟩
  | @tail b c _ hbc ih =>
    obtain ⟨cs, hhead, hlast, hchain⟩ := ih
    refine ⟨cs ++ [c], ?_, by simp, ?_⟩
    · rw [List.head?_append, hhead]; rfl
    · refine List.isChain_append.2 ⟨hchain, List.isChain_singleton _, fun x hx y hy => ?_⟩
      rw [hlast, Option.mem_def, Option.some.injEq] at hx
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
      subst hx; subst hy; exact hbc

end CycList

section AbstractGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (hd tl : E → V)

private def bd (c : E → ℤ) (w : V) : ℤ :=
  (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e)

omit [Fintype V] [DecidableEq E] in
private lemma bd_add (c d : E → ℤ) (w : V) :
    bd hd tl (c + d) w = bd hd tl c w + bd hd tl d w := by
  unfold bd; simp only [Pi.add_apply, Finset.sum_add_distrib]; ring

omit [Fintype V] [DecidableEq E] in
private lemma bd_sub (c d : E → ℤ) (w : V) :
    bd hd tl (c - d) w = bd hd tl c w - bd hd tl d w := by
  unfold bd; simp only [Pi.sub_apply, Finset.sum_sub_distrib]; ring

omit [Fintype V] in
private lemma bd_single (e₀ : E) (w : V) :
    bd hd tl (fun e => if e = e₀ then (1 : ℤ) else 0) w =
      (if w = hd e₀ then 1 else 0) - (if w = tl e₀ then 1 else 0) := by
  unfold bd
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_univ, true_and, eq_comm (a := w)]

omit [Fintype V] [DecidableEq E] in
private lemma bd_smul (n : ℤ) (c : E → ℤ) (w : V) :
    bd hd tl (n • c) w = n * bd hd tl c w := by
  unfold bd; simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]; ring

omit [Fintype V] [DecidableEq E] in
private lemma bd_finsum {ι : Type*} (s : Finset ι) (f : ι → E → ℤ) (w : V) :
    bd hd tl (fun e => ∑ i ∈ s, f i e) w = ∑ i ∈ s, bd hd tl (f i) w := by
  unfold bd
  simp only [Finset.sum_sub_distrib]
  rw [Finset.sum_comm (t := s), Finset.sum_comm (t := s)]

private def IsTree (T : Finset E) : Prop :=
  ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧ ∀ w, bd hd tl c w =
    (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)

omit [Fintype V] [DecidableEq E] in

private lemma sum_bd_eq (c : E → ℤ) (A : Finset V) :
    ∑ w ∈ A, bd hd tl c w =
      ∑ e, ((if hd e ∈ A then c e else 0) - (if tl e ∈ A then c e else 0)) := by
  classical
  have heq : ∀ g : E → V, (∑ w ∈ A, ∑ e with g e = w, c e) =
      ∑ e, (if g e ∈ A then c e else 0) := by
    intro g
    rw [show (∑ w ∈ A, ∑ e with g e = w, c e) =
          ∑ w ∈ A, ∑ e, (if g e = w then c e else 0) from
        Finset.sum_congr rfl (fun w _ => Finset.sum_filter _ _),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_ite_eq A (g e) (fun _ => c e))
  unfold bd; rw [Finset.sum_sub_distrib, heq hd, heq tl, Finset.sum_sub_distrib]

omit [Fintype V] in

private lemma exists_crossing {T : Finset E} (hT : IsTree hd tl T) {A : Finset V} {u v : V}
    (hu : u ∈ A) (hv : v ∉ A) : ∃ e ∈ T, ¬ (hd e ∈ A ↔ tl e ∈ A) := by
  classical
  obtain ⟨c, ⟨hcT, hcbd⟩, -⟩ := hT u v
  by_contra hall
  push Not at hall
  have hsum : ∑ w ∈ A, bd hd tl c w = -1 := by
    rw [Finset.sum_congr rfl (fun w _ => hcbd w), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' A v, Finset.sum_ite_eq' A u, if_neg hv, if_pos hu]
    ring
  rw [sum_bd_eq] at hsum
  have hzero : ∀ e ∈ (Finset.univ : Finset E),
      ((if hd e ∈ A then c e else 0) - (if tl e ∈ A then c e else 0)) = 0 := by
    intro e _
    by_cases heT : e ∈ T
    · have hiff := hall e heT
      by_cases hh : hd e ∈ A
      · rw [if_pos hh, if_pos (hiff.1 hh), sub_self]
      · rw [if_neg hh, if_neg (fun h => hh (hiff.2 h)), sub_self]
    · rw [hcT e heT]; simp
  rw [Finset.sum_eq_zero hzero] at hsum
  exact absurd hsum (by norm_num)

private lemma spanningTree_card [Nonempty V] (T : Finset E) (hT : IsTree hd tl T) :
    T.card + 1 = Fintype.card V := by
  classical
  obtain ⟨v₀⟩ := ‹Nonempty V›
  set ext : (↥T → ℤ) → (E → ℤ) := fun d e => if he : e ∈ T then d ⟨e, he⟩ else 0
  have hext_T : ∀ d e (he : e ∈ T), ext d e = d ⟨e, he⟩ := fun d e he => dif_pos he
  have hext_nT : ∀ d, ∀ e ∉ T, ext d e = 0 := fun d e he => dif_neg he
  set c : V → E → ℤ := fun v => Classical.choose (hT v₀ v).exists
  have hcspec : ∀ v, (∀ e ∉ T, c v e = 0) ∧
      ∀ w, bd hd tl (c v) w = (if w = v then (1:ℤ) else 0) - (if w = v₀ then 1 else 0) :=
    fun v => Classical.choose_spec (hT v₀ v).exists
  have hsum0 : ∀ d : E → ℤ, ∑ w, bd hd tl d w = 0 := by
    intro d
    have := sum_bd_eq hd tl d Finset.univ
    simp only [Finset.mem_univ, if_true, sub_self, Finset.sum_const_zero] at this
    exact this
  let L : (↥T → ℤ) →ₗ[ℤ] ({v : V // v ≠ v₀} → ℤ) :=
    { toFun := fun d v => bd hd tl (ext d) v.1
      map_add' := fun d₁ d₂ => funext fun v => by
        rw [show ext (d₁ + d₂) = ext d₁ + ext d₂ from funext (fun e => by
          simp only [ext, Pi.add_apply]; split_ifs <;> simp), bd_add]; rfl
      map_smul' := fun n d => funext fun v => by
        rw [show ext (n • d) = n • ext d from funext (fun e => by
          simp only [ext, Pi.smul_apply]; split_ifs <;> simp), bd_smul]; rfl }
  have hLinj : Function.Injective L := by
    intro d₁ d₂ heq
    have hbd0 : ∀ w, bd hd tl (ext d₁ - ext d₂) w = 0 := by
      intro w
      by_cases hw : w = v₀
      · subst hw
        have h := hsum0 (ext d₁ - ext d₂)
        rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ w)] at h
        have hrest : ∑ w' ∈ Finset.univ \ {w}, bd hd tl (ext d₁ - ext d₂) w' = 0 := by
          refine Finset.sum_eq_zero (fun w' hw' => ?_)
          simp only [Finset.mem_sdiff, Finset.mem_singleton] at hw'
          have := congrFun heq ⟨w', hw'.2⟩
          simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
          rw [bd_sub]; linarith
        linarith
      · have := congrFun heq ⟨w, hw⟩
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [bd_sub]; linarith
    have hdiff : (ext d₁ - ext d₂) = (0 : E → ℤ) :=
      (hT v₀ v₀).unique
        ⟨fun e he => by
            show ext d₁ e - ext d₂ e = 0
            rw [hext_nT d₁ e he, hext_nT d₂ e he]; ring,
         fun w => by simp only [hbd0 w]; split_ifs <;> ring⟩
        ⟨fun _ _ => rfl, fun w => by unfold bd; simp⟩
    funext e
    have := congrFun hdiff e.1
    simp only [Pi.sub_apply, hext_T d₁ e.1 e.2, hext_T d₂ e.1 e.2, Pi.zero_apply] at this
    linarith
  have hLsurj : Function.Surjective L := by
    intro a
    refine ⟨fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e.1, ?_⟩
    funext ⟨w, hw⟩
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk]
    have hext_eq : ext (fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e.1) =
        fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e := by
      funext e
      by_cases he : e ∈ T
      · simp only [ext, dif_pos he]
      · simp only [ext, dif_neg he]
        exact (Finset.sum_eq_zero (fun v _ => by rw [(hcspec v.1).1 e he, mul_zero])).symm
    rw [hext_eq, show (fun e => ∑ v : {v : V // v ≠ v₀}, a v * c v.1 e) =
          (fun e => ∑ v : {v : V // v ≠ v₀}, ((a v) • (c v.1)) e) from
        funext (fun e => Finset.sum_congr rfl (fun v _ => by
          simp only [Pi.smul_apply, smul_eq_mul])),
      bd_finsum]
    rw [show (∑ v : {v : V // v ≠ v₀}, bd hd tl ((a v) • (c v.1)) w) =
          ∑ v : {v : V // v ≠ v₀}, a v * ((if w = v.1 then (1:ℤ) else 0) - if w = v₀ then 1 else 0)
        from Finset.sum_congr rfl (fun v _ => by rw [bd_smul, (hcspec v.1).2 w])]
    rw [if_neg hw]
    simp only [sub_zero]
    rw [Finset.sum_eq_single ⟨w, hw⟩]
    · rw [if_pos rfl, mul_one]
    · intro v _ hne
      rw [if_neg (fun h => hne (Subtype.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hequiv := LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩
  have hc := card_eq_of_linearEquiv ℤ hequiv
  simp only [Fintype.card_coe, Fintype.card_subtype_compl, Fintype.card_subtype_eq] at hc
  have hVpos : 1 ≤ Fintype.card V := Fintype.card_pos
  omega

end AbstractGraph

section Dissection

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  (𝒟 : CellDissection F)

private noncomputable abbrev Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
  fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1

private noncomputable abbrev Cs (q : 𝒟.ιE × Bool) : 𝒟.ιC := Cside 𝒟 q.1 q.2

private abbrev sV (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2

private abbrev eV (q : 𝒟.ιE × Bool) : 𝒟.ιV :=
  if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1

private lemma eV_not (g : 𝒟.ιE) (σ : Bool) : eV 𝒟 (g, !σ) = sV 𝒟 (g, σ) := by
  cases σ <;> rfl

private lemma sV_mem_ends (g : 𝒟.ιE) (σ : Bool) :
    sV 𝒟 (g, σ) = (𝒟.ends g).1 ∨ sV 𝒟 (g, σ) = (𝒟.ends g).2 := by
  cases σ <;> simp [sV]

private lemma Cside_eq_iff (e : 𝒟.ιE) (σ : Bool) (C : 𝒟.ιC) :
    Cside 𝒟 e σ = C ↔ ∃ k, 𝒟.side C k = (e, σ) := by
  classical
  have hsurj := Function.surjInv_eq 𝒟.side_bij.surjective (e, σ)
  constructor
  · intro hC
    subst hC
    exact ⟨_, hsurj⟩
  · rintro ⟨k, hk⟩
    have heq : Function.surjInv 𝒟.side_bij.surjective (e, σ) = ⟨C, k⟩ :=
      𝒟.side_bij.injective (a₁ := Function.surjInv 𝒟.side_bij.surjective (e, σ))
        (a₂ := ⟨C, k⟩) (hsurj.trans hk.symm)
    exact congrArg Sigma.fst heq

private lemma Cs_side (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N) : Cs 𝒟 (𝒟.side C k) = C :=
  (Cside_eq_iff 𝒟 _ _ C).2 ⟨k, rfl⟩

private lemma side_injective (C : 𝒟.ιC) : Function.Injective (𝒟.side C) := by
  intro k k' hkk'
  have := 𝒟.side_bij.injective (a₁ := ⟨C, k⟩) (a₂ := ⟨C, k'⟩) hkk'
  exact (Sigma.mk.inj_iff.1 this).2.eq

private def nxt {N : ℕ} (k : Fin N) : Fin N :=
  if h : k.val + 1 < N then ⟨k.val + 1, h⟩ else ⟨0, k.pos⟩

private lemma nxt_val {N : ℕ} (j : Fin N) : (nxt j).val = (j.val + 1) % N := by
  simp only [nxt]
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hj := j.isLt
    have heq : j.val + 1 = N := by omega
    simp [heq]

private lemma cell_bdry_periodic (C : AlgebraicCurve.Cell F) (φ : ℝ) :
    C.bdry (φ + 2 * π) = C.bdry φ := by
  unfold AlgebraicCurve.Cell.bdry AlgebraicCurve.RadialRegion.loop
  rw [C.R.hper,
    show ((φ + 2 * π : ℝ) : ℂ) * Complex.I = ↑φ * Complex.I + 2 * ↑π * Complex.I from by
      push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma corner_arc (hvert : Function.Injective 𝒟.vert) (C : 𝒟.ιC)
    (k : Fin (𝒟.cell C).R.N) : eV 𝒟 (𝒟.side C k) = sV 𝒟 (𝒟.side C (nxt k)) := by
  apply hvert
  have h1 := (𝒟.arc_ends C k).2
  have h2 := (𝒟.arc_ends C (nxt k)).1
  have hb : (𝒟.cell C).bdry ((𝒟.cell C).R.φs k.succ) =
      (𝒟.cell C).bdry ((𝒟.cell C).R.φs (nxt k).castSucc) := by
    by_cases hk : k.val + 1 < (𝒟.cell C).R.N
    · rw [show (nxt k).castSucc = k.succ from Fin.ext (by simp [nxt, hk])]
    · have h0 : (nxt k).castSucc = (0 : Fin _) := Fin.ext (by simp [nxt, hk])
      have hl : k.succ = Fin.last _ := Fin.ext (by
        simp only [Fin.val_succ, Fin.val_last]; omega)
      rw [h0, hl, (𝒟.cell C).R.hφ0, (𝒟.cell C).R.hφN,
        show (2 * π : ℝ) = 0 + 2 * π from by ring, cell_bdry_periodic]
  simp only [eV, sV]
  rw [← h1, ← h2, hb]

private def crossAt (G : Finset 𝒟.ιE) (v : 𝒟.ιV) (D D' : 𝒟.ιC) : Prop :=
  ∃ g ∈ G, ((Cside 𝒟 g true = D ∧ Cside 𝒟 g false = D') ∨
      (Cside 𝒟 g true = D' ∧ Cside 𝒟 g false = D)) ∧
    (v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2)

private def Corner (G : Finset 𝒟.ιE) (x y : 𝒟.ιE × Bool) : Prop :=
  eV 𝒟 x = sV 𝒟 y ∧ Relation.ReflTransGen (crossAt 𝒟 G (eV 𝒟 x)) (Cs 𝒟 x) (Cs 𝒟 y)

private lemma crossAt_mono {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') (v : 𝒟.ιV) {D D' : 𝒟.ιC}
    (h : crossAt 𝒟 G v D D') : crossAt 𝒟 G' v D D' := by
  obtain ⟨g, hg, hside, hv⟩ := h
  exact ⟨g, hGG' hg, hside, hv⟩

private lemma corner_mono {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') {x y : 𝒟.ιE × Bool}
    (h : Corner 𝒟 G x y) : Corner 𝒟 G' x y :=
  ⟨h.1, Relation.ReflTransGen.mono (fun _ _ hDD' => crossAt_mono 𝒟 hGG' _ hDD') _ _ h.2⟩

private lemma crossAt_pair {G : Finset 𝒟.ιE} {g : 𝒟.ιE} (hg : g ∈ G) (σ : Bool) {v : 𝒟.ιV}
    (hv : v = (𝒟.ends g).1 ∨ v = (𝒟.ends g).2) :
    crossAt 𝒟 G v (Cs 𝒟 (g, σ)) (Cs 𝒟 (g, !σ)) := by
  refine ⟨g, hg, ?_, hv⟩
  cases σ
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

private lemma corner_junction {G G' : Finset 𝒟.ιE} (hGG' : G ⊆ G') {g : 𝒟.ιE} (hg : g ∈ G')
    (σ : Bool) {x y : 𝒟.ιE × Bool} (h₁ : Corner 𝒟 G' x (g, σ)) (h₂ : Corner 𝒟 G (g, !σ) y) :
    Corner 𝒟 G' x y := by
  obtain ⟨hv₁, hl₁⟩ := h₁
  obtain ⟨hv₂, hl₂⟩ := h₂
  have hvx : eV 𝒟 (g, !σ) = eV 𝒟 x := by rw [eV_not, hv₁]
  refine ⟨?_, ?_⟩
  · rw [← hv₂, hvx]
  · rw [hvx] at hl₂
    refine hl₁.trans (Relation.ReflTransGen.head ?_
      (Relation.ReflTransGen.mono (fun _ _ hDD' => crossAt_mono 𝒟 hGG' _ hDD') _ _ hl₂))
    refine crossAt_pair 𝒟 hg σ ?_
    rw [hv₁]; exact sV_mem_ends 𝒟 g σ

private noncomputable def arcs (C : 𝒟.ιC) : List (𝒟.ιE × Bool) :=
  List.ofFn (fun k : Fin (𝒟.cell C).R.N => 𝒟.side C k)

private lemma mem_arcs (C : 𝒟.ιC) (q : 𝒟.ιE × Bool) : q ∈ arcs 𝒟 C ↔ Cs 𝒟 q = C := by
  rw [arcs, List.mem_ofFn, Cs, Cside_eq_iff]

private lemma arcs_nodup (C : 𝒟.ιC) : (arcs 𝒟 C).Nodup := by
  rw [arcs, List.nodup_ofFn]
  exact side_injective 𝒟 C

private lemma cyc_arcs (hvert : Function.Injective 𝒟.vert) (G : Finset 𝒟.ιE) (C : 𝒟.ιC) :
    Cyc (Corner 𝒟 G) (arcs 𝒟 C) := by
  refine cyc_of_getElem (fun k hk => ?_)
  have hlen : (arcs 𝒟 C).length = (𝒟.cell C).R.N := by simp [arcs]
  have hk' : k < (𝒟.cell C).R.N := hlen ▸ hk
  have h1 : (arcs 𝒟 C)[k] = 𝒟.side C ⟨k, hk'⟩ := by simp [arcs]
  have h2 : (arcs 𝒟 C)[(k + 1) % (arcs 𝒟 C).length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)) =
      𝒟.side C (nxt ⟨k, hk'⟩) := by
    simp only [arcs, List.getElem_ofFn, List.length_ofFn]
    congr 1
    exact Fin.ext (by simp [nxt_val])
  rw [h1, h2]
  refine ⟨corner_arc 𝒟 hvert C _, ?_⟩
  rw [Cs_side, Cs_side]

private structure State (𝒯s : Finset 𝒟.ιE) (𝒞 : Finset 𝒟.ιC) (G : Finset 𝒟.ιE)
    (ws : List (𝒟.ιE × Bool)) : Prop where
  hG : G ⊆ 𝒯s
  hGin : ∀ g ∈ G, Cside 𝒟 g true ∈ 𝒞 ∧ Cside 𝒟 g false ∈ 𝒞
  hcard : G.card + 1 = 𝒞.card
  hnd : ws.Nodup
  hmem : ∀ q : 𝒟.ιE × Bool, q ∈ ws ↔ (Cs 𝒟 q ∈ 𝒞 ∧ q.1 ∉ G)
  hcyc : Cyc (Corner 𝒟 G) ws

private lemma state_init (hvert : Function.Injective 𝒟.vert) (𝒯s : Finset 𝒟.ιE) (C₀ : 𝒟.ιC) :
    State 𝒟 𝒯s {C₀} ∅ (arcs 𝒟 C₀) where
  hG := Finset.empty_subset _
  hGin := fun g hg => absurd hg (Finset.notMem_empty g)
  hcard := by simp
  hnd := arcs_nodup 𝒟 C₀
  hmem := fun q => by simp [mem_arcs]
  hcyc := cyc_arcs 𝒟 hvert ∅ C₀

private lemma state_step (hvert : Function.Injective 𝒟.vert) {𝒯s : Finset 𝒟.ιE}
    (hT : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s)
    {𝒞 : Finset 𝒟.ιC} {G : Finset 𝒟.ιE} {ws : List (𝒟.ιE × Bool)} (hS : State 𝒟 𝒯s 𝒞 G ws)
    (h𝒞 : 𝒞 ≠ Finset.univ) :
    ∃ (𝒞' : Finset 𝒟.ιC) (G' : Finset 𝒟.ιE) (ws' : List (𝒟.ιE × Bool)),
      State 𝒟 𝒯s 𝒞' G' ws' ∧ 𝒞'.card = 𝒞.card + 1 := by
  classical

  have h𝒞ne : 𝒞.Nonempty := Finset.card_pos.1 (by have := hS.hcard; omega)
  obtain ⟨Cin, hCin⟩ := h𝒞ne
  obtain ⟨Cout, hCout⟩ : ∃ D, D ∉ 𝒞 := by
    by_contra hall
    push Not at hall
    exact h𝒞 (Finset.eq_univ_of_forall hall)

  obtain ⟨g, hg𝒯s, hcross⟩ := exists_crossing _ _ hT hCin hCout
  obtain ⟨σ, hin, hout⟩ : ∃ σ : Bool, Cside 𝒟 g σ ∈ 𝒞 ∧ Cside 𝒟 g (!σ) ∉ 𝒞 := by
    by_cases ht : Cside 𝒟 g true ∈ 𝒞
    · exact ⟨true, ht, fun hf => hcross ⟨fun _ => hf, fun _ => ht⟩⟩
    · refine ⟨false, ?_, ht⟩
      by_contra hf
      exact hcross ⟨fun h => absurd h ht, fun h => absurd h hf⟩

  have hgG : g ∉ G := by
    intro hgG
    obtain ⟨h1, h2⟩ := hS.hGin g hgG
    cases σ
    · exact hout h1
    · exact hout h2
  have hboth : Cside 𝒟 g true ∈ insert (Cside 𝒟 g (!σ)) 𝒞 ∧
      Cside 𝒟 g false ∈ insert (Cside 𝒟 g (!σ)) 𝒞 := by
    cases σ
    · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hin⟩
    · exact ⟨Finset.mem_insert_of_mem hin, Finset.mem_insert_self _ _⟩
  have hq_in : ∀ q : 𝒟.ιE × Bool, q.1 = g → Cs 𝒟 q ∈ 𝒞 → q = (g, σ) := by
    intro q hq1 hq
    obtain ⟨q₁, q₂⟩ := q
    simp only at hq1
    subst hq1
    by_cases h : q₂ = σ
    · rw [h]
    · exfalso
      have hq₂ : q₂ = !σ := by cases σ <;> cases q₂ <;> simp_all
      rw [hq₂] at hq
      exact hout hq
  have hq_out : ∀ q : 𝒟.ιE × Bool, q.1 = g → Cs 𝒟 q = Cside 𝒟 g (!σ) → q = (g, !σ) := by
    intro q hq1 hq
    obtain ⟨q₁, q₂⟩ := q
    simp only at hq1
    subst hq1
    by_cases h : q₂ = !σ
    · rw [h]
    · exfalso
      have hq₂ : q₂ = σ := by cases σ <;> cases q₂ <;> simp_all
      rw [hq₂] at hq
      exact hout (by rw [← hq]; exact hin)
  set a : 𝒟.ιE × Bool := (g, σ) with ha_def
  set b : 𝒟.ιE × Bool := (g, !σ) with hb_def
  set C' : 𝒟.ιC := Cside 𝒟 g (!σ) with hC'_def
  have hC'𝒞 : C' ∉ 𝒞 := hout
  have ha_ws : a ∈ ws := (hS.hmem a).2 ⟨hin, hgG⟩
  have hb_arcs : b ∈ arcs 𝒟 C' := (mem_arcs 𝒟 C' b).2 rfl

  obtain ⟨n₁, l₁, hrot₁⟩ := exists_rotate_cons ha_ws
  obtain ⟨n₂, l₂, hrot₂⟩ := exists_rotate_cons hb_arcs
  have hnd₁ : (a :: l₁).Nodup := hrot₁ ▸ List.nodup_rotate.2 hS.hnd
  have hnd₂ : (b :: l₂).Nodup := hrot₂ ▸ List.nodup_rotate.2 (arcs_nodup 𝒟 C')
  have hmem₁ : ∀ q, q ∈ l₁ ↔ (q ∈ ws ∧ q ≠ a) := by
    intro q
    have h := (List.mem_rotate (l := ws) (a := q) (n := n₁))
    rw [hrot₁, List.mem_cons] at h
    rw [← h]
    constructor
    · intro hq
      exact ⟨Or.inr hq, fun hqa => (List.nodup_cons.1 hnd₁).1 (hqa ▸ hq)⟩
    · rintro ⟨hqa | hq, hne⟩
      · exact absurd hqa hne
      · exact hq
  have hmem₂ : ∀ q, q ∈ l₂ ↔ (Cs 𝒟 q = C' ∧ q ≠ b) := by
    intro q
    have h := (List.mem_rotate (l := arcs 𝒟 C') (a := q) (n := n₂))
    rw [hrot₂, List.mem_cons, mem_arcs] at h
    rw [← h]
    constructor
    · intro hq
      exact ⟨Or.inr hq, fun hqb => (List.nodup_cons.1 hnd₂).1 (hqb ▸ hq)⟩
    · rintro ⟨hqb | hq, hne⟩
      · exact absurd hqb hne
      · exact hq
  have hcyc₁ : Cyc (Corner 𝒟 G) (a :: l₁) := hrot₁ ▸ cyc_rotate n₁ hS.hcyc
  have hcyc₂ : Cyc (Corner 𝒟 G) (b :: l₂) := hrot₂ ▸ cyc_rotate n₂ (cyc_arcs 𝒟 hvert G C')
  have hGG' : G ⊆ insert g G := Finset.subset_insert g G
  have hg' : g ∈ insert g G := Finset.mem_insert_self g G
  refine ⟨insert C' 𝒞, insert g G, l₁ ++ l₂, ?_, Finset.card_insert_of_notMem hC'𝒞⟩
  refine
    { hG := Finset.insert_subset hg𝒯s hS.hG
      hGin := ?_
      hcard := by
        have := hS.hcard
        rw [Finset.card_insert_of_notMem hgG, Finset.card_insert_of_notMem hC'𝒞]; omega
      hnd := ?_
      hmem := ?_
      hcyc := ?_ }
  · intro g' hg'
    rcases Finset.mem_insert.1 hg' with rfl | hg'G
    · cases σ
      · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hin⟩
      · exact ⟨Finset.mem_insert_of_mem hin, Finset.mem_insert_self _ _⟩
    · obtain ⟨h1, h2⟩ := hS.hGin g' hg'G
      exact ⟨Finset.mem_insert_of_mem h1, Finset.mem_insert_of_mem h2⟩
  · refine List.Nodup.append (List.nodup_cons.1 hnd₁).2 (List.nodup_cons.1 hnd₂).2 ?_
    intro q hq₁ hq₂
    have hq₁' := ((hS.hmem q).1 ((hmem₁ q).1 hq₁).1).1
    have hq₂' := ((hmem₂ q).1 hq₂).1
    exact hC'𝒞 (hq₂' ▸ hq₁')
  · intro q
    rw [List.mem_append, hmem₁, hmem₂, hS.hmem, Finset.mem_insert, Finset.mem_insert]
    constructor
    · rintro (⟨⟨hq𝒞, hqG⟩, hqa⟩ | ⟨hqC', hqb⟩)
      · refine ⟨Or.inr hq𝒞, ?_⟩
        rintro (hqg | hqG')
        · exact hqa (hq_in q hqg hq𝒞)
        · exact hqG hqG'
      · refine ⟨Or.inl hqC', ?_⟩
        rintro (hqg | hqG')
        · exact hqb (hq_out q hqg hqC')
        · exfalso
          have h2 := hS.hGin q.1 hqG'
          have hCs : Cs 𝒟 q ∈ 𝒞 := by
            obtain ⟨q₁, q₂⟩ := q
            cases q₂
            · exact h2.2
            · exact h2.1
          rw [hqC'] at hCs
          exact hC'𝒞 hCs
    · rintro ⟨hq𝒞, hqG'⟩
      have hqg : q.1 ≠ g := fun h => hqG' (Or.inl h)
      have hqG : q.1 ∉ G := fun h => hqG' (Or.inr h)
      rcases hq𝒞 with hqC' | hq𝒞
      · exact Or.inr ⟨hqC', fun h => hqg (by rw [h])⟩
      · exact Or.inl ⟨⟨hq𝒞, hqG⟩, fun h => hqg (by rw [h])⟩
  · refine cyc_splice hcyc₁ hcyc₂ (fun x y h => corner_mono 𝒟 hGG' h) ?_ ?_
    · intro x y hxa hby
      exact corner_junction 𝒟 hGG' hg' σ hxa hby
    · intro x y hxb hay
      have hay' : Corner 𝒟 G (g, !(!σ)) y := by rw [Bool.not_not]; exact hay
      exact corner_junction 𝒟 hGG' hg' (!σ) hxb hay'

private lemma state_final (hvert : Function.Injective 𝒟.vert) {𝒯s : Finset 𝒟.ιE}
    (hT : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s) :
    ∀ (n : ℕ) (𝒞 : Finset 𝒟.ιC) (G : Finset 𝒟.ιE) (ws : List (𝒟.ιE × Bool)),
      State 𝒟 𝒯s 𝒞 G ws → 𝒞.card + n = Fintype.card 𝒟.ιC →
      ∃ (G : Finset 𝒟.ιE) (ws : List (𝒟.ιE × Bool)), State 𝒟 𝒯s Finset.univ G ws
  | 0, 𝒞, G, ws, hS, hn => by
    have h𝒞 : 𝒞 = Finset.univ := Finset.eq_univ_of_card 𝒞 (by simpa using hn)
    exact ⟨G, ws, h𝒞 ▸ hS⟩
  | n + 1, 𝒞, G, ws, hS, hn => by
    have h𝒞 : 𝒞 ≠ Finset.univ := by
      rintro rfl
      rw [Finset.card_univ] at hn
      omega
    obtain ⟨𝒞', G', ws', hS', hcard'⟩ := state_step 𝒟 hvert hT hS h𝒞
    exact state_final hvert hT n 𝒞' G' ws' hS' (by omega)

end Dissection

section W3

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  (𝒟 : CellDissection F)

private lemma filter_indicator (P : 𝒟.ιE → Prop) [DecidablePred P] (x : 𝒟.ιE) (s : ℤ) :
    (∑ f with P f, s * (if x = f then (1 : ℤ) else 0)) = s * (if P x then 1 else 0) := by
  rw [Finset.sum_filter,
    Finset.sum_eq_single x (fun f _ hne => by rw [if_neg (Ne.symm hne), mul_zero, ite_self])
      (fun h => absurd (Finset.mem_univ x) h)]
  rw [if_pos rfl]
  split_ifs <;> ring

private lemma letter_bd (q : 𝒟.ιE × Bool) (w : 𝒟.ιV) :
    (if q.2 then (1 : ℤ) else -1) * (if (𝒟.ends q.1).2 = w then 1 else 0) -
        (if q.2 then (1 : ℤ) else -1) * (if (𝒟.ends q.1).1 = w then 1 else 0) =
      (if eV 𝒟 q = w then 1 else 0) - (if sV 𝒟 q = w then 1 else 0) := by
  obtain ⟨e, σ⟩ := q
  cases σ <;> simp only [eV, sV, Bool.false_eq_true, if_false, if_true] <;> ring

private lemma w3_of_w1 {𝒯s : Finset 𝒟.ιE} {m : ℕ} [NeZero m]
    (wd : ZMod m ≃ {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s})
    (hW1 : ∀ i : ZMod m, eV 𝒟 (wd i).1 = sV 𝒟 (wd (i + 1)).1)
    (e : 𝒟.ιE) (he : e ∉ 𝒯s) :
    let αe : ZMod m := wd.symm ⟨(e, true), he⟩
    let βe : ZMod m := wd.symm ⟨(e, false), he⟩
    let pe : 𝒟.ιE → ℤ := fun e' =>
      ∑ i ∈ Finset.univ.filter
          (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
        (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
    ∀ w : 𝒟.ιV,
      (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f) := by
  intro αe βe pe w
  classical
  set d : ℕ := (βe - αe).val with hd_def
  set S : Finset (ZMod m) :=
    Finset.univ.filter (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < d) with hS_def

  have hcollapse : ∀ (P : 𝒟.ιE → Prop) [DecidablePred P],
      (∑ f with P f, pe f) =
        ∑ i ∈ S, (if (wd i).1.2 then (1 : ℤ) else -1) * (if P (wd i).1.1 then 1 else 0) := by
    intro P _
    simp only [pe]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact filter_indicator 𝒟 P _ _
  rw [hcollapse, hcollapse, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => letter_bd 𝒟 (wd i).1 w)]

  have hαβ : αe ≠ βe := by
    intro h
    have := wd.symm.injective h
    simp at this
  have hd_pos : 0 < d := by
    rw [hd_def]
    exact Nat.pos_of_ne_zero (fun h0 => hαβ (by
      have := (ZMod.val_eq_zero _).1 h0
      exact (sub_eq_zero.1 this).symm))
  have hd_lt : d < m := ZMod.val_lt _
  have hαd : αe + (d : ZMod m) = βe := by
    rw [hd_def, ZMod.natCast_zmod_val, add_sub_cancel]
  have hS : S = (Finset.Ico 1 d).image (fun k : ℕ => αe + (k : ZMod m)) := by
    ext i
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_Ico]
    constructor
    · rintro ⟨hiα, hid⟩
      refine ⟨(i - αe).val, ⟨?_, hid⟩, ?_⟩
      · exact Nat.pos_of_ne_zero (fun h0 => hiα (sub_eq_zero.1 ((ZMod.val_eq_zero _).1 h0)))
      · rw [ZMod.natCast_zmod_val, add_sub_cancel]
    · rintro ⟨k, ⟨hk1, hkd⟩, rfl⟩
      have hkval : ((k : ZMod m) - 0).val = k := by
        rw [sub_zero, ZMod.val_cast_of_lt (hkd.trans hd_lt)]
      refine ⟨?_, ?_⟩
      · intro h
        have h' : (k : ZMod m) = 0 := by
          have := congrArg (fun z => z - αe) h
          simpa using this
        rw [h'] at hkval
        simp only [sub_zero, ZMod.val_zero] at hkval
        omega
      · rw [add_sub_cancel_left, ZMod.val_cast_of_lt (hkd.trans hd_lt)]
        exact hkd
  have hinj : Set.InjOn (fun k : ℕ => αe + (k : ZMod m)) ↑(Finset.Ico 1 d) := by
    intro k hk k' hk' hkk'
    simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
    have h := add_left_cancel hkk'
    have := congrArg ZMod.val h
    rwa [ZMod.val_cast_of_lt (hk.2.trans hd_lt), ZMod.val_cast_of_lt (hk'.2.trans hd_lt)] at this
  rw [hS, Finset.sum_image hinj]

  set u : ℕ → ℤ := fun k => if eV 𝒟 (wd (αe + (k : ZMod m))).1 = w then 1 else 0 with hu_def
  have hterm : ∀ k ∈ Finset.Ico 1 d,
      ((if eV 𝒟 (wd (αe + (k : ZMod m))).1 = w then (1 : ℤ) else 0) -
        (if sV 𝒟 (wd (αe + (k : ZMod m))).1 = w then 1 else 0)) = u k - u (k - 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk' : αe + (k : ZMod m) = αe + ((k - 1 : ℕ) : ZMod m) + 1 := by
      rw [add_assoc, ← Nat.cast_add_one, Nat.sub_add_cancel hk.1]
    have hsv : sV 𝒟 (wd (αe + (k : ZMod m))).1 = eV 𝒟 (wd (αe + ((k - 1 : ℕ) : ZMod m))).1 := by
      rw [hk', ← hW1]
    simp only [hu_def, hsv]
  rw [Finset.sum_congr rfl hterm, Finset.sum_Ico_eq_sum_range]
  have hshift : ∀ j ∈ Finset.range (d - 1), u (1 + j) - u (1 + j - 1) = u (j + 1) - u j := by
    intro j _
    rw [show 1 + j - 1 = j by omega, add_comm]
  rw [Finset.sum_congr rfl hshift, Finset.sum_range_sub]

  have hlast : u (d - 1) = if (𝒟.ends e).2 = w then 1 else 0 := by
    have h1 : αe + ((d - 1 : ℕ) : ZMod m) + 1 = βe := by
      rw [← hαd, add_assoc, ← Nat.cast_add_one, Nat.sub_add_cancel hd_pos]
    have h2 : eV 𝒟 (wd (αe + ((d - 1 : ℕ) : ZMod m))).1 = (𝒟.ends e).2 := by
      rw [hW1, h1]
      simp [βe, sV]
    show (if eV 𝒟 (wd (αe + ((d - 1 : ℕ) : ZMod m))).1 = w then (1 : ℤ) else 0) = _
    rw [h2]
  have hfirst : u 0 = if (𝒟.ends e).2 = w then 1 else 0 := by
    have h0 : eV 𝒟 (wd (αe + ((0 : ℕ) : ZMod m))).1 = (𝒟.ends e).2 := by
      simp [αe, eV]
    show (if eV 𝒟 (wd (αe + ((0 : ℕ) : ZMod m))).1 = w then (1 : ℤ) else 0) = _
    rw [h0]
  rw [hlast, hfirst, sub_self]

end W3

end SolWORD

open SolWORD in
theorem solution
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F)
    (hvert : Function.Injective 𝒟.vert)
    (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
        fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
      ∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0))
    (hL : ∃ e : 𝒟.ιE, e ∉ 𝒯s) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    let startV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).1 else (𝒟.ends q.1).2
    let endV : 𝒟.ιE × Bool → 𝒟.ιV := fun q => if q.2 then (𝒟.ends q.1).2 else (𝒟.ends q.1).1
    let L := {q : 𝒟.ιE × Bool // q.1 ∉ 𝒯s}
    let m := Fintype.card L
    ∃ (_ : NeZero m) (wd : ZMod m ≃ L),
      (∀ i : ZMod m, endV (wd i).1 = startV (wd (i + 1)).1 ∧
        ∃ cs : List 𝒟.ιC, cs.head? = some (Cside (wd i).1.1 (wd i).1.2) ∧
          cs.getLast? = some (Cside (wd (i + 1)).1.1 (wd (i + 1)).1.2) ∧
          cs.IsChain (fun D D' => ∃ g ∈ 𝒯s,
            ((Cside g true = D ∧ Cside g false = D') ∨
             (Cside g true = D' ∧ Cside g false = D)) ∧
            (endV (wd i).1 = (𝒟.ends g).1 ∨ endV (wd i).1 = (𝒟.ends g).2))) ∧
      ∀ (e : 𝒟.ιE) (he : e ∉ 𝒯s),
        let αe : ZMod m := wd.symm ⟨(e, true), he⟩
        let βe : ZMod m := wd.symm ⟨(e, false), he⟩
        let pe : 𝒟.ιE → ℤ := fun e' =>
          ∑ i ∈ Finset.univ.filter
              (fun i : ZMod m => i ≠ αe ∧ (i - αe).val < (βe - αe).val),
            (if (wd i).1.2 then (1 : ℤ) else (-1)) * (if (wd i).1.1 = e' then 1 else 0)
        ∀ w : 𝒟.ιV,
          (∑ f with (𝒟.ends f).2 = w, pe f) = (∑ f with (𝒟.ends f).1 = w, pe f) := by
  intro Cside startV endV L m
  classical
  obtain ⟨e₀, he₀⟩ := hL
  have hT : IsTree (fun e => SolWORD.Cside 𝒟 e true) (fun e => SolWORD.Cside 𝒟 e false) 𝒯s := h𝒯s
  haveI : Nonempty 𝒟.ιC := ⟨SolWORD.Cside 𝒟 e₀ true⟩

  have hS₀ := state_init 𝒟 hvert 𝒯s (SolWORD.Cside 𝒟 e₀ true)
  obtain ⟨G, ws, hS⟩ := state_final 𝒟 hvert hT (Fintype.card 𝒟.ιC - 1) _ _ _ hS₀ (by
    have : 1 ≤ Fintype.card 𝒟.ιC := Fintype.card_pos
    simp only [Finset.card_singleton]; omega)

  have hG : G = 𝒯s := by
    refine Finset.eq_of_subset_of_card_le hS.hG ?_
    have h1 := spanningTree_card _ _ 𝒯s hT
    have h2 := hS.hcard
    rw [Finset.card_univ] at h2
    omega
  have hmemL : ∀ q : 𝒟.ιE × Bool, q ∈ ws ↔ q.1 ∉ 𝒯s := fun q => by
    rw [hS.hmem, hG]; simp
  have hcyc : Cyc (Corner 𝒟 𝒯s) ws := hG ▸ hS.hcyc

  have hlen : ws.length = m := by
    rw [← List.toFinset_card_of_nodup hS.hnd]
    show ws.toFinset.card = Fintype.card L
    rw [Fintype.card_subtype]
    congr 1
    ext q
    simp [hmemL]
  haveI hm : NeZero m := ⟨(Fintype.card_pos_iff.2 ⟨(⟨(e₀, true), he₀⟩ : L)⟩).ne'⟩
  have hidx : ∀ i : ZMod m, i.val < ws.length := fun i => by rw [hlen]; exact ZMod.val_lt i
  let f : ZMod m → L := fun i => ⟨ws[i.val]'(hidx i), (hmemL _).1 (List.getElem_mem _)⟩
  have hf_inj : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    simp only [f] at h
    exact ZMod.val_injective m ((hS.hnd.getElem_inj_iff).1 h)
  have hf_bij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, by rw [ZMod.card]⟩
  let wd : ZMod m ≃ L := Equiv.ofBijective f hf_bij
  have hwd : ∀ i, (wd i).1 = ws[i.val]'(hidx i) := fun i => rfl

  have hsucc : ∀ i : ZMod m, (i + 1).val = (i.val + 1) % ws.length := fun i => by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, hlen]
  have hcorner : ∀ i : ZMod m, Corner 𝒟 𝒯s (wd i).1 (wd (i + 1)).1 := fun i => by
    rw [hwd, hwd]
    have := cyc_getElem hcyc i.val (hidx i)
    simpa only [hsucc i] using this
  refine ⟨hm, wd, fun i => ⟨(hcorner i).1, ?_⟩, fun e he => ?_⟩
  · obtain ⟨cs, hh, hl, hchain⟩ := exists_list_of_rtg (hcorner i).2
    exact ⟨cs, hh, hl, hchain⟩
  · exact w3_of_w1 𝒟 wd (fun i => (hcorner i).1) e he

end S_AlgebraicCurve_CellDissection_exists_polygonWord
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_polygonWord (solution)

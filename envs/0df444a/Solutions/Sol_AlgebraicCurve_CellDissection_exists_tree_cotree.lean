-- Prove2me | solution 1 for AlgebraicCurve.CellDissection.exists_tree_cotree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9eee1a12-e336-5e7d-af19-1f544491edd1

import Definitions.Def_AlgebraicCurve_CellDissection
import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_RegularDifferentials
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_CellDissection_exists_tree_cotree

open AlgebraicCurve
open scoped Real

namespace SolTREES

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

private def IsConn (S : Finset E) : Prop :=
  ∀ u v : V, ∃ c : E → ℤ, (∀ e ∉ S, c e = 0) ∧ ∀ w, bd hd tl c w =
    (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)

private def IsTree (T : Finset E) : Prop :=
  ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧ ∀ w, bd hd tl c w =
    (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)

private def adj (S : Finset E) : V → V → Prop :=
  fun a b => ∃ e ∈ S, (hd e = a ∧ tl e = b) ∨ (hd e = b ∧ tl e = a)

private abbrev IsWalkConn (S : Finset E) : Prop :=
  ∀ u v : V, Relation.ReflTransGen (adj hd tl S) u v

private lemma isConn_walk (S : Finset E) (hconn : IsConn hd tl S) : IsWalkConn hd tl S := by
  classical
  intro u v
  by_contra hcontra
  haveI : DecidablePred (Relation.ReflTransGen (adj hd tl S) u ·) :=
    Classical.decPred _
  set A : Finset V := Finset.univ.filter (Relation.ReflTransGen (adj hd tl S) u ·)
  have huA : u ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ u, .refl⟩
  have hvA : v ∉ A := fun h => hcontra (Finset.mem_filter.mp h).2
  have hedge : ∀ e ∈ S, hd e ∈ A ↔ tl e ∈ A := by
    intro e he
    constructor <;> intro h
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e, he, .inl ⟨rfl, rfl⟩⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e, he, .inr ⟨rfl, rfl⟩⟩⟩
  obtain ⟨c, hcS, hcbd⟩ := hconn u v
  have key : ∀ e, (if hd e ∈ A then c e else 0) = (if tl e ∈ A then c e else 0) := by
    intro e
    by_cases heS : e ∈ S
    · by_cases h : hd e ∈ A
      · rw [if_pos h, if_pos ((hedge e heS).mp h)]
      · rw [if_neg h, if_neg (fun h' => h ((hedge e heS).mpr h'))]
    · rw [hcS e heS]; split_ifs <;> rfl
  have heq : ∀ g : E → V, (∑ w ∈ A, ∑ e with g e = w, c e) =
      ∑ e, (if g e ∈ A then c e else 0) := by
    intro g
    rw [show (∑ w ∈ A, ∑ e with g e = w, c e) =
          ∑ w ∈ A, ∑ e, (if g e = w then c e else 0) from
        Finset.sum_congr rfl (fun w _ => Finset.sum_filter _ _),
      Finset.sum_comm]
    exact Finset.sum_congr rfl (fun e _ => Finset.sum_ite_eq A (g e) (fun _ => c e))
  have hsum0 : ∑ w ∈ A, bd hd tl c w = 0 := by
    unfold bd; simp_rw [Finset.sum_sub_distrib, heq hd, heq tl, key, sub_self]
  have hsum1 : ∑ w ∈ A, bd hd tl c w = -1 := by
    simp_rw [hcbd, Finset.sum_sub_distrib, Finset.sum_ite_eq' A v (fun _ => (1:ℤ)),
      Finset.sum_ite_eq' A u (fun _ => (1:ℤ)), if_pos huA, if_neg hvA]
    ring
  exact absurd (hsum0.symm.trans hsum1) (by norm_num)

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

private lemma chain_of_walk (S : Finset E) {u v : V}
    (hw : Relation.ReflTransGen (adj hd tl S) u v) :
    ∃ c : E → ℤ, (∀ e ∉ S, c e = 0) ∧
      ∀ w, bd hd tl c w = (if w = v then (1:ℤ) else 0) - (if w = u then 1 else 0) := by
  classical
  induction hw with
  | refl => exact ⟨0, fun _ _ => rfl, fun w => by unfold bd; simp⟩
  | @tail a b _ hab ih =>
    obtain ⟨c₀, hc₀S, hc₀bd⟩ := ih
    obtain ⟨e, heS, heab⟩ := hab
    rcases heab with ⟨hha, htb⟩ | ⟨hhb, hta⟩
    · refine ⟨c₀ + (-1 : ℤ) • (fun e' => if e' = e then (1:ℤ) else 0), ?_, ?_⟩
      · intro e' he'
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hc₀S e' he',
          if_neg (fun h : e' = e => he' (h ▸ heS))]; ring
      · intro w
        rw [bd_add, bd_smul, bd_single, hc₀bd w, hha, htb]; split_ifs <;> ring
    · refine ⟨c₀ + (fun e' => if e' = e then (1:ℤ) else 0), ?_, ?_⟩
      · intro e' he'
        simp only [Pi.add_apply, hc₀S e' he',
          if_neg (fun h : e' = e => he' (h ▸ heS))]; ring
      · intro w
        rw [bd_add, bd_single, hc₀bd w, hhb, hta]; split_ifs <;> ring

private lemma exists_spanningTree (S : Finset E) (hconn : IsConn hd tl S) :
    ∃ T ⊆ S, IsTree hd tl T ∧ IsWalkConn hd tl T := by
  classical

  have hne : {T : Finset E | T ⊆ S ∧ IsWalkConn hd tl T}.Nonempty :=
    ⟨S, le_refl S, isConn_walk hd tl S hconn⟩
  obtain ⟨T, ⟨hTS, hTwalk⟩, hTmin⟩ :=
    Set.Finite.exists_minimalFor id _ (Set.toFinite _) hne
  refine ⟨T, hTS, ?_, hTwalk⟩

  intro u v
  obtain ⟨c, hcT, hcbd⟩ := chain_of_walk hd tl T (hTwalk u v)
  refine ⟨c, ⟨hcT, hcbd⟩, ?_⟩
  rintro c' ⟨hc'T, hc'bd⟩

  funext e
  by_contra hdne

  have heT : e ∈ T := by
    by_contra he; exact hdne (by rw [hc'T e he, hcT e he])
  set d : E → ℤ := fun e' => c' e' - c e'
  have hdT : ∀ e' ∉ T, d e' = 0 := fun e' he' => by
    simp only [d, hc'T e' he', hcT e' he', sub_zero]
  have hdbd : ∀ w, bd hd tl d w = 0 := fun w => by
    rw [show d = c' - c from rfl, bd_sub, hc'bd w, hcbd w, sub_self]
  have hde : d e ≠ 0 := fun h => hdne (by simp only [d] at h; linarith)

  have hTerase : ¬ IsWalkConn hd tl (T.erase e) := by
    intro hwalk'
    have hsub : T.erase e ⊆ S := (Finset.erase_subset e T).trans hTS
    have hmem : T.erase e ∈ {T' | T' ⊆ S ∧ IsWalkConn hd tl T'} := ⟨hsub, hwalk'⟩
    exact absurd (hTmin hmem (Finset.erase_subset e T) heT) (Finset.notMem_erase e T)

  unfold IsWalkConn at hTerase
  simp only [not_forall] at hTerase
  obtain ⟨u₀, v₀, hv₀⟩ := hTerase
  haveI : DecidablePred (Relation.ReflTransGen (adj hd tl (T.erase e)) u₀ ·) :=
    Classical.decPred _
  set A : Finset V := Finset.univ.filter (Relation.ReflTransGen (adj hd tl (T.erase e)) u₀ ·)
  have hedge : ∀ e' ∈ T.erase e, hd e' ∈ A ↔ tl e' ∈ A := by
    intro e' he'
    refine ⟨fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e', he', .inl ⟨rfl, rfl⟩⟩⟩,
      fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp h).2.tail ⟨e', he', .inr ⟨rfl, rfl⟩⟩⟩⟩
  have hAne : ¬ (hd e ∈ A ↔ tl e ∈ A) := by

    intro hiff
    have hallT : ∀ e' ∈ T, hd e' ∈ A ↔ tl e' ∈ A := by
      intro e' he'
      rcases eq_or_ne e' e with rfl | hne'
      · exact hiff
      · exact hedge e' (Finset.mem_erase.mpr ⟨hne', he'⟩)

    apply hv₀
    have hu₀A : u₀ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, .refl⟩

    have hv₀A : v₀ ∈ A := by
      have h := hTwalk u₀ v₀
      clear hv₀
      induction h with
      | refl => exact hu₀A
      | @tail a b _ hab ih =>
        obtain ⟨e', he'T, heab⟩ := hab
        rcases heab with ⟨hha, htb⟩ | ⟨hhb, hta⟩
        · rw [← htb]; exact (hallT e' he'T).mp (hha ▸ ih)
        · rw [← hhb]; exact (hallT e' he'T).mpr (hta ▸ ih)
    exact (Finset.mem_filter.mp hv₀A).2

  have hsum : ∑ w ∈ A, bd hd tl d w =
      (if hd e ∈ A then d e else 0) - (if tl e ∈ A then d e else 0) := by
    rw [sum_bd_eq]
    rw [Finset.sum_eq_single e]
    · intro e' _ hne'
      by_cases he'T : e' ∈ T
      · have h := hedge e' (Finset.mem_erase.mpr ⟨hne', he'T⟩)
        by_cases hh : hd e' ∈ A
        · rw [if_pos hh, if_pos (h.mp hh), sub_self]
        · rw [if_neg hh, if_neg (fun h' => hh (h.mpr h')), sub_self]
      · rw [hdT e' he'T]; split_ifs <;> ring
    · intro h; exact absurd (Finset.mem_univ e) h
  have hsum0 : ∑ w ∈ A, bd hd tl d w = 0 :=
    Finset.sum_eq_zero (fun w _ => hdbd w)
  rw [hsum0] at hsum

  by_cases hhd : hd e ∈ A <;> by_cases htl : tl e ∈ A
  · exact absurd (iff_of_true hhd htl) hAne
  · rw [if_pos hhd, if_neg htl] at hsum; exact hde (by linarith)
  · rw [if_neg hhd, if_pos htl] at hsum; exact hde (by linarith)
  · exact absurd (iff_of_false hhd htl) hAne

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

  have hkey : ∀ e ∈ T, ∀ e', c (hd e) e' - c (tl e) e' = if e' = e then (1:ℤ) else 0 := by
    intro e heT
    have heq := (hT (tl e) (hd e)).unique
      (y₁ := fun e' => c (hd e) e' - c (tl e) e')
      (y₂ := fun e' => if e' = e then (1 : ℤ) else 0)
      ⟨fun e' he' => by
          show c (hd e) e' - c (tl e) e' = 0
          rw [(hcspec (hd e)).1 e' he', (hcspec (tl e)).1 e' he']; ring,
       fun w => by
        rw [show (fun e' => c (hd e) e' - c (tl e) e') = c (hd e) - c (tl e) from rfl,
          bd_sub, (hcspec (hd e)).2 w, (hcspec (tl e)).2 w]; ring⟩
      ⟨fun e' he' => if_neg (fun (h : e' = e) => he' (h ▸ heT)),
       fun w => bd_single hd tl e w⟩
    exact fun e' => congrFun heq e'

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

section CellDissection

variable {F : Type*} [Field F] [Algebra ℂ F]
  [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
  (𝒟 : CellDissection F)

private abbrev hdΓ : 𝒟.ιE → 𝒟.ιV := fun e => (𝒟.ends e).2
private abbrev tlΓ : 𝒟.ιE → 𝒟.ιV := fun e => (𝒟.ends e).1

private noncomputable abbrev Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
  fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1

private def cellBdryChain (C : 𝒟.ιC) : 𝒟.ιE → ℤ := fun e =>
  ∑ k : Fin (𝒟.cell C).R.N,
    (if (𝒟.side C k).2 then (1 : ℤ) else (-1)) * (if (𝒟.side C k).1 = e then 1 else 0)

private def nxt {N : ℕ} (k : Fin N) : Fin N :=
  if h : k.val + 1 < N then ⟨k.val + 1, h⟩ else ⟨0, k.pos⟩

private lemma nxt_bijective {N : ℕ} : Function.Bijective (nxt (N := N)) := by
  rw [← Finite.injective_iff_bijective]
  intro k k' h
  simp only [nxt] at h
  split_ifs at h with h1 h2 h2
  · exact Fin.ext (by simpa using Fin.mk.inj_iff.1 h)
  · simp at h
  · simp at h
  · exact Fin.ext (by omega)

private lemma nxt_val {N : ℕ} (j : Fin N) : (nxt j).val = (j.val + 1) % N := by
  simp only [nxt]
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have hj := j.isLt
    have heq : j.val + 1 = N := by omega
    simp [heq]

private lemma nxt_iterate_val {N : ℕ} (k : Fin N) (m : ℕ) :
    (nxt^[m] k).val = (k.val + m) % N := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt k.isLt]
  | succ n ih =>
    rw [Function.iterate_succ', Function.comp_apply, nxt_val, ih,
      Nat.mod_add_mod, Nat.add_assoc]

private lemma cell_bdry_periodic (C : AlgebraicCurve.Cell F) (φ : ℝ) :
    C.bdry (φ + 2 * π) = C.bdry φ := by
  unfold AlgebraicCurve.Cell.bdry AlgebraicCurve.RadialRegion.loop
  rw [C.R.hper,
    show ((φ + 2 * π : ℝ) : ℂ) * Complex.I = ↑φ * Complex.I + 2 * ↑π * Complex.I from by
      push_cast; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private lemma bd_cellBdryChain (hvert : Function.Injective 𝒟.vert) :
    ∀ C w, bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w = 0 := by
  classical
  intro C w

  set sV : Fin (𝒟.cell C).R.N → 𝒟.ιV := fun k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1 else (𝒟.ends (𝒟.side C k).1).2
    with hsV_def
  set eV : Fin (𝒟.cell C).R.N → 𝒟.ιV := fun k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).2 else (𝒟.ends (𝒟.side C k).1).1
    with heV_def

  have hfilt : ∀ (P : 𝒟.ιE → Prop) [DecidablePred P] (x : 𝒟.ιE) (s : ℤ),
      (∑ e with P e, s * (if x = e then (1 : ℤ) else 0)) =
      s * (if P x then 1 else 0) := by
    intro P _ x s
    rw [Finset.sum_filter,
      Finset.sum_eq_single x (fun b _ hne => by rw [if_neg (Ne.symm hne), mul_zero, ite_self])
        (fun h => absurd (Finset.mem_univ x) h), if_pos rfl]
    split_ifs <;> ring

  have hbd_eq : bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w =
      ∑ k, ((if eV k = w then (1:ℤ) else 0) - (if sV k = w then 1 else 0)) := by
    unfold bd cellBdryChain
    rw [Finset.sum_comm (t := Finset.univ (α := Fin (𝒟.cell C).R.N)),
        Finset.sum_comm (t := Finset.univ (α := Fin (𝒟.cell C).R.N)),
        ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hfilt (fun e => hdΓ 𝒟 e = w), hfilt (fun e => tlΓ 𝒟 e = w)]
    simp only [hdΓ, tlΓ, hsV_def, heV_def]
    by_cases hσ : (𝒟.side C k).2 <;>
      simp only [hσ, if_true] <;>
      split_ifs <;> ring

  have hcorner : ∀ k, eV k = sV (nxt k) := by
    intro k
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
    simp only [heV_def, hsV_def]
    rw [← h1, ← h2, hb]
  rw [hbd_eq]
  simp_rw [hcorner, Finset.sum_sub_distrib]
  rw [Fintype.sum_bijective nxt nxt_bijective
    (fun k => if sV (nxt k) = w then (1:ℤ) else 0)
    (fun k => if sV k = w then (1:ℤ) else 0) (fun k => rfl)]
  ring

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

private lemma sum_side_indicator (e : 𝒟.ιE) (σ : Bool) (C : 𝒟.ιC) :
    (∑ k : Fin (𝒟.cell C).R.N, if 𝒟.side C k = (e, σ) then (1 : ℤ) else 0) =
      if Cside 𝒟 e σ = C then 1 else 0 := by
  classical
  by_cases h : Cside 𝒟 e σ = C
  · obtain ⟨k₀, hk₀⟩ := (Cside_eq_iff 𝒟 e σ C).mp h
    rw [if_pos h, Finset.sum_eq_single k₀]
    · rw [if_pos hk₀]
    · intro k' _ hne
      rw [if_neg]
      intro hk'
      have : (⟨C, k'⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨C, k₀⟩ :=
        𝒟.side_bij.injective (hk'.trans hk₀.symm)
      exact hne (by injection this)
    · intro h'; exact absurd (Finset.mem_univ k₀) h'
  · rw [if_neg h, Finset.sum_eq_zero]
    intro k _
    rw [if_neg]
    intro hk
    exact h ((Cside_eq_iff 𝒟 e σ C).mpr ⟨k, hk⟩)

private lemma cellBdryChain_eq (C : 𝒟.ιC) (e : 𝒟.ιE) :
    cellBdryChain 𝒟 C e =
      (if Cside 𝒟 e true = C then (1 : ℤ) else 0) -
      (if Cside 𝒟 e false = C then 1 else 0) := by
  classical
  unfold cellBdryChain
  have hrw : ∀ k, (if (𝒟.side C k).2 then (1 : ℤ) else (-1)) *
      (if (𝒟.side C k).1 = e then 1 else 0) =
      (if 𝒟.side C k = (e, true) then 1 else 0) -
      (if 𝒟.side C k = (e, false) then 1 else 0) := by
    intro k
    obtain ⟨e', σ⟩ := 𝒟.side C k
    by_cases he' : e' = e <;> rcases σ <;>
      simp only [he', if_true, if_false, Prod.mk.injEq, and_true, and_false,
        mul_one, mul_zero, sub_zero, zero_sub, reduceCtorEq, sub_self]
  simp_rw [hrw, Finset.sum_sub_distrib, sum_side_indicator]

private lemma Γconn (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v) :
    IsConn (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ := by
  classical

  set sV : ∀ C : 𝒟.ιC, Fin (𝒟.cell C).R.N → 𝒟.ιV := fun C k =>
    if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1 else (𝒟.ends (𝒟.side C k).1).2

  have hintra : ∀ (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N),
      adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ (sV C k) (sV C (nxt k)) := by
    intro C k
    refine ⟨(𝒟.side C k).1, Finset.mem_univ _, ?_⟩

    have heV : sV C (nxt k) =
        if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).2
        else (𝒟.ends (𝒟.side C k).1).1 := by
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
      simp only [sV]
      rw [← h1, ← h2, hb]
    have hsVk : sV C k = if (𝒟.side C k).2 then (𝒟.ends (𝒟.side C k).1).1
        else (𝒟.ends (𝒟.side C k).1).2 := rfl
    simp only [hdΓ, tlΓ]
    by_cases hσ : (𝒟.side C k).2
    · rw [show sV C k = (𝒟.ends (𝒟.side C k).1).1 from hsVk.trans (if_pos hσ),
        show sV C (nxt k) = (𝒟.ends (𝒟.side C k).1).2 from heV.trans (if_pos hσ)]
      exact .inr ⟨rfl, rfl⟩
    · rw [show sV C k = (𝒟.ends (𝒟.side C k).1).2 from hsVk.trans (if_neg hσ),
        show sV C (nxt k) = (𝒟.ends (𝒟.side C k).1).1 from heV.trans (if_neg hσ)]
      exact .inl ⟨rfl, rfl⟩

  have hcell : ∀ (C : 𝒟.ιC) (k k' : Fin (𝒟.cell C).R.N),
      Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k) (sV C k') := by
    intro C k k'
    suffices h : ∀ m, Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ)
        (sV C k) (sV C (nxt^[m] k)) by
      have heq : nxt^[k'.val + (𝒟.cell C).R.N - k.val] k = k' := by
        apply Fin.ext
        rw [nxt_iterate_val]
        have hk := k.isLt; have hk' := k'.isLt
        rw [show k.val + (k'.val + (𝒟.cell C).R.N - k.val) = k'.val + (𝒟.cell C).R.N
          from by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hk']
      exact heq ▸ h (k'.val + (𝒟.cell C).R.N - k.val)
    intro m
    induction m with
    | zero => exact .refl
    | succ n ih =>
      rw [Function.iterate_succ']
      exact ih.tail (hintra C (nxt^[n] k))

  have hcross : ∀ C C' : 𝒟.ιC, ∀ (k₀ : Fin (𝒟.cell C).R.N) (k₀' : Fin (𝒟.cell C').R.N),
      Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k₀) (sV C' k₀') := by
    intro C C' k₀ k₀'
    suffices h : ∀ C C', Relation.ReflTransGen
        (fun A B : 𝒟.ιC => ∃ (k : Fin (𝒟.cell A).R.N) (k' : Fin (𝒟.cell B).R.N),
          (𝒟.side A k).1 = (𝒟.side B k').1) C C' →
        ∀ (k₀ : Fin (𝒟.cell C).R.N), ∃ (k' : Fin (𝒟.cell C').R.N),
          Relation.ReflTransGen (adj (hdΓ 𝒟) (tlΓ 𝒟) Finset.univ) (sV C k₀) (sV C' k') by
      obtain ⟨k', hk'⟩ := h C C' (𝒟.conn C C') k₀
      exact hk'.trans (hcell C' k' k₀')
    intro C C' hconn
    induction hconn with
    | refl => exact fun k₀ => ⟨k₀, .refl⟩
    | @tail B B' _ hBB' ih =>
      intro k₀
      obtain ⟨kB, hkB⟩ := ih k₀
      obtain ⟨k, k', hedge⟩ := hBB'
      by_cases hsame : (𝒟.side B k).2 = (𝒟.side B' k').2
      ·
        have hinj : (⟨B, k⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨B', k'⟩ :=
          𝒟.side_bij.injective (a₁ := ⟨B, k⟩) (a₂ := ⟨B', k'⟩) (Prod.ext hedge hsame)
        obtain rfl : B = B' := congrArg Sigma.fst hinj
        exact ⟨k', hkB.trans (hcell B kB k')⟩
      ·
        refine ⟨k', (hkB.trans (hcell B kB k)).tail ?_⟩
        refine ⟨(𝒟.side B k).1, Finset.mem_univ _, ?_⟩
        have hopp : (𝒟.side B' k').2 = !(𝒟.side B k).2 := by
          revert hsame
          rcases (𝒟.side B k).2 <;> rcases (𝒟.side B' k').2 <;> simp
        simp only [sV, hdΓ, tlΓ, ← hedge, hopp]
        by_cases hσ : (𝒟.side B k).2 <;>
          simp only [hσ, Bool.not_true, Bool.not_false, if_true, if_false,
            Bool.false_eq_true]
        · exact .inr ⟨trivial, trivial⟩
        · exact .inl ⟨trivial, trivial⟩

  have hevery : ∀ v : 𝒟.ιV, ∃ (C : 𝒟.ιC) (k : Fin (𝒟.cell C).R.N), sV C k = v := by
    intro v
    obtain ⟨e, he⟩ := hends v

    rcases he with htl | hhd
    ·
      set p := Function.surjInv 𝒟.side_bij.surjective (e, true)
      have hp := Function.surjInv_eq 𝒟.side_bij.surjective (e, true)
      refine ⟨p.1, p.2, ?_⟩
      simp only [sV, show (𝒟.side p.1 p.2) = (e, true) from hp]
      exact htl
    · set p := Function.surjInv 𝒟.side_bij.surjective (e, false)
      have hp := Function.surjInv_eq 𝒟.side_bij.surjective (e, false)
      refine ⟨p.1, p.2, ?_⟩
      simp only [sV, show (𝒟.side p.1 p.2) = (e, false) from hp,
        if_neg (by simp : ¬ (false = true))]
      exact hhd

  intro u v
  obtain ⟨Cu, ku, hu⟩ := hevery u
  obtain ⟨Cv, kv, hv⟩ := hevery v
  exact chain_of_walk _ _ _ (hu ▸ hv ▸ hcross Cu Cv ku kv)

private lemma Γstar_conn : IsConn (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
    Finset.univ := by
  classical
  intro C C'
  induction 𝒟.conn C C' with
  | refl => exact ⟨0, fun e he => absurd (Finset.mem_univ e) he, fun w => by unfold bd; simp⟩
  | @tail A B _ hstep ih =>
    obtain ⟨c₀, _, hc₀⟩ := ih
    obtain ⟨k, k', hkk'⟩ := hstep
    set e := (𝒟.side A k).1 with he_def
    have hA : Cside 𝒟 e (𝒟.side A k).2 = A :=
      (Cside_eq_iff 𝒟 e (𝒟.side A k).2 A).mpr ⟨k, Prod.ext he_def.symm rfl⟩
    have hB : Cside 𝒟 e (𝒟.side B k').2 = B :=
      (Cside_eq_iff 𝒟 e (𝒟.side B k').2 B).mpr ⟨k', Prod.ext (he_def ▸ hkk'.symm) rfl⟩
    by_cases hAB : A = B
    · subst hAB; exact ⟨c₀, fun e' he' => absurd (Finset.mem_univ e') he', hc₀⟩
    have hσ : (𝒟.side A k).2 ≠ (𝒟.side B k').2 := by
      intro hσeq
      have : (⟨A, k⟩ : Σ D, Fin (𝒟.cell D).R.N) = ⟨B, k'⟩ :=
        𝒟.side_bij.injective (Prod.ext (he_def ▸ hkk') hσeq)
      exact hAB (congrArg Sigma.fst this)
    set sgn : ℤ := if (𝒟.side A k).2 then -1 else 1
    refine ⟨c₀ + sgn • (fun e' => if e' = e then (1:ℤ) else 0),
      fun e' he' => absurd (Finset.mem_univ e') he', fun D => ?_⟩
    rw [bd_add, bd_smul, hc₀ D, bd_single]
    cases hσA : (𝒟.side A k).2 with
    | false =>
      have hσB : (𝒟.side B k').2 = true := by
        cases h : (𝒟.side B k').2
        · exact absurd (hσA.trans h.symm) hσ
        · rfl
      rw [show Cside 𝒟 e true = B from hσB ▸ hB,
          show Cside 𝒟 e false = A from hσA ▸ hA]
      simp only [sgn, hσA, reduceCtorEq, if_false, one_mul]
      split_ifs <;> ring
    | true =>
      have hσB : (𝒟.side B k').2 = false := by
        cases h : (𝒟.side B k').2
        · rfl
        · exact absurd (hσA.trans h.symm) hσ
      rw [show Cside 𝒟 e true = A from hσA ▸ hA,
          show Cside 𝒟 e false = B from hσB ▸ hB]
      simp only [sgn, hσA, if_true, neg_one_mul, neg_sub]
      split_ifs <;> ring

private lemma Γconn_sdiff_cotree (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (𝒯s : Finset 𝒟.ιE)
    (h𝒯s : IsTree (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) 𝒯s) :
    IsConn (hdΓ 𝒟) (tlΓ 𝒟) 𝒯sᶜ := by
  classical

  set Cp := fun g => Cside 𝒟 g true
  have hchain : ∀ C : 𝒟.ιC, ∀ g ∈ 𝒯s, ∃! c : 𝒟.ιE → ℤ,
      (∀ e ∉ 𝒯s, c e = 0) ∧ ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) c D =
        (if D = C then (1 : ℤ) else 0) - (if D = Cp g then 1 else 0) :=
    fun C g _ => h𝒯s (Cp g) C

  set ch : 𝒟.ιE → 𝒟.ιC → 𝒟.ιE → ℤ :=
    fun g C => if hg : g ∈ 𝒯s then Classical.choose (hchain C g hg).exists else 0
  have hch_spec : ∀ g ∈ 𝒯s, ∀ C, (∀ e ∉ 𝒯s, ch g C e = 0) ∧
      ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false) (ch g C) D =
        (if D = C then (1 : ℤ) else 0) - (if D = Cp g then 1 else 0) := by
    intro g hg C
    simp only [ch, dif_pos hg]
    exact Classical.choose_spec (hchain C g hg).exists
  set Ag : 𝒟.ιE → Finset 𝒟.ιC := fun g => Finset.univ.filter (fun C => ch g C g = 0)

  have hCp_mem : ∀ g ∈ 𝒯s, Cp g ∈ Ag g := by
    intro g hg

    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have h0 : (fun _ : 𝒟.ιE => (0 : ℤ)) = ch g (Cp g) :=
      (hchain (Cp g) g hg).unique ⟨fun _ _ => rfl, fun D => by unfold bd; simp⟩
        (hch_spec g hg (Cp g))
    rw [← h0]
  have hCm_notmem : ∀ g ∈ 𝒯s, Cside 𝒟 g false ∉ Ag g := by
    intro g hg hmem

    have hPδg : (∀ e ∉ 𝒯s, (if e = g then (-1:ℤ) else 0) = 0) ∧
        ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
          (fun e => if e = g then (-1:ℤ) else 0) D =
          (if D = Cside 𝒟 g false then (1:ℤ) else 0) - (if D = Cp g then 1 else 0) := by
      refine ⟨fun e he => if_neg (fun (heq : e = g) => he (heq ▸ hg)), fun D => ?_⟩
      have heq : (fun e => if e = g then (-1:ℤ) else 0) =
          (-1 : ℤ) • (fun e => if e = g then (1:ℤ) else 0) :=
        funext (fun e => by simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring)
      rw [heq, bd_smul, bd_single]; split_ifs <;> ring
    have hδg : ch g (Cside 𝒟 g false) = (fun e => if e = g then (-1 : ℤ) else 0) :=
      (hchain (Cside 𝒟 g false) g hg).unique (hch_spec g hg _) hPδg
    simp only [Ag, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    rw [hδg] at hmem; simp at hmem
  have hAg_edge : ∀ g ∈ 𝒯s, ∀ g' ∈ 𝒯s, g' ≠ g →
      (Cside 𝒟 g' true ∈ Ag g ↔ Cside 𝒟 g' false ∈ Ag g) := by
    intro g hg g' hg' hne

    have hδg' : ∀ e, ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e =
        if e = g' then (1 : ℤ) else 0 := by
      have hP1 : (∀ e ∉ 𝒯s,
            ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e = 0) ∧
          ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
            (fun e => ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e) D =
            (if D = Cside 𝒟 g' true then (1:ℤ) else 0) -
            (if D = Cside 𝒟 g' false then 1 else 0) := by
        refine ⟨fun e he => ?_, fun D => ?_⟩
        · rw [(hch_spec g hg (Cside 𝒟 g' true)).1 e he,
            (hch_spec g hg (Cside 𝒟 g' false)).1 e he]; ring
        · have h1 := (hch_spec g hg (Cside 𝒟 g' true)).2 D
          have h2 := (hch_spec g hg (Cside 𝒟 g' false)).2 D
          rw [show (fun e => ch g (Cside 𝒟 g' true) e - ch g (Cside 𝒟 g' false) e) =
                ch g (Cside 𝒟 g' true) - ch g (Cside 𝒟 g' false) from rfl,
            bd_sub, h1, h2]; ring
      have hP2 : (∀ e ∉ 𝒯s, (if e = g' then (1:ℤ) else 0) = 0) ∧
          ∀ D, bd (fun e => Cside 𝒟 e true) (fun e => Cside 𝒟 e false)
            (fun e => if e = g' then (1:ℤ) else 0) D =
            (if D = Cside 𝒟 g' true then (1:ℤ) else 0) -
            (if D = Cside 𝒟 g' false then 1 else 0) :=
        ⟨fun e he => if_neg (fun (heq : e = g') => he (heq ▸ hg')),
         fun D => bd_single _ _ g' D⟩
      exact fun e => congrFun
        ((h𝒯s (Cside 𝒟 g' false) (Cside 𝒟 g' true)).unique hP1 hP2) e
    simp only [Ag, Finset.mem_filter, Finset.mem_univ, true_and]
    have hkey := hδg' g
    rw [if_neg (fun h : g = g' => hne h.symm)] at hkey
    omega

  set q : 𝒟.ιE → 𝒟.ιE → ℤ := fun g e => ∑ C ∈ Ag g, cellBdryChain 𝒟 C e
  have hq_cycle : ∀ g ∈ 𝒯s, ∀ w, bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w = 0 := by
    intro g hg w
    have hsum : bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w =
        ∑ C ∈ Ag g, bd (hdΓ 𝒟) (tlΓ 𝒟) (cellBdryChain 𝒟 C) w := by
      simp only [q]; rw [bd_finsum]
    rw [hsum, Finset.sum_eq_zero (fun C _ => bd_cellBdryChain 𝒟 hvert C w)]
  have hq_eq : ∀ g e, q g e =
      (if Cside 𝒟 e true ∈ Ag g then (1 : ℤ) else 0) -
      (if Cside 𝒟 e false ∈ Ag g then 1 else 0) := by
    intro g e
    simp only [q]
    simp_rw [cellBdryChain_eq, Finset.sum_sub_distrib,
      Finset.sum_ite_eq (Ag g) (Cside 𝒟 e true) (fun _ => (1:ℤ)),
      Finset.sum_ite_eq (Ag g) (Cside 𝒟 e false) (fun _ => (1:ℤ))]
  have hq_g : ∀ g ∈ 𝒯s, q g g = 1 := by
    intro g hg
    rw [hq_eq, if_pos (hCp_mem g hg), if_neg (hCm_notmem g hg)]; ring
  have hq_g' : ∀ g ∈ 𝒯s, ∀ g' ∈ 𝒯s, g' ≠ g → q g g' = 0 := by
    intro g hg g' hg' hne
    rw [hq_eq]
    rcases (hAg_edge g hg g' hg' hne) with h
    by_cases hm : Cside 𝒟 g' true ∈ Ag g
    · rw [if_pos hm, if_pos (h.mp hm)]; ring
    · rw [if_neg hm, if_neg (fun h' => hm (h.mpr h'))]; ring

  intro u v
  obtain ⟨c, _, hcbd⟩ := Γconn 𝒟 hvert hends u v
  refine ⟨fun e => c e - ∑ g ∈ 𝒯s, c g * q g e, ?_, ?_⟩
  · intro e he
    rw [Finset.mem_compl, not_not] at he
    rw [sub_eq_zero, Finset.sum_eq_single e]
    · rw [hq_g e he, mul_one]
    · intro g hg hne
      rw [hq_g' g hg e he (Ne.symm hne), mul_zero]
    · intro h; exact absurd he h
  · intro w
    have hbd_sub : bd (hdΓ 𝒟) (tlΓ 𝒟) (fun e => c e - ∑ g ∈ 𝒯s, c g * q g e) w =
        bd (hdΓ 𝒟) (tlΓ 𝒟) c w -
        ∑ g ∈ 𝒯s, c g * bd (hdΓ 𝒟) (tlΓ 𝒟) (q g) w := by
      have heq : (fun e => c e - ∑ g ∈ 𝒯s, c g * q g e) =
          c - (fun e => ∑ g ∈ 𝒯s, ((c g) • (q g)) e) :=
        funext (fun e => by simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul])
      rw [heq, bd_sub, bd_finsum]
      congr 1
      exact Finset.sum_congr rfl (fun g _ => bd_smul (hdΓ 𝒟) (tlΓ 𝒟) (c g) (q g) w)
    rw [hbd_sub, hcbd w,
      Finset.sum_eq_zero (fun g hg => by rw [hq_cycle g hg w, mul_zero]), sub_zero]

end CellDissection

end SolTREES

open SolTREES in
theorem solution
    {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (𝒟 : CellDissection F) [Nonempty 𝒟.ιC]
    (hvert : Function.Injective 𝒟.vert)
    (hends : ∀ v : 𝒟.ιV, ∃ e : 𝒟.ιE, (𝒟.ends e).1 = v ∨ (𝒟.ends e).2 = v)
    (hEuler : (Fintype.card 𝒟.ιV : ℤ) - (Fintype.card 𝒟.ιE : ℤ) + (Fintype.card 𝒟.ιC : ℤ)
      = 2 - 2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ)) :
    let Cside : 𝒟.ιE → Bool → 𝒟.ιC :=
      fun e s => (Function.surjInv 𝒟.side_bij.surjective (e, s)).1
    ∃ (𝒯 𝒯s : Finset 𝒟.ιE),
      (∀ u v : 𝒟.ιV, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯, c e = 0) ∧
        ∀ w, (∑ e with (𝒟.ends e).2 = w, c e) - (∑ e with (𝒟.ends e).1 = w, c e) =
          (if w = v then (1 : ℤ) else 0) - (if w = u then 1 else 0)) ∧
      (∀ C C' : 𝒟.ιC, ∃! c : 𝒟.ιE → ℤ, (∀ e ∉ 𝒯s, c e = 0) ∧
        ∀ D, (∑ e with Cside e true = D, c e) - (∑ e with Cside e false = D, c e) =
          (if D = C' then (1 : ℤ) else 0) - (if D = C then 1 else 0)) ∧
      Disjoint 𝒯 𝒯s ∧
      (𝒯 ∪ 𝒯s)ᶜ.card = 2 * Module.finrank ℂ ↥(regularDifferentials ℂ F) ∧
      ∀ u v : 𝒟.ιV, Relation.ReflTransGen
        (fun a b => ∃ e ∈ 𝒯, 𝒟.ends e = (a, b) ∨ 𝒟.ends e = (b, a)) u v := by
  classical

  have hCne : Nonempty 𝒟.ιC := ‹_›
  rcases isEmpty_or_nonempty 𝒟.ιV with hVe | hVne
  ·
    exfalso
    obtain ⟨C⟩ := hCne
    have hN : 1 ≤ (𝒟.cell C).R.N := by
      by_contra hN0
      have hN0' : (𝒟.cell C).R.N = 0 := by omega
      have h0 := (𝒟.cell C).R.hφ0
      have hN := (𝒟.cell C).R.hφN
      rw [show (Fin.last (𝒟.cell C).R.N) = (0 : Fin ((𝒟.cell C).R.N + 1)) from
        Fin.ext (by simp [hN0', Fin.val_last])] at hN
      rw [h0] at hN
      exact Real.two_pi_pos.ne hN
    have hne : Nonempty (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N) :=
      ⟨⟨C, ⟨0, hN⟩⟩⟩
    obtain ⟨p⟩ := hne
    have he : Nonempty 𝒟.ιE := ⟨(𝒟.side p.1 p.2).1⟩
    obtain ⟨e⟩ := he
    exact hVe.elim (𝒟.ends e).1

  obtain ⟨𝒯s, _, h𝒯s, _⟩ := exists_spanningTree (fun e => SolTREES.Cside 𝒟 e true)
    (fun e => SolTREES.Cside 𝒟 e false) Finset.univ (Γstar_conn 𝒟)

  obtain ⟨𝒯, h𝒯sub, h𝒯, h𝒯walk⟩ := exists_spanningTree (hdΓ 𝒟) (tlΓ 𝒟) 𝒯sᶜ
    (Γconn_sdiff_cotree 𝒟 hvert hends 𝒯s h𝒯s)
  refine ⟨𝒯, 𝒯s, h𝒯, h𝒯s, ?_, ?_, ?_⟩
  ·
    exact Finset.disjoint_left.mpr (fun e he => Finset.mem_compl.mp (h𝒯sub he))
  ·
    have hTcard := spanningTree_card (hdΓ 𝒟) (tlΓ 𝒟) 𝒯 h𝒯
    have hTscard := spanningTree_card (fun e => SolTREES.Cside 𝒟 e true)
      (fun e => SolTREES.Cside 𝒟 e false) 𝒯s h𝒯s
    have hdisj : Disjoint 𝒯 𝒯s :=
      Finset.disjoint_left.mpr (fun e he => Finset.mem_compl.mp (h𝒯sub he))
    have hunion : (𝒯 ∪ 𝒯s).card = 𝒯.card + 𝒯s.card :=
      Finset.card_union_of_disjoint hdisj
    have hle : (𝒯 ∪ 𝒯s).card ≤ Fintype.card 𝒟.ιE := Finset.card_le_univ _
    have hcompl : ((𝒯 ∪ 𝒯s)ᶜ.card : ℤ) = (Fintype.card 𝒟.ιE : ℤ) - ((𝒯 ∪ 𝒯s).card : ℤ) := by
      have := Finset.card_compl (𝒯 ∪ 𝒯s)
      omega

    have hTZ : (𝒯.card : ℤ) + 1 = (Fintype.card 𝒟.ιV : ℤ) := by exact_mod_cast hTcard
    have hTsZ : (𝒯s.card : ℤ) + 1 = (Fintype.card 𝒟.ιC : ℤ) := by exact_mod_cast hTscard
    have hgoal : ((𝒯 ∪ 𝒯s)ᶜ.card : ℤ) =
        2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) := by
      rw [hcompl]; push_cast [hunion]; linarith [hEuler, hTZ, hTsZ]
    exact_mod_cast hgoal
  ·
    intro u v
    refine Relation.ReflTransGen.mono (fun a b ⟨e, heT, hcase⟩ => ⟨e, heT, ?_⟩) _ _ (h𝒯walk u v)
    unfold hdΓ tlΓ at hcase
    rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      [exact .inr (Prod.ext h2 h1); exact .inl (Prod.ext h2 h1)]

end S_AlgebraicCurve_CellDissection_exists_tree_cotree
end P2MW
export P2MW.S_AlgebraicCurve_CellDissection_exists_tree_cotree (solution)

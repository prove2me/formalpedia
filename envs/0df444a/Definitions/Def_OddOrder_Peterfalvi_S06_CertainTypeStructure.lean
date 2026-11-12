-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeStructure
-- name    : OddOrder_Peterfalvi_S06_CertainTypeStructure
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:17.943984+00:00
-- url     : https://prove2.me/theorems/7813e837-174c-4a65-95ad-a0fd6a28bd21
-- title:
--   Peterfalvi (2.1): the coprime-coset structure lemma
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §2 (The Dade Isometry), p. 10, statement (2.1): let $g\in G$ and $H\le G$ such that $g$ normalizes $H$ and $\langle g\rangle$, $H$ have coprime orders. Then $Hg$ is the disjoint union of $|H:C_H(g)|$ subsets conjugate to $C_H(g)g$ in $H\langle g\rangle$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeStructure.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeStructure.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_DadeIsometryCertain

namespace OddOrder.Peterfalvi.S06

open scoped Pointwise

variable {G : Type*} [Group G]

/-- A uniform exponent `e` with `g^e = g` and `x^e = 1` for all `x ∈ H`, available when
`o(g)` and `|H|` are coprime.  (Chinese remainder: `e ≡ 1 mod o(g)`, `e ≡ 0 mod |H|`.) -/
private theorem exists_uniform_exponent [Finite G] {H : Subgroup G} {g : G}
    (hcop : Nat.Coprime (orderOf g) (Nat.card H)) :
    ∃ e : ℕ, g ^ e = g ∧ ∀ x ∈ H, x ^ e = 1 := by
  obtain ⟨e, he1, he0⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨e, ?_, ?_⟩
  · -- `g ^ e = g ^ 1` from `e ≡ 1 [MOD o(g)]`.
    have : g ^ e = g ^ 1 := pow_eq_pow_iff_modEq.mpr he1
    rwa [pow_one] at this
  · intro x hx
    -- `|H| ∣ e` from `e ≡ 0 [MOD |H|]`, and `o(x) ∣ |H|`, so `o(x) ∣ e`.
    have hdvd : Nat.card H ∣ e := (Nat.modEq_zero_iff_dvd).mp he0
    have hox : orderOf x ∣ Nat.card H := Subgroup.orderOf_dvd_natCard _ hx
    exact orderOf_dvd_iff_pow_eq_one.mp (hox.trans hdvd)

/-- **Peterfalvi (2.1)** (the form used downstream).  Let `g` normalize `H ≤ G` (i.e.
`g · x · g⁻¹ ∈ H` for all `x ∈ H`) and assume `o(g)` is coprime to `|H|`.  Then every
element of the right coset `Hg` is `H`-conjugate to an element of `C_H(g)·g`. -/
theorem coset_conj_into_centralizer_coset [Finite G] {H : Subgroup G} {g : G}
    (hg : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hcop : Nat.Coprime (orderOf g) (Nat.card H))
    {z : G} (hz : z * g⁻¹ ∈ H) :
    ∃ c ∈ H, ∃ w ∈ Subgroup.centralizer ({g} : Set G) ⊓ H, c⁻¹ * z * c = w * g := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({g} : Set G) ⊓ H with hC
  have hCH : C ≤ H := by rw [hC]; exact inf_le_right
  obtain ⟨e, hge, hHe⟩ := exists_uniform_exponent (H := H) (g := g) hcop
  -- Collapse identity: for `w ∈ C`, `(w·g)^e = g`.
  have hcollapse : ∀ w : G, w ∈ C → (w * g) ^ e = g := by
    intro w hw
    rw [hC, Subgroup.mem_inf] at hw
    obtain ⟨hwc, hwH⟩ := hw
    have hwcomm : Commute w g := (Subgroup.mem_centralizer_iff.mp hwc g rfl).symm
    rw [hwcomm.mul_pow, hHe w hwH, hge, one_mul]
  -- `e`-power of a conjugate of `w·g` (`w ∈ C`) is `a·g·a⁻¹`.
  have hconj_pow : ∀ (a w : G), w ∈ C → (a * (w * g) * a⁻¹) ^ e = a * g * a⁻¹ := by
    intro a w hw
    have hmap := map_pow (MulAut.conj a) (w * g) e
    simp only [MulAut.conj_apply] at hmap
    rw [hcollapse w hw] at hmap
    exact hmap.symm
  -- The conjugation map `Φ` from `(H ⧸ C.subgroupOf H) × C` to `G`.
  let Φ : (H ⧸ C.subgroupOf H) × C → G :=
    fun p => ((p.1.out : H) : G) * ((p.2 : G) * g) * ((p.1.out : H) : G)⁻¹
  -- `Φ` lands in the coset `R = Hg`.
  have hsubR : Set.range Φ ⊆ {x : G | x * g⁻¹ ∈ H} := by
    rintro _ ⟨⟨q, w⟩, rfl⟩
    have haH : ((q.out : H) : G) ∈ H := (q.out : H).2
    have hwH : (w : G) ∈ H := hCH w.2
    change (((q.out : H) : G) * ((w : G) * g) * ((q.out : H) : G)⁻¹) * g⁻¹ ∈ H
    have hgag : g * ((q.out : H) : G)⁻¹ * g⁻¹ ∈ H := hg _ (H.inv_mem haH)
    have hrw : (((q.out : H) : G) * ((w : G) * g) * ((q.out : H) : G)⁻¹) * g⁻¹
        = (((q.out : H) : G) * (w : G)) * (g * ((q.out : H) : G)⁻¹ * g⁻¹) := by group
    rw [hrw]
    exact H.mul_mem (H.mul_mem haH hwH) hgag
  -- `Φ` is injective.
  have hinj : Function.Injective Φ := by
    rintro ⟨q, w⟩ ⟨q', w'⟩ hEq
    have haH : ((q.out : H) : G) ∈ H := (q.out : H).2
    have ha'H : ((q'.out : H) : G) ∈ H := (q'.out : H).2
    -- `Φ` value equation, then raise to the `e`-th power.
    have hval : ((q.out : H) : G) * ((w : G) * g) * ((q.out : H) : G)⁻¹
        = ((q'.out : H) : G) * ((w' : G) * g) * ((q'.out : H) : G)⁻¹ := hEq
    have hpow : ((q.out : H) : G) * g * ((q.out : H) : G)⁻¹
        = ((q'.out : H) : G) * g * ((q'.out : H) : G)⁻¹ := by
      have := congrArg (· ^ e) hval
      simpa only [hconj_pow _ (w : G) w.2, hconj_pow _ (w' : G) w'.2] using this
    -- Hence `a'⁻¹ * a` commutes with `g`, so lies in `C`.
    set a : G := ((q.out : H) : G) with ha
    set a' : G := ((q'.out : H) : G) with ha'
    have hcomm : a⁻¹ * a' ∈ Subgroup.centralizer ({g} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      rw [Set.mem_singleton_iff] at hm
      subst hm
      calc m * (a⁻¹ * a') = a⁻¹ * (a * m * a⁻¹) * a' := by group
        _ = a⁻¹ * (a' * m * a'⁻¹) * a' := by rw [hpow]
        _ = (a⁻¹ * a') * m := by group
    have haa'C : a⁻¹ * a' ∈ C := by
      rw [hC, Subgroup.mem_inf]
      exact ⟨hcomm, H.mul_mem (H.inv_mem haH) ha'H⟩
    -- So `q = q'` (same `C.subgroupOf H`-coset).
    have hout : ∀ r : H ⧸ C.subgroupOf H, QuotientGroup.mk (r.out : H) = r :=
      fun r => Quotient.out_eq r
    have hquot : q = q' := by
      have hcoe : (((q.out : H)⁻¹ * (q'.out : H) : ↥H) : G) = a⁻¹ * a' := by
        push_cast; rw [← ha, ← ha']
      have key : ((q.out : H)⁻¹ * (q'.out : H)) ∈ C.subgroupOf H :=
        Subgroup.mem_subgroupOf.mpr (by rw [hcoe]; exact haa'C)
      calc q = QuotientGroup.mk (q.out : H) := (hout q).symm
        _ = QuotientGroup.mk (q'.out : H) := QuotientGroup.eq.mpr key
        _ = q' := hout q'
    subst hquot
    -- Then `w = w'`.
    have hww' : (w : G) = (w' : G) := by
      have h2 : a * ((w : G) * g) * a⁻¹ = a * ((w' : G) * g) * a⁻¹ := hval
      exact mul_right_cancel (mul_left_cancel (mul_right_cancel h2))
    have : w = w' := Subtype.ext hww'
    subst this; rfl
  -- Cardinalities: `|domain Φ| = |H| = |Hg|`.
  have hcardC : Nat.card (C.subgroupOf H) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv
  have hcardDom : Nat.card ((H ⧸ C.subgroupOf H) × C) = Nat.card H := by
    rw [Nat.card_prod, ← hcardC, ← Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf
        H)]
  -- `Hg` (here `R`) has `|H|` elements (the bijection `h ↦ h·g`).
  set R : Set G := {x : G | x * g⁻¹ ∈ H} with hR
  have hRimg : R = (fun h => h * g) '' (H : Set G) := by
    ext x
    constructor
    · intro hx; exact ⟨x * g⁻¹, hx, by group⟩
    · rintro ⟨h, hh, rfl⟩; change h * g * g⁻¹ ∈ H; simpa [mul_assoc] using hh
  have hRcard : R.ncard = Nat.card H := by
    rw [hRimg, Set.ncard_image_of_injective _ (mul_left_injective g)]
    exact (Nat.card_coe_set_eq _).symm
  have hrangeCard : (Set.range Φ).ncard = Nat.card H := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ]
    exact hcardDom
  have hrangeEqR : Set.range Φ = R :=
    Set.eq_of_subset_of_ncard_le hsubR (by rw [hRcard, hrangeCard]) (Set.toFinite R)
  -- Conclude: `z ∈ R = range Φ`, so `z = a·(w·g)·a⁻¹` and `a⁻¹·z·a = w·g`.
  have hzR : z ∈ Set.range Φ := by rw [hrangeEqR]; exact hz
  obtain ⟨⟨q, w⟩, hΦeq⟩ := hzR
  refine ⟨((q.out : H) : G), (q.out : H).2, (w : G), w.2, ?_⟩
  have hval : ((q.out : H) : G) * ((w : G) * g) * ((q.out : H) : G)⁻¹ = z := hΦeq
  rw [← hval]; group

end OddOrder.Peterfalvi.S06

namespace OddOrder.Peterfalvi.S06.Hypothesis

variable {L : Type*} [Group L] [Finite L] (h : Hypothesis L)

/-- **Peterfalvi (2.1) applied to `L = K ⋊ W₁`.**  Every element `z ∈ L − K` is `L`-conjugate
to an element `x·y` with `x ∈ W₁^#` and `y ∈ W₂`.

`z` decomposes as `k·x` (`k ∈ K`, `x ∈ W₁`) by the complement, with `x ≠ 1` since `z ∉ K`;
then `z ∈ K·x` and (2.1) conjugates `z` into `C_K(x)·x = W₂·x = x·W₂`. -/
theorem mem_compl_conj_into_W {z : L} (hz : z ∉ h.K) :
    ∃ c : L, ∃ x ∈ h.W1, x ≠ 1 ∧ ∃ y ∈ h.W2, c⁻¹ * z * c = x * y := by
  -- Complement decomposition `z = k·x`.
  obtain ⟨⟨⟨kk, hk⟩, ⟨u, hu⟩⟩, hku, -⟩ := Subgroup.IsComplement.existsUnique h.isComplement z
  change kk * u = z at hku
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hz (by rw [← hku, mul_one]; exact hk)
  -- Apply the abstract (2.1) with `H = K`, `g = u`.
  have hnorm : ∀ x ∈ h.K, u * x * u⁻¹ ∈ h.K := fun x hx => h.K_normal.conj_mem x hx u
  have hcop : Nat.Coprime (orderOf u) (Nat.card h.K) :=
    h.card_coprime.symm.coprime_dvd_left (Subgroup.orderOf_dvd_natCard _ hu)
  have hzc : z * u⁻¹ ∈ h.K := by rw [← hku, mul_assoc, mul_inv_cancel, mul_one]; exact hk
  obtain ⟨c, _, w, hwC, hcw⟩ := coset_conj_into_centralizer_coset hnorm hcop hzc
  -- `C_K(u) = W₂` (4.2.b).
  have hwW2 : w ∈ h.W2 := by rw [← h.centralizer_W2 u hu hu1]; exact hwC
  -- `c⁻¹ z c = w·u = u·w` (`W₂` centralizes `W₁`).
  refine ⟨c, u, hu, hu1, w, hwW2, ?_⟩
  rw [hcw]
  exact (h.commute_of_mem_W1_of_mem_W2 hu hwW2).symm

end OddOrder.Peterfalvi.S06.Hypothesis



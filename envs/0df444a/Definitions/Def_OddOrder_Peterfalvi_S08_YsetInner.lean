-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner
-- name    : OddOrder_Peterfalvi_S08_YsetInner
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:09:50.209872+00:00
-- url     : https://prove2.me/theorems/ab756f9a-defb-436a-908e-481026e0a10b
-- title:
--   Peterfalvi §8: nilpotent descent and $Y$-set inner products
-- statement:
--   Part of Peterfalvi §8 (pp. 30–37): the nilpotent normal-subgroup descent, filtration structures, and Dade-decomposition inner-product lemmas used by the §8 coherence proof.
--
--   Main definitions: `sharpImage` ($H^\#=H\setminus\{1\}$ as a subset of the ambient $G$ for $H\le L\le G$) and `memberExtensionDecomposition` (the (5.5) member $\nu$-auxiliary decomposition: the running extension $\nu$ as the auxiliary map).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_YsetInner.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_YsetInner.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner_CharacterBreaks

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **In a finite nilpotent group, a nontrivial normal subgroup meets the centre.**
If `N ◁ G` is nontrivial and `G` is finite nilpotent, then `N ⊓ Z(G) ≠ ⊥`.  Proof: take the least
`m` with `N ⊓ ζₘ ≠ ⊥` (the upper central series reaches `⊤`, so `m` exists; `m = k+1 > 0`); a
nontrivial `x ∈ N ⊓ ζ_{k+1}` has `x·y·x⁻¹·y⁻¹ ∈ ζₖ` (definition of `ζ_{k+1}`) and `∈ N` (`N`
normal), so `∈ N ⊓ ζₖ = ⊥` by minimality; hence `x` is central, `x ∈ N ⊓ Z(G)`.

This is the nilpotency central step of Peterfalvi (6.3): `H/M` nilpotent and `A/B` a nontrivial
normal subgroup give `(A/B) ⊓ Z(H/B) ≠ 1`, which (with maximality of `B`) forces `A/B ⊆ Z(H/B)`. -/
theorem isNilpotent_normal_inf_center_ne_bot {Γ : Type*} [Group Γ] [Finite Γ]
    [Group.IsNilpotent Γ] {N : Subgroup Γ} (hN : N.Normal) (hNne : N ≠ ⊥) :
    N ⊓ Subgroup.center Γ ≠ ⊥ := by
  classical
  have hexists : ∃ i, N ⊓ Subgroup.upperCentralSeries Γ i ≠ ⊥ := by
    refine ⟨Group.nilpotencyClass Γ, ?_⟩
    rw [Subgroup.upperCentralSeries_eq_top_iff_nilpotencyClass_le.mpr (le_refl _), inf_top_eq]
    exact hNne
  have hm := Nat.find_spec hexists
  have hm0 : Nat.find hexists ≠ 0 := by
    intro h0
    rw [h0, Subgroup.upperCentralSeries_zero, inf_bot_eq] at hm
    exact hm rfl
  obtain ⟨k, hk_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hkbot : N ⊓ Subgroup.upperCentralSeries Γ k = ⊥ := by
    by_contra h
    exact Nat.find_min hexists (m := k) (by rw [hk_eq]; exact Nat.lt_succ_self k) h
  rw [hk_eq] at hm
  obtain ⟨⟨x, hxmem⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hm
  have hx1 : x ≠ 1 := fun h => hxne (Subtype.ext h)
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxN, hxU⟩ := hxmem
  have hxcenter : x ∈ Subgroup.center Γ := by
    rw [Subgroup.mem_center_iff]
    intro y
    have hcomm_U : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.upperCentralSeries Γ k :=
      Subgroup.mem_upperCentralSeries_succ_iff.mp hxU y
    have hcomm_N : x * y * x⁻¹ * y⁻¹ ∈ N := by
      have hconj : y * x⁻¹ * y⁻¹ ∈ N := hN.conj_mem x⁻¹ (N.inv_mem hxN) y
      have := N.mul_mem hxN hconj
      rwa [← mul_assoc, ← mul_assoc] at this
    have hbot : x * y * x⁻¹ * y⁻¹ = 1 := by
      have hin : x * y * x⁻¹ * y⁻¹ ∈ N ⊓ Subgroup.upperCentralSeries Γ k :=
        Subgroup.mem_inf.mpr ⟨hcomm_N, hcomm_U⟩
      rw [hkbot, Subgroup.mem_bot] at hin
      exact hin
    have h2 : x * y * x⁻¹ = y := mul_inv_eq_one.mp hbot
    conv_lhs => rw [← h2]
    group
  intro hbot
  have : x ∈ N ⊓ Subgroup.center Γ := Subgroup.mem_inf.mpr ⟨hxN, hxcenter⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact hx1 this

/-- **A maximal normal subgroup strictly between `M` and `A`.**
For a finite group, if `M < A` (with `M` normal) there is a normal `B` with `M ≤ B < A` that is
maximal with this property: any normal `C` with `B ≤ C < A` equals `B`.  This is the maximal-`B`
step of the Peterfalvi (6.3) minimal-`A` induction (find a maximal proper normal subgroup below the
minimal coherent `A`). -/
theorem exists_maximal_normal_between {Γ : Type*} [Group Γ] [Finite Γ] {M A : Subgroup Γ}
    [M.Normal] (hMA : M < A) :
    ∃ B : Subgroup Γ, B.Normal ∧ M ≤ B ∧ B < A ∧
      ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B := by
  classical
  have : Finite (Subgroup Γ) := Finite.of_injective (fun H : Subgroup Γ => (H : Set Γ))
    (fun _ _ h => SetLike.coe_injective h)
  obtain ⟨B, hBmem, hBmax⟩ :=
    Set.Finite.exists_maximalFor (id : Subgroup Γ → Subgroup Γ)
      {N | N.Normal ∧ M ≤ N ∧ N < A} (Set.toFinite _) ⟨M, ‹M.Normal›, le_refl M, hMA⟩
  obtain ⟨hBnorm, hMB, hBA⟩ := hBmem
  refine ⟨B, hBnorm, hMB, hBA, fun C hCnorm hBC hCA => ?_⟩
  exact le_antisymm (hBmax ⟨hCnorm, hMB.trans hBC, hCA⟩ hBC) hBC

/-- **Maximality forces centrality** — the central step of Peterfalvi (6.3).

If `H ◁ Γ` is nilpotent and `A`, `B` are normal subgroups of `Γ` with `B < A ≤ H`, where `B` is
maximal among normal subgroups of `Γ` strictly below `A`, then `A/B ⊆ Z(H/B)`.

Indeed `A/B` is a nontrivial normal subgroup of the nilpotent group `H/B`, so `(A/B) ⊓ Z(H/B) ≠ 1`
(`isNilpotent_normal_inf_center_ne_bot`).  Its full preimage `C` in `Γ` is a normal subgroup with
`B < C ≤ A` (`C` is normal because conjugation by `Γ` preserves both `A/B` and the centre of `H/B`);
by maximality of `B`, `C = A`, i.e. `A/B ⊆ Z(H/B)`.

This discharges the `hcentral` hypothesis of `six_three_index_bound` in the minimal-`A`/maximal-`B`
induction of Peterfalvi (6.3). -/
theorem normal_central_of_maximal_normal_below {Γ : Type*} [Group Γ] [Finite Γ]
    {H A B : Subgroup Γ} (hH : H.Normal)
    [A.Normal] [B.Normal]
    [Group.IsNilpotent (↥H ⧸ B.subgroupOf H)] (hAH : A ≤ H) (hBA : B < A)
    (hmax : ∀ C : Subgroup Γ, C.Normal → B ≤ C → C < A → C = B) :
    (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (↥H ⧸ B.subgroupOf H) := by
  classical
  have hNnorm : (B.subgroupOf H).Normal := (‹B.Normal›).subgroupOf H
  have hANnorm : (A.subgroupOf H).Normal := (‹A.Normal›).subgroupOf H
  have hBH : B ≤ H := hBA.le.trans hAH
  -- `mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H`
  have mk_eq_one : ∀ a : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) a = 1 ↔ a ∈ B.subgroupOf H := by
    intro a; rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  -- centrality of `mk' x` ⟺ all commutators `h x h⁻¹ x⁻¹` land in `B.subgroupOf H`
  have center_iff : ∀ x : ↥H,
      QuotientGroup.mk' (B.subgroupOf H) x ∈ Subgroup.center (↥H ⧸ B.subgroupOf H) ↔
        ∀ h : ↥H, h * x * h⁻¹ * x⁻¹ ∈ B.subgroupOf H := by
    intro x
    rw [Subgroup.mem_center_iff]
    refine ⟨fun hx h => ?_, fun hx q => ?_⟩
    · have h2 := hx (QuotientGroup.mk' (B.subgroupOf H) h)
      rw [← mk_eq_one]
      simp only [map_mul, map_inv]
      rw [h2]; group
    · obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf H) q
      have hcomm := (mk_eq_one (h * x * h⁻¹ * x⁻¹)).2 (hx h)
      simp only [map_mul, map_inv] at hcomm
      calc QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x
          = (QuotientGroup.mk' (B.subgroupOf H) h * QuotientGroup.mk' (B.subgroupOf H) x *
              (QuotientGroup.mk' (B.subgroupOf H) h)⁻¹ *
              (QuotientGroup.mk' (B.subgroupOf H) x)⁻¹) *
              (QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h) := by
            group
        _ = QuotientGroup.mk' (B.subgroupOf H) x * QuotientGroup.mk' (B.subgroupOf H) h := by
            rw [hcomm, one_mul]
  -- `A/B` is nontrivial in `H/B`
  have hAbar_ne : (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≠ ⊥ := by
    intro hbot
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    have hAB : A ≤ B := by
      intro y hy
      have hy' : (⟨y, hAH hy⟩ : ↥H) ∈ A.subgroupOf H := Subgroup.mem_subgroupOf.mpr hy
      exact Subgroup.mem_subgroupOf.mp (hbot hy')
    exact lt_irrefl _ (hBA.trans_le hAB)
  -- nilpotency: `(A/B) ⊓ Z(H/B) ≠ 1`
  have hinf := isNilpotent_normal_inf_center_ne_bot
    (Subgroup.Normal.map hANnorm (QuotientGroup.mk' (B.subgroupOf H))
      (QuotientGroup.mk'_surjective _)) hAbar_ne
  -- the pullback subgroup of `Γ`
  set Zc := (Subgroup.center (↥H ⧸ B.subgroupOf H)).comap (QuotientGroup.mk' (B.subgroupOf H))
    with hZc
  set CH := A.subgroupOf H ⊓ Zc with hCH
  set C := CH.map H.subtype with hC
  -- `B ≤ C`
  have hBC : B ≤ C := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hBH]
    apply Subgroup.map_mono
    rw [hCH]
    refine le_inf (Subgroup.subgroupOf_mono H hBA.le) (fun x hx => ?_)
    rw [hZc, Subgroup.mem_comap, (mk_eq_one x).2 hx]
    exact Subgroup.one_mem _
  -- `C ≤ A`
  have hCA : C ≤ A := by
    rw [hC, ← Subgroup.map_subgroupOf_eq_of_le hAH]
    exact Subgroup.map_mono (by rw [hCH]; exact inf_le_left)
  -- `C` is normal in `Γ`
  have hCnorm : C.Normal := by
    rw [hC]
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_map] at hn
    obtain ⟨c, hcCH, rfl⟩ := hn
    rw [hCH, Subgroup.mem_inf] at hcCH
    obtain ⟨hcA, hcZ⟩ := hcCH
    have hc_center : ∀ k : ↥H, k * c * k⁻¹ * c⁻¹ ∈ B.subgroupOf H := by
      apply (center_iff c).mp
      rw [hZc] at hcZ; exact Subgroup.mem_comap.mp hcZ
    have hc'H : g * (c : Γ) * g⁻¹ ∈ H := hH.conj_mem _ c.2 g
    rw [Subgroup.mem_map]
    refine ⟨⟨g * (c : Γ) * g⁻¹, hc'H⟩, ?_, rfl⟩
    rw [hCH, Subgroup.mem_inf]
    refine ⟨Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
    · exact (‹A.Normal›).conj_mem _ (Subgroup.mem_subgroupOf.mp hcA) g
    · rw [hZc, Subgroup.mem_comap, center_iff]
      intro h
      have hkH : g⁻¹ * (h : Γ) * g ∈ H := by
        have := hH.conj_mem (h : Γ) h.2 g⁻¹; rwa [inv_inv] at this
      have hk := hc_center ⟨g⁻¹ * (h : Γ) * g, hkH⟩
      rw [Subgroup.mem_subgroupOf] at hk ⊢
      have hrel : (((h * ⟨g * (c : Γ) * g⁻¹, hc'H⟩ * h⁻¹ *
            (⟨g * (c : Γ) * g⁻¹, hc'H⟩ : ↥H)⁻¹ : ↥H) : Γ))
          = g * (((⟨g⁻¹ * (h : Γ) * g, hkH⟩ * c *
              (⟨g⁻¹ * (h : Γ) * g, hkH⟩ : ↥H)⁻¹ * c⁻¹ : ↥H) : Γ)) * g⁻¹ := by
        push_cast
        group
      rw [hrel]
      exact (‹B.Normal›).conj_mem _ hk g
  -- a nontrivial element of `(A/B) ⊓ Z(H/B)` gives `B ≠ C`
  obtain ⟨⟨q, hqmem⟩, hqne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  rw [Subgroup.mem_inf] at hqmem
  obtain ⟨hqA, hqZ⟩ := hqmem
  rw [Subgroup.mem_map] at hqA
  obtain ⟨c₀, hc₀A, hc₀q⟩ := hqA
  have hq1 : q ≠ 1 := fun hq => hqne (Subtype.ext hq)
  have hc₀CH : c₀ ∈ CH := by
    rw [hCH, Subgroup.mem_inf]
    exact ⟨hc₀A, by rw [hZc, Subgroup.mem_comap, hc₀q]; exact hqZ⟩
  have hc₀C : (c₀ : Γ) ∈ C := by
    rw [hC]; exact Subgroup.mem_map_of_mem H.subtype hc₀CH
  have hc₀notB : (c₀ : Γ) ∉ B := by
    intro hb
    exact hq1 (by rw [← hc₀q]; exact (mk_eq_one c₀).2 (Subgroup.mem_subgroupOf.mpr hb))
  have hBneC : B ≠ C := fun heq => hc₀notB (heq.symm ▸ hc₀C)
  have hBC_lt : B < C := lt_of_le_of_ne hBC hBneC
  have hCeqA : C = A := by
    rcases eq_or_lt_of_le hCA with h | h
    · exact h
    · exact absurd (hmax C hCnorm hBC h) (Ne.symm (ne_of_lt hBC_lt))
  have hCHmap : CH.map H.subtype = A := by rw [← hC, hCeqA]
  have hCHeq : CH = A.subgroupOf H := by
    rw [← Subgroup.map_subtype_inj, hCHmap, Subgroup.map_subgroupOf_eq_of_le hAH]
  have hle : A.subgroupOf H ≤ Zc := by
    rw [← hCHeq, hCH]; exact inf_le_right
  rw [Subgroup.map_le_iff_le_comap, ← hZc]
  exact hle

/-- For `H ≤ G`, the commutator subgroup of the subtype group `↥H` is the `subgroupOf` of the
ambient commutator `⁅H, H⁆`.  In particular `Abelianization ↥H = ↥H ⧸ ⁅H, H⁆.subgroupOf H`, so the
index `|H : ⁅H,H⁆|` equals `|Abelianization ↥H|`. -/
theorem commutator_subgroupOf_self {G : Type*} [Group G] (H : Subgroup G) :
    (⁅H, H⁆ : Subgroup G).subgroupOf H = _root_.commutator ↥H := by
  have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (_root_.commutator ↥H).map H.subtype = ⁅H, H⁆ := by
    change (⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆).map H.subtype = ⁅H, H⁆
    rw [Subgroup.map_commutator, htop]
  rw [← h1]
  exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _

/-- For a finite `p`-group `K`, every irreducible character has degree a power of `p`
(its degree divides `|K| = pⁿ`).  This supplies the `θ = p^m` source-degree fields of the X-chain
step data once `H` is known to be a `p`-group (Peterfalvi (6.5)/(6.6)). -/
theorem exists_primePow_natDegree_of_isPGroup {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hK : IsPGroup p K) (θ : IrreducibleCharacter K) :
    ∃ k : ℕ, (θ : ClassFunction K ℂ) 1 = ((p ^ k : ℕ) : ℂ) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, _hpos, hval, hdvd⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  obtain ⟨N, hN⟩ := hK.exists_card_eq
  rw [hN] at hdvd
  obtain ⟨k, _hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, by rw [hval, hk]⟩

/-- `H^# = H ∖ {1}` viewed as a subset of the ambient group `G`, for `H ≤ L ≤ G`.  This is the
support set `A` of the §4 Dade hypothesis in Peterfalvi (6.8): the nonidentity elements of `H`,
mapped from `↥L` into `G` along the inclusions. -/
def sharpImage {G : Type*} [Group G] {L : Subgroup G} (H : Subgroup ↥L) : Set G :=
  ((Subgroup.map L.subtype H : Subgroup G) : Set G) \ {1}

/-- **(5.6.1) supported-difference pairing: the Dade map `τ` pairs with the coherent extension `ν`
as the source inner product.**

For a supported `u` (`u.support ⊆ A`, e.g. the degree-matched difference `χ − a·χ₁`) and a
*supported* lattice element `δ ∈ ℤ[S₁] ∩ CF(L,A)` (e.g. a member difference `χⱼ − aⱼ·χ₁`), the Dade
image of `u` pairs with the running extension `ν = hS₁.extension` of `δ` exactly as the source pair:
`⟨τ u, ν δ⟩ = ⟨u, δ⟩`.

This is the recurring move of the (5.6.1) coefficient computation (mmd 04.7 L79): the cross terms
`⟨(χ − a·χ₁)^τ, (χⱼ − aⱼ·χ₁)^τ⟩` are evaluated by the Dade isometry on the supported pair, with
`(χⱼ − aⱼ·χ₁)^τ = (χⱼ − aⱼ·χ₁)^{τ₁} = ν δ` since `δ` is supported (`ν = τ` there,
`extends_on_supported`).

Note this does **not** apply with `δ = χ₁` itself: the induced anchor `χ₁ = Ind θ` is *unsupported*
(`χ₁(1) ≠ 0`, so `1 ∈ supp χ₁ ∉ A`), which is precisely why crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a` is not
a direct corollary but needs the full (5.6.1)→(5.6.2) `Y`-collapse. -/
theorem inner_dade_extension_of_supported
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    {u : ClassFunction ↥L ℂ}
    (husupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {δ : ClassFunction ↥L ℂ}
    (hδ : δ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L)) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData) u)
        (hS₁.extension δ) =
      ClassFunction.inner u δ := by
  -- `ν δ = τ δ` since `δ` is supported (the coherent extension agrees with `τ` on `CF(L,A)`).
  rw [hS₁.extends_on_supported δ hδ]
  -- Dade isometry on the supported pair `{u, δ}`.
  have hδsupp : δ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L :=
    (OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hδ).2
  refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
    (S := {u, δ}) ?_ (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl
  · exact husupp
  · exact hδsupp

/-- **(5.2.e) member R-orthogonality `⟨X, ν χ₁⟩ = 0` — the `hXortho` ingredient of
`crux1_of_collapse`.**

The `R(χ)`-part `X = D.X ∈ ℤ[R(χ)]` of the χ-decomposition `D` is orthogonal to the running image
`ν χ₁ = hS₁.extension χ₁` of any member `χ₁ ∈ S₁`, given the member's own `ψ = 0` decomposition `D'`
(so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` by (5.5)) and the family orthogonality `R(χ₁) ⊥ R(χ)` ((5.2.e)).

Per-`α` orthogonality `⟨ν χ₁, α⟩ = 0` for `α ∈ R(χ)` (`inner_extension_member_orthogonal_imageSet`,
from `D'`/`hortho`/`htau1`) is summed over `R(χ)` by `inner_X_eq_zero_of_orthogonal_imageSet` to
give
`⟨ν χ₁, X⟩ = 0`; conjugate symmetry flips it to `⟨X, ν χ₁⟩ = 0`.  The remaining work for the actual
`hXortho` is to *build* `D'` (the member ν-aux decomposition, needing `ν χ₁ ∈ ZIrr` injected since
`IsCoherent` carries no ZIrr-codomain) and `hortho` (the Dade `R(·)`-family orthogonality). -/
theorem inner_decomposition_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Type*} [Group L] [Fintype L] [Invertible (Nat.card L : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S₁ : Set (ClassFunction L ℂ)} {A' : Set L}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁ A')
    {χ ψ chi1 : ClassFunction L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ χ ψ)
    (D' : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := L) (G := G) τ chi1 0)
    (hortho : D'.imageFamily.Orthogonal D.imageFamily)
    (htau1 : D'.tau1 chi1 = hS₁.extension chi1) :
    ClassFunction.inner D.X (hS₁.extension chi1) = 0 := by
  have h1 : ClassFunction.inner (hS₁.extension chi1) D.X = 0 :=
    D.inner_X_eq_zero_of_orthogonal_imageSet
      (fun α hα => OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet
        hS₁ D.imageFamily D' hortho htau1 hα)
  rw [OddOrder.RepresentationTheory.inner_conj_symm, h1, star_zero]

/-- **(5.5) member ν-aux decomposition: the running extension `ν` as the auxiliary isometry `τ₁`.**

For a member `χ ∈ S₁` (non-real irreducible, with `χ̄ ∈ S₁` and `χ̄ − χ` supported), builds the
(5.5)
`ψ = 0` decomposition `D' : CharacterPsiDecomposition τ χ 0` whose **auxiliary isometry `τ₁` is the
running extension `ν = hS₁.extension`** (not the Dade base map `τ`).  Then `D'.tau1 χ = ν χ`
(definitionally) and, via (5.5) (`eq_sum_of_psi_eq_zero`), `ν χ = D'.X ∈ ℤ[R(χ)]`.

This is the member family input that discharges the `D'`/`htau1` hypotheses of
`inner_decomposition_X_extension_member_eq_zero` (and the (5.6.1) λ-form), built from the Dade
`R(χ)` family (`dadeOrthonormalCharacterImageFamilyOfDiff`) and the coherent extension:

* `htau1_inner_eq` — `ν` is a `ℤ[χ−χ̄, χ]`-isometry: both generators lie in `ℤ[S₁]` (since
  `χ, χ̄ ∈ S₁`), where `hS₁.extension_inner_eq` applies;
* `htau1_agrees` — `ν(χ−χ̄) = τ(χ−χ̄)` since `χ−χ̄` is supported (`extends_on_supported`);
* `htau1_mem` — `ν χ ∈ ZIrr G` is the hypothesis `hνZ`.  Since `IsCoherent` gained the
  `extension_mem_ZIrr` field (route A), this is now derivable from `χ ∈ S₁ ⊆ ℤ[S₁]` via
  `hS₁.extension_mem_ZIrr`; callers discharge it from the field (it is kept as an explicit argument
  here only because this `def` predates the field).

The remaining (5.4) orthogonality scalars `⟨χ, 0⟩ = ⟨χ̄, 0⟩ = 0` are trivial and `⟨χ, χ̄⟩ = 0` is
`hχχbar`. -/
noncomputable def memberExtensionDecomposition
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχ_S1 : (χ : ClassFunction ↥L ℂ) ∈ S₁)
    (hχbar_S1 : (χ : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZ : hS₁.extension (χ : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χ : ClassFunction ↥L ℂ) 0 := by
  classical
  have hχmem : (χ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ S₁ := Submodule.subset_span hχ_S1
  have hχbarmem : (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ S₁ :=
    Submodule.subset_span hχbar_S1
  -- The (5.4) sponsoring set `{χ − χ̄, χ − 0}` lies in `ℤ[S₁]`.
  have hle : Submodule.span ℤ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - 0} : Set (ClassFunction ↥L ℂ)) ≤ Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  -- `χ − χ̄` is supported (vanishes off `A`), hence in `ℤ[S₁] ∩ CF(L,A)`.
  have hdiffsupported : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) :=
    OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
      ⟨Submodule.sub_mem _ hχmem hχbarmem, by
        rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
            -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) by abel,
          ClassFunction.support_neg]
        exact hdiffsupp⟩
  exact OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal hdiffsupp)
    hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp)
    (by simp)
    hχχbar

/-- **(5.2.e) conjugate-difference orthogonality via *difference* supports (induced case).**

`⟨(x − x̄)^τ, (χ − χ̄)^τ⟩ = 0` whenever the **conjugate differences** `x̄ − x` and `χ̄ − χ` are
supported in `CF(L,A)` and `x, x̄ ⊥ χ, χ̄`.  Unlike
`dadeIntegralCharacterMap_inner_conjDifference_eq_zero` (which needs the *individual* supports of
`x, x̄, χ, χ̄`), this evaluates the Dade isometry directly on the two supported differences
`x − x̄`,
`χ − χ̄` (`dadeIntegralCharacterMap_inner_eq_on_supported_span` on the set `{x − x̄, χ − χ̄}`), so
it
applies to **induced** `x = Ind θ`, `χ = Ind θ'` whose individual values at `1` are nonzero.  The
reduced source pairing `⟨x − x̄, χ − χ̄⟩` expands to the four cross terms, all zero. -/
theorem inner_dadeDiff_conjDifference_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {x χ : ClassFunction ↥L ℂ}
    (hxdiffsupp : (x.conj - x).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχdiffsupp : (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner x χ = 0) (hxχbar : ClassFunction.inner x χ.conj = 0)
    (hxbarχ : ClassFunction.inner x.conj χ = 0) (hxbarχbar : ClassFunction.inner x.conj χ.conj = 0)
        :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
          (x - x.conj))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
          (χ - χ.conj)) = 0 := by
  classical
  have hS : ∀ s ∈ ({x - x.conj, χ - χ.conj} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show x - x.conj = -(x.conj - x) by abel, ClassFunction.support_neg]; exact hxdiffsupp
    · rw [show χ - χ.conj = -(χ.conj - χ) by abel, ClassFunction.support_neg]; exact hχdiffsupp
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp hS
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    hxχ, hxχbar, hxbarχ, hxbarχbar, sub_self]

/-- **(5.2.e) Dade `R(·)`-family orthogonality via *difference* supports (induced case).**

`R(x) ⊥ R(χ)` for the difference-support Dade families `dadeOrthonormalCharacterImageFamilyOfDiff`
whenever `x, x̄ ⊥ χ, χ̄`.  Mirrors `dadeOrthonormalCharacterImageFamily_orthogonal` but reduces —
via
`toOrthonormalImage_orthogonal` and `orthogonal_of_signedDifference_inner_eq_zero` — to the
*difference-support* orthogonality `inner_dadeDiff_conjDifference_eq_zero`, so it applies to the
**unsupported induced** X-members.  This is the `hortho` ingredient of
`inner_decomposition_X_extension_member_eq_zero`. -/
theorem dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {x χ : IrreducibleCharacter ↥L}
    (hxreal : ¬ ClassFunction.IsReal (x : ClassFunction ↥L ℂ))
    (hxdiffsupp : ((x : ClassFunction ↥L ℂ).conj - (x : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hχdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hxχ : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hxχbar : ClassFunction.inner (x : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hxbarχ : ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hxbarχbar :
      ClassFunction.inner (x : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ).conj = 0) :
    (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp x hxreal
        hxdiffsupp).Orthogonal
      (OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff hyp χ hreal
        hχdiffsupp) := by
  unfold OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
  refine OddOrder.Peterfalvi.S07.CharacterDifferenceImage.toOrthonormalImage_orthogonal _ _
    (OddOrder.Peterfalvi.S07.CharacterDifferenceImage.orthogonal_of_signedDifference_inner_eq_zero
      _ _ ?_)
  rw [← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference,
    ← OddOrder.Peterfalvi.S07.CharacterDifferenceImage.image_eq_signedDifference]
  exact inner_dadeDiff_conjDifference_eq_zero hyp hxdiffsupp hχdiffsupp
    hxχ hxχbar hxbarχ hxbarχbar

/-- **Member-side R-orthogonality `⟨Da.X, ν χ₁⟩ = 0`, fully assembled for the induced `Da`.**

The `hXortho` ingredient of `crux1_of_collapse`, with *every* member-side input discharged from the
injected data: `Da = decompositionDaFromDadeOfDiff` (the χ-decomposition), the member ν-aux
decomposition `D' = memberExtensionDecomposition` of `χ₁` (so `ν χ₁ = D'.X ∈ ℤ[R(χ₁)]` and
`D'.tau1 χ₁ = ν χ₁` definitionally), and the difference-support family orthogonality `R(χ₁) ⊥ R(χ)`
(`dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal`).  Chained through
`inner_decomposition_X_extension_member_eq_zero`.

This leaves only the (5.6.1)/(5.6.2) `Y`-collapse `Da.Y = a·ν χ₁` as the remaining input for crux1
(via `crux1_of_collapse` + `Da.tau1_image`). -/
theorem inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ chi1 : IrreducibleCharacter ↥L) {a : ℕ}
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (chi1 : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (chi1 : ClassFunction ↥L ℂ)) = 0)
    (hχχbar' : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hrealc1 : ¬ ClassFunction.IsReal (chi1 : ClassFunction ↥L ℂ))
    (hdiffsuppc1 : ((chi1 : ClassFunction ↥L ℂ).conj - (chi1 : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hc1S1 : (chi1 : ClassFunction ↥L ℂ) ∈ S₁) (hc1barS1 : (chi1 : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hνZc1 : hS₁.extension (chi1 : ClassFunction ↥L ℂ) ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ)
      (chi1 : ClassFunction ↥L ℂ).conj = 0)
    (hc1χ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 0)
    (hc1χbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hc1barχ : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hc1barχbar : ClassFunction.inner (chi1 : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0) :
    ClassFunction.inner
        (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp χ hrealχ hdiffsuppχ
          hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar').X
        (hS₁.extension (chi1 : ClassFunction ↥L ℂ)) = 0 :=
  inner_decomposition_X_extension_member_eq_zero hS₁
    (OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp χ hrealχ hdiffsuppχ
      hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar')
    (memberExtensionDecomposition hyp hS₁ chi1 hrealc1 hdiffsuppc1 hc1S1 hc1barS1 hνZc1
      hc1c1bar)
    (dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp hrealc1 hdiffsuppc1 hrealχ
      hdiffsuppχ hc1χ hc1χbar hc1barχ hc1barχbar)
    rfl

end OddOrder.Peterfalvi.S08



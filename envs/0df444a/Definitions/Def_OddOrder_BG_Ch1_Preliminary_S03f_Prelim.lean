-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03f_Prelim
-- name    : OddOrder_BG_Ch1_Preliminary_S03f_Prelim
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:43:38.671194+00:00
-- url     : https://prove2.me/theorems/f7811346-1ce0-48af-9853-67e5708db3ce
-- title:
--   BG §3: standalone preliminaries for Theorem 3.6
-- statement:
--   Reusable helper lemmas extracted from the development of Theorem 3.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §3. Main results include: if $O_{p'}(G)=1$ then $F(G)=O_p(G)$; a finite group with no nontrivial $p'$-element is a $p$-group; and a substep of Theorem 3.6 (3.9) about Frattini quotients and Fitting subgroups.
--
--   Main declarations: `avgFactor`; `avgConj`; `conjSubtypeMulAction`; `mem_normalizer_map_subtype_of_characteristic`.
--
--   The bundle also proves 27 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S03f_Prelim.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S03f_Prelim.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01_Solvable
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_PLengthTransfer

namespace OddOrder.BG.Ch1.S03f

open scoped commutatorElement

/-- **`F(G) = O_p(G)` when `O_{p'}(G) = ⊥`** (BG Theorem 3.6 (3.9)).

The Fitting subgroup is the supremum of the `p`-cores `O_q(G)` over the prime factors `q` of `|G|`
(`fitting_eq_iSup_primeFactors`).  Each `O_q(G)` with `q ≠ p` is a normal `q`-group, hence a normal
`{p}ᶜ`-group, hence `≤ O_{p'}(G) = ⊥`; so only the `q = p` term survives and `F(G) = O_p(G)`. -/
theorem fitting_eq_opCore_of_oPiCore_compl_eq_bot {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) (h : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G = ⊥) :
    OddOrder.Isaacs.Ch01.fitting G = OddOrder.Isaacs.Ch01.opCore p G := by
  have : Fact p.Prime := ⟨hp⟩
  refine le_antisymm ?_ (OddOrder.Isaacs.Ch01.opCore_le_fitting ⟨p, hp⟩ G)
  rw [OddOrder.Isaacs.Ch01.fitting_eq_iSup_primeFactors]
  refine iSup_le (fun q => ?_)
  have : Fact (q : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors q.2⟩
  by_cases hq : (q : ℕ) = p
  · subst hq; exact le_refl _
  · have hle : OddOrder.Isaacs.Ch01.opCore (q : ℕ) G
        ≤ OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) G := by
      refine OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore ?_
      intro r hr
      obtain ⟨nq, hnq⟩ := (OddOrder.Isaacs.Ch01.opCore_isPGroup (q : ℕ) G).exists_card_eq
      rw [hnq] at hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrq : r = (q : ℕ) := (Nat.prime_dvd_prime_iff_eq hrp Fact.out).mp
        (hrp.dvd_of_dvd_pow (Nat.mem_primeFactors.mp hr).2.1)
      simp [hrq, hq]
    rw [h] at hle
    exact le_trans hle bot_le

/-- A finite group with no nontrivial `p'`-element is a `p`-group: the `p'`-part `g ^ (p ^ vₚ)`
of any element has order coprime to `p`, hence is trivial, so `g` has `p`-power order. -/
theorem isPGroup_of_forall_eq_one_of_not_dvd_orderOf {p : ℕ} [hp : Fact p.Prime]
    {W : Type*} [Group W] [Finite W]
    (h : ∀ w : W, ¬ p ∣ orderOf w → w = 1) : IsPGroup p W := by
  intro g
  refine ⟨(orderOf g).factorization p, h _ ?_⟩
  have ho : orderOf g ≠ 0 := (orderOf_pos g).ne'
  have hdvd : p ^ (orderOf g).factorization p ∣ orderOf g := Nat.ordProj_dvd _ _
  rw [orderOf_pow g, Nat.gcd_eq_right hdvd]
  exact hp.out.coprime_iff_not_dvd.mp (Nat.coprime_ordCompl hp.out ho)

/-- The image under `V.subtype` of the Frattini subgroup of `V = F(Hb)` is **characteristic** in
`Hb`: `Φ(V)` is characteristic in the characteristic subgroup `V`
(characteristic-of-characteristic).

The characteristic strength (over mere normality) is needed so that, for `Hb = ↥H` with `H ◁ G`, the
further lift `Φ(V).map H.subtype` is normal in `G` (mathlib instance
`ConjAct.normal_of_characteristic_of_normal`). -/
theorem frattini_fitting_map_characteristic {Hb : Type*} [Group Hb] [Finite Hb] :
    ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
      (OddOrder.Isaacs.Ch01.fitting Hb).subtype).Characteristic := by
  set V : Subgroup Hb := OddOrder.Isaacs.Ch01.fitting Hb with hVdef
  have hVchar : V.Characteristic := by rw [hVdef]; infer_instance
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxPhi, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxPhi
  obtain ⟨k, hkfr, rfl⟩ := hxPhi
  -- restrict `φ` to an automorphism `ψ` of `↥V` (using `V` characteristic)
  have hVmap : V.map φ.toMonoidHom = V := Subgroup.characteristic_iff_map_eq.mp hVchar φ
  set ψ : ↥V ≃* ↥V := (φ.subgroupMap V).trans (MulEquiv.subgroupCongr hVmap) with hψ
  have hψk : ψ k ∈ _root_.frattini ↥V := by
    have hmap := Subgroup.characteristic_iff_map_eq.mp (frattini_characteristic (G := ↥V)) ψ
    rw [← hmap]; exact Subgroup.mem_map_of_mem _ hkfr
  exact ⟨ψ k, hψk, rfl⟩

/-- **BG Theorem 3.6 (3.9), key substep**: if the Fitting subgroup `V = F(Hb)` of a finite solvable
group is a `p`-group, then `O_{p'}(Hb / Φ(V)) = ⊥`.

Let `Q = Hb / Φ(V)`, `Ō = O_{p'}(Q)`, and `W` the preimage of `Ō` in `Hb`.  The image `V̄ = V/Φ(V)`
(a `p`-group) and `Ō` (a `p'`-group) are coprime normal subgroups of `Q`, hence centralize each
other, so `⁅V, W⁆ ≤ Φ(V)`.  Thus every `p'`-element `w` of `W` acts trivially on `V/Φ(V)`, and by
Burnside (Theorem 1.8, `mulAut_eq_one_of_coprime_orderOf_of_frattini`) trivially on `V`; so
`w ∈ C_Hb(V) ≤ V` (Proposition 1.3, `centralizer_fitting_le_fitting`), and being a `p'`-element of
the `p`-group `V` it is trivial.  Hence `W` is a `p`-group, so its image `Ō` is both a `p`- and a
`p'`-group, i.e. trivial. -/
theorem oPiCore_compl_quotient_frattini_fitting_eq_bot
    {p : ℕ} [hp : Fact p.Prime] {Hb : Type*} [Group Hb] [Finite Hb] [Group.IsSolvable Hb]
    (hVp : IsPGroup p ↥(OddOrder.Isaacs.Ch01.fitting Hb))
    [hPhiNorm : ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
      (OddOrder.Isaacs.Ch01.fitting Hb).subtype).Normal] :
    OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ)
      (Hb ⧸ ((_root_.frattini ↥(OddOrder.Isaacs.Ch01.fitting Hb)).map
        (OddOrder.Isaacs.Ch01.fitting Hb).subtype)) = ⊥ := by
  classical
  set V : Subgroup Hb := OddOrder.Isaacs.Ch01.fitting Hb with hVdef
  have hVnorm : V.Normal := by rw [hVdef]; infer_instance
  set Phi : Subgroup Hb := (_root_.frattini ↥V).map V.subtype with hPhidef
  set Ō : Subgroup (Hb ⧸ Phi) := OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) (Hb ⧸ Phi) with hOdef
  set W : Subgroup Hb := Ō.comap (QuotientGroup.mk' Phi) with hWdef
  set Vbar : Subgroup (Hb ⧸ Phi) := V.map (QuotientGroup.mk' Phi) with hVbardef
  -- `Vbar` is a normal `p`-group; `Ō` is a `p'`-group.
  have hVbarNorm : Vbar.Normal :=
    hVbardef ▸ hVnorm.map (QuotientGroup.mk' Phi) (QuotientGroup.mk'_surjective Phi)
  have hVbarP : IsPGroup p ↥Vbar :=
    hVbardef ▸ hVp.of_surjective (MonoidHom.subgroupMap (QuotientGroup.mk' Phi) V)
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Phi) V)
  have hO_p' : ¬ p ∣ Nat.card ↥Ō := by
    intro hd
    have hmem := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := Hb ⧸ Phi) ({p}ᶜ : Set ℕ) p
      (Nat.mem_primeFactors.mpr ⟨hp.out, hd, Nat.card_pos.ne'⟩)
    simp at hmem
  -- `⁅Vbar, Ō⁆ = ⊥` (coprime normal subgroups centralize).
  have hcop : Nat.Coprime (Nat.card ↥Vbar) (Nat.card ↥Ō) := by
    obtain ⟨k, hk⟩ := hVbarP.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (hp.out.coprime_iff_not_dvd.mpr hO_p')
  have hcomm_bot : (⁅Vbar, Ō⁆ : Subgroup (Hb ⧸ Phi)) = ⊥ := by
    have hle : (⁅Vbar, Ō⁆ : Subgroup (Hb ⧸ Phi)) ≤ Vbar ⊓ Ō := Subgroup.commutator_le_inf Vbar Ō
    rw [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot] at hle
    exact le_bot_iff.mp hle
  -- `⁅V, W⁆ ≤ Φ(V)` (pull back the commutator).
  have hVW_le_Phi : (⁅V, W⁆ : Subgroup Hb) ≤ Phi := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    have hmv : QuotientGroup.mk' Phi v ∈ Vbar := hVbardef ▸ Subgroup.mem_map_of_mem _ hv
    have hmw : QuotientGroup.mk' Phi w ∈ Ō := (Subgroup.mem_comap).mp hw
    have hmem : QuotientGroup.mk' Phi ⁅v, w⁆ ∈ (⊥ : Subgroup (Hb ⧸ Phi)) := by
      rw [← hcomm_bot, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator hmv hmw
    rw [Subgroup.mem_bot] at hmem
    have hker : ⁅v, w⁆ ∈ (QuotientGroup.mk' Phi).ker := MonoidHom.mem_ker.mpr hmem
    rwa [QuotientGroup.ker_mk'] at hker
  -- every `p'`-element of `W` is trivial.
  have hWp' : ∀ w : ↥W, ¬ p ∣ orderOf w → w = 1 := by
    rintro ⟨g, hgW⟩ hg_p'
    have hord_eq : orderOf (⟨g, hgW⟩ : ↥W) = orderOf g :=
      (orderOf_injective W.subtype (Subgroup.subtype_injective W) ⟨g, hgW⟩).symm
    rw [hord_eq] at hg_p'
    set f : MulAut ↥V := MulAut.conjNormal (G := Hb) (H := V) g with hf
    have hf_ord : orderOf f ∣ orderOf g := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hf, ← map_pow, pow_orderOf_eq_one, map_one]
    have hf_p' : ¬ p ∣ orderOf f := fun hd => hg_p' (hd.trans hf_ord)
    have hfcop : Nat.Coprime (orderOf f) p := (hp.out.coprime_iff_not_dvd.mpr hf_p').symm
    have hftriv : ∀ z : ℤ, ∀ r : ↥V, ∃ x ∈ _root_.frattini ↥V, (f ^ z) r = r * x := by
      intro z r
      refine ⟨r⁻¹ * (f ^ z) r, ?_, by group⟩
      set x : ↥V := r⁻¹ * (f ^ z) r with hx
      have hcoe : ((f ^ z) r : Hb) = (g ^ z) * (r : Hb) * (g ^ z)⁻¹ := by
        rw [hf, ← map_zpow MulAut.conjNormal g z, MulAut.conjNormal_apply]
      have hxcoe : (x : Hb) = ⁅(r : Hb)⁻¹, g ^ z⁆ := by
        rw [hx, Subgroup.coe_mul, Subgroup.coe_inv, hcoe, commutatorElement_def]; group
      have hmemVW : ⁅(r : Hb)⁻¹, g ^ z⁆ ∈ (⁅V, W⁆ : Subgroup Hb) :=
        Subgroup.commutator_mem_commutator (V.inv_mem r.2) (W.zpow_mem hgW z)
      have hxPhi : (x : Hb) ∈ Phi := by rw [hxcoe]; exact hVW_le_Phi hmemVW
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxPhi
      rw [Subgroup.coe_subtype] at hyx
      have hyx' : y = x := Subtype.coe_injective hyx
      rwa [hyx'] at hy
    have hf1 : f = 1 :=
      OddOrder.BG.Ch1.S01.mulAut_eq_one_of_coprime_orderOf_of_frattini hVp f hfcop hftriv
    have hg_cent : g ∈ Subgroup.centralizer (V : Set Hb) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 : ((MulAut.conjNormal (G := Hb) (H := V) g) ⟨v, hv⟩ : Hb) = v := by
        rw [show (MulAut.conjNormal (G := Hb) (H := V) g) = f from hf.symm, hf1, MulAut.one_apply]
      rw [MulAut.conjNormal_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    have hgV : g ∈ V := by
      have := OddOrder.GroupTheory.centralizer_fitting_le_fitting (G := Hb)
      rw [← hVdef] at this
      exact this hg_cent
    obtain ⟨m, hm⟩ := hVp ⟨g, hgV⟩
    have hordV : orderOf (⟨g, hgV⟩ : ↥V) = orderOf g :=
      (orderOf_injective V.subtype (Subgroup.subtype_injective V) ⟨g, hgV⟩).symm
    have hdvd : orderOf g ∣ p ^ m := by
      rw [← hordV]; exact orderOf_dvd_of_pow_eq_one hm
    obtain ⟨a, _, ha⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    rcases Nat.eq_zero_or_pos a with ha0 | hapos
    · have hgone : orderOf g = 1 := by rw [ha, ha0, pow_zero]
      exact Subtype.ext (orderOf_eq_one_iff.mp hgone)
    · exact absurd (ha ▸ dvd_pow_self p hapos.ne') hg_p'
  -- `W` is a `p`-group, hence its image `Ō` is a `p`-group; being also `p'`, `Ō = ⊥`.
  have hWp : IsPGroup p ↥W := isPGroup_of_forall_eq_one_of_not_dvd_orderOf hWp'
  have hO_eq : Ō = W.map (QuotientGroup.mk' Phi) :=
    hWdef ▸ (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Phi) Ō).symm
  have hO_pgroup : IsPGroup p ↥Ō :=
    hO_eq ▸ hWp.of_surjective (MonoidHom.subgroupMap (QuotientGroup.mk' Phi) W)
      (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Phi) W)
  obtain ⟨k, hk⟩ := hO_pgroup.exists_card_eq
  have hk0 : k = 0 := by by_contra hk0; exact hO_p' (hk ▸ dvd_pow_self p hk0)
  exact Subgroup.card_eq_one.mp (by rw [hk, hk0, pow_zero])

section

open scoped Pointwise

/-- **Push an invariant subgroup of an invariant ambient subgroup back to the whole group**: if
`U ≤ G` is `A`-invariant and `L ≤ ↥U` is invariant under the restricted action, then
`L.map U.subtype ≤ G` is `A`-invariant.

(Public version of a helper that exists `private`ly in `S01_Solvable` and `S04e_GorThm37`;
consolidating the three copies into `Ch03_SplitExtensions` is part of the Theorem 3.6 cleanup.) -/
theorem isAInvariant_map_subtype_of_restrict
    {G A : Type*} [Group G] [Group A] {φ : A →* MulAut G}
    {U : Subgroup G} (hU : OddOrder.Isaacs.Ch03.IsAInvariant φ U)
    {L : Subgroup ↥U} (hL : OddOrder.Isaacs.Ch03.IsAInvariant hU.restrict L) :
    OddOrder.Isaacs.Ch03.IsAInvariant φ (L.map U.subtype) := by
  rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
  intro a x hx
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨l, hl, rfl⟩ := hx
  exact ⟨(hU.restrict a) l, hL.smul_mem a hl,
    OddOrder.Isaacs.Ch03.IsAInvariant.restrict_apply_val hU a l⟩

/-- **A subgroup of `H ⊴ G` that is normal in `↥H` and `R`-invariant is normal in `G = HR`**: with
`H ⊔ R = ⊤`, conjugation by any `g = h * r` preserves `X.map H.subtype` (the `r`-part by
`R`-invariance under the conjugation action, the `h`-part by normality in `↥H`).

Used at BG Theorem 3.6 (3.14) for `C_V(K)` and `[V,K]` (normal in `↥H` via (3.12), `R`-invariant
since `V` is characteristic and `K` is `R`-invariant), and again in Phase D. -/
theorem normal_map_subtype_of_isAInvariant_conjNormal
    {G : Type*} [Group G] {H R : Subgroup G} [H.Normal] (hsup : H ⊔ R = ⊤)
    {X : Subgroup ↥H} [hXn : X.Normal]
    (hX_inv : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) X) :
    (X.map H.subtype).Normal := by
  constructor
  rintro _ ⟨x, hx, rfl⟩ g
  -- decompose `g = h * r` with `h ∈ H`, `r ∈ R` (normal product, `H ⊔ R = ⊤`).
  have hg : g ∈ (H : Set G) * (R : Set G) := by
    rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top]; trivial
  obtain ⟨h, hh, r, hr, rfl⟩ := hg
  -- conjugate by `r` first (`R`-invariance), then by `h` (normality in `↥H`).
  set y : ↥H := ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) ⟨r, hr⟩ x with hy
  have hyX : y ∈ X := hX_inv.smul_mem ⟨r, hr⟩ hx
  have hyval : (y : G) = r * (x : G) * r⁻¹ := by
    simp only [hy, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  refine ⟨⟨h, hh⟩ * y * ⟨h, hh⟩⁻¹, hXn.conj_mem y hyX ⟨h, hh⟩, ?_⟩
  rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hyval]
  group

/-- One inequality of `fitting_map_eq_of_mulEquiv`: the image of the Fitting subgroup under an
isomorphism is a normal nilpotent subgroup, hence contained in the Fitting subgroup. -/
theorem fitting_map_le_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (f : G ≃* G') :
    (OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom ≤ OddOrder.Isaacs.Ch01.fitting G' := by
  have : ((OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance f.toMonoidHom f.surjective
  have : Group.IsNilpotent ↥((OddOrder.Isaacs.Ch01.fitting G).map f.toMonoidHom) := by
    have e' := Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting G) f.toMonoidHom
      f.injective
    exact Group.nilpotent_of_surjective e'.toMonoidHom e'.surjective
  exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **The Fitting subgroup transports along group isomorphisms**: `F(G).map e = F(G')` for
`e : G ≃* G'`.  (The image is a normal nilpotent subgroup, hence `≤ F(G')`; symmetrically with
`e.symm`.)  Used at BG Theorem 3.6 (3.15) (`K = F(N_H(K))` via `N_H(K) ≃* H/V`). -/
theorem fitting_map_eq_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') :
    (OddOrder.Isaacs.Ch01.fitting G).map e.toMonoidHom = OddOrder.Isaacs.Ch01.fitting G' := by
  refine le_antisymm (fitting_map_le_of_mulEquiv e) ?_
  have h2 := fitting_map_le_of_mulEquiv e.symm
  rw [Subgroup.map_equiv_eq_comap_symm', MulEquiv.symm_symm] at h2
  have h3 := Subgroup.map_mono (f := e.toMonoidHom) h2
  rwa [Subgroup.map_comap_eq_self_of_surjective e.surjective] at h3

/-- **Hall subgroups transport along group isomorphisms** (cardinality and index are preserved).
Used in the Frattini argument at BG Theorem 3.6 (3.12): the conjugate of a Hall `p'`-subgroup of
`U` under `MulAut.conjNormal h` is again a Hall `p'`-subgroup. -/
theorem isHallSubgroup_map_of_mulEquiv {G G' : Type*} [Group G] [Finite G] [Group G'] [Finite G']
    {π : Set ℕ} {K : Subgroup G} (e : G ≃* G')
    (hK : OddOrder.Isaacs.Ch03.IsHallSubgroup π K) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup π (K.map e.toMonoidHom) := by
  have hcard : Nat.card ↥(K.map e.toMonoidHom) = Nat.card ↥K :=
    Subgroup.card_map_of_injective e.injective
  have hidx : (K.map e.toMonoidHom).index = K.index := by
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index (K.map e.toMonoidHom)
    rw [hcard, ← Nat.card_congr e.toEquiv] at h2
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h2.trans h1.symm)
  exact ⟨fun q hq => hK.1 q (hcard ▸ hq), fun q hq => hK.2 q (hidx ▸ hq)⟩

/-- **Conjugation by a normalizer element fixes the subgroup**: if `g` normalizes `A`, the
conjugation automorphism `MulAut.conj g` maps `A` onto `A`. -/
theorem map_conj_eq_self_of_mem_normalizer {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj g).toMonoidHom = A := by
  rw [Subgroup.mem_normalizer_iff] at hg
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (hg a).mp ha
  · intro hx
    refine ⟨g⁻¹ * x * g, (hg _).mpr ?_, by group⟩
    have heq : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rwa [heq]

/-- **A subgroup fixed by the conjugation automorphism of `g` admits `g` in its normalizer**
(converse of `map_conj_eq_self_of_mem_normalizer`). -/
theorem mem_normalizer_of_map_conj_eq {G : Type*} [Group G] {A : Subgroup G} {g : G}
    (hmap : A.map (MulAut.conj g).toMonoidHom = A) :
    g ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : (MulAut.conj g).toMonoidHom x ∈ A.map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hx
    rw [hmap] at h1
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using h1
  · intro hx
    rw [← hmap, Subgroup.mem_map] at hx
    obtain ⟨a, ha, haeq⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at haeq
    have hax : a = x := mul_left_cancel (mul_right_cancel haeq)
    rwa [← hax]

/-- **Normalizing two subgroups normalizes their join**.  Used at BG Theorem 3.6 (3.22) to see
that `R₀` normalizes `VXP = V ⊔ X ⊔ P`. -/
theorem mem_normalizer_sup {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) :=
  mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_sup, map_conj_eq_self_of_mem_normalizer hA,
      map_conj_eq_self_of_mem_normalizer hB])

/-- **Normalizing both arguments normalizes their commutator subgroup**.  Used at BG Theorem 3.6
(3.24) to see that `R₀` normalizes `[K, P]`. -/
theorem mem_normalizer_commutator {G : Type*} [Group G] {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) :=
  mem_normalizer_of_map_conj_eq (by
    rw [Subgroup.map_commutator, map_conj_eq_self_of_mem_normalizer hA,
      map_conj_eq_self_of_mem_normalizer hB])

set_option backward.isDefEq.respectTransparency false in
/-- **Lifted characteristic subgroups inherit normalizer elements**: if `g` normalizes `W ≤ G`,
then `g` normalizes `C.map W.subtype` for every characteristic `C ≤ ↥W` (conjugation by `g`
restricts to an automorphism of `↥W`, which fixes `C`).  Used at BG Theorem 3.6 (3.22) for
`O_p([VXP, R₀])`. -/
theorem mem_normalizer_map_subtype_of_characteristic {G : Type*} [Group G] {W : Subgroup G}
    {C : Subgroup ↥W} [hC : C.Characteristic] {g : G}
    (hg : g ∈ Subgroup.normalizer (W : Set G)) :
    g ∈ Subgroup.normalizer ((C.map W.subtype : Subgroup G) : Set G) := by
  have key : ∀ k : G, k ∈ Subgroup.normalizer (W : Set G) →
      ∀ x ∈ C.map W.subtype, k * x * k⁻¹ ∈ C.map W.subtype := by
    intro k hk x hx
    obtain ⟨c, hc, rfl⟩ := hx
    have hWmap : W.map (MulAut.conj k).toMonoidHom = W :=
      map_conj_eq_self_of_mem_normalizer hk
    set ψ : ↥W ≃* ↥W :=
      ((MulAut.conj k).subgroupMap W).trans (MulEquiv.subgroupCongr hWmap) with hψ
    have hψc : ψ c ∈ C := by
      have hmap := Subgroup.characteristic_iff_map_eq.mp hC ψ
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hc
    refine ⟨ψ c, hψc, ?_⟩
    simp only [hψ, Subgroup.coe_subtype, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
      MulEquiv.coe_subgroupMap_apply, MulAut.conj_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => key g hg x hx
  · intro hx
    have h2 := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    have heq : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [heq] at h2

/-- **An `R`-invariant subgroup of `H ⊴ G` is normalized by every element of `R` at the `G`
level**: the `G`-level form of `IsAInvariant` for the conjugation action.  Used at BG Theorem 3.6
Phase C/D for `K_G`, `P_G` and the (3.22) ambient `VXP`. -/
theorem mem_normalizer_map_subtype_of_isAInvariant {G : Type*} [Group G] {H R : Subgroup G}
    [H.Normal] {L : Subgroup ↥H}
    (hL : OddOrder.Isaacs.Ch03.IsAInvariant
      ((MulAut.conjNormal (G := G) (H := H)).comp R.subtype) L)
    {g : G} (hg : g ∈ R) :
    g ∈ Subgroup.normalizer ((L.map H.subtype : Subgroup G) : Set G) := by
  set φ : ↥R →* MulAut ↥H := (MulAut.conjNormal (G := G) (H := H)).comp R.subtype with hφ
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨φ ⟨g, hg⟩ k, hL.smul_mem _ hk, ?_⟩
    simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
  · rintro ⟨k, hk, hkeq⟩
    refine ⟨(φ ⟨g, hg⟩)⁻¹ k, hL.inv_smul_mem _ hk, ?_⟩
    have hv2 : ((φ ⟨g, hg⟩ ((φ ⟨g, hg⟩)⁻¹ k) : ↥H) : G)
        = g * ((((φ ⟨g, hg⟩)⁻¹ k : ↥H)) : G) * g⁻¹ := by
      simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulAut.conjNormal_apply]
    rw [MulAut.apply_inv_self] at hv2
    have h3 := hv2.symm.trans hkeq
    exact mul_left_cancel (mul_right_cancel h3)

/-- **Invariant subgroups have `G`-level normalizer elements, for any action with conjugation
values**: if `L ≤ ↥W` is invariant under `φ : A →* MulAut ↥W` and `φ a` is conjugation by `g`
(`↑(φ a k) = g·k·g⁻¹`), then `g` normalizes `L.map W.subtype`.  Generic core of
`mem_normalizer_map_subtype_of_isAInvariant`; used with the `Subgroup.normalizerMonoidHom`
action at BG Theorem 3.6 (3.25). -/
theorem mem_normalizer_map_subtype_of_smul_val {G : Type*} [Group G] {W : Subgroup G}
    {A : Type*} [Group A] {φ : A →* MulAut ↥W} {L : Subgroup ↥W}
    (hL : OddOrder.Isaacs.Ch03.IsAInvariant φ L) {a : A} {g : G}
    (hval : ∀ k : ↥W, ((φ a k : ↥W) : G) = g * (k : G) * g⁻¹) :
    g ∈ Subgroup.normalizer ((L.map W.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨φ a k, hL.smul_mem _ hk, hval k⟩
  · rintro ⟨k, hk, hkeq⟩
    refine ⟨(φ a)⁻¹ k, hL.inv_smul_mem _ hk, ?_⟩
    have hv2 := hval ((φ a)⁻¹ k)
    rw [MulAut.apply_inv_self] at hv2
    have h3 := hv2.symm.trans hkeq
    exact mul_left_cancel (mul_right_cancel h3)

/-- **`O_{p'}(W) = ⊥` when `W` has a self-centralizing normal `p`-subgroup** (BG Theorem 3.6,
(3.10)→(3.22) step): `N` and `O_{p'}(W)` are coprime normal subgroups, hence commute elementwise,
so `O_{p'}(W) ≤ C_W(N) ≤ N`; a `p'`-subgroup of a `p`-group is trivial. -/
theorem oPiCore_compl_eq_bot_of_isPGroup_centralizer_le {p : ℕ} [hp : Fact p.Prime]
    {W : Type*} [Group W] [Finite W] {N : Subgroup W} [N.Normal] (hNp : IsPGroup p ↥N)
    (hCent : Subgroup.centralizer (N : Set W) ≤ N) :
    OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) W = ⊥ := by
  set O : Subgroup W := OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) W with hO
  have hOnorm : O.Normal := by rw [hO]; infer_instance
  have hOp' : ¬ p ∣ Nat.card ↥O := by
    intro hd
    have hmem := OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := W) ({p}ᶜ : Set ℕ) p
      (Nat.mem_primeFactors.mpr ⟨hp.out, hO ▸ hd, Nat.card_pos.ne'⟩)
    simp at hmem
  have hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥O) := by
    obtain ⟨k, hk⟩ := hNp.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (hp.out.coprime_iff_not_dvd.mpr hOp')
  have hcomm : (⁅O, N⁆ : Subgroup W) = ⊥ := by
    have hle : (⁅N, O⁆ : Subgroup W) ≤ N ⊓ O := Subgroup.commutator_le_inf N O
    rw [(Subgroup.disjoint_of_coprime_natCard hcop).eq_bot] at hle
    rw [Subgroup.commutator_comm]
    exact le_bot_iff.mp hle
  have hO_le_N : O ≤ N :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hCent
  have hOp : IsPGroup p ↥O := hNp.to_le hO_le_N
  obtain ⟨k, hk⟩ := hOp.exists_card_eq
  have hk0 : k = 0 := by
    by_contra h
    exact hOp' (hk ▸ dvd_pow_self p h)
  exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])

/-- **`O_π`-triviality descends along normal-in-context inclusions**: if `A ≤ B` with
`A.subgroupOf B` normal in `↥B` and `O_π(↥B) = ⊥`, then `O_π(↥A) = ⊥`: the lift of `O_π(↥A)`
(characteristic in `↥A`) is a normal π-subgroup of `↥B`, hence lands in `O_π(↥B)`
(`IsPiGroup.le_oPiCore`).  Used at BG Theorem 3.6 (3.22) with `A = [VXP, R₀] ⊴ B = VXP`. -/
theorem oPiCore_eq_bot_of_subgroupOf_normal {G : Type*} [Group G] [Finite G] {π : Set ℕ}
    {A B : Subgroup G} (hAB : A ≤ B) (hnorm : (A.subgroupOf B).Normal)
    (hB : OddOrder.Isaacs.Ch03.oPiCore π ↥B = ⊥) :
    OddOrder.Isaacs.Ch03.oPiCore π ↥A = ⊥ := by
  set O : Subgroup ↥A := OddOrder.Isaacs.Ch03.oPiCore π ↥A with hO
  have hOchar : O.Characteristic := by rw [hO]; infer_instance
  set L : Subgroup G := O.map A.subtype with hL
  have hLA : L ≤ A := Subgroup.map_subtype_le O
  have hLB : L ≤ B := hLA.trans hAB
  -- every element of `B` normalizes `A` in `G`
  have hbn : ∀ b : ↥B, (b : G) ∈ Subgroup.normalizer (A : Set G) := by
    intro b
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h1 : (⟨x, hAB hx⟩ : ↥B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.mpr hx
      have h2 := hnorm.conj_mem _ h1 b
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2
    · intro hx
      have h1 : (⟨(b : G) * x * (b : G)⁻¹, hAB hx⟩ : ↥B) ∈ A.subgroupOf B :=
        Subgroup.mem_subgroupOf.mpr hx
      have h2 := hnorm.conj_mem _ h1 b⁻¹
      rw [Subgroup.mem_subgroupOf] at h2
      have h4 : ((b⁻¹ * (⟨(b : G) * x * (b : G)⁻¹, hAB hx⟩ : ↥B) * b⁻¹⁻¹ : ↥B) : G) = x := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group
      rwa [h4] at h2
  -- the lift `L` is normal in context `↥B`
  have hLnorm : (L.subgroupOf B).Normal := by
    constructor
    intro n hn b
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hkey := mem_normalizer_map_subtype_of_characteristic (C := O) (hbn b)
    rw [Subgroup.mem_normalizer_iff] at hkey
    have h2 := (hkey (n : G)).mp hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact h2
  -- `L.subgroupOf B` is a π-group, hence lands in `O_π(↥B) = ⊥`
  have hcardL : Nat.card ↥(L.subgroupOf B) = Nat.card ↥O := by
    rw [hL]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLB).toEquiv).trans
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective A))
  have hpiL : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π (L.subgroupOf B) := by
    intro q hq
    rw [hcardL] at hq
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := ↥A) π q (hO ▸ hq)
  have hle : L.subgroupOf B ≤ OddOrder.Isaacs.Ch03.oPiCore π ↥B :=
    OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore hpiL
  rw [hB] at hle
  have hLbot : L = ⊥ := by
    have hdisj := Subgroup.subgroupOf_eq_bot.mp (le_bot_iff.mp hle)
    have h2 : L ⊓ B = ⊥ := disjoint_iff.mp hdisj
    rwa [inf_eq_left.mpr hLB] at h2
  have h3 : O.map A.subtype = (⊥ : Subgroup ↥A).map A.subtype := by
    rw [Subgroup.map_bot, ← hL]
    exact hLbot
  exact Subgroup.map_injective (Subgroup.subtype_injective A) h3

/-- **Cardinality of a join with a normalizing, disjoint factor**: if `B ≤ N_G(A)` and
`A ⊓ B = ⊥`, then `|A ⊔ B| = |A| · |B|` (`A` is normal in `A ⊔ B` with complement `B`).
Used in the counting step of BG Theorem 3.6 (3.23) (`|VYP| = |V|·|Y|·|P|`). -/
theorem card_sup_of_le_normalizer_of_disjoint {G : Type*} [Group G] [Finite G]
    {A B : Subgroup G} (hn : B ≤ Subgroup.normalizer (A : Set G)) (hd : Disjoint A B) :
    Nat.card ↥(A ⊔ B : Subgroup G) = Nat.card ↥A * Nat.card ↥B := by
  set S : Subgroup G := A ⊔ B with hS
  have hA_le : A ≤ S := le_sup_left
  have hB_le : B ≤ S := le_sup_right
  have hnorm : S ≤ Subgroup.normalizer (A : Set G) := sup_le Subgroup.le_normalizer hn
  have hAnormal : ((A.subgroupOf S) : Subgroup ↥S).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hcompl' : Subgroup.IsComplement' (A.subgroupOf S) (B.subgroupOf S) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · refine disjoint_iff.mpr (eq_bot_iff.mpr fun x hx => ?_)
      rw [Subgroup.mem_inf] at hx
      simp only [Subgroup.mem_subgroupOf] at hx
      have hmem : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
      rw [hd.eq_bot, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]
      exact Subtype.ext (by simpa using hmem)
    · have hsup : ((A.subgroupOf S) : Subgroup ↥S) ⊔ (B.subgroupOf S) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hA_le hB_le, Subgroup.subgroupOf_self]
      have hmul := Subgroup.normal_mul ((A.subgroupOf S) : Subgroup ↥S) (B.subgroupOf S)
      rw [hsup, Subgroup.coe_top] at hmul
      exact hmul.symm
  have hcard := hcompl'.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le).toEquiv] at hcard
  exact hcard.symm

/-- **A group of `p`-length one with `O_{p'}(W) = ⊥` has a normal Sylow `p`-subgroup**: every
`p`-subgroup lies in `O_p(W)`.  (`O_{p',p}(W) = O_p(W)` by
`oPiPrimePiCore_eq_oPiCore_of_compl_bot`, and `W/O_p(W)` is then a `p'`-group, so the image of a
`p`-subgroup is trivial.)  Used at BG Theorem 3.6 (3.22) for `W = [VXP, R₀]`. -/
theorem le_opCore_of_hasPLengthOne_of_oPiCore_compl_eq_bot
    {p : ℕ} [hp : Fact p.Prime] {W : Type*} [Group W] [Finite W]
    (hpl : hasPLengthOne p W)
    (hOp' : OddOrder.Isaacs.Ch03.oPiCore ({p}ᶜ : Set ℕ) W = ⊥)
    {Q : Subgroup W} (hQ : IsPGroup p ↥Q) :
    Q ≤ OddOrder.Isaacs.Ch01.opCore p W := by
  rw [hasPLengthOne, oPiPrimePiCore_eq_oPiCore_of_compl_bot hOp'] at hpl
  have hQmap : Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W)) = ⊥ := by
    have hQp : IsPGroup p
        ↥(Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W))) :=
      hQ.map _
    obtain ⟨k, hk⟩ := hQp.exists_card_eq
    have hdvd : Nat.card
        ↥(Q.map (QuotientGroup.mk' (OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W)))
        ∣ Nat.card (W ⧸ OddOrder.Isaacs.Ch03.oPiCore ({p} : Set ℕ) W) :=
      Subgroup.card_subgroup_dvd_card _
    have hk0 : k = 0 := by
      by_contra hk0
      exact hpl ((hk ▸ dvd_pow_self p hk0).trans hdvd)
    exact Subgroup.eq_bot_of_card_eq _ (by rw [hk, hk0, pow_zero])
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hQmap
  rwa [← OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore]

end

section PhaseF

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- The single conjugate `b v b⁻¹ ∈ W` (`W` normal), as an element of `↥W` — the factor of the
averaging map `avgConj`.  Public so that consumers can compute `avgConj` factor-by-factor
(BG (3.38) evaluates `eᵢ ∘ norm` this way). -/
def avgFactor (B W : Subgroup G) [W.Normal] (v : ↥W) (b : ↥B) : ↥W :=
  ⟨(b : G) * (v : G) * (b : G)⁻¹,
    Subgroup.Normal.conj_mem inferInstance _ v.2 _⟩

theorem avgFactor_coe (B W : Subgroup G) [W.Normal] (v : ↥W) (b : ↥B) :
    ((avgFactor B W v b : ↥W) : G) = (b : G) * (v : G) * (b : G)⁻¹ :=
  rfl

/-- **Averaging over a finite subgroup `B` inside an abelian normal subgroup `W`**:
`avgConj B W v = ∏_{b ∈ B} b v b⁻¹` (no normalization; on `C_W(B)` it is the `|B|`-power map,
which is injective when `(|B|, exp W) = 1`).  BG (3.38) uses it both as the projection
`V → Vᵢ = C_V(Kᵢ)` (with `B = Kᵢ`) and as the norm map `v ↦ v + vx + ⋯ + vx^{r-1}`
(with `B = R₀ = ⟨x⟩`). -/
def avgConj (B W : Subgroup G) [W.Normal] [IsMulCommutative ↥W] [Fintype ↥B] : ↥W →* ↥W :=
  MonoidHom.mk' (fun v => ∏ b : ↥B, avgFactor B W v b) (fun v w => by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => Subtype.ext ?_
    simp only [avgFactor_coe, Subgroup.coe_mul]
    group)

theorem avgConj_apply (B W : Subgroup G) [W.Normal] [IsMulCommutative ↥W] [Fintype ↥B]
    (v : ↥W) :
    avgConj B W v = ∏ b : ↥B, avgFactor B W v b :=
  rfl

/-- The average `avgConj B W v` centralizes `B` (conjugating by `b₀ ∈ B` permutes the factors). -/
theorem avgConj_coe_mem_centralizer (B W : Subgroup G) [W.Normal] [IsMulCommutative ↥W]
    [Fintype ↥B] (v : ↥W) :
    ((avgConj B W v : ↥W) : G) ∈ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  -- conjugation by `b` as an endomorphism of `↥W`
  set c : ↥W →* ↥W := MonoidHom.mk' (fun w => avgFactor B W w ⟨b, hb⟩) (fun w₁ w₂ => by
    refine Subtype.ext ?_
    simp only [avgFactor_coe, Subgroup.coe_mul]
    group) with hc
  have h1 : c (avgConj B W v) = avgConj B W v := by
    have h2 : ∀ b' : ↥B, c (avgFactor B W v b') = avgFactor B W v (⟨b, hb⟩ * b') := by
      intro b'
      refine Subtype.ext ?_
      have hcval : (c (avgFactor B W v b') : G)
          = b * ((avgFactor B W v b' : ↥W) : G) * b⁻¹ := rfl
      rw [hcval, avgFactor_coe, avgFactor_coe]
      simp only [Subgroup.coe_mul]
      group
    calc c (avgConj B W v) = ∏ b' : ↥B, c (avgFactor B W v b') := by
          rw [avgConj_apply, map_prod]
      _ = ∏ b' : ↥B, avgFactor B W v (⟨b, hb⟩ * b') :=
          Finset.prod_congr rfl fun b' _ => h2 b'
      _ = ∏ b' : ↥B, avgFactor B W v b' :=
          Fintype.prod_equiv (Equiv.mulLeft (⟨b, hb⟩ : ↥B)) _ _ (fun _ => rfl)
      _ = avgConj B W v := (avgConj_apply B W v).symm
  have h3 : b * ((avgConj B W v : ↥W) : G) * b⁻¹ = ((avgConj B W v : ↥W) : G) :=
    congrArg Subtype.val h1
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3

/-- On `C_W(B)` the average is the `|B|`-power map. -/
theorem avgConj_apply_of_mem_centralizer (B W : Subgroup G) [W.Normal] [IsMulCommutative ↥W]
    [Fintype ↥B] {v : ↥W} (hv : (v : G) ∈ Subgroup.centralizer (B : Set G)) :
    avgConj B W v = v ^ Nat.card ↥B := by
  rw [avgConj_apply]
  have h1 : ∀ b : ↥B, avgFactor B W v b = v := by
    intro b
    refine Subtype.ext ?_
    rw [avgFactor_coe, Subgroup.mem_centralizer_iff.mp hv (b : G) b.2, mul_inv_cancel_right]
  rw [Finset.prod_congr rfl fun b _ => h1 b, Finset.prod_const, Finset.card_univ,
    Nat.card_eq_fintype_card]

/-- The average of an element of a `B`-stable subgroup `X` stays in `X`. -/
theorem avgConj_coe_mem (B W : Subgroup G) [W.Normal] [IsMulCommutative ↥W] [Fintype ↥B]
    {X : Subgroup G} (hX : ∀ b ∈ B, ∀ x ∈ X, b * x * b⁻¹ ∈ X) {v : ↥W} (hv : (v : G) ∈ X) :
    ((avgConj B W v : ↥W) : G) ∈ X := by
  rw [avgConj_apply]
  refine Finset.prod_induction _ (fun w : ↥W => (w : G) ∈ X)
    (fun a b ha hb => by
      change ((a * b : ↥W) : G) ∈ X
      rw [Subgroup.coe_mul]
      exact X.mul_mem ha hb)
    (by
      change ((1 : ↥W) : G) ∈ X
      rw [Subgroup.coe_one]
      exact X.one_mem)
    (fun b _ => ?_)
  show ((avgFactor B W v b : ↥W) : G) ∈ X
  rw [avgFactor_coe]
  exact hX (b : G) b.2 _ hv

/-- **Disjointness of sups over disjoint index sets from pointwise projections.**  If each `e i`
is the `m`-power map on `V i` and kills `V j` (`j ≠ i`), and `x ↦ x^m` is injective at `1`, then
`⨆_{i ∈ s} V i` and `⨆_{i ∈ t} V i` intersect trivially for disjoint `s t`.  (Applied with
`e i = avgConj (Kᵢ) W`: both the directness of `V = V₁ × ⋯ × Vₙ` and the separation of distinct
`R`-orbit blocks in BG (3.38).) -/
theorem disjoint_biSup_biSup_of_proj {M : Type*} [Group M] [IsMulCommutative M] {ι : Type*}
    (V : ι → Subgroup M) (e : ι → (M →* M)) {m : ℕ}
    (hfix : ∀ i, ∀ v ∈ V i, e i v = v ^ m)
    (hkill : ∀ i j, i ≠ j → ∀ v ∈ V j, e i v = 1)
    (hm : ∀ x : M, x ^ m = 1 → x = 1)
    (s t : Finset ι) (hst : Disjoint s t) :
    Disjoint (⨆ i ∈ s, V i) (⨆ i ∈ t, V i) := by
  rw [disjoint_iff_inf_le]
  intro z hz
  obtain ⟨hzs, hzt⟩ := Subgroup.mem_inf.mp hz
  set E : M →* M := ∏ l ∈ t, e l with hE
  have hEt : E z = z ^ m := by
    have hle : (⨆ i ∈ t, V i : Subgroup M) ≤ MonoidHom.eqLocus E (powMonoidHom m) := by
      refine iSup₂_le fun j hj => fun v hv => ?_
      change E v = powMonoidHom m v
      rw [powMonoidHom_apply, hE, MonoidHom.finsetProd_apply]
      rw [Finset.prod_eq_single j (fun b _ hbj => hkill b j hbj v hv)
        (fun hj' => absurd hj hj')]
      exact hfix j v hv
    exact hle hzt
  have hEs : E z = 1 := by
    rw [hE, MonoidHom.finsetProd_apply]
    refine Finset.prod_eq_one fun l hl => ?_
    have hker : (⨆ i ∈ s, V i : Subgroup M) ≤ (e l).ker := by
      refine iSup₂_le fun k hk => fun v hv => ?_
      rw [MonoidHom.mem_ker]
      refine hkill l k (fun h => ?_) v hv
      exact Finset.disjoint_left.mp hst hk (h ▸ hl)
    exact hker hzs
  rw [Subgroup.mem_bot]
  exact hm z (by rw [← hEt, hEs])

/-- **Conjugation action of a subgroup `A` on a conjugation-closed family of subgroups of `G`**
(as a subtype of `Subgroup G`).  BG (3.38): the `PR`-action on `{K₁, …, Kₙ}`. -/
@[reducible]
def conjSubtypeMulAction (A : Subgroup G) (P : Subgroup G → Prop)
    (hP : ∀ (a : ↥A) (X : Subgroup G), P X → P (X.map (MulAut.conj (a : G)).toMonoidHom)) :
    MulAction ↥A {X : Subgroup G // P X} where
  smul a X := ⟨(X : Subgroup G).map (MulAut.conj (a : G)).toMonoidHom, hP a X X.2⟩
  one_smul X := by
    refine Subtype.ext ?_
    change Subgroup.map _ _ = _
    have h1 : (MulAut.conj ((1 : ↥A) : G)).toMonoidHom = MonoidHom.id G := by
      ext g
      simp
    rw [h1, Subgroup.map_id]
  mul_smul a b X := by
    refine Subtype.ext ?_
    change Subgroup.map _ _ = Subgroup.map _ (Subgroup.map _ _)
    rw [Subgroup.map_map]
    congr 1
    ext g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.coe_mul]
    group

/-- **Normalizing elements of a cyclic subgroup have centralizing commutator** (`Aut` of a cyclic
group is abelian).  BG (3.38), `i > r` step: `[K, R] ⊆ C_K(Vᵢ)` for `R`-invariant `Vᵢ` of prime
order. -/
theorem commutator_mem_centralizer_of_isCyclic {W : Subgroup G} [IsCyclic ↥W] {a b : G}
    (ha : a ∈ Subgroup.normalizer (W : Set G)) (hb : b ∈ Subgroup.normalizer (W : Set G)) :
    ⁅a, b⁆ ∈ Subgroup.centralizer (W : Set G) := by
  set ψ := W.normalizerMonoidHom with hψ
  obtain ⟨ma, hma⟩ := (ψ ⟨a, ha⟩).toMonoidHom.map_cyclic
  obtain ⟨mb, hmb⟩ := (ψ ⟨b, hb⟩).toMonoidHom.map_cyclic
  have hcomm : ψ ⟨a, ha⟩ * ψ ⟨b, hb⟩ = ψ ⟨b, hb⟩ * ψ ⟨a, ha⟩ := by
    ext w
    have h1 : ∀ w : ↥W, ψ ⟨a, ha⟩ w = w ^ ma := fun w => hma w
    have h2 : ∀ w : ↥W, ψ ⟨b, hb⟩ w = w ^ mb := fun w => hmb w
    rw [MulAut.mul_apply, MulAut.mul_apply, h1, h2, h1, h2, ← zpow_mul, ← zpow_mul,
      mul_comm ma mb]
  have hker : ψ ⁅(⟨a, ha⟩ : ↥(Subgroup.normalizer (W : Set G))), ⟨b, hb⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h5 : ⁅a, b⁆ * w * ⁅a, b⁆⁻¹ = w := by
    have h3 : (ψ ⁅(⟨a, ha⟩ : ↥(Subgroup.normalizer (W : Set G))), ⟨b, hb⟩⁆ ⟨w, hw⟩ : G)
        = ⁅a, b⁆ * w * ⁅a, b⁆⁻¹ := rfl
    rw [← h3, hker]
    rfl
  calc w * ⁅a, b⁆ = ⁅a, b⁆ * w * ⁅a, b⁆⁻¹ * ⁅a, b⁆ := by rw [h5]
    _ = ⁅a, b⁆ * w := by group

/-- **Conjugation transport for centralizers**: `C_G(K^g) = C_G(K)^g`. -/
theorem centralizer_map_conj (g : G) (K : Subgroup G) :
    Subgroup.centralizer ((K.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)
      = (Subgroup.centralizer (K : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, fun k hk => ?_, by group⟩
    have h1 := hx (g * k * g⁻¹) ⟨k, hk, rfl⟩
    calc k * (g⁻¹ * x * g) = g⁻¹ * (g * k * g⁻¹ * x) * g := by group
      _ = g⁻¹ * (x * (g * k * g⁻¹)) * g := by rw [h1]
      _ = g⁻¹ * x * g * k := by group
  · rintro ⟨y, hy, rfl⟩ z hz
    obtain ⟨k, hk, rfl⟩ := hz
    have h1 := hy k hk
    calc g * k * g⁻¹ * (g * y * g⁻¹) = g * (k * y) * g⁻¹ := by group
      _ = g * (y * k) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * (g * k * g⁻¹) := by group

end PhaseF

end OddOrder.BG.Ch1.S03f



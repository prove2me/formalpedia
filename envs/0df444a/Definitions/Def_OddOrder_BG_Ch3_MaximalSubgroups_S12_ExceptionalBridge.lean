-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_ExceptionalBridge
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_ExceptionalBridge
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:22:26.337703+00:00
-- url     : https://prove2.me/theorems/da5490b9-84da-42f3-8edc-be48adda72f6
-- title:
--   BG §12: the exceptional bridge, Lemma 12.3 (and Lemma 12.2(b))
-- statement:
--   Formalizes Lemma 12.2(b) (the $\sigma$-case) and Lemma 12.3 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12. This is the bridge connecting §11 (exceptional maximal subgroups) to §12 and the root of the $\tau_2$-cascade 12.4 → 12.5 → 12.6–12.16. It includes the constructor `Hypothesis111.of_normalizer_le` for BG Hypothesis 11.1.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_ExceptionalBridge.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_LocalLemmasCore
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S11_MsigmaANormal
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1218

namespace OddOrder.BG.Ch3

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

namespace S12

/-- Conjugacy of subgroups is symmetric (in the `¬∃ g` form used by Lemma 10.12). -/
theorem not_conj_symm {M H : Subgroup G} (h : ¬ ∃ g : G, MulAut.conj g • M = H) :
    ¬ ∃ g : G, MulAut.conj g • H = M := by
  rintro ⟨g, hg⟩
  exact h ⟨g⁻¹, by rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]⟩

/-- A normal subgroup `W ⊴ ↥M` has its image `W.map M.subtype` normalized by `M`. -/
theorem le_normalizer_map_subtype_of_normal {M : Subgroup G} {W : Subgroup ↥M}
    (hW : W.Normal) :
    M ≤ Subgroup.normalizer ((W.map M.subtype : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨w, hwW, rfl⟩
    exact ⟨⟨m, hm⟩ * w * ⟨m, hm⟩⁻¹, hW.conj_mem w hwW ⟨m, hm⟩, rfl⟩
  · rintro ⟨w, hwW, hwx⟩
    refine ⟨⟨m, hm⟩⁻¹ * w * ⟨m, hm⟩, ?_, ?_⟩
    · have h1 := hW.conj_mem w hwW ⟨m, hm⟩⁻¹
      rwa [inv_inv] at h1
    · have hsub : M.subtype ⟨m, hm⟩ = m := rfl
      rw [map_mul, map_mul, map_inv, hsub, hwx]
      group

/-- **Coprime sup-reduction**: if `P` normalizes `N` and `H ≤ N ⊔ P` has order coprime to
`|P|`, then `H ≤ N`. (In `L = N ⊔ P` the subgroup `N` is normal and `L/N` is an image of
`P`, so the image of `H` in `L/N` has order dividing `gcd(|H|, |P|) = 1`.) -/
theorem le_of_le_sup_of_coprime_card [Finite G] {N P H : Subgroup G}
    (hPN : P ≤ Subgroup.normalizer (N : Set G)) (hH : H ≤ N ⊔ P)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥P)) : H ≤ N := by
  classical
  set L : Subgroup G := N ⊔ P with hLdef
  have hNL : N ≤ L := le_sup_left
  have hPL : P ≤ L := le_sup_right
  have hL_norm : L ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hPN
  have hNsub_norm : (N.subgroupOf L).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hL_norm g.2) (n : G)).mp hn
  set π : ↥L →* ↥L ⧸ N.subgroupOf L := QuotientGroup.mk' (N.subgroupOf L) with hπdef
  -- the quotient is the image of `P`.
  have htop : (P.subgroupOf L).map π = ⊤ := by
    have h1 : ((N.subgroupOf L) ⊔ (P.subgroupOf L)).map π = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hNL hPL, ← hLdef, Subgroup.subgroupOf_self,
        ← MonoidHom.range_eq_map]
      exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    have h2 : (N.subgroupOf L).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup, h2, bot_sup_eq] at h1
  have hcard_quot : Nat.card (↥L ⧸ N.subgroupOf L) ∣ Nat.card ↥P := by
    calc Nat.card (↥L ⧸ N.subgroupOf L)
        = Nat.card ↥(⊤ : Subgroup (↥L ⧸ N.subgroupOf L)) :=
          (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
      _ = Nat.card ↥((P.subgroupOf L).map π) := by rw [htop]
      _ ∣ Nat.card ↥(P.subgroupOf L) := Subgroup.card_map_dvd _ π
      _ = Nat.card ↥P := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv
  -- the image of `H` is trivial.
  have hHbot : (H.subgroupOf L).map π = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥H := by
      calc Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥(H.subgroupOf L) :=
            Subgroup.card_map_dvd _ π
        _ = Nat.card ↥H := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH).toEquiv
    have h2 : Nat.card ↥((H.subgroupOf L).map π) ∣ Nat.card ↥P :=
      (Subgroup.card_subgroup_dvd_card _).trans hcard_quot
    exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd h1 h2)
  intro h hh
  have hmem : (⟨h, hH hh⟩ : ↥L) ∈ H.subgroupOf L := Subgroup.mem_subgroupOf.mpr hh
  have hker : H.subgroupOf L ≤ π.ker := by
    rw [← Subgroup.map_eq_bot_iff]
    exact hHbot
  have h2 : (⟨h, hH hh⟩ : ↥L) ∈ N.subgroupOf L := by
    have := hker hmem
    rwa [hπdef, QuotientGroup.ker_mk'] at this
  exact Subgroup.mem_subgroupOf.mp h2

end S12

namespace S11

/-- **BG Hypothesis 11.1 constructor**: from the literal hypothesis data — `M ∈ ℳ`,
`p ∉ σ(M)`, `A₀ ∈ ℰ_p¹(M)`, `N_G(A₀) ⊆ M` — together with a given
`A ∈ ℰ_p²(M)` containing `A₀`, produce the §11 standing assumption `Hypothesis111`.
The derived data follows BG (mmd L2951-2957): `r_p(M) = 2` is Lemma 10.5
(`pRank_eq_two_of_normalizer_le`); `P` is any Sylow `p`-subgroup of `M` containing `A`;
`N_G(P) ⊄ M` holds because `p ∉ σ(M)`; and `A ∈ ℰ_p*(G)` because any elementary abelian
`F ⊇ A` lies in `C_G(A) ⊆ C_G(A₀) ⊆ N_G(A₀) ⊆ M` and `r_p(M) = 2`. -/
theorem Hypothesis111.of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ S10.sigma M) {A₀ A : Subgroup G}
    (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hN : Subgroup.normalizer (A₀ : Set G) ≤ M)
    (hA : A ∈ elemAbelianOfRank G p 2) (hA₀A : A₀ ≤ A) (hAM : A ≤ M) :
    ∃ P : Subgroup G, Hypothesis111 M p A₀ A P := by
  classical
  have hA₀M : A₀ ≤ M := Subgroup.le_normalizer.trans hN
  -- Lemma 10.5: `r_p(M) = 2`.
  obtain ⟨hr2, -, -⟩ := S10.pRank_eq_two_of_normalizer_le hG hM hp hA₀ hN
  -- a Sylow `p`-subgroup `P` of `M` containing `A`.
  have hApg : IsPGroup p ↥A := hA.1.isPGroup
  obtain ⟨PM, hAPM⟩ := hApg.comap_subtype.exists_le_sylow (G := M)
  set P : Subgroup G := (PM : Subgroup ↥M).map M.subtype with hPdef
  have hPM_le : P ≤ M := Subgroup.map_subtype_le _
  have hAP : A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hAM]
    exact Subgroup.map_mono hAPM
  have hPpg : IsPGroup p ↥P := by
    rw [hPdef]; exact PM.isPGroup'.map _
  -- `P` is `p`-maximal in `M`.
  have hPsyl : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P := by
    intro R hPR hRM hRpg
    have hle : (PM : Subgroup ↥M) ≤ R.subgroupOf M := by
      refine le_trans (fun x hx => Subgroup.mem_subgroupOf.mpr ?_) (Subgroup.comap_mono hPR)
      rw [hPdef]
      exact Subgroup.mem_map_of_mem _ hx
    have heq : R.subgroupOf M = PM := PM.3 hRpg.comap_subtype hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, heq, hPdef]
  -- `N_G(P) ⊄ M` since `p ∉ σ(M)`.
  have hPnot : ¬ Subgroup.normalizer (P : Set G) ≤ M := by
    intro hcon
    apply hp
    rw [S10.mem_sigma_iff]
    refine ⟨?_, PM, ?_⟩
    · have hdvd : p ∣ Nat.card ↥M := by
        have h1 : (p : ℕ) ∣ Nat.card ↥A := by
          rw [hA.2]; exact dvd_pow_self p two_ne_zero
        exact h1.trans (Subgroup.card_dvd_of_le hAM)
      exact Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩
    · rw [← hPdef]; exact hcon
  -- `A ∈ ℰ_p*(G)`: any elementary abelian `F ⊇ A` lies in `M`, and `r_p(M) = 2`.
  have hAmax : IsMaximalElementaryAbelian p A := by
    refine ⟨hA.1, fun F hF hAF => ?_⟩
    by_contra hne
    have hFM : F ≤ M := by
      refine le_trans (fun f hf => ?_) ((Subgroup.centralizer_le_normalizer _).trans hN)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      simpa using congrArg Subtype.val (hF.comm (⟨a, hAF (hA₀A ha)⟩ : ↥F) ⟨f, hf⟩)
    have hAltF : A < F := lt_of_le_of_ne hAF (fun h => hne h.symm)
    have hcard_lt : Nat.card ↥A < Nat.card ↥F := by
      refine lt_of_le_of_ne
        (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hAltF.le))
        (fun hcard => ?_)
      exact hne ((Subgroup.eq_of_le_of_card_ge hAF hcard.ge).symm)
    obtain ⟨k, hk⟩ := hF.isPGroup.exists_card_eq
    have hk3 : 3 ≤ k := by
      by_contra hk3
      have hle : Nat.card ↥F ≤ p ^ 2 := by
        rw [hk]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
      rw [hA.2] at hcard_lt
      omega
    have hFsub_ea : (F.subgroupOf M).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hFM).symm hF
    have hle := le_pRank (G := ↥M) (F.subgroupOf M) hFsub_ea
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFM).toEquiv, hk,
      Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    omega
  exact ⟨P, hM, Fact.out, hp, hA₀, hA₀M, hN, hA, hAM, hA₀A, hPpg, hAP, hPM_le, hPsyl,
    hPnot, hAmax⟩

end S11

namespace S12

/-- **BG Lemma 12.2(b)** (σ-case): if `p ∈ σ(M)`, `X` is a nonidentity `p`-subgroup of `M`
with `N_G(X) ⊆ M* ≠ M`, then `M*` is not conjugate to `M` in `G`. By Theorem 10.1(b),
`C_G(X)` acts transitively on `{M^g | X ⊆ M^g}`; if `M* = M^h` then some `c ∈ C_G(X)`
conjugates `M*` to `M`, but `c ∈ C_G(X) ⊆ N_G(X) ⊆ M*` fixes `M*`, so `M* = M`. -/
theorem not_conj_of_mem_sigma_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ S10.sigma M) {X : Subgroup G} (hXM : X ≤ M) (hXne : X ≠ ⊥)
    (hXp : IsPGroup p ↥X) (hN : Subgroup.normalizer (X : Set G) ≤ Mstar)
    (hMne : Mstar ≠ M) :
    ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
  rintro ⟨h, hh⟩
  have hb := (S10.fusion_control_of_mem_sigma hG hM hp hXne hXp).2.1
  have hXMstar : X ≤ MulAut.conj h • M := by
    rw [hh]; exact Subgroup.le_normalizer.trans hN
  have hXM1 : X ≤ MulAut.conj (1 : G) • M := by
    rw [map_one, one_smul]; exact hXM
  obtain ⟨c, hcC, hc⟩ := hb h 1 hXMstar hXM1
  rw [map_one, one_smul, hh] at hc
  have hcMstar : c ∈ Mstar := hN (Subgroup.centralizer_le_normalizer _ hcC)
  have hfix : MulAut.conj c • Mstar = Mstar :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hcMstar)
  rw [hfix] at hc
  exact hMne hc

/-- Pointwise `MulAut`-smul of a subgroup is its image.
(Public: §12 uses this for conjugation transport, e.g. in Theorem 12.7.) -/
theorem mulAut_smul_eq_map (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map φ.toMonoidHom := by
  ext x
  exact ⟨fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩, fun ⟨y, hy, hyx⟩ => ⟨y, hy, hyx⟩⟩

/-- Conjugation commutes with the normalizer. -/
theorem normalizer_conj_smul (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.normalizer (H : Set G)
      = Subgroup.normalizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  rw [mulAut_smul_eq_map, mulAut_smul_eq_map]
  exact Subgroup.map_normalizer_eq_of_bijective H (MulAut.conj g).bijective

/-- Conjugation commutes with the centralizer. -/
theorem centralizer_conj_smul (g : G) (H : Subgroup G) :
    MulAut.conj g • Subgroup.centralizer (H : Set G)
      = Subgroup.centralizer ((MulAut.conj g • H : Subgroup G) : Set G) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro hx h hh
    rw [SetLike.mem_coe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hh
    have h1 := hx _ (SetLike.mem_coe.mpr hh)
    -- `h1` says `(g⁻¹hg)(g⁻¹xg) = (g⁻¹xg)(g⁻¹hg)`; conjugate back by `g`.
    have h2 := congrArg (fun z => g * z * g⁻¹) h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h2
  · intro hx h hh
    have hgh : g * h * g⁻¹ ∈ (MulAut.conj g • H : Subgroup G) := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hh
    have h1 := hx _ (SetLike.mem_coe.mpr hgh)
    have h2 := congrArg (fun z => g⁻¹ * z * g) h1
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using h2

/-- Conjugation preserves coatoms (maximal subgroups). -/
theorem isCoatom_conj_smul {g : G} {M : Subgroup G} (h : IsCoatom M) :
    IsCoatom (MulAut.conj g • M) := by
  have hMeq : M = MulAut.conj g⁻¹ • (MulAut.conj g • M) := by
    rw [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  constructor
  · intro htop
    apply h.1
    rw [eq_top_iff]
    intro x _
    have hx : g * x * g⁻¹ ∈ MulAut.conj g • M := by
      rw [htop]; exact Subgroup.mem_top _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simpa [MulAut.smul_def, mul_assoc] using hx
  · intro b hb
    have hle : M ≤ MulAut.conj g⁻¹ • b := by
      rw [hMeq]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hb.le
    have h1 : M < MulAut.conj g⁻¹ • b := by
      refine lt_of_le_of_ne hle (fun heq => hb.ne ?_)
      rw [heq, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    have h2 := h.2 _ h1
    have h3 := congrArg (fun K => MulAut.conj g • K) h2
    simpa [← mul_smul, ← map_mul, mul_inv_cancel] using h3

/-- **BG Lemma 12.2(b)** (τ₁∪τ₃-case): if `p ∈ τ₁(M) ∪ τ₃(M)`, `X` is a nonidentity
`p`-subgroup of `M`, and `N_G(X) ≤ M*`, then `M*` is not conjugate to `M` in `G`.
If `M* = M^g`, then `X' = X^{g⁻¹}` is a nonidentity `p`-subgroup of `M` with
`N_G(X') ≤ M`, so Lemma 12.2(a) (applied with `M* := M`) forces `p ∈ σ(M) ∪ τ₂(M)` —
contradicting `r_p(M) = 1` and `p ∉ σ(M)`. -/
theorem not_conj_of_mem_tau1_union_tau3_of_normalizer_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau1 M ∪ tau3 M) {X : Subgroup G} (_hXM : X ≤ M)
    (hXne : X ≠ ⊥) (hXp : IsPGroup p ↥X)
    (hN : Subgroup.normalizer (X : Set G) ≤ Mstar) :
    ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
  rintro ⟨g, hg⟩
  set X' : Subgroup G := MulAut.conj g⁻¹ • X with hX'def
  have hcollapse : MulAut.conj g⁻¹ • Mstar = M := by
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hX'M : X' ≤ M := by
    rw [hX'def, ← hcollapse]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
      (Subgroup.le_normalizer.trans hN)
  have hX'ne : X' ≠ ⊥ := by
    intro hbot
    apply hXne
    have h1 : MulAut.conj g • X' = X := by
      rw [hX'def, ← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
    rw [← h1, hbot]
    ext x
    simp
  have hX'p : IsPGroup p ↥X' := by
    rw [hX'def, mulAut_smul_eq_map]
    exact hXp.map _
  have hN' : Subgroup.normalizer (X' : Set G) ≤ M := by
    rw [hX'def, ← normalizer_conj_smul, ← hcollapse]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hN
  have h122a := prime_mem_sigma_or_tau2 hG hM hX'M hX'ne hX'p
    (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hN'⟩)
  rcases hp with hp1 | hp3
  · rcases h122a with hσ | hτ2
    · exact hp1.1 hσ
    · have h1 := tau1_pRank_eq_one hp1
      have h2 := ((mem_tau2_iff M p).mp hτ2).2
      omega
  · rcases h122a with hσ | hτ2
    · exact hp3.1 hσ
    · have h1 := tau3_pRank_eq_one hp3
      have h2 := ((mem_tau2_iff M p).mp hτ2).2
      omega

/-- **BG Theorem 10.2(d), Sylow `p`-closure** (used in the proof of Lemma 12.3(a),
mmd L3115-3119): for `p ∈ σ(M)` and a Sylow `p`-subgroup `S` of `M`, the join
`M_α ⊔ S` is normalized by `M`. In the quotient `M/M_α` the image of `S` is a Sylow
`p`-subgroup lying inside the nilpotent Fitting subgroup `F(M/M_α)` (because `S ≤ M_σ`
and `M_σ M_α/M_α ≤ F(M/M_α)` by Theorem 10.2(d)), hence is normal in `M/M_α`;
its preimage `M_α ⊔ S` is therefore normal in `M`. -/
theorem normalizer_Malpha_sup_sylow_of_mem_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ S10.sigma M) (SM : Sylow p ↥M) :
    M ≤ Subgroup.normalizer
      ((S10.Malpha M ⊔ (SM : Subgroup ↥M).map M.subtype : Subgroup G) : Set G) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set N : Subgroup ↥M := (S10.Malpha M).subgroupOf M with hNdef
  have hN_norm : N.Normal := by rw [hNdef, S10.Malpha_subgroupOf]; infer_instance
  set π : ↥M →* ↥M ⧸ N := QuotientGroup.mk' N with hπdef
  -- the image of `SM` is a Sylow `p`-subgroup of the quotient.
  set Sb : Sylow p (↥M ⧸ N) := SM.mapSurjective (QuotientGroup.mk'_surjective N) with hSbdef
  have hSb_coe : (Sb : Subgroup (↥M ⧸ N)) = (SM : Subgroup ↥M).map π := rfl
  -- `SM ≤ M_σ.subgroupOf M` since `p ∈ σ(M)`.
  have hSM_Mσ : (SM : Subgroup ↥M) ≤ (S10.Msigma M).subgroupOf M := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact S10.sigma_subgroup_le_Msigma_of_isHall
      (S10.isHall_Msigma_Malpha hG hM).1 (Subgroup.map_subtype_le _)
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem (SM.isPGroup'.map _) hp)
      (Subgroup.mem_map_of_mem _ hx)
  -- hence `Sb ≤ F(M/M_α)`, which is nilpotent.
  have hSb_F : (Sb : Subgroup (↥M ⧸ N)) ≤ Ch01.fitting (↥M ⧸ N) := by
    rw [hSb_coe]
    exact (Subgroup.map_mono hSM_Mσ).trans (S10.Msigma_quotient_Malpha_le_fitting hG hM)
  -- a Sylow subgroup inside a nilpotent normal subgroup is normal.
  set SbF : Sylow p ↥(Ch01.fitting (↥M ⧸ N)) := Sb.subtype hSb_F with hSbFdef
  have hSbF_norm : (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).Normal := by
    have htfae := (Group.isNilpotent_of_finite_tfae (G := ↥(Ch01.fitting (↥M ⧸ N)))).out 0 3
    exact htfae.mp inferInstance p ⟨Fact.out⟩ SbF
  have hSbF_char : (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).Characteristic :=
    Sylow.characteristic_of_normal SbF hSbF_norm
  have hSb_norm : (Sb : Subgroup (↥M ⧸ N)).Normal := by
    have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := Ch01.fitting (↥M ⧸ N)) (W := (SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))))
    have h2 : ((SbF : Subgroup ↥(Ch01.fitting (↥M ⧸ N))).map
        (Ch01.fitting (↥M ⧸ N)).subtype) = (Sb : Subgroup (↥M ⧸ N)) := by
      rw [hSbFdef, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSb_F]
    rw [h2] at h1
    have h3 : Subgroup.normalizer
        ((Ch01.fitting (↥M ⧸ N) : Subgroup (↥M ⧸ N)) : Set (↥M ⧸ N)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr (Ch01.fitting.normal (↥M ⧸ N))
    constructor
    intro n hn g
    have hg : g ∈ Subgroup.normalizer ((Sb : Subgroup (↥M ⧸ N)) : Set (↥M ⧸ N)) :=
      h1 (h3 ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  -- pull back: `SM ⊔ N` is normal in `↥M`, and maps to `S ⊔ M_α` in `G`.
  have hcomap_norm : ((Sb : Subgroup (↥M ⧸ N)).comap π).Normal := hSb_norm.comap π
  have hcomap_eq : (Sb : Subgroup (↥M ⧸ N)).comap π = (SM : Subgroup ↥M) ⊔ N := by
    rw [hSb_coe, Subgroup.comap_map_eq, hπdef, QuotientGroup.ker_mk']
  have htransport := le_normalizer_map_subtype_of_normal (hcomap_eq ▸ hcomap_norm)
  have hmap_eq : ((SM : Subgroup ↥M) ⊔ N).map M.subtype
      = S10.Malpha M ⊔ (SM : Subgroup ↥M).map M.subtype := by
    rw [Subgroup.map_sup, hNdef, Subgroup.map_subgroupOf_eq_of_le (S10.Malpha_le M), sup_comm]
  rwa [hmap_eq] at htransport

/-- **Lemma 12.3, commutator engine** (mmd L3107-3111): whether `p ∈ σ(M*)` (then
`A ≤ M*_σ`) or not (then `M*_σ A ⊴ M*` by Theorem 11.7 via Hypothesis 11.1), the join
`M*_σ ⊔ A` is normalized by `M*`. Consequently every `A`-invariant `p'`-subgroup
`K ≤ M*` satisfies `⁅A, K⁆ ≤ K ⊓ M*_σ A ≤ K ⊓ M*_σ`. -/
theorem commutator_le_inf_Msigma_of_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {Mstar : Subgroup G} (hMstar : Mstar ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A₀ A : Subgroup G} (hA₀ : A₀ ∈ elemAbelianOfRank G p 1)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar)
    (hA : A ∈ elemAbelianOfRank G p 2) (hA₀A : A₀ ≤ A) (hAMstar : A ≤ Mstar)
    {K : Subgroup G} (hKM : K ≤ Mstar) (hKinv : A ≤ Subgroup.normalizer (K : Set G))
    (hKp : ¬ p ∣ Nat.card ↥K) :
    ⁅A, K⁆ ≤ K ⊓ S10.Msigma Mstar := by
  classical
  -- `M* ≤ N_G(M*_σ ⊔ A)` in either case.
  have hsup : Mstar ≤ Subgroup.normalizer ((S10.Msigma Mstar ⊔ A : Subgroup G) : Set G) := by
    by_cases hpσ : p ∈ S10.sigma Mstar
    · have hAMσ : A ≤ S10.Msigma Mstar :=
        S10.sigma_subgroup_le_Msigma_of_isHall (S10.isHall_Msigma_Malpha hG hMstar).1
          hAMstar (Subgroup.isPiSubgroup_of_isPGroup_of_mem hA.1.isPGroup hpσ)
      rw [sup_eq_left.mpr hAMσ]
      exact le_normalizer_opiCoreInG _ _
    · obtain ⟨P, h111⟩ :=
        S11.Hypothesis111.of_normalizer_le hG hMstar hpσ hA₀ hN hA hA₀A hAMstar
      exact S11.MsigmaA_normal hG h111
  -- elementwise: `⁅A, K⁆ ≤ K ⊓ (M*_σ ⊔ A)`.
  have h1 : ⁅A, K⁆ ≤ K ⊓ (S10.Msigma Mstar ⊔ A) := by
    rw [Subgroup.commutator_le]
    intro a ha k hk
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h2 : a * k * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKinv ha) k).mp hk
      have h3 : a * k * a⁻¹ * k⁻¹ ∈ K := K.mul_mem h2 (K.inv_mem hk)
      rwa [commutatorElement_def]
    · have hkM : k ∈ Mstar := hKM hk
      have h2 : k * a⁻¹ * k⁻¹ ∈ S10.Msigma Mstar ⊔ A :=
        (Subgroup.mem_normalizer_iff.mp (hsup hkM) a⁻¹).mp
          (Subgroup.mem_sup_right (A.inv_mem ha))
      have h3 : a * (k * a⁻¹ * k⁻¹) ∈ S10.Msigma Mstar ⊔ A :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_right ha) h2
      rw [commutatorElement_def]
      simpa [mul_assoc] using h3
  -- coprime reduction: `K ⊓ (M*_σ ⊔ A) ≤ M*_σ`.
  refine h1.trans (le_inf inf_le_left ?_)
  have hAnorm : A ≤ Subgroup.normalizer ((S10.Msigma Mstar : Subgroup G) : Set G) :=
    hAMstar.trans (le_normalizer_opiCoreInG _ _)
  refine le_of_le_sup_of_coprime_card hAnorm inf_le_right ?_
  have hnp : ¬ p ∣ Nat.card ↥(K ⊓ (S10.Msigma Mstar ⊔ A) : Subgroup G) :=
    fun h => hKp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  rw [hA.2]
  exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm.pow_right 2

/-- **BG Lemma 12.3(a)** (mmd L3101): `M* ∈ ℳ − {M}`, `A ∈ ℰ_p²(M ∩ M*)`,
`A₀ ∈ ℰ¹(A)` with `N_G(A₀) ⊆ M*`, and `p ∉ σ(M)`. Then `A` centralizes `M_σ ∩ M*`.

Proof (mmd L3113-3123): let `K = M_σ ∩ M*`, an `A`-invariant `p'`-subgroup of `M*`.
If `p ∉ σ(M*)`, the engine gives `⁅A,K⁆ ≤ M_σ ∩ M*_σ`, which is `⊥` by Corollary 11.4
(else `M* = M`). If `p ∈ σ(M*)`, then `M*` is not conjugate to `M` (σ-sets differ),
`A ≤ S` for a Sylow `p`-subgroup `S` of `M*` with `M*_α S ⊴ M*` (Theorem 10.2(d)
Sylow closure), so `⁅A,K⁆ ≤ K ⊓ M*_α S ≤ M*_α ⊓ M_σ = ⊥` by Lemma 10.12(a). -/
theorem elemAb_centralizes_Msigma_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hne : Mstar ≠ M) {p : ℕ} [Fact p.Prime]
    (hp : p ∉ S10.sigma M) {A A₀ : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M ⊓ Mstar) (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) := by
  classical
  have hAM' : A ≤ M := hAM.trans inf_le_left
  have hAMstar : A ≤ Mstar := hAM.trans inf_le_right
  set K : Subgroup G := S10.Msigma M ⊓ Mstar with hKdef
  have hKMstar : K ≤ Mstar := inf_le_right
  have hKMσ : K ≤ S10.Msigma M := inf_le_left
  have hKinv : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf (hAM'.trans (le_normalizer_opiCoreInG _ _))
      (hAMstar.trans Subgroup.le_normalizer)
  have hKp : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    have h1 : p ∣ Nat.card ↥(S10.Msigma M) := hdvd.trans (Subgroup.card_dvd_of_le hKMσ)
    exact hp (S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, h1, Nat.card_pos.ne'⟩))
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  by_cases hpσ : p ∈ S10.sigma Mstar
  · -- `p ∈ σ(M*)`: `M*` is not conjugate to `M`, and `⁅A,K⁆ ≤ M*_α ⊓ M_σ = ⊥`.
    have hnc : ¬ ∃ g : G, MulAut.conj g • M = Mstar := by
      rintro ⟨g, hg⟩
      apply hp
      have h1 : p ∈ S10.sigma (MulAut.conj g⁻¹ • (MulAut.conj g • M)) :=
        S10.sigma_conj g⁻¹ (hg ▸ hpσ)
      rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h1
    have h1012 := ((S10.disjoint_of_not_conj hG hMstar hM (not_conj_symm hnc)).1).1
    -- `A ≤ M*_σ` and a Sylow `p`-subgroup `S ⊇ A` of `M*`.
    have hApg : IsPGroup p ↥A := hA.1.isPGroup
    obtain ⟨SM, hASM⟩ := hApg.comap_subtype.exists_le_sylow (G := Mstar)
    set S : Subgroup G := (SM : Subgroup ↥Mstar).map Mstar.subtype with hSdef
    have hAS : A ≤ S := by
      rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hAMstar]
      exact Subgroup.map_mono hASM
    have hT := normalizer_Malpha_sup_sylow_of_mem_sigma hG hMstar hpσ SM
    -- `⁅A,K⁆ ≤ K ⊓ (M*_α ⊔ S)` elementwise.
    have hcomm_le : ⁅A, K⁆ ≤ K ⊓ (S10.Malpha Mstar ⊔ S) := by
      rw [Subgroup.commutator_le]
      intro a ha k hk
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h2 : a * k * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hKinv ha) k).mp hk
        have h3 : a * k * a⁻¹ * k⁻¹ ∈ K := K.mul_mem h2 (K.inv_mem hk)
        rwa [commutatorElement_def]
      · have hkM : k ∈ Mstar := hKMstar hk
        have h2 : k * a⁻¹ * k⁻¹ ∈ S10.Malpha Mstar ⊔ S :=
          (Subgroup.mem_normalizer_iff.mp (hT hkM) a⁻¹).mp
            (Subgroup.mem_sup_right (S.inv_mem (hAS ha)))
        have h3 : a * (k * a⁻¹ * k⁻¹) ∈ S10.Malpha Mstar ⊔ S :=
          Subgroup.mul_mem _ (Subgroup.mem_sup_right (hAS ha)) h2
        rw [commutatorElement_def]
        simpa [mul_assoc] using h3
    -- coprime reduction to `M*_α`, then Lemma 10.12(a).
    have hred : K ⊓ (S10.Malpha Mstar ⊔ S) ≤ S10.Malpha Mstar := by
      refine le_of_le_sup_of_coprime_card
        ((Subgroup.map_subtype_le _).trans (le_normalizer_opiCoreInG _ _)) inf_le_right ?_
      have hnp : ¬ p ∣ Nat.card ↥(K ⊓ (S10.Malpha Mstar ⊔ S) : Subgroup G) :=
        fun h => hKp (h.trans (Subgroup.card_dvd_of_le inf_le_left))
      obtain ⟨k, hk⟩ := (SM.isPGroup'.map Mstar.subtype).exists_card_eq
      rw [← hSdef] at hk
      rw [hk]
      exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm.pow_right k
    have hfin : ⁅A, K⁆ ≤ S10.Malpha Mstar ⊓ S10.Msigma M :=
      le_inf (hcomm_le.trans hred) ((hcomm_le.trans inf_le_left).trans hKMσ)
    rw [← le_bot_iff, ← h1012]
    exact hfin
  · -- `p ∉ σ(M*)`: engine + Corollary 11.4.
    have heng := commutator_le_inf_Msigma_of_normalizer_le hG hMstar hA₀ hN hA hA₀A
      hAMstar hKMstar hKinv hKp
    rcases eq_or_ne ⁅A, K⁆ ⊥ with hbot | hne_bot
    · exact hbot
    · exfalso
      obtain ⟨P, h111⟩ :=
        S11.Hypothesis111.of_normalizer_le hG hMstar hpσ hA₀ hN hA hA₀A hAMstar
      have hmeet : S10.Msigma Mstar ⊓ S10.Msigma M ≠ ⊥ := by
        intro hmeet_bot
        apply hne_bot
        rw [← le_bot_iff, ← hmeet_bot]
        exact le_inf (heng.trans inf_le_right) (heng.trans (inf_le_left.trans hKMσ))
      exact hne (S11.eq_of_Msigma_meet_Hsigma hG h111
        (mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hM, hAM'⟩) hmeet)

/-- **BG Lemma 12.3(b)** (mmd L3103): `M* ∈ ℳ − {M}`, `A ∈ ℰ_p²(M ∩ M*)`,
`A₀ ∈ ℰ¹(A)` with `N_G(A₀) ⊆ M*`, and `p ∈ σ(M) − α(M)`. Then `A` centralizes
`M_α ∩ M*`.

Proof (mmd L3113): `K = M_α ∩ M*` is an `A`-invariant `p'`-subgroup of `M*`
(`p ∉ α(M)`), so the engine gives `⁅A,K⁆ ≤ K ⊓ M*_σ ≤ M_α ⊓ M*_σ`. By Lemma 12.2(b)
`M*` is not conjugate to `M`, so `M_α ⊓ M*_σ = ⊥` by Lemma 10.12(a). -/
theorem elemAb_centralizes_Malpha_meet [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hne : Mstar ≠ M) {p : ℕ} [Fact p.Prime]
    (hpσ : p ∈ S10.sigma M) (hpα : p ∉ S10.alpha M) {A A₀ : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M ⊓ Mstar)
    (hA₀ : A₀ ∈ elemAbelianOfRank G p 1) (hA₀A : A₀ ≤ A)
    (hN : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    A ≤ Subgroup.centralizer ((S10.Malpha M ⊓ Mstar : Subgroup G) : Set G) := by
  classical
  have hAM' : A ≤ M := hAM.trans inf_le_left
  have hAMstar : A ≤ Mstar := hAM.trans inf_le_right
  set K : Subgroup G := S10.Malpha M ⊓ Mstar with hKdef
  have hKMstar : K ≤ Mstar := inf_le_right
  have hKMα : K ≤ S10.Malpha M := inf_le_left
  have hKinv : A ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_inf (hAM'.trans (le_normalizer_opiCoreInG _ _))
      (hAMstar.trans Subgroup.le_normalizer)
  have hKp : ¬ p ∣ Nat.card ↥K := by
    intro hdvd
    have h1 : p ∣ Nat.card ↥(S10.Malpha M) := hdvd.trans (Subgroup.card_dvd_of_le hKMα)
    exact hpα (S10.Malpha_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨Fact.out, h1, Nat.card_pos.ne'⟩))
  -- non-conjugacy via Lemma 12.2(b) with `X = A₀`.
  have hA₀M : A₀ ≤ M := hA₀A.trans hAM'
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A₀ = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hA₀.2, pow_one] at h1
    exact (Fact.out : p.Prime).one_lt.ne' h1
  have hnc := not_conj_of_mem_sigma_of_normalizer_le hG hM hpσ hA₀M hA₀ne
    hA₀.1.isPGroup hN hne
  have h1012 := ((S10.disjoint_of_not_conj hG hM hMstar hnc).1).1
  -- engine + Lemma 10.12(a).
  have heng := commutator_le_inf_Msigma_of_normalizer_le hG hMstar hA₀ hN hA hA₀A
    hAMstar hKMstar hKinv hKp
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← h1012]
  exact le_inf ((heng.trans inf_le_left).trans hKMα) (heng.trans inf_le_right)

/-- A member of `ℰ_p¹(G)` is nontrivial. -/
theorem ne_bot_of_mem_elemAbelianOfRank_one {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : X ∈ elemAbelianOfRank G p 1) : X ≠ ⊥ := by
  intro hbot
  have h1 : Nat.card ↥X = 1 := by rw [hbot]; exact Subgroup.card_bot
  rw [hX.2, pow_one] at h1
  exact (Fact.out : p.Prime).one_lt.ne' h1

/-- A nontrivial elementary abelian `p`-subgroup contains a line (`ℰ¹`-member). -/
theorem exists_line_le [Finite G] {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A.IsElementaryAbelian p) (hne : A ≠ ⊥) :
    ∃ X ∈ elemAbelianOfRank G p 1, X ≤ A := by
  obtain ⟨x, hxA, hx1⟩ := (A.bot_or_exists_ne_one).resolve_left hne
  have hxp : x ^ p = 1 := by
    simpa using congrArg Subtype.val (hA.pow_eq_one ⟨x, hxA⟩)
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  refine ⟨Subgroup.zpowers x, ⟨?_, ?_⟩, (Subgroup.zpowers_le).mpr hxA⟩
  · exact Subgroup.IsElementaryAbelian.of_card_prime (by rw [Nat.card_zpowers, hord])
  · rw [Nat.card_zpowers, hord, pow_one]

/-- The normalizer of a nontrivial subgroup of a maximal subgroup is proper (the ambient
group is simple). -/
theorem normalizer_lt_top_of_le_of_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXM : X ≤ M)
    (hXne : X ≠ ⊥) :
    Subgroup.normalizer (X : Set G) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro hNtop
  have hXnormal : X.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  rcases hG.simple.eq_bot_or_eq_top_of_normal X inferInstance with hXbot | hXtop
  · exact hXne hXbot
  · exact (mem_maximalSubgroups.mp hM).1 (top_le_iff.mp (hXtop ▸ hXM))

/-- If `ℳ(N_G(X)) ≠ {M}` for a nontrivial `X ≤ M`, then some maximal subgroup other than
`M` contains `N_G(X)`. -/
theorem exists_maximal_ne_of_normalizer_ne_singleton [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {X : Subgroup G} (hXne : X ≠ ⊥)
    (hXM : X ≤ M)
    (hne : maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {M}) :
    ∃ Mstar ∈ maximalSubgroups G, Mstar ≠ M ∧
      Subgroup.normalizer (X : Set G) ≤ Mstar := by
  classical
  have hNlt := normalizer_lt_top_of_le_of_ne_bot hG hM hXM hXne
  obtain ⟨Mst, hMst_co, hMst_le⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left hNlt.ne
  rcases Classical.em (∃ H ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)),
      H ≠ M) with ⟨H, hH, hHne⟩ | hall
  · obtain ⟨hH_co, hH_le⟩ := mem_maximalSubgroupsContaining.mp hH
    exact ⟨H, mem_maximalSubgroups.mpr hH_co, hHne, hH_le⟩
  · exfalso
    apply hne
    have hMstM : Mst = M := by
      by_contra hMM
      exact hall ⟨Mst, mem_maximalSubgroupsContaining.mpr ⟨hMst_co, hMst_le⟩, hMM⟩
    refine Set.eq_singleton_iff_unique_mem.mpr
      ⟨hMstM ▸ mem_maximalSubgroupsContaining.mpr ⟨hMst_co, hMst_le⟩, fun H hH => ?_⟩
    by_contra hHne
    exact hall ⟨H, hH, hHne⟩

/-- Centralizing is symmetric: `H ≤ C_G(K)` iff `K ≤ C_G(H)` (one direction). -/
theorem le_centralizer_swap {H K : Subgroup G}
    (h : H ≤ Subgroup.centralizer (K : Set G)) :
    K ≤ Subgroup.centralizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.mp (h hy) k hk).symm

/-- An elementary abelian subgroup centralizes itself. -/
theorem le_centralizer_self_of_isElementaryAbelian {p : ℕ} {A : Subgroup G}
    (hA : A.IsElementaryAbelian p) : A ≤ Subgroup.centralizer (A : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hA.comm ⟨y, hy⟩ ⟨a, ha⟩)

/-- An element centralizing `A` and `B` centralizes `A ⊔ B`. -/
theorem inf_centralizer_le_centralizer_sup {A B : Subgroup G} :
    Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) ≤
      Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  rintro x ⟨hxA, hxB⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hle : A ⊔ B ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le ?_ ?_ <;> intro a ha <;> rw [Subgroup.mem_centralizer_iff] <;>
      intro y hy <;> rw [Set.mem_singleton_iff] at hy <;> subst hy
    · exact (Subgroup.mem_centralizer_iff.mp hxA a ha).symm
    · exact (Subgroup.mem_centralizer_iff.mp hxB a ha).symm
  exact (Subgroup.mem_centralizer_iff.mp (hle hh) x (Set.mem_singleton x)).symm

/-- The join of two elementwise-commuting elementary abelian `p`-subgroups is elementary
abelian. -/
theorem isElementaryAbelian_sup_of_le_centralizer {p : ℕ} {A B : Subgroup G}
    (hA : A.IsElementaryAbelian p) (hB : B.IsElementaryAbelian p)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    (A ⊔ B).IsElementaryAbelian p := by
  have hsup_eq : A ⊔ B = Subgroup.closure ((A : Set G) ∪ B) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  have hcent : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    sup_le
      ((le_inf (le_centralizer_self_of_isElementaryAbelian hA) hAB).trans
        inf_centralizer_le_centralizer_sup)
      ((le_inf (le_centralizer_swap hAB) (le_centralizer_self_of_isElementaryAbelian hB)).trans
        inf_centralizer_le_centralizer_sup)
  constructor
  · intro x y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent y.2) (x : G) x.2)
  · intro x
    have hx : (x : G) ∈ Subgroup.closure ((A : Set G) ∪ B) := by
      rw [← hsup_eq]; exact x.2
    have hxp : (x : G) ^ p = 1 := by
      refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
      · rintro g (hg | hg)
        · simpa using congrArg Subtype.val (hA.pow_eq_one ⟨g, hg⟩)
        · simpa using congrArg Subtype.val (hB.pow_eq_one ⟨g, hg⟩)
      · exact one_pow p
      · intro g h hg hh hgp hhp
        have hgs : g ∈ A ⊔ B := by rw [hsup_eq]; exact hg
        have hhs : h ∈ A ⊔ B := by rw [hsup_eq]; exact hh
        have hcomm : Commute g h :=
          (Subgroup.mem_centralizer_iff.mp (hcent hgs) h hhs).symm
        rw [hcomm.mul_pow, hgp, hhp, mul_one]
      · intro g hg hgp
        rw [inv_pow, hgp, inv_one]
    exact Subtype.ext (by simpa using hxp)

/-- A rank-two member of `ℰ_p²(G)` has rank at least `2` (as an abstract group). -/
theorem two_le_rank_of_mem_elemAbelianOfRank_two [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) : 2 ≤ rank ↥A := by
  have htop_ea : (⊤ : Subgroup ↥A).IsElementaryAbelian p :=
    OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv Subgroup.topEquiv.symm hA.1
  have hle := le_pRank (G := ↥A) ⊤ htop_ea
  rw [Nat.card_congr Subgroup.topEquiv.toEquiv, hA.2,
    Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
  exact hle.trans (pRank_le_rank p)

/-- **Line-generation engine** (BG Proposition 1.16(2), specialised to a rank-two
elementary abelian `A`): if `A` normalizes a `p'`-subgroup `W` and
`C_W(Y) = W ⊓ C_G(Y) ≤ T` for **every** line `Y ∈ ℰ¹(A)`, then `W ≤ T`.
By 1.16(2), `W = ⟨C_W(Y) | Y ≤ A, A/Y cyclic⟩`; a cocyclic `Y ≤ A` is `⊥` (impossible:
`A` is not cyclic), a line (supplied), or all of `A` (then `C_W(A) ≤ C_W(Y₀)` for any
line `Y₀`). Used in Proposition 12.4 (`T = C_G(A)`) and Theorem 12.7 (`T = C_G(A₀)`). -/
theorem le_of_forall_line_inf_centralizer_le [Finite G] {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    {W : Subgroup G} (hWinv : A ≤ Subgroup.normalizer (W : Set G))
    (hWp : ¬ p ∣ Nat.card ↥W) {T : Subgroup G}
    (hsupply : ∀ Y ∈ elemAbelianOfRank G p 1, Y ≤ A →
      W ⊓ Subgroup.centralizer (Y : Set G) ≤ T) :
    W ≤ T := by
  classical
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hA.2] at h1
    have := (Fact.out : p.Prime).one_lt
    nlinarith
  obtain ⟨X₀, hX₀, hX₀A⟩ := exists_line_le hA.1 hAne
  -- conjugation action of `A` on `W`.
  let act : MulDistribMulAction ↥A ↥W :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (W : Set G))) ↥W
      (Subgroup.inclusion hWinv)
  set φ : ↥A →* MulAut ↥W := MulDistribMulAction.toMulAut ↥A ↥W with hφdef
  have hφ_coe : ∀ (a : ↥A) (x : ↥W),
      (W.subtype ((φ a) x)) = (↑a) * (W.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥W) := by
    rw [hA.2]
    exact Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hWp)
  have hAnc : ¬ IsCyclic ↥A := by
    refine not_isCyclic_of_isElementaryAbelian_of_two_le_log_card hA.1 ?_
    rw [hA.2, Nat.log_pow (Fact.out : p.Prime).one_lt]
  have : IsMulCommutative ↥A := ⟨⟨hA.1.comm⟩⟩
  have hgen :=
    OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic φ hcop hAnc
  -- the fixed points of a cocyclic subgroup land in `T`.
  have hle : OddOrder.BG.Ch1.S01.cocyclicFixedByClosure φ ≤ T.comap W.subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨Y, ⟨a, hYa⟩, hfix⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    have hYdvd : Nat.card ↥Y ∣ Nat.card ↥A := Subgroup.card_subgroup_dvd_card Y
    rw [hA.2] at hYdvd
    obtain ⟨i, hi2, hicard⟩ := (Nat.dvd_prime_pow Fact.out).mp hYdvd
    -- the generator centralizes the image of `Y` in `G`.
    have hgC : W.subtype g ∈ Subgroup.centralizer ((Y.map A.subtype : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_map] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      have h1 := congrArg W.subtype (hfix y' hy')
      rw [hφ_coe] at h1
      change (y' : G) * W.subtype g = W.subtype g * (y' : G)
      calc (y' : G) * W.subtype g
          = ((y' : G) * W.subtype g * (↑y')⁻¹) * ↑y' := by group
        _ = W.subtype g * (y' : G) := by rw [h1]
    interval_cases i
    · -- `|Y| = 1`: then `A = ⟨a⟩` is cyclic, contradiction.
      exfalso
      have hYbot : Y = ⊥ := Subgroup.card_eq_one.mp (by rw [hicard, pow_zero])
      rw [hYbot, bot_sup_eq] at hYa
      refine hAnc ⟨⟨a, fun x => ?_⟩⟩
      have hx : x ∈ Subgroup.zpowers a := by rw [hYa]; exact Subgroup.mem_top x
      exact hx
    · -- `|Y| = p`: a line; the supply applies directly.
      set Yg : Subgroup G := Y.map A.subtype with hYgdef
      have hYg_card : Nat.card ↥Yg = p := by
        rw [hYgdef, Subgroup.card_map_of_injective A.subtype_injective, hicard, pow_one]
      have hYg_mem : Yg ∈ elemAbelianOfRank G p 1 :=
        ⟨Subgroup.IsElementaryAbelian.of_card_prime hYg_card, by rw [hYg_card, pow_one]⟩
      exact hsupply Yg hYg_mem (Subgroup.map_subtype_le _) ⟨g.2, hgC⟩
    · -- `|Y| = p²`: `Y = ⊤`, so the generator centralizes `A ⊇ X₀` and the supply
      -- for the line `X₀` applies.
      have hYtop : Y = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hicard, hA.2])
      have hmapA : (Y.map A.subtype : Subgroup G) = A := by
        rw [hYtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hgCA : W.subtype g ∈ Subgroup.centralizer (A : Set G) := hmapA ▸ hgC
      exact hsupply X₀ hX₀ hX₀A
        ⟨g.2, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₀A) hgCA⟩
  intro w hw
  have hmem : (⟨w, hw⟩ : ↥W) ∈ OddOrder.BG.Ch1.S01.cocyclicFixedByClosure φ := by
    rw [hgen]; exact Subgroup.mem_top _
  exact Subgroup.mem_comap.mp (hle hmem)

/-- **Generation engine for Proposition 12.4** (mmd L3133-3137 / L3149-3151): under the
hypothesis of 12.4(b), let `W` be an `A`-invariant `p'`-subgroup of `M` such that for
every line `Y ∈ ℰ¹(A)` and every maximal `M* ≠ M` over `N_G(Y)`, `A` centralizes
`W ⊓ M*` (this is what Lemma 12.3(a)/(b) supplies). Then `W ≤ C_G(A)`. -/
private theorem le_centralizer_of_forall_line [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M)
    (hb : ∀ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A →
      maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M})
    {W : Subgroup G} (hWinv : A ≤ Subgroup.normalizer (W : Set G))
    (hWp : ¬ p ∣ Nat.card ↥W)
    (hsupply : ∀ Y ∈ elemAbelianOfRank G p 1, Y ≤ A → ∀ Mstar ∈ maximalSubgroups G,
      Mstar ≠ M → Subgroup.normalizer (Y : Set G) ≤ Mstar →
      A ≤ Subgroup.centralizer ((W ⊓ Mstar : Subgroup G) : Set G)) :
    W ≤ Subgroup.centralizer (A : Set G) := by
  refine le_of_forall_line_inf_centralizer_le hA hWinv hWp ?_
  intro Y hY hYA
  obtain ⟨Mst, hMst_mem, hMst_ne, hMst_le⟩ :=
    exists_maximal_ne_of_normalizer_ne_singleton hG hM
      (ne_bot_of_mem_elemAbelianOfRank_one hY) (hYA.trans hAM) (hb Y hY hYA)
  have hcent := hsupply Y hY hYA Mst hMst_mem hMst_ne hMst_le
  rintro x ⟨hxW, hxC⟩
  have hxMst : x ∈ Mst := hMst_le (Subgroup.centralizer_le_normalizer _ hxC)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (hcent ha) x ⟨hxW, hxMst⟩).symm

/-- **BG Proposition 12.4(b)** (mmd L3125): `A ∈ ℰ_p²(M)`, and suppose
`ℳ(N_G(A₀)) ≠ {M}` for every `A₀ ∈ ℰ¹(A)`. Then `p ∈ σ(M)`, `M_α = 1`, and `M_σ` is
nilpotent — and moreover `C_G(A) ≤ M` (the case of (a) under this hypothesis).

Proof (mmd L3131-3157): the Uniqueness Theorem bounds `r(C_M(X)) ≤ 2` for every line
`X ∈ ℰ¹(A)`. If `p ∉ σ(M)`, Lemma 12.3(a) and Proposition 1.16(2) give
`M_σ = ⟨C_{M_σ}(Y)⟩ ≤ C_M(A)`, contradicting Proposition 10.11(b); so `p ∈ σ(M)`.
For a Sylow `p`-subgroup `P` of `M_σ` containing `A`, the rank bound forces
`Z = Ω₁(Z(P)) ≤ A`, whence `r(P) ≤ r(C_M(X)) ≤ 2` for a line `X ≤ Z` and `p ∉ α(M)`.
Lemma 12.3(b) and Proposition 1.16(2) then give `M_α ≤ C_M(A)`, forcing `M_α = 1`
(any `q ∈ α(M)` would put a rank-`3` subgroup inside `C_M(A)`); `M_σ ≅ M_σ/M_α` is
nilpotent by Theorem 10.2(d). Finally `P ⊴ M`, so `N_G(Z) = M` and
`C_G(A) ≤ C_G(Z) ≤ N_G(Z) = M`. -/
theorem mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne [Finite G]
    (hG : IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} [Fact p.Prime] {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2)
    (hAM : A ≤ M)
    (hb : ∀ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A →
      maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M}) :
    p ∈ S10.sigma M ∧ S10.Malpha M = ⊥ ∧ Group.IsNilpotent ↥(S10.Msigma M) ∧
      Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  have hMcoatom : IsCoatom M := mem_maximalSubgroups.mp hM
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥A = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hA.2] at h1
    have := (Fact.out : p.Prime).one_lt
    nlinarith
  -- (1) the Uniqueness rank bound: `r(C_M(X)) ≤ 2` for every line `X ∈ ℰ¹(A)`.
  have hrCX : ∀ X ∈ elemAbelianOfRank G p 1, X ≤ A →
      rank ↥(Subgroup.centralizer (X : Set G) ⊓ M) ≤ 2 := by
    intro X hX hXA
    by_contra hcon
    have h3 : 3 ≤ rank ↥(Subgroup.centralizer (X : Set G) ⊓ M) := by omega
    have hlt : Subgroup.centralizer (X : Set G) ⊓ M < ⊤ :=
      lt_of_le_of_lt inf_le_right hMcoatom.lt_top
    have hU := OddOrder.BG.Ch2.S09.uniquenessTheorem hG hlt (by omega) (Or.inl h3)
    have hXne := ne_bot_of_mem_elemAbelianOfRank_one hX
    have hNXlt := normalizer_lt_top_of_le_of_ne_bot hG hM (hXA.trans hAM) hXne
    have hCN : Subgroup.centralizer (X : Set G) ⊓ M ≤ Subgroup.normalizer (X : Set G) :=
      inf_le_left.trans (Subgroup.centralizer_le_normalizer _)
    have hUNX := hU.of_le_of_lt_top hCN hNXlt
    have huniq : hUNX.uniqueMaximalSubgroup = M :=
      (hU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hUNX.uniqueMaximalSubgroup_isCoatom
          (hCN.trans hUNX.le_uniqueMaximalSubgroup)).trans
        (hU.eq_uniqueMaximalSubgroup_of_isCoatom_of_le hMcoatom inf_le_right).symm
    exact hb X hX hXA
      (hUNX.maximalSubgroupsContaining_eq_singleton.trans (by rw [huniq]))
  -- (2) `r(C_M(A)) ≤ 2` via any line of `A`.
  obtain ⟨X₀, hX₀, hX₀A⟩ := exists_line_le hA.1 hAne
  have hrA : rank ↥(Subgroup.centralizer (A : Set G) ⊓ M) ≤ 2 := by
    refine le_trans ?_ (hrCX X₀ hX₀ hX₀A)
    have hle : Subgroup.centralizer (A : Set G) ⊓ M ≤
        Subgroup.centralizer (X₀ : Set G) ⊓ M :=
      inf_le_inf_right M (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₀A))
    exact rank_le_of_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  -- (3) `p ∈ σ(M)`.
  have hpσ : p ∈ S10.sigma M := by
    by_contra hpσ
    have hWp : ¬ p ∣ Nat.card ↥(S10.Msigma M) := fun h =>
      hpσ (S10.Msigma_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, h, Nat.card_pos.ne'⟩))
    have hsupply : ∀ Y ∈ elemAbelianOfRank G p 1, Y ≤ A → ∀ Mstar ∈ maximalSubgroups G,
        Mstar ≠ M → Subgroup.normalizer (Y : Set G) ≤ Mstar →
        A ≤ Subgroup.centralizer ((S10.Msigma M ⊓ Mstar : Subgroup G) : Set G) := by
      intro Y hY hYA Mstar hMst hMne hNle
      have hAMst : A ≤ Mstar :=
        ((le_centralizer_self_of_isElementaryAbelian hA.1).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hYA))).trans
          ((Subgroup.centralizer_le_normalizer _).trans hNle)
      exact elemAb_centralizes_Msigma_meet hG hM hMst hMne hpσ hA (le_inf hAM hAMst)
        hY hYA hNle
    have hgen := le_centralizer_of_forall_line hG hM hA hAM hb
      (hAM.trans (le_normalizer_opiCoreInG _ _)) hWp hsupply
    -- `A` centralizes `M_σ`, contradicting Proposition 10.11(b).
    have hAC : A ≤ Subgroup.centralizer ((S10.Msigma M : Subgroup G) : Set G) :=
      le_centralizer_swap hgen
    have h1011 := S10.rank_centralizer_Msigma_inf_le_one hG hM hAM
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hA.1.isPGroup hpσ)
    rw [inf_eq_right.mpr hAC] at h1011
    have h2 := two_le_rank_of_mem_elemAbelianOfRank_two hA
    omega
  -- (4) `A ≤ M_σ` and a Sylow `p`-subgroup `Pg` of `M_σ` containing `A`.
  have hAMσ : A ≤ S10.Msigma M := S10.sigma_subgroup_le_Msigma_of_isHall
    (S10.isHall_Msigma_Malpha hG hM).1 hAM
    (Subgroup.isPiSubgroup_of_isPGroup_of_mem hA.1.isPGroup hpσ)
  obtain ⟨PW, hAPW⟩ := hA.1.isPGroup.comap_subtype.exists_le_sylow (G := S10.Msigma M)
  set Pg : Subgroup G := (PW : Subgroup ↥(S10.Msigma M)).map (S10.Msigma M).subtype
    with hPgdef
  have hAP : A ≤ Pg := by
    rw [hPgdef, ← Subgroup.map_subgroupOf_eq_of_le hAMσ]
    exact Subgroup.map_mono hAPW
  have hPg_le : Pg ≤ S10.Msigma M := Subgroup.map_subtype_le _
  have hPg_le_M : Pg ≤ M := hPg_le.trans (S10.Msigma_le M)
  have hPg_pg : IsPGroup p ↥Pg := by rw [hPgdef]; exact PW.isPGroup'.map _
  -- (5) `Z = Ω₁(Z(Pg))` and its basic properties.
  set Z : Subgroup G := S10.omega1CenterInG Pg p with hZdef
  have hZ_eq : Z = (omega1OfAbelian ↥Pg (Subgroup.center ↥Pg) p
      (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)).map Pg.subtype := rfl
  have hZ_le : Z ≤ Pg := S10.omega1CenterInG_le Pg p
  have hPg_cent_Z : Pg ≤ Subgroup.centralizer (Z : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, hZ_eq, Subgroup.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have hz'c : z' ∈ Subgroup.center ↥Pg := (mem_omega1OfAbelian.mp hz').1
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'c ⟨q, hq⟩)).symm
  have : Nontrivial ↥Pg := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt
      _ = Nat.card ↥A := hA.2.symm
      _ ≤ Nat.card ↥Pg := Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAP)
  have hZ_ne : Z ≠ ⊥ := by
    have hcent_nt : Nontrivial ↥(Subgroup.center ↥Pg) := hPg_pg.center_nontrivial
    have hp_center : p ∣ Nat.card ↥(Subgroup.center ↥Pg) := by
      obtain ⟨k, hk⟩ := (hPg_pg.to_subgroup (Subgroup.center ↥Pg)).exists_card_eq
      have hne1 : Nat.card ↥(Subgroup.center ↥Pg) ≠ 1 :=
        (Finite.one_lt_card_iff_nontrivial.mpr hcent_nt).ne'
      rw [hk] at hne1 ⊢
      exact dvd_pow_self p (fun h0 => hne1 (by rw [h0, pow_zero]))
    have hpRank1 : 1 ≤ pRank ↥(Subgroup.center ↥Pg) p :=
      one_le_pRank_of_mem_primeFactors
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hp_center, Nat.card_pos.ne'⟩)
    have h1 : p ^ 1 ∣ Nat.card ↥(omega1OfAbelian ↥Pg (Subgroup.center ↥Pg) p
        (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)) :=
      pow_dvd_card_omega1OfAbelian_of_pos_le_pRank one_pos hpRank1
    intro hbot
    rw [hZ_eq] at hbot
    have h2 := Subgroup.card_eq_one.mpr
      ((Subgroup.map_eq_bot_iff_of_injective _ Pg.subtype_injective).mp hbot)
    rw [pow_one] at h1
    rw [h2] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one h1)
  have hZ_ea : Z.IsElementaryAbelian p := by
    rw [hZ_eq]
    exact Subgroup.IsElementaryAbelian.map Pg.subtype_injective
      omega1OfAbelian_isElementaryAbelian
  -- (6) `Z ≤ A` via the rank bound on `C_M(A)`.
  have hA_cent_Z : A ≤ Subgroup.centralizer (Z : Set G) := hAP.trans hPg_cent_Z
  have hsup_ea : (A ⊔ Z).IsElementaryAbelian p :=
    isElementaryAbelian_sup_of_le_centralizer hA.1 hZ_ea hA_cent_Z
  have hAZ_le : A ⊔ Z ≤ Subgroup.centralizer (A : Set G) ⊓ M :=
    sup_le (le_inf (le_centralizer_self_of_isElementaryAbelian hA.1) hAM)
      (le_inf (le_centralizer_swap hA_cent_Z) (hZ_le.trans hPg_le_M))
  have hZA : Z ≤ A := by
    obtain ⟨k, hk⟩ := hsup_ea.isPGroup.exists_card_eq
    have hsub_ea : ((A ⊔ Z).subgroupOf
        (Subgroup.centralizer (A : Set G) ⊓ M)).IsElementaryAbelian p :=
      OddOrder.GroupTheory.IsElementaryAbelian.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hAZ_le).symm hsup_ea
    have hle := le_pRank (G := ↥(Subgroup.centralizer (A : Set G) ⊓ M)) _ hsub_ea
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ_le).toEquiv, hk,
      Nat.log_pow (Fact.out : p.Prime).one_lt] at hle
    have h2 := (pRank_le_rank (G := ↥(Subgroup.centralizer (A : Set G) ⊓ M)) p).trans hrA
    have hcard_le : Nat.card ↥(A ⊔ Z) ≤ p ^ 2 := by
      rw [hk]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
    have hsup_eq : A = A ⊔ Z :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hA.2]; exact hcard_le)
    exact le_sup_right.trans hsup_eq.ge
  -- (7) `p ∉ α(M)`: a line `X₁ ≤ Z` gives `r_p(M) = r(Pg) ≤ r(C_M(X₁)) ≤ 2`.
  obtain ⟨X₁, hX₁, hX₁Z⟩ := exists_line_le hZ_ea hZ_ne
  have hX₁A : X₁ ≤ A := hX₁Z.trans hZA
  have hPg_max_M : ∀ R : Subgroup G, Pg ≤ R → R ≤ M → IsPGroup p ↥R → R = Pg := by
    intro R hPR hRM hRpg
    have hRMσ : R ≤ S10.Msigma M := S10.sigma_subgroup_le_Msigma_of_isHall
      (S10.isHall_Msigma_Malpha hG hM).1 hRM
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem hRpg hpσ)
    have hle : (PW : Subgroup ↥(S10.Msigma M)) ≤ R.subgroupOf (S10.Msigma M) := by
      refine le_trans (fun x hx => Subgroup.mem_subgroupOf.mpr ?_) (Subgroup.comap_mono hPR)
      rw [hPgdef]
      exact Subgroup.mem_map_of_mem _ hx
    have heq : R.subgroupOf (S10.Msigma M) = PW := PW.3 hRpg.comap_subtype hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hRMσ, heq, hPgdef]
  have hpα : p ∉ S10.alpha M := by
    intro hα
    have h3 : 3 ≤ pRank ↥M p := ((S10.mem_alpha_iff M p).mp hα).2
    have hmaxM : ∀ {T : Subgroup ↥M}, IsPGroup p ↥T → Pg.subgroupOf M ≤ T →
        T = Pg.subgroupOf M := by
      intro T hT hle
      have hTmap_le : T.map M.subtype ≤ M := Subgroup.map_subtype_le T
      have hTpg : IsPGroup p ↥(T.map M.subtype) := hT.map _
      have hPgle : Pg ≤ T.map M.subtype := by
        conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hPg_le_M]
        exact Subgroup.map_mono hle
      have hTeq := hPg_max_M _ hPgle hTmap_le hTpg
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hPg_le_M, ← hTeq]
    let SM' : Sylow p ↥M := ⟨Pg.subgroupOf M, hPg_pg.comap_subtype, hmaxM⟩
    have e : ↥(Pg.subgroupOf M) ≃* ↥Pg := Subgroup.subgroupOfEquivOfLe hPg_le_M
    have hPg_cent : Pg ≤ Subgroup.centralizer (X₁ : Set G) ⊓ M :=
      le_inf (hPg_cent_Z.trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₁Z))) hPg_le_M
    have hchain : pRank ↥M p ≤ 2 := by
      calc pRank ↥M p = pRank ↥(SM' : Subgroup ↥M) p := (pRank_sylow_eq SM').symm
        _ ≤ pRank ↥Pg p := pRank_le_of_injective (f := e.toMonoidHom) e.injective
        _ ≤ pRank ↥(Subgroup.centralizer (X₁ : Set G) ⊓ M) p :=
            pRank_le_of_injective (f := Subgroup.inclusion hPg_cent)
              (Subgroup.inclusion_injective hPg_cent)
        _ ≤ rank ↥(Subgroup.centralizer (X₁ : Set G) ⊓ M) := pRank_le_rank p
        _ ≤ 2 := hrCX X₁ hX₁ hX₁A
    omega
  -- (8) `M_α = ⊥` via Lemma 12.3(b) and Proposition 1.16(2).
  have hMαC : S10.Malpha M ≤ Subgroup.centralizer (A : Set G) := by
    have hWp : ¬ p ∣ Nat.card ↥(S10.Malpha M) := fun h =>
      hpα (S10.Malpha_isPiGroup M p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, h, Nat.card_pos.ne'⟩))
    refine le_centralizer_of_forall_line hG hM hA hAM hb
      (hAM.trans (le_normalizer_opiCoreInG _ _)) hWp ?_
    intro Y hY hYA Mstar hMst hMne hNle
    have hAMst : A ≤ Mstar :=
      ((le_centralizer_self_of_isElementaryAbelian hA.1).trans
        (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hYA))).trans
        ((Subgroup.centralizer_le_normalizer _).trans hNle)
    exact elemAb_centralizes_Malpha_meet hG hM hMst hMne hpσ hpα hA (le_inf hAM hAMst)
      hY hYA hNle
  have hMαbot : S10.Malpha M = ⊥ := by
    by_contra hne'
    have hcard_ne : Nat.card ↥(S10.Malpha M) ≠ 1 := fun h =>
      hne' (Subgroup.card_eq_one.mp h)
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd hcard_ne
    have : Fact q.Prime := ⟨hq_prime⟩
    have hqα : q ∈ S10.alpha M := S10.Malpha_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩)
    have h3 : 3 ≤ pRank ↥M q := ((S10.mem_alpha_iff M q).mp hqα).2
    -- a Sylow `q`-subgroup of `M` lies in `M_α ≤ C_M(A)`, giving rank `≥ 3` there.
    obtain ⟨Sq⟩ := (inferInstance : Nonempty (Sylow q ↥M))
    have hSq_le : (Sq : Subgroup ↥M).map M.subtype ≤ S10.Malpha M := by
      refine S10.alpha_subgroup_le_Malpha_of_isHall (S10.isHall_Msigma_Malpha hG hM).2.1
        (Subgroup.map_subtype_le _) ?_
      exact Subgroup.isPiSubgroup_of_isPGroup_of_mem (Sq.isPGroup'.map _) hqα
    have hSq_le' : (Sq : Subgroup ↥M).map M.subtype ≤
        Subgroup.centralizer (A : Set G) ⊓ M :=
      le_inf (hSq_le.trans hMαC) (Subgroup.map_subtype_le _)
    have e : ↥(Sq : Subgroup ↥M) ≃* ↥((Sq : Subgroup ↥M).map M.subtype) :=
      Subgroup.equivMapOfInjective _ _ M.subtype_injective
    have hchain : 3 ≤ rank ↥(Subgroup.centralizer (A : Set G) ⊓ M) := by
      calc (3 : ℕ) ≤ pRank ↥M q := h3
        _ = pRank ↥(Sq : Subgroup ↥M) q := (pRank_sylow_eq Sq).symm
        _ ≤ pRank ↥((Sq : Subgroup ↥M).map M.subtype) q :=
            pRank_le_of_injective (f := e.toMonoidHom) e.injective
        _ ≤ pRank ↥(Subgroup.centralizer (A : Set G) ⊓ M) q :=
            pRank_le_of_injective (f := Subgroup.inclusion hSq_le')
              (Subgroup.inclusion_injective hSq_le')
        _ ≤ rank ↥(Subgroup.centralizer (A : Set G) ⊓ M) := pRank_le_rank q
    omega
  -- (9) `M_σ` is nilpotent.
  have hM'nil := isNilpotent_derived_of_Malpha_eq_bot hG hM hMαbot
  have hMσM' : S10.Msigma M ≤ derivedInG M := S10.Msigma_le_derived hG hM
  have hMσnil : Group.IsNilpotent ↥(S10.Msigma M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσM')
  -- (10) `C_G(A) ≤ M`: `Pg ⊴`-by-`M`, `Z` characteristic, `N_G(Z) = M`.
  have hPW_norm : (PW : Subgroup ↥(S10.Msigma M)).Normal := by
    have htfae := (Group.isNilpotent_of_finite_tfae (G := ↥(S10.Msigma M))).out 0 3
    exact htfae.mp hMσnil p ⟨Fact.out⟩ PW
  have hPW_char : (PW : Subgroup ↥(S10.Msigma M)).Characteristic :=
    Sylow.characteristic_of_normal PW hPW_norm
  have hM_norm_P : M ≤ Subgroup.normalizer (Pg : Set G) := by
    have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
      (K := S10.Msigma M) (W := (PW : Subgroup ↥(S10.Msigma M)))
    rw [← hPgdef] at h1
    exact (le_normalizer_opiCoreInG _ _).trans h1
  have hM_norm_Z : M ≤ Subgroup.normalizer (Z : Set G) :=
    hM_norm_P.trans (S10.normalizer_le_normalizer_omega1CenterInG Pg p)
  have hNZ_eq : Subgroup.normalizer (Z : Set G) = M := by
    have hlt := normalizer_lt_top_of_le_of_ne_bot hG hM (hZ_le.trans hPg_le_M) hZ_ne
    by_contra hne'
    exact hlt.ne (hMcoatom.2 _ (lt_of_le_of_ne hM_norm_Z (Ne.symm hne')))
  refine ⟨hpσ, hMαbot, hMσnil, ?_⟩
  calc Subgroup.centralizer (A : Set G)
      ≤ Subgroup.centralizer (Z : Set G) :=
        Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZA)
    _ ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
    _ = M := hNZ_eq

/-- **BG Proposition 12.4(a)** (mmd L3125): `A ∈ ℰ_p²(M)` implies `C_G(A) ≤ M`.

If some `A₀ ∈ ℰ¹(A)` has `ℳ(N_G(A₀)) = {M}`, then `N_G(A₀) ≤ M` and
`C_G(A) ≤ C_G(A₀) ≤ N_G(A₀) ≤ M` directly; otherwise the hypothesis of (b) holds and
`mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne` concludes. -/
theorem centralizer_le_of_elemAb_rank_two [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) :
    Subgroup.centralizer (A : Set G) ≤ M := by
  classical
  rcases Classical.em (∀ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A →
      maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M}) with hball | hex
  · exact (mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne hG hM hA hAM hball).2.2.2
  · simp only [not_forall, not_not] at hex
    obtain ⟨A₀, hA₀, hA₀A, hsingle⟩ := hex
    have hNM : Subgroup.normalizer (A₀ : Set G) ≤ M := by
      have hNlt := normalizer_lt_top_of_le_of_ne_bot hG hM (hA₀A.trans hAM)
        (ne_bot_of_mem_elemAbelianOfRank_one hA₀)
      obtain ⟨Mst, hMst_co, hMst_le⟩ :=
        (eq_top_or_exists_le_coatom (Subgroup.normalizer (A₀ : Set G))).resolve_left
          hNlt.ne
      have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) :=
        mem_maximalSubgroupsContaining.mpr ⟨hMst_co, hMst_le⟩
      rw [hsingle, Set.mem_singleton_iff] at hmem
      exact hmem ▸ hMst_le
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hA₀A)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNM)

/-- **BG Corollary 12.4 (`norm_noncyclic_sigma`)** (BGsection12, mmd L3138): a *noncyclic*
`σ(M)`-`p`-subgroup `P ≤ M` has `N_G(P) ≤ M`.  A noncyclic odd `p`-group contains a rank-two
elementary abelian subgroup `A` (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`), whose
`G`-centralizer lies in `M` (`centralizer_le_of_elemAb_rank_two`, BG Proposition 12.4(a)); the
`σ`-fusion control (`fusion_control_of_mem_sigma`, third clause `N_G(P) = (N_G(P) ⊓ M)·C_G(P)`)
factors every `n ∈ N_G(P)` as `n = a·c` with `a ∈ N_G(P) ⊓ M ≤ M` and `c ∈ C_G(P) ≤ C_G(A) ≤ M`, so
`N_G(P) ≤ M`.  This is the `σ`-uniqueness input to BG Lemma `sigma_compl_embedding` (the cyclicity
of
`M_σ ∩ M^g`, BG Theorem D(2)). -/
theorem norm_noncyclic_sigma [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hpσ : p ∈ S10.sigma M) {P : Subgroup G} (hPp : IsPGroup p ↥P) (hPM : P ≤ M)
    (hPnc : ¬ IsCyclic ↥P) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  -- `p` is odd (`p ∣ |M| ∣ |G|`, `|G|` odd).
  have hodd : Odd p := hG.odd.of_dvd_nat
    ((Nat.dvd_of_mem_primeFactors ((S10.mem_sigma_iff M p).mp hpσ).1).trans
      (Subgroup.card_subgroup_dvd_card M))
  -- A rank-two elementary abelian `A ≤ P` inside the noncyclic odd `p`-group `P`.
  obtain ⟨E, hEelem, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic hPp hodd hPnc
  set A : Subgroup G := E.map P.subtype with hAdef
  have hAP : A ≤ P := hAdef ▸ Subgroup.map_subtype_le E
  have hArank : A ∈ elemAbelianOfRank G p 2 := by
    rw [mem_elemAbelianOfRank]
    refine ⟨hEelem.map P.subtype_injective, ?_⟩
    rw [hAdef, Subgroup.card_map_of_injective P.subtype_injective, hEcard]
  -- `C_G(A) ≤ M` (Prop 12.4(a)), and `C_G(P) ≤ C_G(A)` since `A ≤ P`.
  have hCAM : Subgroup.centralizer (A : Set G) ≤ M :=
    centralizer_le_of_elemAb_rank_two hG hM hArank (hAP.trans hPM)
  have hCPA : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hAP)
  have hPne : P ≠ ⊥ := by rintro rfl; exact hPnc inferInstance
  -- `σ`-fusion: `n = a·c` with `a ∈ N_G(P) ⊓ M` and `c ∈ C_G(P) ≤ M`.
  intro n hn
  obtain ⟨a, haNM, c, hcC, hnac⟩ :=
    (S10.fusion_control_of_mem_sigma hG hM hpσ hPne hPp).2.2.1 hPM n hn
  rw [hnac]
  exact M.mul_mem (Subgroup.mem_inf.mp haNM).2 (hCAM (hCPA hcC))

end S12

end OddOrder.BG.Ch3



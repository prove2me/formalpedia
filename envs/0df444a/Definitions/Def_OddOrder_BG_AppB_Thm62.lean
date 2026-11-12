-- Prove2me | Definitions.Def_OddOrder_BG_AppB_Thm62
-- name    : OddOrder_BG_AppB_Thm62
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:50:58.650873+00:00
-- url     : https://prove2.me/theorems/54a0c510-ee01-450c-b6f5-87db8c7f2401
-- title:
--   Bender–Glauberman Theorem 6.2 (general form): $Z(L(S))\cdot O_{p'}(G)\trianglelefteq G$
-- statement:
--   Combines Theorem B.4(a)/(b) of Bender–Glauberman Appendix B into the general form of BG Theorem 6.2 (the self-contained replacement for Glauberman's $Z(J)$-theorem): $Z(L(S))\cdot O_{p'}(G)\trianglelefteq G$. The case $O_{p'}(G)=1$ is applied to $G/O_{p'}(G)$ and pulled back. The key is covariance of the $L$-operator under isomorphisms of different groups: $\bar S\cong S$ and $Z(L(\bar S))=\mathrm{mk}(Z(L(S)))$.
--
--   Main results: `lRelIn_map_equiv'`, `lNIn_map_equiv'` and `lOddIn_map_equiv'` (covariance under a group isomorphism $G\simeq G'$), and `lOddIn_eq_map_subtype` ($L(H)$ is the image of $L(\uparrow H)$).
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppB_Thm62.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/AppB_Thm62.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppB_PuigB3B4

namespace OddOrder.BG.AppB

open OddOrder.Isaacs.Ch01 OddOrder.Isaacs.Ch03

variable {G : Type*} [Group G]

/-- `L_H(X)` の異群 iso `φ : G ≃* G'` 同変性 (`≤` 方向). -/
private theorem lRelIn_map_le {G' : Type*} [Group G'] (φ : G ≃* G') (H X : Subgroup G) :
    (lRelIn H X).map φ.toMonoidHom ≤ lRelIn (H.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine lRelIn_le fun A hcomm hAH hnorm => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  have := hcomm
  refine le_lRelIn inferInstance (Subgroup.map_mono hAH) ?_
  rw [← Subgroup.map_equiv_normalizer_eq A φ]
  exact Subgroup.map_mono hnorm

/-- **`L_H(X)` の異群 iso `φ : G ≃* G'` 同変性**: `(L_H(X)).map φ = L_{φ(H)}(φ(X))`. -/
theorem lRelIn_map_equiv' {G' : Type*} [Group G'] (φ : G ≃* G') (H X : Subgroup G) :
    (lRelIn H X).map φ.toMonoidHom = lRelIn (H.map φ.toMonoidHom) (X.map φ.toMonoidHom) := by
  have hAB : ∀ K : Subgroup G, (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
    intro K; rw [Subgroup.map_map]; simp
  have hBA : ∀ K : Subgroup G', (K.map φ.symm.toMonoidHom).map φ.toMonoidHom = K := by
    intro K; rw [Subgroup.map_map]; simp
  refine le_antisymm (lRelIn_map_le φ H X) ?_
  have h := lRelIn_map_le φ.symm (H.map φ.toMonoidHom) (X.map φ.toMonoidHom)
  rw [hAB, hAB] at h
  have h2 := Subgroup.map_mono (f := φ.toMonoidHom) h
  rwa [hBA] at h2

/-- `L_n(H)` の異群 iso 同変性: `(L_n(H)).map φ = L_n(φ(H))`. -/
theorem lNIn_map_equiv' {G' : Type*} [Group G'] (φ : G ≃* G') (H : Subgroup G) :
    ∀ k, (lNIn H k).map φ.toMonoidHom = lNIn (H.map φ.toMonoidHom) k
  | 0 => by rw [lNIn_zero, lNIn_zero, Subgroup.map_bot]
  | (k + 1) => by
      rw [lNIn_succ H k, lNIn_succ (H.map φ.toMonoidHom) k,
        lRelIn_map_equiv' φ H (lNIn H k), lNIn_map_equiv' φ H k]

/-- **`L(H)` の異群 iso 同変性**: `(L(H)).map φ = L(φ(H))`. -/
theorem lOddIn_map_equiv' {G' : Type*} [Group G'] (φ : G ≃* G') (H : Subgroup G) :
    (lOddIn H).map φ.toMonoidHom = lOddIn (H.map φ.toMonoidHom) := by
  change (⨅ n, lNIn H (2 * n + 1)).map φ.toMonoidHom = ⨅ n, lNIn (H.map φ.toMonoidHom) (2 * n + 1)
  rw [Subgroup.map_iInf φ.toMonoidHom φ.injective]
  exact iInf_congr fun n => lNIn_map_equiv' φ H (2 * n + 1)

/-- **bridge**: `L_H(X) = (L_{↥H}(X.subgroupOf H)).map H.subtype` (`X ≤ H`).
`subgroupOf_normalizer_eq` で `H` 内 normalizer と `↥H` の normalizer を対応させる. -/
theorem lRelIn_eq_map_subtype {H : Subgroup G} (X : Subgroup G) (hX : X ≤ H) :
    lRelIn H X = (lRelIn (⊤ : Subgroup ↥H) (X.subgroupOf H)).map H.subtype := by
  refine le_antisymm (lRelIn_le fun A hcomm hAH hnorm => ?_) ?_
  · have hAeq : A = (A.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hAH]
    rw [hAeq]
    refine Subgroup.map_mono ?_
    have := hcomm
    refine le_lRelIn (Subgroup.comap_injective_isMulCommutative A H.subtype_injective) le_top ?_
    rw [← Subgroup.subgroupOf_normalizer_eq hAH]
    exact Subgroup.comap_mono hnorm
  · rw [Subgroup.map_le_iff_le_comap]
    refine lRelIn_le fun B hcomm hBH hnorm => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have := hcomm
    have hBsub : B.map H.subtype ≤ H := Subgroup.map_subtype_le B
    refine le_lRelIn inferInstance hBsub ?_
    have hBB : (B.map H.subtype).subgroupOf H = B :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective B
    have hnorm' : X.subgroupOf H
        ≤ (Subgroup.normalizer (↑(B.map H.subtype) : Set G)).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hBsub, hBB]; exact hnorm
    have h2 := Subgroup.map_mono (f := H.subtype) hnorm'
    rw [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hX] at h2
    exact h2.trans inf_le_left

/-- `L_n(H) = (L_n(↥H)).map H.subtype`. -/
theorem lNIn_eq_map_subtype (H : Subgroup G) :
    ∀ k, lNIn H k = (lNIn (⊤ : Subgroup ↥H) k).map H.subtype
  | 0 => by rw [lNIn_zero, lNIn_zero, Subgroup.map_bot]
  | (k + 1) => by
      have hmm : ((lNIn (⊤ : Subgroup ↥H) k).map H.subtype).subgroupOf H
          = lNIn (⊤ : Subgroup ↥H) k :=
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
      rw [lNIn_succ H k, lNIn_succ (⊤ : Subgroup ↥H) k, lNIn_eq_map_subtype H k,
        lRelIn_eq_map_subtype ((lNIn (⊤ : Subgroup ↥H) k).map H.subtype)
          (Subgroup.map_subtype_le _), hmm]

/-- **bridge (`L`)**: `L(H) = (L(↥H)).map H.subtype`. -/
theorem lOddIn_eq_map_subtype (H : Subgroup G) :
    lOddIn H = (lOddIn (⊤ : Subgroup ↥H)).map H.subtype := by
  change (⨅ n, lNIn H (2 * n + 1)) = (⨅ n, lNIn (⊤ : Subgroup ↥H) (2 * n + 1)).map H.subtype
  rw [Subgroup.map_iInf H.subtype H.subtype_injective]
  exact iInf_congr fun n => lNIn_eq_map_subtype H (2 * n + 1)

/-- **`L`-共変性 (`H` 上単射)**: `f` が `↥H` に制限して単射なら `(L(H)).map f = L(f(H))`.
`f|_H : ↥H ≃* ↥(f(H))` (像への iso) で `↥H` の絶対 `L` を移し, bridge で相対 `L` に戻す.
量子化 `Ḡ = G/O_{p'}` への `S ↪ Ḡ` (`S ∩ O_{p'} = ⊥`) に適用する. -/
theorem lOddIn_map_of_injOn {G' : Type*} [Group G'] (f : G →* G') {H : Subgroup G}
    (hf : Function.Injective (f.comp H.subtype)) :
    (lOddIn H).map f = lOddIn (H.map f) := by
  -- 像への iso `e : ↥H ≃* ↥(H.map f)`
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  set e : ↥H ≃* ↥(H.map f) :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hrange) with he_def
  have he : ∀ x : ↥H, ((e x : ↥(H.map f)) : G') = f (x : G) := by
    intro x
    rw [he_def]
    simp [MonoidHom.ofInjective_apply, MulEquiv.subgroupCongr_apply]
  have hcomp : f.comp H.subtype = (H.map f).subtype.comp e.toMonoidHom := by
    ext x; simpa using (he x).symm
  have hetop : (⊤ : Subgroup ↥H).map e.toMonoidHom = ⊤ := by
    rw [← MonoidHom.range_eq_map]; exact MonoidHom.range_eq_top.mpr e.surjective
  calc (lOddIn H).map f
      = ((lOddIn (⊤ : Subgroup ↥H)).map H.subtype).map f := by rw [lOddIn_eq_map_subtype]
    _ = (lOddIn (⊤ : Subgroup ↥H)).map (f.comp H.subtype) := by rw [Subgroup.map_map]
    _ = (lOddIn (⊤ : Subgroup ↥H)).map ((H.map f).subtype.comp e.toMonoidHom) := by rw [hcomp]
    _ = ((lOddIn (⊤ : Subgroup ↥H)).map e.toMonoidHom).map (H.map f).subtype := by
          rw [Subgroup.map_map]
    _ = (lOddIn ((⊤ : Subgroup ↥H).map e.toMonoidHom)).map (H.map f).subtype := by
          rw [lOddIn_map_equiv']
    _ = (lOddIn (⊤ : Subgroup ↥(H.map f))).map (H.map f).subtype := by rw [hetop]
    _ = lOddIn (H.map f) := (lOddIn_eq_map_subtype (H.map f)).symm

/-- `f` が `↥L` に制限して単射なら `f(C_G(L)⊓L) = C_{G'}(f(L))⊓f(L)`. -/
theorem map_centralizer_inf {G' : Type*} [Group G'] (f : G →* G') {L : Subgroup G}
    (hf : Function.Injective (f.comp L.subtype)) :
    (Subgroup.centralizer (L : Set G) ⊓ L).map f
      = Subgroup.centralizer ((L.map f : Subgroup G') : Set G') ⊓ L.map f := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hx
    obtain ⟨hxc, hxL⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, Subgroup.mem_map_of_mem f hxL⟩
    rintro m hm
    rw [SetLike.mem_coe, Subgroup.mem_map] at hm
    obtain ⟨l, hl, rfl⟩ := hm
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hxc l (SetLike.mem_coe.mpr hl)]
  · rintro hy
    rw [Subgroup.mem_inf] at hy
    obtain ⟨hy_cent, x, hxL, rfl⟩ := hy
    rw [Subgroup.mem_map]
    refine ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_inf]
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun l hl => ?_, hxL⟩
    have hc := Subgroup.mem_centralizer_iff.mp hy_cent (f l)
      (SetLike.mem_coe.mpr (Subgroup.mem_map_of_mem f (SetLike.mem_coe.mp hl)))
    rw [← map_mul, ← map_mul] at hc
    have hlxL : l * x ∈ L := L.mul_mem (SetLike.mem_coe.mp hl) hxL
    have hxlL : x * l ∈ L := L.mul_mem hxL (SetLike.mem_coe.mp hl)
    exact Subtype.ext_iff.mp (hf (a₁ := ⟨l * x, hlxL⟩) (a₂ := ⟨x * l, hxlL⟩) hc)

/-- **`Z(L(·))` の `H` 上単射 hom 共変性**: `f(Z(L(H))) = Z(L(f(H)))`. -/
theorem map_zCenterLOdd_of_injOn {G' : Type*} [Group G'] (f : G →* G') {H : Subgroup G}
    (hf : Function.Injective (f.comp H.subtype)) :
    (zCenterLOdd H).map f = zCenterLOdd (H.map f) := by
  have hfL : Function.Injective (f.comp (lOddIn H).subtype) := by
    have heq : f.comp (lOddIn H).subtype
        = (f.comp H.subtype).comp (Subgroup.inclusion (lOddIn_le_self H)) := by
      ext x; rfl
    rw [heq]; exact hf.comp (Subgroup.inclusion_injective _)
  rw [zCenterLOdd_eq_centralizer_inf, zCenterLOdd_eq_centralizer_inf,
    map_centralizer_inf f hfL, lOddIn_map_of_injOn f hf]

/-- **BG Theorem 6.2 一般形** (Puig, B.4(a)/(b) 合流, mmd L4688-4703): `p` odd,
`G` solvable of odd order, `S ∈ Syl_p(G)` ⇒ `Z(L(S))·O_{p'}(G) ⊴ G`
(部分群の積を `⊔` で表す; `O_{p'}(G) = oPiCore {q ≠ p} G`).

これが Isaacs FGT が省く **Glauberman `Z(J)`-定理 (BG Thm 6.2) の自己完結代替の一般形**で,
§7-§16 が参照する normal-`J` ハブ. 証明 (mmd Step 1): `Ḡ = G/O_{p'}(G)` で `O_{p'}(Ḡ) = 1`
(`oPiCore_quotient_self_eq_bot`), `S̄ = mk(S) ≅ S` (∵ `S ∩ O_{p'} = ⊥`) ゆえ
`Z(L(S̄)) = mk(Z(L(S)))` (共変性). `Z(L(S̄)) ⊴ Ḡ` (B.4(b)) を引き戻す:
`Z(L(S))·O_{p'} = mk⁻¹(Z(L(S̄)))` は正規 (`comap` が正規性を保つ). -/
theorem zCenter_lOdd_sup_oPiCore_normal [Finite G] {p : ℕ} [Fact p.Prime]
    (hp_odd : p ≠ 2) (hsolv : Group.IsSolvable G) (hodd : Odd (Nat.card G)) (S : Sylow p G) :
    (zCenterLOdd (S : Subgroup G) ⊔ oPiCore {q | q ≠ p} G).Normal := by
  have : Group.IsSolvable G := hsolv
  set N := oPiCore {q | q ≠ p} G with hN_def
  have hN_normal : N.Normal := by rw [hN_def]; infer_instance
  -- `S ∩ N = ⊥` (p-群 ∩ p'-群)
  have hSN : (↑S : Subgroup G) ⊓ N = ⊥ := by
    have hpg : IsPGroup p ↥((↑S : Subgroup G) ⊓ N) := S.2.to_inf_left
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
    have hdvd : Nat.card ↥((↑S : Subgroup G) ⊓ N) ∣ Nat.card ↥N := by
      rw [← Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : (↑S : Subgroup G) ⊓ N ≤ N)).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have hpN : ¬ p ∣ Nat.card ↥N := fun hd =>
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q | q ≠ p} p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)) rfl
    rw [Subgroup.eq_bot_iff_card, hk]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero]
    · exact absurd (dvd_trans (dvd_pow_self p hkpos.ne') (hk ▸ hdvd)) hpN
  -- `mk` は `S` 上単射
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp (↑S : Subgroup G).subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : (x : G) ∈ N := by rw [← QuotientGroup.ker_mk' N]; exact hx
    have hxSN : (x : G) ∈ (↑S : Subgroup G) ⊓ N := ⟨x.2, hxN⟩
    rw [hSN, Subgroup.mem_bot] at hxSN
    exact Subtype.ext hxSN
  -- `Sbar ∈ Syl_p(Ḡ)`, `↑Sbar = mk(S)`
  set Sbar : Sylow p (G ⧸ N) := S.mapSurjective (QuotientGroup.mk'_surjective N) with hSbar_def
  have hSbar_coe : (↑Sbar : Subgroup (G ⧸ N)) = (↑S : Subgroup G).map (QuotientGroup.mk' N) := rfl
  -- B.4(b) の前提 (odd / solvable / `O_{p'}=1`)
  have hoddbar : Odd (Nat.card (G ⧸ N)) := by
    obtain ⟨c, hc⟩ := N.index_dvd_card
    rw [hc] at hodd
    exact (Nat.odd_mul.mp hodd).1
  -- `Z(L(Sbar)) ⊴ Ḡ`
  have hZbar : (zCenterLOdd (↑Sbar : Subgroup (G ⧸ N))).Normal :=
    zCenter_lOdd_normal_of_oPiCore_eq_bot hp_odd inferInstance hoddbar
      (oPiCore_quotient_self_eq_bot {q | q ≠ p}) Sbar
  -- 共変性 `mk(Z(L(S))) = Z(L(Sbar))`
  have hcov : (zCenterLOdd (↑S : Subgroup G)).map (QuotientGroup.mk' N)
      = zCenterLOdd (↑Sbar : Subgroup (G ⧸ N)) := by
    rw [hSbar_coe]; exact map_zCenterLOdd_of_injOn (QuotientGroup.mk' N) hinj
  -- `Z(L(S))·O_{p'} = mk⁻¹(Z(L(Sbar)))`, ゆえ正規
  have hassemble : zCenterLOdd (↑S : Subgroup G) ⊔ N
      = (zCenterLOdd (↑Sbar : Subgroup (G ⧸ N))).comap (QuotientGroup.mk' N) := by
    rw [← hcov, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  rw [hassemble]
  exact hZbar.comap (QuotientGroup.mk' N)

end OddOrder.BG.AppB



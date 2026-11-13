-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Assembly
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Assembly
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:03:42.761809+00:00
-- url     : https://prove2.me/theorems/12c942b6-bb89-4780-9de7-eda2ebb16457
-- title:
--   BG §15: Theorem 15.2, assembly
-- statement:
--   The assembly part of Theorem 15.2 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §15, split from the Corollary 15.5 file: step (c) ($Q=O_q(M)$ is the Sylow $q$-subgroup of $M_\sigma$), (g) the section-Fitting containment $C_{M_\sigma}(\bar Q)\subseteq F(M)$, (f)+(g) $[Q:Q_0]=q^p$ and $D'\subseteq C_D(\bar Q)$, and the prime-manner action of $K$ on the chief factor $\bar Q=Q/Q_0$, as gated-endpoint skeletons.
--
--   Main declarations: `q_not_dvd_index_of_msigma_quotient_isNilpotent`; `centralizer_msigma_quotient_le_fittingInAmbient`; `chiefFactor_card_and_commutator_of_inputs`; `centralizes_quotient_iff_mem_kstar_sup` (`C_{Q̄}(K)` is the image of `K* ⊔ Q₀` (BG Proposition 1.5(d), the `hCfix` core of Theorem 15.2(f))); and 1 more.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Theorem152Assembly.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Theorem152Assembly.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_MsigmaNilpotent

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Theorem 15.2 step (c)(d) — `M_σ/Q` is nilpotent** (mmd L4192, "`K` acts regularly on `M_σ/Q`,
therefore by Theorem 3.7 (applied to `K₁M_σ/Q`), `M_σ/Q` is nilpotent").  In the type-`P` setting
with `K` a Hall `κ`-subgroup, `K* = C_{M_σ}(K) ⊆ Q = O_q(M)` (step 2), so `K` acts
fixed-point-freely
on `M_σ/Q` (Proposition 1.5(d): the fixed classes lift to `C_{M_σ}(k) = K* ⊆ Q`).  Theorem 3.7
applied to a prime-order `K₁ ≤ K` makes `M_σ/Q` nilpotent.

The FPF condition for `M_σ/Q` is `fpf_of_centralizer_inf_le_general` (`A = M_σ`, `Q₀ = Q`) with the
prime-manner input `C_G(k) ⊓ M_σ = K* ≤ Q` (`actsPrimeManner_of_typeP` + `hKstarQ`); the nilpotence
of `M_σ/Q` is then `isNilpotent_quotient_of_regular_general` (`N = M_σ`, `Q₀ = Q`, `K₁` of prime
order in `K`).  The disjointness/normalizer data comes from `K` complementing `M_σ` in `M`
(`hcompl`, `hcop`) and `Q ⊴ M` (`hMnormQ`, `hQMσ`).  Gated only through `§14`/structural inputs
(`hP`, `hKstarQ`, `hQneMσ`), all already discharged. -/
theorem msigma_quotient_isNilpotent_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥)
    (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal] :
    Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  -- the prime-manner action `C_G(x) ⊓ M_σ = K*` for `x ∈ K#`.
  have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
  -- `K₁ ≤ K` of prime order (Cauchy in `↥K`).
  have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
  obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
  have : Fact r.Prime := ⟨hr_prime⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
  set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
  have hcK : (c : G) ∈ K := c.2
  have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
  have hK1M : K1 ≤ M := hK1K.trans hKM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
  have hK1prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K1 = p := ⟨r, hr_prime, hcardK1⟩
  -- structural facts for `isNilpotent_quotient_of_regular_general` (`N = M_σ`, `Q₀ = Q`, `K₁`).
  have hQltMσ : Q < Mσ := lt_of_le_of_ne hQMσ hQneMσ
  have hMσK1solv : Group.IsSolvable ↥(Mσ ⊔ K1) := by
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (sup_le hMσM hK1M))
  have hMσK1normQ : Mσ ⊔ K1 ≤ Subgroup.normalizer (Q : Set G) := sup_le (hMσM.trans hMnormQ)
    (hK1M.trans hMnormQ)
  have hK1normMσ : K1 ≤ Subgroup.normalizer (Mσ : Set G) := hK1M.trans hMnormMσ
  have hMσK1disj : Disjoint Mσ K1 := (hKMσdisj.symm).mono_right hK1K
  have hK1Qdisj : Disjoint K1 Q := (hKMσdisj.mono_left hK1K).mono_right hQMσ
  -- the FPF condition `k·x⁻¹·k⁻¹·x ∈ Q ⟹ x ∈ Q` for `k ∈ K₁#`.
  have hFPF : ∀ k ∈ K1, k ≠ 1 → ∀ x ∈ Mσ, k * x⁻¹ * k⁻¹ * x ∈ Q → x ∈ Q := by
    intro k hkK1 hk1 x hxMσ hpre
    have hkK : k ∈ K := hK1K hkK1
    -- `C_G(k) ⊓ M_σ = K* ≤ Q`.
    have hCk : Subgroup.centralizer ({k} : Set G) ⊓ Mσ ≤ Q := by
      rw [hprime k hkK hk1]; exact hKstarQ
    -- coprime `(|⟨k⟩|, |M_σ|)`: `|⟨k⟩| ∣ |K|` coprime `|M_σ|`.
    have hcopk : Nat.Coprime (Nat.card ↥(Subgroup.zpowers k)) (Nat.card ↥Mσ) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hkK))
    have hkM : k ∈ M := hKM hkK
    have hk_normMσ : k ∈ Subgroup.normalizer (Mσ : Set G) := hMnormMσ hkM
    have hk_normQ : k ∈ Subgroup.normalizer (Q : Set G) := hMnormQ hkM
    have hMσnormQ : Mσ ≤ Subgroup.normalizer (Q : Set G) := hMσM.trans hMnormQ
    have : Group.IsSolvable ↥Mσ :=
      have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMσM)
    exact fpf_of_centralizer_inf_le_general (k := k) hk_normMσ hk_normQ hMσnormQ hQMσ hcopk
      (Or.inr inferInstance) hCk x hxMσ hpre
  exact isNilpotent_quotient_of_regular_general hMσK1solv hMσK1normQ hK1normMσ hK1prime
    hMσK1disj hK1Qdisj hQltMσ hFPF

/-- **A nilpotent group with trivial `q`-core is a `q'`-group** (`§14`-independent, reusable):
if `O_q(H) = ⊥` for a finite nilpotent `H`, then `q ∤ |H|`.  The Sylow `q`-subgroup of a nilpotent
group is normal (`Group.normalizerCondition_of_isNilpotent`), hence equals `O_q(H)`
(`Sylow.eq_opCore_of_normal`); if that is `⊥` then `q ∤ |H|`. -/
theorem not_dvd_card_of_opCore_eq_bot {H : Type*} [Group H] [Finite H] {q : ℕ} [Fact q.Prime]
    [Group.IsNilpotent H] (hbot : OddOrder.Isaacs.Ch01.opCore q H = ⊥) : ¬ q ∣ Nat.card H := by
  intro hdvd
  obtain ⟨P⟩ := Sylow.nonempty (p := q) (G := H)
  have hPnorm : (P : Subgroup H).Normal :=
    Sylow.normal_of_normalizerCondition Group.normalizerCondition_of_isNilpotent P
  have hPcore : (P : Subgroup H) = OddOrder.Isaacs.Ch01.opCore q H :=
    OddOrder.Isaacs.Ch01.Sylow.eq_opCore_of_normal P hPnorm
  exact (OddOrder.Isaacs.Ch07.Sylow.ne_bot_of_dvd_card hdvd P) (hPcore.trans hbot)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Theorem 15.2 step (c) — `Q = O_q(M)` is the Sylow `q`-subgroup of `M_σ`** (mmd L4192, the
implicit content of "choose a complement `D` of `Q` in `M_σ`"): with `M_σ/Q` nilpotent (step (c)(d),
`msigma_quotient_isNilpotent_of_inputs`) and `Q = O_q(M)` the maximal normal `q`-subgroup of `M`,
the index `[M_σ : Q]` is coprime to `q`, i.e. `Q` is a Hall `{q}`-subgroup (= normal Sylow `q`) of
`M_σ`.

Argument: were `q ∣ [M_σ : Q]`, the (characteristic, since `M_σ/Q` is nilpotent) `q`-core
`R̄ = O_q(M_σ/Q)` would be nontrivial; its preimage `R` in `M_σ` is a `q`-group properly above `Q`,
and `R.map M_σ.subtype ⊴ M` (the `q`-core `R̄` is characteristic, so preserved by the
`M`-conjugation
automorphisms of `M_σ/Q`; `M` normalizes `M_σ` and `Q`).  A normal `q`-subgroup of `M` lies in
`O_q(M) = Q`, forcing `R = Q`, i.e. `R̄ = ⊥` — contradiction.  Hence `O_q(M_σ/Q) = ⊥`, and
`not_dvd_card_of_opCore_eq_bot` gives `q ∤ [M_σ : Q]`. -/
theorem q_not_dvd_index_of_msigma_quotient_isNilpotent [Finite G]
    {M Mσ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (_hQMσ : Q ≤ Mσ) (hMσM : Mσ ≤ M) (hQpg : IsPGroup q ↥Q)
    (hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G))
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQmax : ∀ R : Subgroup G, R ≤ M → (R.subgroupOf M).Normal → IsPGroup q ↥R → R ≤ Q)
    [hQn : (Q.subgroupOf Mσ).Normal]
    (hNil : Group.IsNilpotent (↥Mσ ⧸ Q.subgroupOf Mσ)) :
    ¬ q ∣ (Q.subgroupOf Mσ).index := by
  classical
  have := hNil
  set Cq : Subgroup (↥Mσ ⧸ Q.subgroupOf Mσ) := OddOrder.Isaacs.Ch01.opCore q (↥Mσ ⧸ Q.subgroupOf Mσ)
    with hCq
  -- It suffices to show `Cq = ⊥` (then `q ∤ |Mσ/Q| = [Mσ:Q]`).
  suffices hbot : Cq = ⊥ by
    have h := not_dvd_card_of_opCore_eq_bot (H := ↥Mσ ⧸ Q.subgroupOf Mσ) (q := q) hbot
    rwa [show Nat.card (↥Mσ ⧸ Q.subgroupOf Mσ) = (Q.subgroupOf Mσ).index from rfl] at h
  -- `R := preimage of Cq in ↥Mσ`, a `q`-group containing `Q.subgroupOf Mσ`.
  set R : Subgroup ↥Mσ := Cq.comap (QuotientGroup.mk' (Q.subgroupOf Mσ)) with hR
  set RG : Subgroup G := R.map Mσ.subtype with hRG
  have hRG_le_Mσ : RG ≤ Mσ := Subgroup.map_subtype_le _
  have hRG_le_M : RG ≤ M := hRG_le_Mσ.trans hMσM
  have hmem : ∀ x : G, x ∈ RG ↔
      ∃ hx : x ∈ Mσ, QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨x, hx⟩ ∈ Cq := by
    intro x
    constructor
    · rintro ⟨z, hzR, rfl⟩
      have : QuotientGroup.mk' (Q.subgroupOf Mσ) z ∈ Cq := Subgroup.mem_comap.mp hzR
      exact ⟨z.2, this⟩
    · rintro ⟨hx, hxC⟩
      exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr hxC, rfl⟩
  have hQsub_le_R : Q.subgroupOf Mσ ≤ R := by
    intro x hx
    rw [hR, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Cq.one_mem
  -- `R` is a `q`-group: extension of the `q`-group `Q.subgroupOf Mσ` by the `q`-group `Cq`.
  have hQpg' : IsPGroup q ↥(Q.subgroupOf Mσ) :=
    hQpg.comap_of_injective (Subgroup.subtype Mσ) Mσ.subtype_injective
  have hCq_pg : IsPGroup q ↥Cq := OddOrder.Isaacs.Ch01.opCore_isPGroup q _
  have hR_pg : IsPGroup q ↥R := by
    -- the map `g : ↥R → Cq`, `r ↦ [r]`, is surjective with kernel `(Q.subgroupOf Mσ).subgroupOf R`.
    have hmem_Cq : ∀ r : ↥R, QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype r) ∈ Cq := fun r =>
      Subgroup.mem_comap.mp r.2
    set g : ↥R →* ↥Cq :=
      ((QuotientGroup.mk' (Q.subgroupOf Mσ)).comp R.subtype).codRestrict Cq hmem_Cq with hg
    have hgsurj : Function.Surjective g := by
      rintro ⟨w, hw⟩
      obtain ⟨z, hz⟩ := QuotientGroup.mk_surjective w
      have hzmem : z ∈ R := by
        rw [hR, Subgroup.mem_comap]; rw [← hz] at hw; exact hw
      refine ⟨⟨z, hzmem⟩, Subtype.ext ?_⟩
      rw [hg]
      change (QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype ⟨z, hzmem⟩) : ↥Mσ ⧸ Q.subgroupOf Mσ) =
          w
      rw [QuotientGroup.mk'_apply]; exact hz
    have hgval : ∀ r : ↥R, (g r : ↥Mσ ⧸ Q.subgroupOf Mσ)
        = QuotientGroup.mk' (Q.subgroupOf Mσ) (R.subtype r) := fun r => rfl
    have hgker : g.ker = (Q.subgroupOf Mσ).subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        ← Subtype.coe_inj, hgval, OneMemClass.coe_one, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    rw [IsPGroup.iff_card]
    have hkpg : IsPGroup q ↥g.ker := by
      rw [hgker]
      exact hQpg'.of_equiv (Subgroup.subgroupOfEquivOfLe hQsub_le_R).symm
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hkpg
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hCq_pg
    have hcard : Nat.card ↥R = Nat.card ↥g.ker * Nat.card ↥Cq := by
      have he : (↥R ⧸ g.ker) ≃* ↥Cq :=
        QuotientGroup.quotientKerEquivOfSurjective g hgsurj
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker, Nat.card_congr he.toEquiv,
        mul_comm]
    exact ⟨a + b, by rw [hcard, ha, hb, ← pow_add]⟩
  have hRG_pg : IsPGroup q ↥RG := hR_pg.map Mσ.subtype
  -- `RG ⊴ M`: the `q`-core `Cq` of `M_σ/Q` is characteristic, so preserved by `M`-conjugation.
  have hCq_char : Cq.Characteristic := by rw [hCq]; infer_instance
  have hRG_normM : (RG.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hRG_le_M]
    intro m hm
    have hmMσ : m ∈ Subgroup.normalizer (Mσ : Set G) := hMnormMσ hm
    -- conj by `m` on `↥Mσ`, the induced quotient automorphism `ᾱ`, and the `Q`-invariance of `α`.
    set α : ↥Mσ ≃* ↥Mσ := (Subgroup.normalizerMonoidHom Mσ) ⟨m, hmMσ⟩ with hα
    have hαval : ∀ x : ↥Mσ, (α x : G) = m * (x : G) * m⁻¹ := fun x => rfl
    -- `α z ∈ Q.subgroupOf Mσ ↔ z ∈ Q.subgroupOf Mσ` (conjugation by `m ∈ N_G(Q)`).
    have hαQiff : ∀ z : ↥Mσ, (α z ∈ Q.subgroupOf Mσ) ↔ (z ∈ Q.subgroupOf Mσ) := by
      intro z
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      show (α z : G) ∈ Q ↔ (z : G) ∈ Q
      rw [hαval]
      exact (Subgroup.mem_normalizer_iff.mp (hMnormQ hm) (z : G)).symm
    have hαmapQ : (Q.subgroupOf Mσ).map α.toMonoidHom = Q.subgroupOf Mσ := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hzQ, rfl⟩; exact (hαQiff z).mpr hzQ
      · intro hxQ
        exact ⟨α.symm x, (hαQiff (α.symm x)).mp (by rw [α.apply_symm_apply]; exact hxQ),
          α.apply_symm_apply x⟩
    set ᾱ : (↥Mσ ⧸ Q.subgroupOf Mσ) ≃* (↥Mσ ⧸ Q.subgroupOf Mσ) :=
      QuotientGroup.congr (Q.subgroupOf Mσ) (Q.subgroupOf Mσ) α hαmapQ with hαbar
    have hαbarval : ∀ x : ↥Mσ, ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) x)
        = QuotientGroup.mk' (Q.subgroupOf Mσ) (α x) := fun x => by
      rw [hαbar]; exact QuotientGroup.congr_mk' (Q.subgroupOf Mσ) (Q.subgroupOf Mσ) α hαmapQ x
    -- `ᾱ c ∈ Cq ↔ c ∈ Cq` (`Cq` characteristic ⟹ `ᾱ`-invariant).
    have hCqiff : ∀ c : ↥Mσ ⧸ Q.subgroupOf Mσ, (ᾱ c ∈ Cq) ↔ (c ∈ Cq) := by
      intro c
      have hfix := hCq_char.fixed ᾱ
      constructor
      · intro h; rw [← hfix, Subgroup.mem_comap]; exact h
      · intro h; rw [← hfix, Subgroup.mem_comap] at h; exact h
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [hmem, hmem]
    constructor
    · rintro ⟨hyMσ, hyC⟩
      have hmym : m * y * m⁻¹ ∈ Mσ := (Subgroup.mem_normalizer_iff.mp hmMσ y).mp hyMσ
      refine ⟨hmym, ?_⟩
      -- `mk'⟨m·y·m⁻¹⟩ = ᾱ(mk'⟨y⟩) ∈ ᾱ(Cq) = Cq`.
      have heqcls : QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨m * y * m⁻¹, hmym⟩
          = ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨y, hyMσ⟩) := by
        rw [hαbarval]
        exact congrArg (QuotientGroup.mk' (Q.subgroupOf Mσ)) (Subtype.ext (hαval ⟨y, hyMσ⟩).symm)
      rw [heqcls]; exact (hCqiff _).mpr hyC
    · rintro ⟨hmymMσ, hmymC⟩
      -- `mk'⟨m·y·m⁻¹⟩ ∈ Cq ⟹ mk'⟨y⟩ ∈ Cq` (via `ᾱ`-invariance).
      have hyMσ : y ∈ Mσ := (Subgroup.mem_normalizer_iff.mp hmMσ y).mpr hmymMσ
      refine ⟨hyMσ, ?_⟩
      have heqcls : QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨m * y * m⁻¹, hmymMσ⟩
          = ᾱ (QuotientGroup.mk' (Q.subgroupOf Mσ) ⟨y, hyMσ⟩) := by
        rw [hαbarval]
        exact congrArg (QuotientGroup.mk' (Q.subgroupOf Mσ)) (Subtype.ext (hαval ⟨y, hyMσ⟩).symm)
      rw [heqcls] at hmymC
      exact (hCqiff _).mp hmymC
  have hRG_le_Q : RG ≤ Q := hQmax RG hRG_le_M hRG_normM hRG_pg
  -- `R ≤ Q.subgroupOf Mσ`, so combined with `hQsub_le_R`, `R = Q.subgroupOf Mσ`, forcing `Cq = ⊥`.
  have hR_le_Qsub : R ≤ Q.subgroupOf Mσ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hRG_le_Q ⟨x, hx, rfl⟩
  have hReq : R = Q.subgroupOf Mσ := le_antisymm hR_le_Qsub hQsub_le_R
  -- `comap (mk') Cq = R = Q.subgroupOf Mσ = ker (mk') = comap (mk') ⊥`; `mk'` surjective ⟹
  -- `Cq = ⊥`.
  have hcomapbot : Cq.comap (QuotientGroup.mk' (Q.subgroupOf Mσ))
      = (⊥ : Subgroup (↥Mσ ⧸ Q.subgroupOf Mσ)).comap (QuotientGroup.mk' (Q.subgroupOf Mσ)) := by
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rw [← hR]; exact hReq
  exact (Subgroup.comap_injective (QuotientGroup.mk'_surjective _)) hcomapbot

/-- **`Q.subgroupOf M_σ` is a Hall `{q}`-subgroup of `↥M_σ`** (`§14`-independent helper): for a
`q`-subgroup `Q ≤ M_σ` with `q ∤ [M_σ : Q]`, the relative subgroup is a `{q}`-Hall (= normal Sylow
`q`) of `↥M_σ`.  Used to complement `Q` by a `{q}ᶜ`-Hall in the `D`-construction. -/
theorem isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index [Finite G]
    {Mσ Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hQMσ : Q ≤ Mσ) (hQpg : IsPGroup q ↥Q) (hidx : ¬ q ∣ (Q.subgroupOf Mσ).index) :
    Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mσ) := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have hcard : Nat.card ↥(Q.subgroupOf Mσ) = Nat.card ↥Q :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv
    rw [hcard] at hp
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn] at hp
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · simp [hn0] at hp
    · rw [Nat.primeFactors_prime_pow hn0.ne' Fact.out, Finset.mem_singleton] at hp
      exact Set.mem_singleton_iff.mpr hp
  · rw [Set.mem_singleton_iff]; rintro rfl; exact hidx (Nat.dvd_of_mem_primeFactors hp)

/-- **Theorem 15.2 step 3 — the `K`-invariant complement `D` of `Q` in `M_σ`** (mmd L4194, "By
Proposition 1.5(a), we may choose a `K`-invariant complement `D` of `Q` in `M_σ`").  In the
type-`P₁` setting (`hP`, `hKstarQ`, `hQneMσ` giving `M_σ` non-nilpotent), with `Q = O_q(M)` the
normal Sylow `q`-subgroup of `M_σ` (`msigma_quotient_isNilpotent_of_inputs` +
`q_not_dvd_index_of_msigma_quotient_isNilpotent`), Proposition 1.5(a) (`exists_aInvariant_hall`)
furnishes a `K`-invariant `{q}ᶜ`-Hall subgroup `D` of `M_σ`, which complements `Q` (coprime Hall
orders) and is nilpotent (`complement_isNilpotent_of_inputs`).

Output (matching the wrapper's existential block): `D ≤ M_σ`, `K ≤ N_G(D)`, `Disjoint Q D`, the
complement `IsComplement' (Q.subgroupOf M_σ) (D.subgroupOf M_σ)`, `D` nilpotent, and `D ≠ ⊥`. -/
theorem exists_kInvariant_qComplement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKne : K ≠ ⊥) (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M))) :
    ∃ D : Subgroup G, D ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      K ≤ Subgroup.normalizer (D : Set G) ∧ Disjoint Q D ∧
      Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
        (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
      Group.IsNilpotent ↥D ∧ D ≠ ⊥ ∧ q ∉ (Nat.card ↥D).primeFactors := by
  classical
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Group.IsSolvable ↥Mσ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hMσM)
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  have hQnMσ : (Q.subgroupOf Mσ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  -- `M_σ/Q` nilpotent (step (c)(d)) and `q ∤ [M_σ:Q]` (step (c), `Q` is the Sylow `q`).
  have hNil : Group.IsNilpotent (↥Mσ ⧸ Q.subgroupOf Mσ) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcop
  have hQmax : ∀ R : Subgroup G, R ≤ M → (R.subgroupOf M).Normal → IsPGroup q ↥R → R ≤ Q := by
    intro R hRM hRnorm hRpg
    rw [hQ]
    refine le_opiCoreInG_of_normal_of_isPiSubgroup hRM hRnorm ?_
    intro p hp
    obtain ⟨n, hn⟩ := hRpg.exists_card_eq
    rw [hn] at hp
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0] at hp
    · rw [Nat.primeFactors_prime_pow h0.ne' Fact.out, Finset.mem_singleton] at hp
      exact Set.mem_singleton_iff.mpr hp
  have hidx : ¬ q ∣ (Q.subgroupOf Mσ).index :=
    q_not_dvd_index_of_msigma_quotient_isNilpotent hQMσ hMσM hQpg hMnormMσ hMnormQ hQmax hNil
  have hQHall : Ch03.IsHallSubgroup ({q} : Set ℕ) (Q.subgroupOf Mσ) :=
    isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index hQMσ hQpg hidx
  -- the `K`-conjugation action on `↥M_σ` and the `K`-invariant `{q}ᶜ`-Hall `D_M`.
  have hKnormMσ : K ≤ Subgroup.normalizer (Mσ : Set G) := hKM.trans hMnormMσ
  set φ : ↥K →* MulAut ↥Mσ :=
    (Subgroup.normalizerMonoidHom Mσ).comp (Subgroup.inclusion hKnormMσ) with hφ
  obtain ⟨DM, hDM_hall, hDM_inv⟩ :=
    OddOrder.BG.Ch1.S01.exists_aInvariant_hall (G := ↥Mσ) (A := ↥K) (φ := φ) hcop ({q}ᶜ : Set ℕ)
  set D : Subgroup G := DM.map Mσ.subtype with hD
  have hD_le_Mσ : D ≤ Mσ := Subgroup.map_subtype_le _
  have hDsub_eq : D.subgroupOf Mσ = DM := by
    rw [hD, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Mσ.subtype_injective]
  -- `{q}ᶜ`-Hall `DM` = `{p ∉ {q}}`-Hall (defeq, for `hall_compl_isComplement`).
  have hDM_hall' : Ch03.IsHallSubgroup {p | p ∉ ({q} : Set ℕ)} DM := hDM_hall
  -- `IsComplement' DM (Q.subgroupOf Mσ)`, hence
  -- `IsComplement' (Q.subgroupOf Mσ) (D.subgroupOf Mσ)`.
  have hcompl : Subgroup.IsComplement' (Q.subgroupOf Mσ) (D.subgroupOf Mσ) := by
    rw [hDsub_eq]
    exact (OddOrder.BG.Ch1.S01.hall_compl_isComplement hDM_hall' hQHall).symm
  -- `Disjoint Q D`: complement disjointness lifted to `G`.
  have hdisjQD : Disjoint Q D := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    have hxMσ : x ∈ Mσ := hQMσ hxQ
    have hmem : (⟨x, hxMσ⟩ : ↥Mσ) ∈ (Q.subgroupOf Mσ) ⊓ (D.subgroupOf Mσ) :=
      ⟨Subgroup.mem_subgroupOf.mpr hxQ, Subgroup.mem_subgroupOf.mpr hxD⟩
    rw [hcompl.disjoint.eq_bot, Subgroup.mem_bot] at hmem
    exact congrArg (Subgroup.subtype Mσ) hmem
  -- `K ≤ N_G(D)`: `K`-invariance of `DM` (`φ k • DM = DM`) ⟹ `k·d·k⁻¹ ∈ D` for `d ∈ D`.
  have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype ?_
    intro x hxD
    rw [hD] at hxD ⊢
    obtain ⟨w, hwDM, rfl⟩ := hxD
    -- `k·↑w·k⁻¹ = ↑(φk w)`, and `φk w ∈ DM` (invariance `φk • DM = DM`).
    have hφwDM : φ ⟨k, hk⟩ w ∈ DM := by
      have hmem : φ ⟨k, hk⟩ w ∈ φ ⟨k, hk⟩ • DM := by
        rw [Subgroup.pointwise_smul_def]; exact Subgroup.mem_map.mpr ⟨w, hwDM, rfl⟩
      rwa [hDM_inv ⟨k, hk⟩] at hmem
    refine ⟨φ ⟨k, hk⟩ w, hφwDM, ?_⟩
    change ((φ ⟨k, hk⟩ w : ↥Mσ) : G) = k * (Mσ.subtype w) * k⁻¹
    rfl
  -- `D` nilpotent (`complement_isNilpotent_of_inputs`, prime-order `K₁ ≤ K`).
  -- (assembled below via a prime-order `K₁ ≤ K` and the prime-manner action).
  refine ⟨D, hD_le_Mσ, hKnormD, hdisjQD, hcompl, ?_, ?_, ?_⟩
  · -- `D` nilpotent: prime-order `K₁ ≤ K` acts FPF on `D` (Theorem 3.7).
    have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
    have hKcard1 : Nat.card ↥K ≠ 1 := fun hc => hKne (Subgroup.card_eq_one.mp hc)
    obtain ⟨r, hr_prime, hr_dvd⟩ := Nat.exists_prime_and_dvd hKcard1
    have : Fact r.Prime := ⟨hr_prime⟩
    obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) r hr_dvd
    set K1 : Subgroup G := Subgroup.zpowers (c : G) with hK1
    have hcK : (c : G) ∈ K := c.2
    have hK1K : K1 ≤ K := by rw [hK1]; exact Subgroup.zpowers_le.mpr hcK
    have hK1M : K1 ≤ M := hK1K.trans hKM
    have hDM_le_M : D ≤ M := hD_le_Mσ.trans hMσM
    have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
    have hcardK1 : Nat.card ↥K1 = r := by rw [hK1, Nat.card_zpowers, hord_coe]
    -- `D ≠ ⊥`: else `Q = M_σ` (`Q ⊔ D = M_σ`), contradicting `hQneMσ`.
    have hDne : D ≠ ⊥ := by
      intro hbot
      apply hQneMσ
      have : Q.subgroupOf Mσ = ⊤ := by
        have hsup : Q.subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ := hcompl.sup_eq_top
        rw [hbot] at hsup; simpa using hsup
      have hQeq : Q.subgroupOf Mσ = (⊤ : Subgroup Mσ) := this
      have := Subgroup.subgroupOf_eq_top.mp hQeq
      exact le_antisymm hQMσ this
    have hK1ne : K1 ≠ ⊥ := by
      rw [hK1, Ne, Subgroup.zpowers_eq_bot]
      intro hc1
      have : orderOf (c : G) = 1 := by rw [hc1]; exact orderOf_one
      rw [hord_coe] at this; exact hr_prime.ne_one this
    have hDQ_disj : Disjoint D Q := hdisjQD.symm
    have hDK1disj : Disjoint D K1 := (hKMσdisj.symm.mono_left hD_le_Mσ).mono_right hK1K
    have hK1normD : K1 ≤ Subgroup.normalizer (D : Set G) := hK1K.trans hKnormD
    refine complement_isNilpotent_of_inputs hG hM hDM_le_M hK1M hD_le_Mσ hDQ_disj hK1K
      hK1normD hDK1disj hDne hK1ne ⟨r, hr_prime, hcardK1⟩ ?_
    -- `hCentleQ`: `C_G(r) ⊓ M_σ = K* ⊆ Q` for `r ∈ K#` (prime-manner + `K* ⊆ Q`).
    intro x hxK hx1
    rw [hprime x hxK hx1]; exact hKstarQ
  · -- `D ≠ ⊥`: as above.
    intro hbot
    apply hQneMσ
    have hsup : Q.subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ := hcompl.sup_eq_top
    rw [hbot] at hsup; simp only [Subgroup.bot_subgroupOf, sup_bot_eq] at hsup
    exact le_antisymm hQMσ (Subgroup.subgroupOf_eq_top.mp hsup)
  · -- `q ∤ |D|`: `|D| = [M_σ : Q]` (complement) and `q ∤ [M_σ : Q]` (`hidx`).
    intro hmem
    apply hidx
    have hDcard : Nat.card ↥D = (Q.subgroupOf Mσ).index := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hD_le_Mσ).toEquiv]
      exact (hcompl.symm.index_eq_card).symm
    rw [← hDcard]; exact (Nat.mem_primeFactors.mp hmem).2.1

/-- **Theorem 15.2 step 4, the `D`-side fixed-point fact** (BG Proposition 1.5(d)/1.6(d), mmd
L4196-4200): a single `q'`-element `d` (here `d ∈ D`, coprime to `Q`) that *centralizes the chief
factor* `Q̄ = Q/Q₀` (`⁅d, y⁆ ∈ Q₀` for every `y ∈ Q`) already centralizes `Q` itself, **provided**
`Q₀ ⊆ C_G(d)` (which holds since `Q₀ = C_Q(D) ⊆ C_G(d)` for `d ∈ D`).

This is the BG step "`C_D(Q̄) = C_D(Q)`".  Proof via the coprime decomposition (Proposition 1.6(d),
`subgroup_coprime_decomposition`): for the coprime action of `A = ⟨d⟩` on `Q`,
`Q = C_Q(⟨d⟩) ⊔ ⁅Q, ⟨d⟩⁆`.  The set of `x ∈ N(Q₀)` whose conjugation centralizes `Q̄` is a subgroup
containing `d` (closure uses `⁅x x', y⁆ = x ⁅x', y⁆ x⁻¹ · ⁅x, y⁆`), hence `⟨d⟩`, so `⁅Q, ⟨d⟩⁆ ≤ Q₀`.
With `Q₀ ⊆ C_G(d)` and `C_Q(⟨d⟩) ⊆ C_G(d)` (as `d ∈ ⟨d⟩`), both summands centralize `d`, so does
`Q`.

Used in `centralizer_msigma_quotient_le_fittingInAmbient` to decompose `C_{M_σ}(Q̄) = Q·C_D(Q)`. -/
theorem centralizes_Q_of_centralizes_quotient [Finite G]
    {Q Q0 : Subgroup G} {d : G}
    (hdN : d ∈ Subgroup.normalizer (Q : Set G))
    (_hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hdQ0 : d ∈ Subgroup.normalizer (Q0 : Set G))
    (_hQ0Q : Q0 ≤ Q) (hQ0d : Q0 ≤ Subgroup.centralizer ({d} : Set G))
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥Q))
    (hSolv : Group.IsSolvable ↥Q)
    (hfix : ∀ y ∈ Q, ⁅d, y⁆ ∈ Q0) :
    Q ≤ Subgroup.centralizer ({d} : Set G) := by
  classical
  have hAN : Subgroup.zpowers d ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le).mpr hdN
  -- The set of `x ∈ N(Q₀)` whose conjugation centralizes `Q̄` (`⁅x, y⁆ ∈ Q₀` for all `y ∈ Q`) is a
  -- subgroup of `G`; it contains `d`, hence all of `⟨d⟩`.  `⁅x x', y⁆ = x ⁅x', y⁆ x⁻¹ · ⁅x, y⁆`.
  let T : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (Q0 : Set G) ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0}
      one_mem' := ⟨(Subgroup.normalizer (Q0 : Set G)).one_mem, fun y _ => by
        rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {x x'} hx hx' => ⟨(Subgroup.normalizer (Q0 : Set G)).mul_mem hx.1 hx'.1,
        fun y hyQ => by
          have heq : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
            rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
          rw [heq]
          exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hx.1 ⁅x', y⁆).mp (hx'.2 y hyQ))
            (hx.2 y hyQ)⟩
      inv_mem' := fun {x} hx => ⟨(Subgroup.normalizer (Q0 : Set G)).inv_mem hx.1, fun y hyQ => by
        have heq : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * (x⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hx.1)
          ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hx.2 y hyQ))⟩ }
  have hdT : d ∈ T := ⟨hdQ0, hfix⟩
  have hzpT : Subgroup.zpowers d ≤ T := (Subgroup.zpowers_le).mpr hdT
  -- Hence `⁅Q, ⟨d⟩⁆ ≤ Q₀`.
  have hcommQ0 : ⁅Q, Subgroup.zpowers d⁆ ≤ Q0 := by
    rw [Subgroup.commutator_le]
    intro y hyQ a ha
    rw [← commutatorElement_inv]
    exact Q0.inv_mem ((hzpT ha).2 y hyQ)
  -- Proposition 1.6(d): `Q = C_Q(⟨d⟩) ⊔ ⁅Q, ⟨d⟩⁆`.
  have hdecomp := OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition hAN hcop (Or.inr hSolv)
  -- Both summands centralize `d`: `C(⟨d⟩) ⊆ C(d)` and `⁅Q, ⟨d⟩⁆ ≤ Q₀ ⊆ C(d)`.
  rw [hdecomp]
  refine sup_le (inf_le_left.trans ?_) (hcommQ0.trans hQ0d)
  exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers d))

/-- From an `IsComplement'` of `H.subgroupOf N` and `K.subgroupOf N` (with `H, K ≤ N`), every
`x ∈ N` factors as `x = a·b` with `a ∈ H`, `b ∈ K` (`§14`-independent, generic helper; keeps the
`↥N`-complement reasoning away from later `M_σ`-unfolding). -/
theorem exists_mul_mem_of_isComplement_subgroupOf {N H K : Subgroup G} (_hHN : H ≤ N) (_hKN : K ≤ N)
    (hcompl : Subgroup.IsComplement' (H.subgroupOf N) (K.subgroupOf N))
    {x : G} (hxN : x ∈ N) : ∃ a ∈ H, ∃ b ∈ K, x = a * b := by
  -- `(H.subgroupOf N) * (K.subgroupOf N) = univ` (complement), so `⟨x, _⟩` factors there.
  have hmul : (⟨x, hxN⟩ : ↥N) ∈
      ((H.subgroupOf N : Set ↥N) * (K.subgroupOf N : Set ↥N)) := by
    rw [hcompl.mul_eq]; exact Set.mem_univ _
  obtain ⟨u, huH, v, hvK, huv⟩ := Set.mem_mul.mp hmul
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at huH hvK
  refine ⟨(u : G), huH, (v : G), hvK, ?_⟩
  have hcoe : ((⟨x, hxN⟩ : ↥N) : G) = ((u * v : ↥N) : G) := congrArg _ huv.symm
  rw [Subgroup.coe_mul] at hcoe
  exact hcoe

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped commutatorElement in
/-- **Theorem 15.2(g) — the section-Fitting containment `C_{M_σ}(Q̄) ⊆ F(M)`** (mmd L4196-4198,
"`F(M) = Q·C_M(Q) = C_{M_σ}(Q̄)`"), which discharges `hsecFit` of
`derivedDerived_le_fittingInAmbient_of_inputs`.  Unlike the *full* centralizer `C_M(Q)` (which needs
the genuine `σ`-uniqueness gate `C_M(Q) ⊆ M_σ`), the `M_σ`-section centralizer `C_{M_σ}(Q̄)` lands
in
`F(M)` from the local `M_σ = Q ⋊ D` structure alone:

* `S := C_{M_σ}(Q̄) = {x ∈ M_σ : ⁅x, y⁆ ∈ Q₀ ∀ y ∈ Q}` decomposes as `S = Q ⊔ (D ⊓ S)`: writing
  `x ∈ M_σ` as `a·d'` (`a ∈ Q`, `d' ∈ D`, the complement), `a ∈ Q ⊆ S` (`Q̄` abelian, `hQab`), so
  `d' = a⁻¹x ∈ D ⊓ S`;
* `D ⊓ S ⊆ C_G(Q)`: each `d' ∈ D ⊓ S` centralizes `Q̄` and is a `q'`-element, hence centralizes `Q`
  (`centralizes_Q_of_centralizes_quotient`);
* so `⁅Q, D ⊓ S⁆ = ⊥`, and `S = Q ⊔ (D ⊓ S)` is nilpotent (`Q` a `q`-group, `D ⊓ S ⊆ D` nilpotent,
  commuting: `isNilpotent_sup_of_commutator_eq_bot`);
* `S ◁ M` (`M` normalizes `Q`, `Q₀`, and `M_σ`), so a nilpotent normal subgroup of `M` lands in
  `F(M)` (`nilpotent_normal_le_fitting`).

No `σ`-uniqueness input is needed (the `C_M(Q) ⊆ M_σ` gate is only for the *full* `C_M(Q)`). -/
theorem centralizer_msigma_quotient_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q Q0 D : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hQ0 : Q0 = Q ⊓ Subgroup.centralizer (D : Set G)) (hQ0Q : Q0 ≤ Q)
    (hcompl : Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
      (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)))
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hMnormQ0 : M ≤ Subgroup.normalizer (Q0 : Set G))
    (hQpg : IsPGroup q ↥Q) (hDnil : Group.IsNilpotent ↥D)
    (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) :
    ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) → x ∈ fittingInAmbient M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set Mσ : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hMσM : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMnormMσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hDM : D ≤ M := hDMσ.trans hMσM
  have : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQM)
  -- The section centralizer `S = C_{M_σ}(Q̄)`, realized as a subgroup of `G`.
  -- (Membership in `M_σ` already gives `x ∈ N(Q₀)` since `M_σ ≤ M ≤ N(Q₀)`.)
  have hMσnormQ0 : Mσ ≤ Subgroup.normalizer (Q0 : Set G) := hMσM.trans hMnormQ0
  let S : Subgroup G :=
    { carrier := {x | x ∈ Mσ ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0}
      one_mem' := ⟨Mσ.one_mem, fun y _ => by rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {x x'} hx hx' => ⟨Mσ.mul_mem hx.1 hx'.1, fun y hyQ => by
        have heq : ⁅x * x', y⁆ = (x * ⁅x', y⁆ * x⁻¹) * ⁅x, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
        exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN0 ⁅x', y⁆).mp (hx'.2 y hyQ))
          (hx.2 y hyQ)⟩
      inv_mem' := fun {x} hx => ⟨Mσ.inv_mem hx.1, fun y hyQ => by
        have heq : ⁅x⁻¹, y⁆ = x⁻¹ * ⁅x, y⁆⁻¹ * (x⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hMσnormQ0 hx.1
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN0)
          ⁅x, y⁆⁻¹).mp (Q0.inv_mem (hx.2 y hyQ))⟩ }
  have hSmem : ∀ x, x ∈ S ↔ x ∈ Mσ ∧ ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := fun x => Iff.rfl
  have hSMσ : S ≤ Mσ := fun x hx => hx.1
  -- `Q ≤ S` (`Q̄` abelian) and `D ⊓ S ⊆ C_G(Q)` (the `q'`-elements of `S` centralize `Q`).
  have hQS : Q ≤ S := fun a haQ => ⟨hQMσ haQ, fun y hyQ => hQab a haQ y hyQ⟩
  have hDScent : (D ⊓ S : Subgroup G) ≤ Subgroup.centralizer (Q : Set G) := by
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdD, hdS⟩ := hd
    have hdN : d ∈ Subgroup.normalizer (Q : Set G) := hMnormQ (hDM hdD)
    have hdN0 : d ∈ Subgroup.normalizer (Q0 : Set G) := hMnormQ0 (hDM hdD)
    -- coprimality `|⟨d⟩| | |Q|`.
    have hcopd : Nat.Coprime (Nat.card ↥(Subgroup.zpowers d)) (Nat.card ↥Q) :=
      hcop.coprime_dvd_left (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hdD))
    -- `Q₀ ⊆ C_G(d)` (since `Q₀ = Q ⊓ C(D)` and `d ∈ D`).
    have hQ0d : Q0 ≤ Subgroup.centralizer ({d} : Set G) := by
      rw [hQ0]
      refine inf_le_right.trans ?_
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdD)
    have hQN0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQMσ.trans hMσnormQ0
    have hQleCd : Q ≤ Subgroup.centralizer ({d} : Set G) :=
      centralizes_Q_of_centralizes_quotient hdN hQN0 hdN0 hQ0Q hQ0d hcopd ‹Group.IsSolvable ↥Q›
          hdS.2
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Subgroup.mem_centralizer_iff.mp (hQleCd hg) d (Set.mem_singleton d)).symm
  -- `S = Q ⊔ (D ⊓ S)`: the `M_σ = Q·D` decomposition lands the `q'`-part in `D ⊓ S`.
  have hSdecomp : S = Q ⊔ (D ⊓ S) := by
    refine le_antisymm (fun x hx => ?_) (sup_le hQS inf_le_right)
    -- `x ∈ M_σ = Q·D`, so `x = a·b` with `a ∈ Q`, `b ∈ D`; then `b = a⁻¹x ∈ D ⊓ S`.
    obtain ⟨a, haQ, b, hbD, hxeq⟩ :=
      exists_mul_mem_of_isComplement_subgroupOf hQMσ hDMσ hcompl (hSMσ hx)
    have haS : a ∈ S := hQS haQ
    have hbS : b ∈ S := by
      have hbeq : b = a⁻¹ * x := by rw [hxeq]; group
      rw [hbeq]; exact S.mul_mem (S.inv_mem haS) hx
    rw [hxeq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left haQ)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hbD, hbS⟩))
  -- `S` is nilpotent: `Q ⊔ (D ⊓ S)` with `⁅Q, D ⊓ S⁆ = ⊥` (`D ⊓ S` centralizes `Q`).
  have : Group.IsNilpotent ↥Q := hQpg.isNilpotent
  have hDSnil : Group.IsNilpotent ↥((D ⊓ S : Subgroup G).subgroupOf D) := inferInstance
  have : Group.IsNilpotent ↥(D ⊓ S : Subgroup G) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : (D ⊓ S : Subgroup G) ≤ D))
  have hcommbot : ⁅Q, (D ⊓ S : Subgroup G)⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hDScent
  have : Group.IsNilpotent ↥S := by
    rw [hSdecomp]; exact isNilpotent_sup_of_commutator_eq_bot hcommbot
  -- `S ◁ M`: `M` normalizes `Q`, `Q₀`, and `M_σ`, hence the section centralizer.  Single direction
  -- `m·S·m⁻¹ ⊆ S` for `m ∈ M`, applied to `m` and `m⁻¹` gives normality.
  have hpreserve : ∀ m ∈ M, ∀ z ∈ S, m * z * m⁻¹ ∈ S := by
    intro m hm z hz
    obtain ⟨hzMσ, hzc⟩ := hz
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hMnormMσ hm) z).mp hzMσ, fun y hyQ => ?_⟩
    -- `⁅m z m⁻¹, y⁆ = m ⁅z, m⁻¹ y m⁆ m⁻¹ ∈ m Q₀ m⁻¹ = Q₀`.
    have hyQ' : m⁻¹ * y * m ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (hMnormQ (M.inv_mem hm)) y).mp hyQ
      rwa [inv_inv] at this
    have hc := hzc (m⁻¹ * y * m) hyQ'
    have heq : ⁅m * z * m⁻¹, y⁆ = m * ⁅z, m⁻¹ * y * m⁆ * m⁻¹ := by
      rw [conjugate_commutatorElement]; congr 1; group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp (hMnormQ0 hm) ⁅z, m⁻¹ * y * m⁆).mp hc
  have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz; exact hpreserve m hm z hz
    · intro hz
      have := hpreserve m⁻¹ (M.inv_mem hm) (m * z * m⁻¹) hz
      rwa [show m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z by group] at this
  -- `S` nilpotent + normal in `M` ⟹ `S ⊆ F(M)`.
  have hSnormM : (S.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hSMσ.trans hMσM)).mpr hMnormS
  have : Group.IsNilpotent ↥(S.subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hSMσ.trans hMσM)).symm
  have hSF : S ≤ fittingInAmbient M := by
    calc S = (S.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le (hSMσ.trans
        hMσM)).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
          Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      _ = fittingInAmbient M := rfl
  intro x hxMσ hxc
  exact hSF ⟨hxMσ, hxc⟩

/-- A finite `ZMod q`-module of cardinality `q` (`q` prime) has `Module.finrank ≤ 1`
(`§14`-independent, reusable).  Used to feed the cyclicity hypothesis `hcyc` of BG Theorem 3.10(c)
once `|C_{Q̄}(K)| = q` is known. -/
theorem finrank_le_one_of_card_eq {q : ℕ} [Fact q.Prime] {Mod : Type*}
    [AddCommGroup Mod] [Module (ZMod q) Mod] [Finite Mod] (h : Nat.card Mod = q) :
    Module.finrank (ZMod q) Mod ≤ 1 := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  have : Fintype Mod := Fintype.ofFinite Mod
  have hpow : Fintype.card Mod = q ^ Module.finrank (ZMod q) Mod := by
    rw [Module.card_eq_pow_finrank (K := ZMod q), ZMod.card]
  rw [Nat.card_eq_fintype_card, hpow] at h
  have hfin : Module.finrank (ZMod q) Mod = 1 :=
    Nat.pow_right_injective (Fact.out : q.Prime).two_le (h.trans (pow_one q).symm)
  omega

/-- **Counting the invariants of a quotient module by its fixed-point subgroup** (`§14`-independent,
reusable).  For a finite commutative `H`-module `Mod` over `ZMod q` (with `H` acting through a
`MulDistribMulAction`) and a subgroup `R ≤ H`, if `Cbar ≤ Mod` is exactly the set of `R`-fixed
points (`hchar`), then the `R`-invariants of the associated representation have cardinality
`|Cbar|`.

This isolates the `Module.End`/`Additive` instance bookkeeping (the module is an *instance argument*
here, mirroring `card_eq_pow_card_invariants_of_elemAbelian_general`), so the caller can apply it
without re-synthesising the representation.  Used in Theorem 15.2(f) to read off `|C_{Q̄}(K)|`. -/
theorem card_invariants_eq_card_of_fixedPoints {q : ℕ} {H : Type*} [Group H]
    {Mod : Type*} [CommGroup Mod] [Finite Mod] [Module (ZMod q) (Additive Mod)]
    [MulDistribMulAction H Mod] {R : Subgroup H} (Cbar : Subgroup Mod)
    (hchar : ∀ w : Mod, (∀ r : ↥R, (r : H) • w = w) ↔ w ∈ Cbar) :
    Nat.card ↥(Representation.invariants
      ((Representation.ofDistribMulAction (ZMod q) H (Additive Mod)).comp R.subtype))
      = Nat.card ↥Cbar := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv Additive.toMul (fun v => ?_)
  rw [Representation.mem_invariants, ← hchar (Additive.toMul v)]
  refine forall_congr' (fun r => ?_)
  change ((r : H) • v = v) ↔ ((r : H) • Additive.toMul v = Additive.toMul v)
  constructor
  · intro h
    have := congrArg Additive.toMul h
    rwa [show Additive.toMul ((r : H) • v) = (r : H) • Additive.toMul v from rfl] at this
  · intro h
    apply Additive.toMul.injective
    rwa [show Additive.toMul ((r : H) • v) = (r : H) • Additive.toMul v from rfl]

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
open scoped IsMulCommutative in
/-- **Theorem 15.2(f)+(g) — `[Q : Q₀] = q^p` and `D' ⊆ C_D(Q̄)`, gated-endpoint skeleton**
(mmd L4196-4200, BG Theorem 3.10(b)(c)).  The Frobenius group `D ⋊ K` (kernel `D`, complement `K`)
acts by conjugation on the elementary-abelian chief factor `Q̄ = Q/Q₀` (`hEA`).  The
caller-supplied subgroup `C` records the `K`-fixed classes (`C/Q₀ = C_{Q̄}(K)` via `hCfix`, with
`|C : Q₀| = q` via `hCcard`), so `|C_{Q̄}(K)| = q`.  Then:

* **(f)** BG Theorem 3.10(b) (`card_eq_pow_card_invariants_of_elemAbelian_general`) gives
  `|Q̄| = |C_{Q̄}(K)|^{|K|} = q^{|K|}`, i.e. `[Q : Q₀] = q^{|K|}`;
* **(g)** BG Theorem 3.10(c) (`commutator_acts_trivially_of_elemAbelian_general`, with the cyclicity
  hypothesis discharged by `finrank_le_one_of_card_eq` from `|C_{Q̄}(K)| = q`) gives
  `D' ⊆ C_D(Q̄)`, i.e. `∀ g ∈ ⁅D,D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q₀`.

The §14-gated inputs are `hcond3` (prime-manner action of `K`, Proposition 14.2(a)) and
`hCcard`/`hCfix` (`|K*| = q`, Theorem 14.7(f)); `hFPF` is discharged by
`mem_centralizer_of_centralizes_quotient`.  Both BG Theorem 3.10 forms share the one conjugation
`MulDistribMulAction` setup built here. -/
theorem chiefFactor_card_and_commutator_of_inputs [Finite G]
    {Q Q0 D K C : Subgroup G} {q : ℕ} [Fact q.Prime] [(Q0.subgroupOf Q).Normal]
    (_hQ0Q : Q0 ≤ Q) (hQ0C : Q0 ≤ C) (hCQ : C ≤ Q) (hDne : D ≠ ⊥)
    (hEA : OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q))
    (hNT : Nontrivial (↥Q ⧸ Q0.subgroupOf Q))
    (hDQ : D ≤ Subgroup.normalizer (Q : Set G)) (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hDQ0 : D ≤ Subgroup.normalizer (Q0 : Set G)) (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hsolv : Group.IsSolvable ↥(D ⊔ K))
    (hfrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(D ⊔ K)
      (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)))
    (hcop : Nat.Coprime (Nat.card ↥(D ⊔ K)) (Nat.card ↥Q))
    (hFPF : ∀ x ∈ Q, (∀ d ∈ D, ⁅d, x⁆ ∈ Q0) → x ∈ Q0)
    (hcond3 : ∀ x ∈ K, x ≠ 1 → ∀ y ∈ Q, (⁅x, y⁆ ∈ Q0 ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q0))
    (hCfix : ∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ C))
    (hCcard : (Q0.subgroupOf C).index = q) :
    (Nat.card ↥K).Prime ∧
      (Q0.subgroupOf Q).index = q ^ Nat.card ↥K ∧
      ∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0 := by
  classical
  set H : Subgroup G := D ⊔ K with hH
  have hDH : D ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hHQ : H ≤ Subgroup.normalizer (Q : Set G) := sup_le hDQ hKQ
  have hHQ0 : H ≤ Subgroup.normalizer (Q0 : Set G) := sup_le hDQ0 hKQ0
  have : Finite ↥H := inferInstance
  have hHsolv : Group.IsSolvable ↥H := hsolv
  -- conjugation hom of `H = D ⊔ K` on `↥Q`, descended to the chief factor `Q̄ = Q/Q₀`.
  set φ : ↥H →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hHQ) with hφ
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    change (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hHQ0 a.2) (y : G)).mp hy
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  let act : MulDistribMulAction ↥H (↥Q ⧸ Q0.subgroupOf Q) :=
    MulDistribMulAction.compHom _ (quotientMulAutHom hMinv)
  have hcomm : IsMulCommutative (↥Q ⧸ Q0.subgroupOf Q) :=
    (isMulCommutative_iff).mpr (fun a b => hEA.comm a b)
  let : CommGroup (↥Q ⧸ Q0.subgroupOf Q) := inferInstance
  let : Module (ZMod q) (Additive (↥Q ⧸ Q0.subgroupOf Q)) := hEA.zmodModule
  -- the conjugation-fixed-class characterization: `a • [x] = [x] ↔ ⁅a, x⁆ ∈ Q₀`.
  have hsmul_iff : ∀ (a : ↥H) (x : ↥Q),
      ((a • (QuotientGroup.mk x : ↥Q ⧸ Q0.subgroupOf Q)) = QuotientGroup.mk x)
        ↔ ⁅(a : G), (x : G)⁆ ∈ Q0 := by
    intro a x
    change (quotientMulAutHom hMinv a (QuotientGroup.mk' (Q0.subgroupOf Q) x)
        = QuotientGroup.mk' (Q0.subgroupOf Q) x) ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G) ∈ Q0 ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    have hxN : (x : G) ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 x.2
    have heq : ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G)
        = (x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    have htransfer : ((x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ ∈ Q0)
        ↔ ⁅(a : G), (x : G)⁆⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
        (⁅(a : G), (x : G)⁆⁻¹)).symm
    rw [htransfer, Subgroup.inv_mem_iff]
  -- **BG Theorem 3.10(b)** applied to `Q̄`, kernel `K_thm = D̄`, complement `R_thm = K̄`.
  have hRne : K.subgroupOf H ≠ ⊥ := hfrob.ne_bot_complement
  have hKnormal : (D.subgroupOf H).Normal := hfrob.isNormal
  have hKne : D.subgroupOf H ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hDH]; exact hDne
  -- `q ∣ |Q|`, hence `¬ q ∣ |H|` by coprimality.
  have hqdvdQ : q ∣ Nat.card ↥Q := by
    have h1 : q ∣ (Q0.subgroupOf Q).index := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp hEA.isPGroup
      have : (Q0.subgroupOf Q).index = Nat.card (↥Q ⧸ Q0.subgroupOf Q) := rfl
      rw [this, hn]
      rcases n with _ | n
      · simp only [pow_zero] at hn
        exact absurd hn (Finite.one_lt_card_iff_nontrivial.mpr hNT).ne'
      · exact dvd_pow_self q (Nat.succ_ne_zero n)
    exact h1.trans (Subgroup.index_dvd_card (Q0.subgroupOf Q))
  have hpH : ¬ q ∣ Nat.card ↥H := by
    intro hqH
    exact (Fact.out : q.Prime).one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hqH hqdvdQ)
  -- module-level `hCK`, `hFrob`, `hcond3`.
  have hCK : ∀ m : ↥Q ⧸ Q0.subgroupOf Q,
      (∀ k : ↥(D.subgroupOf H), ((k : ↥H) • m = m)) → m = 1 := by
    intro m hm
    induction m using QuotientGroup.induction_on with
    | _ x =>
      have hd : ∀ d ∈ D, ⁅d, (x : G)⁆ ∈ Q0 := by
        intro d hdD
        have hdsub : (⟨d, hDH hdD⟩ : ↥H) ∈ D.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hdD
        exact (hsmul_iff ⟨d, hDH hdD⟩ x).mp (hm ⟨⟨d, hDH hdD⟩, hdsub⟩)
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hFPF (x : G) x.2 hd
  have hFrob : ∀ r ∈ K.subgroupOf H, r ≠ 1 → ∀ k ∈ D.subgroupOf H, k ≠ 1 →
      r * k * r⁻¹ ≠ k := hfrob.conj_frobenius
  have hcond3' : ∀ x : ↥H, x ∈ K.subgroupOf H → x ≠ 1 →
      ∀ m : ↥Q ⧸ Q0.subgroupOf Q,
        ((x : ↥H) • m = m) ↔ (∀ s : ↥(K.subgroupOf H), (s : ↥H) • m = m) := by
    intro x hxK hx1 m
    induction m using QuotientGroup.induction_on with
    | _ y =>
      have hxG : (x : G) ∈ K := (Subgroup.mem_subgroupOf).mp hxK
      have hxG1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
      rw [hsmul_iff x y]
      rw [hcond3 (x : G) hxG hxG1 (y : G) y.2]
      constructor
      · intro h s
        have hsG : (s : G) ∈ K := (Subgroup.mem_subgroupOf).mp s.2
        exact (hsmul_iff (s : ↥H) y).mpr (h (s : G) hsG)
      · intro h s hsK
        have hsHmem : (⟨s, hKH hsK⟩ : ↥H) ∈ K.subgroupOf H := (Subgroup.mem_subgroupOf).mpr hsK
        exact (hsmul_iff ⟨s, hKH hsK⟩ y).mp (h ⟨⟨s, hKH hsK⟩, hsHmem⟩)
  have hmain := OddOrder.BG.Ch1.S03.card_eq_pow_card_invariants_of_elemAbelian_general
    (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q)
    (K := D.subgroupOf H) (R := K.subgroupOf H) hRne hKne hpH
    (by
      have := (hfrob.coprime_card_kernel_complement)
      rwa [Nat.coprime_comm] at this)
    hCK hFrob hcond3'
  have hcardK : Nat.card ↥(K.subgroupOf H) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  -- **BG Theorem 3.10(a)**: `|K| = |K̄|` is prime (the same Frobenius/module data).
  obtain ⟨pK, hpK_prime, hpK_eq, _⟩ :=
    OddOrder.BG.Ch1.S03.prime_card_and_finrank_of_elemAbelian_general
      (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q)
      (K := D.subgroupOf H) (R := K.subgroupOf H) hRne hKne hpH
      (by
        have := (hfrob.coprime_card_kernel_complement)
        rwa [Nat.coprime_comm] at this)
      hCK hFrob hcond3'
  have hKprime : (Nat.card ↥K).Prime := by rw [← hcardK, hpK_eq]; exact hpK_prime
  -- `g : ↥C →* Q̄`, the natural map `c ↦ [c]`; its range is the image of `C`, of order `[C:Q₀]=q`.
  set g : ↥C →* (↥Q ⧸ Q0.subgroupOf Q) :=
    (QuotientGroup.mk' (Q0.subgroupOf Q)).comp (Subgroup.inclusion hCQ) with hg
  have hg_mem : ∀ x : ↥Q,
      (QuotientGroup.mk x : ↥Q ⧸ Q0.subgroupOf Q) ∈ g.range ↔ (x : G) ∈ C := by
    intro x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨c, hc⟩
      rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hc
      have h1 : ((c : G)⁻¹ * (x : G)) ∈ Q0 := hc
      have hx' : (x : G) = (c : G) * ((c : G)⁻¹ * (x : G)) := by group
      rw [hx']; exact C.mul_mem c.2 (hQ0C h1)
    · intro hxC
      refine ⟨⟨(x : G), hxC⟩, ?_⟩
      rw [hg, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      change ((x : G))⁻¹ * (x : G) ∈ Q0
      rw [inv_mul_cancel]; exact Q0.one_mem
  -- the `K`-fixed classes of `Q̄` are exactly `g.range` (the image of `C`), via
  -- `hsmul_iff`+`hCfix`.
  have hchar : ∀ w : ↥Q ⧸ Q0.subgroupOf Q,
      (∀ r : ↥(K.subgroupOf H), (r : ↥H) • w = w) ↔ w ∈ g.range := by
    intro w
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective w
    rw [← hx, hg_mem x, ← hCfix (x : G) x.2]
    constructor
    · intro h k hkK
      exact (hsmul_iff ⟨k, hKH hkK⟩ x).mp (h ⟨⟨k, hKH hkK⟩, (Subgroup.mem_subgroupOf).mpr hkK⟩)
    · intro h r
      exact (hsmul_iff (r : ↥H) x).mpr (h _ ((Subgroup.mem_subgroupOf).mp r.2))
  -- `ker g = Q₀.subgroupOf C`, so `|g.range| = [C : Q₀] = q` (first isomorphism theorem).
  have hker : g.ker = Q0.subgroupOf C := by
    ext c
    simp only [hg, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
  have hinvq : Nat.card ↥(g.range) = q := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv, hker,
      ← Subgroup.index_eq_card]
    exact hCcard
  refine ⟨hKprime, ?_, ?_⟩
  · -- **(f)**: `[Q : Q₀] = q^{|K|}` (Thm 3.10(b), with `|C_{Q̄}(K)| = |g.range| = q`).
    rw [show (Q0.subgroupOf Q).index = Nat.card (↥Q ⧸ Q0.subgroupOf Q) from rfl, hmain, hcardK]
    congr 1
    rw [card_invariants_eq_card_of_fixedPoints g.range hchar]; exact hinvq
  · -- **(g)**: `D' ⊆ C_D(Q̄)`, i.e. `∀ g ∈ ⁅D,D⁆, ∀ x ∈ Q, ⁅g,x⁆ ∈ Q₀` (Thm 3.10(c)).
    -- `hcyc` (C_{Q̄}(K) cyclic) holds since `|C_{Q̄}(K)| = q` (`finrank_le_one_of_card_eq`).
    have hcomm := OddOrder.BG.Ch1.S03.commutator_acts_trivially_of_elemAbelian_general
      (p := q) (H := ↥H) (M := ↥Q ⧸ Q0.subgroupOf Q) (K := D.subgroupOf H) (R := K.subgroupOf H)
      hfrob hRne hKne hpH hCK hcond3'
      (by apply finrank_le_one_of_card_eq
          rw [card_invariants_eq_card_of_fixedPoints g.range hchar]; exact hinvq)
    intro g0 hg0 x hxQ
    -- lift `g0 ∈ ⁅D,D⁆` to `⁅D̄,D̄⁆ ≤ ↥H`, apply `hcomm`, and read off via `hsmul_iff`.
    have hmapeq : (⁅D.subgroupOf H, D.subgroupOf H⁆ : Subgroup ↥H).map H.subtype = ⁅D, D⁆ := by
      rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hDH]
    rw [← hmapeq] at hg0
    obtain ⟨gbar, hgbarmem, hgbareq⟩ := Subgroup.mem_map.mp hg0
    have hbrk := (hsmul_iff gbar ⟨x, hxQ⟩).mp (hcomm gbar hgbarmem (QuotientGroup.mk ⟨x, hxQ⟩))
    have hg0eq : ((gbar : ↥H) : G) = g0 := hgbareq
    rw [← hg0eq]; exact hbrk

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
open scoped commutatorElement in
/-- **`C_{Q̄}(K)` is the image of `K* ⊔ Q₀`** (BG Proposition 1.5(d), the `hCfix` core of Theorem
15.2(f)).  For a coprime `K`-action on the `q`-group `Q` (with `Q ≤ M_σ`, `K* = C_{M_σ}(K)`,
`K* ≤ Q`, `Q₀ ⊴` normalized by `K` and `Q`), a class `[x]` of `Q̄ = Q/Q₀` is `K`-fixed iff its
representative lies in `K* ⊔ Q₀`:
`(∀ k ∈ K, ⁅k, x⁆ ∈ Q₀) ↔ x ∈ K* ⊔ Q₀`.

Proof: `C_{↥Q}(K)` pushes forward to `C_G(K) ⊓ Q = M_σ ⊓ C_G(K) = K*`
(`fixedPointsOfMulAut_conj_map_subtype`); Proposition 1.5(d)
(`fixedPointsOfMulAut_quotientMulAutHom_eq_map`) gives `C_{Q̄}(K) = (C_{↥Q}(K))·Q₀/Q₀`, whose
preimage in `Q` is `C_{↥Q}(K) ⊔ (Q₀ ↾ Q)`, mapping to `K* ⊔ Q₀` in `G`.

Used both by `card_centralizer_quotient_eq_of_kstar` (its `hCfix` half) and by
`actsPrimeManner_quotient_of_inputs` (applying it to `K` and to each `⟨x⟩`, `x ∈ K#`, whose `K*`
coincides by the prime-manner action) to discharge the chief-factor engine's `hcond3`. -/
theorem centralizes_quotient_iff_mem_kstar_sup [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hQ0Q : Q0 ≤ Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : Group.IsSolvable ↥K ∨ Group.IsSolvable ↥Q) :
    ∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ Kstar ⊔ Q0) := by
  classical
  set φ : ↥K →* MulAut ↥Q :=
    (Subgroup.normalizerMonoidHom Q).comp (Subgroup.inclusion hKQ) with hφ
  have hfixmap : (Subgroup.fixedPointsOfMulAut φ).map Q.subtype = Kstar := by
    rw [OddOrder.BG.Ch1.S06.fixedPointsOfMulAut_conj_map_subtype hKQ]
    apply le_antisymm
    · rw [hKstar]; exact le_inf (inf_le_right.trans hQMσ) inf_le_left
    · rw [hKstar] at hKstarQ ⊢; exact le_inf inf_le_right hKstarQ
  have hMinv : OddOrder.Isaacs.Ch03.IsAInvariant φ (Q0.subgroupOf Q) := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a y hy
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    change (a : G) * (y : G) * (a : G)⁻¹ ∈ Q0
    exact (Subgroup.mem_normalizer_iff.mp (hKQ0 a.2) (y : G)).mp hy
  have hsmul_iff : ∀ (a : ↥K) (x : ↥Q),
      ((quotientMulAutHom hMinv a (QuotientGroup.mk' (Q0.subgroupOf Q) x)
          = QuotientGroup.mk' (Q0.subgroupOf Q) x)) ↔ ⁅(a : G), (x : G)⁆ ∈ Q0 := by
    intro a x
    rw [quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    change ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G) ∈ Q0 ↔ ⁅(a : G), (x : G)⁆ ∈ Q0
    have hxN : (x : G) ∈ Subgroup.normalizer (Q0 : Set G) := hQQ0 x.2
    have heq : ((a : G) * (x : G) * (a : G)⁻¹)⁻¹ * (x : G)
        = (x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ := by
      rw [commutatorElement_def]; group
    rw [heq]
    have htransfer : ((x : G)⁻¹ * ⁅(a : G), (x : G)⁆⁻¹ * ((x : G)⁻¹)⁻¹ ∈ Q0)
        ↔ ⁅(a : G), (x : G)⁆⁻¹ ∈ Q0 :=
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem hxN)
        (⁅(a : G), (x : G)⁆⁻¹)).symm
    rw [htransfer, Subgroup.inv_mem_iff]
  have hmap := OddOrder.BG.Ch1.S03h.fixedPointsOfMulAut_quotientMulAutHom_eq_map
    (φ := φ) hcop hSolv hMinv
  have hpreimage : (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype
      = Kstar ⊔ Q0 := by
    rw [Subgroup.map_sup, hfixmap, Subgroup.map_subgroupOf_eq_of_le hQ0Q]
  intro x hxQ
  have hcomapeq : (Subgroup.fixedPointsOfMulAut (quotientMulAutHom hMinv)).comap
        (QuotientGroup.mk' (Q0.subgroupOf Q))
      = Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q := by
    rw [hmap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hkey : (∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ (⟨x, hxQ⟩ : ↥Q) ∈
      (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q) := by
    rw [← hcomapeq, Subgroup.mem_comap, Subgroup.mem_fixedPointsOfMulAut]
    constructor
    · intro h r
      rcases r with ⟨k, hk⟩
      exact (hsmul_iff ⟨k, hk⟩ ⟨x, hxQ⟩).mpr (h k hk)
    · intro h k hk
      exact (hsmul_iff ⟨k, hk⟩ ⟨x, hxQ⟩).mp (h ⟨k, hk⟩)
  rw [hkey]
  constructor
  · intro hx
    have : x ∈ (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype :=
      ⟨⟨x, hxQ⟩, hx, rfl⟩
    rwa [hpreimage] at this
  · intro hx
    have hx' : x ∈ (Subgroup.fixedPointsOfMulAut φ ⊔ Q0.subgroupOf Q).map Q.subtype := by
      rwa [hpreimage]
    obtain ⟨z, hz, hzeq⟩ := hx'
    have : z = ⟨x, hxQ⟩ := Subtype.ext hzeq
    rwa [this] at hz

/-- **Theorem 15.2(f) — the chief-factor `C`-interface `|C_{Q̄}(K)| = q`, gated producer** (mmd
L4196, BG Theorem 14.7(f)).  Discharges the `hCfix`/`hCcard` hypotheses of
`chiefFactor_card_and_commutator_of_inputs` by exhibiting the subgroup `C = K* ⊔ Q₀` of `Q` whose
image in `Q̄ = Q/Q₀` is the `K`-fixed-class subgroup `C_{Q̄}(K)`, and showing `[C : Q₀] = q`.

In the type-`P₁` situation `K* = C_{M_σ}(K) = M_σ ⊓ C_G(K)` (`hKstar`) with `|K*| = q` prime
(`hKstar_prime`), `K* ≤ Q ≤ M_σ` (`hKstarQ`, `hQMσ`), and `K* ⊄ Q₀` (`hKstarQ0`, an output of
`kstar_le_Q1_of_inputs`).  The argument (verified):

* **`C_Q(K) = K*`**: the conjugation-fixed points of `K` on `↥Q` push forward to `C_G(K) ⊓ Q`
  (`fixedPointsOfMulAut_conj_map_subtype`), and `C_G(K) ⊓ Q = M_σ ⊓ C_G(K) = K*` since `Q ≤ M_σ`
  and `K* ≤ Q`.
* **`C_{Q̄}(K)` is the image of `K*·Q₀`** (BG Proposition 1.5(d), coprime `K`-action, `hcop`):
  `C_{Q̄}(K) = (C_{↥Q}(K))·Q₀/Q₀` via `fixedPointsOfMulAut_quotientMulAutHom_eq_map`, so the
  `K`-fixed-class preimage in `Q` is `C_{↥Q}(K) ⊔ (Q₀ ↾ Q) = (K* ⊔ Q₀) ↾ Q` (`comap_map_eq`).
  This gives the membership iff `hCfix`.
* **`K* ⊓ Q₀ = ⊥`**: since `|K*| = q` is prime, `Q₀ ↾ K*` is `⊥` or `⊤`
  (`eq_bot_or_eq_top_of_prime_card`); `⊤` would force `K* ≤ Q₀`, against `hKstarQ0`.  Hence
  `|K* ⊔ Q₀| = |K*|·|Q₀|` (`card_sup_eq_mul_of_le_normalizer_of_disjoint`), so
  `[K* ⊔ Q₀ : Q₀] = |K*| = q` (`hCcard`).

The §14-gated input is `hKstar_prime` (`|K*| = q`, Theorem 14.7(f)); the normalizer/coprimality
data are structural.  Removes `hCfix`/`hCcard` from being unproduced named hypotheses of the engine:
the wrapper instantiates the engine with `C := K* ⊔ Q₀` and these two facts. -/
theorem card_centralizer_quotient_eq_of_kstar [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} {q : ℕ} [Fact q.Prime] [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hKstar_prime : Nat.card ↥Kstar = q)
    (hQ0Q : Q0 ≤ Q) (hKstarQ0 : ¬ Kstar ≤ Q0)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hKstarQ0norm : Kstar ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : Group.IsSolvable ↥K ∨ Group.IsSolvable ↥Q) :
    ∃ C : Subgroup G, Q0 ≤ C ∧ C ≤ Q ∧
      (∀ x ∈ Q, ((∀ k ∈ K, ⁅k, x⁆ ∈ Q0) ↔ x ∈ C)) ∧
      (Q0.subgroupOf C).index = q := by
  classical
  refine ⟨Kstar ⊔ Q0, le_sup_right, sup_le hKstarQ hQ0Q,
    centralizes_quotient_iff_mem_kstar_sup hKstar hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0 hcop hSolv, ?_⟩
  · -- `hCcard`: `[K* ⊔ Q₀ : Q₀] = |K*| = q` via `|K* ⊔ Q₀| = |K*|·|Q₀|` and `card_mul_index`.
    have hprime : Fact (Nat.card ↥Kstar).Prime := ⟨hKstar_prime ▸ Fact.out⟩
    -- `K* ⊓ Q₀ = ⊥`: `Q₀ ↾ K*` is `⊥` or `⊤`; `⊤` forces `K* ≤ Q₀`, against `hKstarQ0`.
    have hdisj : Kstar ⊓ Q0 = ⊥ := by
      rcases (Q0.subgroupOf Kstar).eq_bot_or_eq_top_of_prime_card with hbot | htop
      · have : Disjoint Q0 Kstar := Subgroup.subgroupOf_eq_bot.mp hbot
        rw [disjoint_iff, inf_comm] at this; exact this
      · exact absurd (Subgroup.subgroupOf_eq_top.mp htop) hKstarQ0
    have hKstarN : Kstar ≤ Subgroup.normalizer (Q0 : Set G) := hKstarQ0norm
    -- `|K* ⊔ Q₀| = |K*|·|Q₀|`.
    have hcard_sup : Nat.card ↥(Kstar ⊔ Q0) = Nat.card ↥Kstar * Nat.card ↥Q0 :=
      card_sup_eq_mul_of_le_normalizer_of_disjoint hKstarN hdisj
    -- `|Q₀ ↾ (K* ⊔ Q₀)| = |Q₀|` and `card · index = |K* ⊔ Q₀|`.
    have hcardQ0sub : Nat.card ↥(Q0.subgroupOf (Kstar ⊔ Q0)) = Nat.card ↥Q0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : Q0 ≤ Kstar ⊔ Q0)).toEquiv
    have hmul := Subgroup.card_mul_index (Q0.subgroupOf (Kstar ⊔ Q0))
    rw [hcardQ0sub, hcard_sup, hKstar_prime, mul_comm q (Nat.card ↥Q0)] at hmul
    -- `hmul : |Q₀| * index = |Q₀| * q`; cancel `|Q₀| > 0`.
    have hQ0pos : 0 < Nat.card ↥Q0 := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hQ0pos hmul

open scoped commutatorElement in
/-- **Theorem 15.2(f) — `K` acts in a prime manner on the chief factor `Q̄ = Q/Q₀`** (mmd L4196,
the chief-factor engine's `hcond3`).  For a coprime `K`-action on the `q`-group `Q` with the
prime-manner action `C_{M_σ}(x) = K*` (∀ `x ∈ K#`, Proposition 14.2(a), `hprime`), every nontrivial
`x ∈ K` and `y ∈ Q` satisfy
`⁅x, y⁆ ∈ Q₀ ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q₀` (i.e. `C_{Q̄}(x) = C_{Q̄}(K)`).

Proof: both `C_{Q̄}(x)` and `C_{Q̄}(K)` equal the image of `K* ⊔ Q₀`
(`centralizes_quotient_iff_mem_kstar_sup`, applied to `K` and to `⟨x⟩`, whose
`K* = M_σ ⊓ C_G(⟨x⟩) = M_σ ⊓ C_G(x)` coincides by the prime-manner action).  The bridge
`⁅x, y⁆ ∈ Q₀ → ∀ k ∈ ⟨x⟩, ⁅k, y⁆ ∈ Q₀` uses that `{g ∈ N_G(Q₀) | ⁅g, y⁆ ∈ Q₀}` is a subgroup
containing `x` (the standard `⁅g g', y⁆ = g ⁅g', y⁆ g⁻¹ · ⁅g, y⁆` closure), hence `⟨x⟩`.

Discharges the `hcond3` named hypothesis of `chiefFactor_card_and_commutator_of_inputs` — the only
one of its inputs without a producer. -/
theorem actsPrimeManner_quotient_of_inputs [Finite G]
    {Q Q0 K Kstar Mσ : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hKstar : Kstar = Mσ ⊓ Subgroup.centralizer (K : Set G))
    (hprime : ∀ x ∈ K, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ⊓ Mσ = Kstar)
    (hQMσ : Q ≤ Mσ) (hKstarQ : Kstar ≤ Q) (hQ0Q : Q0 ≤ Q)
    (hKQ : K ≤ Subgroup.normalizer (Q : Set G))
    (hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G))
    (hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q))
    (hSolv : Group.IsSolvable ↥K ∨ Group.IsSolvable ↥Q) :
    ∀ x ∈ K, x ≠ 1 → ∀ y ∈ Q, (⁅x, y⁆ ∈ Q0 ↔ ∀ s ∈ K, ⁅s, y⁆ ∈ Q0) := by
  classical
  have hCfixK := centralizes_quotient_iff_mem_kstar_sup hKstar hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0
    hcop hSolv
  intro x hxK hx1 y hyQ
  have hxN0 : x ∈ Subgroup.normalizer (Q0 : Set G) := hKQ0 hxK
  have hxzK : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
  -- `C_G(⟨x⟩) = C_G(x)`, so the `⟨x⟩`-version's `K*` is the same `Kstar`.
  have hcentEq : Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
    apply le_antisymm
    · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers x))
    · intro g hg
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact (Commute.zpow_left (hg x (Set.mem_singleton x)) n)
  have hKstarX : Kstar = Mσ ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [hcentEq, inf_comm]; exact (hprime x hxK hx1).symm
  have : Group.IsSolvable ↥(Subgroup.zpowers x) := inferInstance
  have hCfixX := centralizes_quotient_iff_mem_kstar_sup hKstarX hQMσ hKstarQ hQ0Q
    (hxzK.trans hKQ) hQQ0 (hxzK.trans hKQ0)
    (hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hxzK)) (Or.inl inferInstance)
  refine ⟨fun hxy => (hCfixK y hyQ).mpr ((hCfixX y hyQ).mp ?_), fun h => h x hxK⟩
  -- bridge: `{g ∈ N_G(Q₀) | ⁅g, y⁆ ∈ Q₀}` is a subgroup containing `x`, hence `⟨x⟩`.
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (Q0 : Set G) ∧ ⁅g, y⁆ ∈ Q0}
      one_mem' := ⟨(Subgroup.normalizer (Q0 : Set G)).one_mem, by
        rw [commutatorElement_one_left]; exact Q0.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨(Subgroup.normalizer (Q0 : Set G)).mul_mem ha.1 hb.1, by
        have heq : ⁅a * b, y⁆ = (a * ⁅b, y⁆ * a⁻¹) * ⁅a, y⁆ := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact Q0.mul_mem ((Subgroup.mem_normalizer_iff.mp ha.1 ⁅b, y⁆).mp hb.2) ha.2⟩
      inv_mem' := fun {a} ha => ⟨(Subgroup.normalizer (Q0 : Set G)).inv_mem ha.1, by
        have heq : ⁅a⁻¹, y⁆ = a⁻¹ * ⁅a, y⁆⁻¹ * (a⁻¹)⁻¹ := by
          rw [commutatorElement_def, commutatorElement_def]; group
        rw [heq]
        exact (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (Q0 : Set G)).inv_mem ha.1)
          ⁅a, y⁆⁻¹).mp (Q0.inv_mem ha.2)⟩ }
  have hxT : x ∈ T := ⟨hxN0, hxy⟩
  exact fun k hk => ((Subgroup.zpowers_le.mpr hxT) hk).2

/-- **§14-independent `⊆`-half of Theorem 15.2(g)** (mmd L4198, the easy inclusion of
`F(M) = Q ⊔ (C_G(Q) ⊓ M)`): the nilpotent `F(M)` splits as `O_π(F(M)) ⊔ O_{π'}(F(M))`
(`opiCoreInG_sup_compl_eq_of_isNilpotent`), and the `π'`-part centralizes the `π`-part
(`opiCoreInG_commutator_compl_eq_bot`) while lying in `M`, so
`F(M) ≤ O_π(F(M)) ⊔ (C_G(O_π(F(M))) ⊓ M)`.  Instantiated at `π = {q}` (with `O_q(F(M)) = Q`) this
is the easy inclusion of conjunct (g); the reverse `Q ⊔ (C_G(Q) ⊓ M) ≤ F(M)` is the
situation-specific `C_M(Q) ⊆ F(M)` (`D` nilpotent, `M_σ` not), deferred to the step-4 core. -/
theorem fittingInAmbient_le_opiCore_sup_centralizer_inf [Finite G] {M : Subgroup G} (π : Set ℕ) :
    fittingInAmbient M ≤ opiCoreInG π (fittingInAmbient M) ⊔
      (Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) ⊓ M) := by
  have : Group.IsNilpotent ↥(fittingInAmbient M) := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  have hsplit : opiCoreInG π (fittingInAmbient M) ⊔ opiCoreInG πᶜ (fittingInAmbient M) =
      fittingInAmbient M := opiCoreInG_sup_compl_eq_of_isNilpotent π
  have hcomm : ⁅opiCoreInG π (fittingInAmbient M), opiCoreInG πᶜ (fittingInAmbient M)⁆ = ⊥ :=
    OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot π (fittingInAmbient M)
  have hcent : opiCoreInG πᶜ (fittingInAmbient M) ≤
      Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) := by
    have hcomm' : ⁅opiCoreInG πᶜ (fittingInAmbient M), opiCoreInG π (fittingInAmbient M)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]; exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  have hleM : opiCoreInG πᶜ (fittingInAmbient M) ≤ M :=
    (OddOrder.GroupTheory.opiCoreInG_le πᶜ (fittingInAmbient M)).trans
      (OddOrder.BG.Ch2.S08.fittingInG_le M)
  calc fittingInAmbient M
      = opiCoreInG π (fittingInAmbient M) ⊔ opiCoreInG πᶜ (fittingInAmbient M) := hsplit.symm
    _ ≤ opiCoreInG π (fittingInAmbient M) ⊔
          (Subgroup.centralizer ((opiCoreInG π (fittingInAmbient M) : Subgroup G) : Set G) ⊓ M) :=
        sup_le_sup_left (le_inf hcent hleM) _

/-- **`O_q(F(M)) = O_q(M)`** (`§14`-independent, reusable): the `q`-core of the Fitting subgroup
equals the `q`-core of `M`.  `O_q(M) ≤ F(M)` (`opiCoreInG_singleton_le_fittingInG`) is normal in
`F(M)` (it is normal in `M ⊇ F(M)`) and a `q`-group, so `O_q(M) ≤ O_q(F(M))`; conversely
`O_q(F(M))` is normal in `M` (`M` normalizes `F(M)`, hence its `q`-core) and a `q`-subgroup of `M`,
so `O_q(F(M)) ≤ O_q(M)`.  Bridges `fittingInAmbient_le_opiCore_sup_centralizer_inf` (phrased with
`O_q(F(M))`) to Theorem 15.2's `Q = O_q(M)`. -/
theorem opiCore_singleton_fittingInAmbient_eq [Finite G] {M : Subgroup G} {q : ℕ} [Fact q.Prime] :
    opiCoreInG ({q} : Set ℕ) (fittingInAmbient M) = opiCoreInG ({q} : Set ℕ) M := by
  refine le_antisymm ?_ ?_
  · -- `O_q(F(M)) ≤ O_q(M)`: normal in `M` (char in `F(M) ◁ M`), a `q`-subgroup of `M`.
    have hle : opiCoreInG ({q} : Set ℕ) (fittingInAmbient M) ≤ M :=
      (OddOrder.GroupTheory.opiCoreInG_le _ _).trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
    have hMnorm : M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) (fittingInAmbient M)) :=
      OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer _
        (fun x hx => OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem hx)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hMnorm)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _)
  · -- `O_q(M) ≤ O_q(F(M))`: `≤ F(M)`, normal in `F(M)`, a `q`-subgroup.
    have hle : opiCoreInG ({q} : Set ℕ) M ≤ fittingInAmbient M :=
      OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG M
    have hFnorm : fittingInAmbient M ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ) M) :=
      (OddOrder.BG.Ch2.S08.fittingInG_le M).trans
        (OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer _ Subgroup.le_normalizer)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hle
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr hFnorm)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _)

/-- **Theorem 15.2(g), `⊆`-conjunct in the `Q = O_q(M)` form** (`§14`-independent): combines the
`O_π` decomposition (`fittingInAmbient_le_opiCore_sup_centralizer_inf` at `π = {q}`) with the bridge
`O_q(F(M)) = O_q(M)` (`opiCore_singleton_fittingInAmbient_eq`), giving the wrapper-ready inclusion
`F(M) ≤ Q ⊔ (C_G(Q) ⊓ M)` for the theorem's `Q = O_q(M)`.  The reverse inclusion `C_M(Q) ⊆ F(M)`
(the situation-specific step-4 core) completes the equality. -/
theorem fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore [Finite G] {M Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hQ : Q = opiCoreInG ({q} : Set ℕ) M) :
    fittingInAmbient M ≤ Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) := by
  subst hQ
  have h := fittingInAmbient_le_opiCore_sup_centralizer_inf (M := M) ({q} : Set ℕ)
  rwa [opiCore_singleton_fittingInAmbient_eq] at h

/-- **Theorem 15.2(g) equality — gated-endpoint skeleton** (`§14`-independent assembly): from the
hard step-4 inclusion `C_M(Q) ⊆ F(M)` (hypothesis `hcent`; the situation-specific content of
"Proposition 1.5(d) yields `F(M) = Q C_M(Q)`", which holds because `D` is nilpotent while `M_σ` is
not) together with the landed `⊆`-half (`fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore`) and
`O_q(M) ⊆ F(M)`, this gives the conjunct-(g) equality `F(M) = Q ⊔ (C_G(Q) ⊓ M)` for `Q = O_q(M)`.
Once the step-4 core discharges `hcent`, the equality becomes unconditional. -/
theorem fittingInAmbient_eq_sup_centralizer_inf_of_inputs [Finite G] {M Q : Subgroup G} {q : ℕ}
    [Fact q.Prime] (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hcent : Subgroup.centralizer (Q : Set G) ⊓ M ≤ fittingInAmbient M) :
    fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) := by
  refine le_antisymm (fittingInAmbient_le_sup_centralizer_inf_of_eq_qcore hQ) (sup_le ?_ hcent)
  rw [hQ]; exact OddOrder.BG.Ch2.S08.opiCoreInG_singleton_le_fittingInG M

/-- **Central-extension nilpotency** (`§14`-independent, reusable): a subgroup `H ≤ K` that
centralizes a normal subgroup `Q ◁ K` is nilpotent whenever the quotient `K/Q` is nilpotent.
`H ∩ Q` lies in the centre of `H` (since `H` centralizes `Q`), and `H/(H ∩ Q)` embeds in the
nilpotent `K/Q`, so `H` is a central extension of a nilpotent group, hence nilpotent
(`Subgroup.isNilpotent_of_ker_le_center` applied to `H → K/Q`).

This is the crux of Theorem 15.2(g)'s reverse inclusion: with `K = M_σ`, `Q = O_q(M)`, and
`H = C_M(Q) ⊆ M_σ`, it shows `C_M(Q)` is nilpotent, hence (being normal in `M`) lands in `F(M)`. -/
theorem isNilpotent_of_centralizes_normal_of_quotient_isNilpotent {Q K H : Subgroup G}
    [(Q.subgroupOf K).Normal] [Group.IsNilpotent (↥K ⧸ Q.subgroupOf K)]
    (hHK : H ≤ K) (hHQ : H ≤ Subgroup.centralizer (Q : Set G)) :
    Group.IsNilpotent ↥H := by
  refine Subgroup.isNilpotent_of_ker_le_center
    ((QuotientGroup.mk' (Q.subgroupOf K)).comp (Subgroup.inclusion hHK)) ?_
  intro x hx
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (Subgroup.mem_centralizer_iff.mp (hHQ y.2) _ hx).symm

/-- **`κ(M)`-subgroup pushed into the `κ`-Hall complement `K`** (§14 Prop 14.2 Hall machinery):
in a maximal subgroup `M` (solvable, BG `IsMinimalSimpleOdd`) with a `κ(M)`-Hall subgroup `K ≤ M`,
any `κ(M)`-subgroup `X ≤ M` is `M`-conjugate into `K`: some `w ∈ M` has `w X w⁻¹ ≤ K`.

Mirrors `exists_conj_smul_le_hallPiece` (which targets the `E`-setup Hall pieces) but targets the
ambient `κ`-Hall `K` directly: `aInvariant_piSubgroup_le_aInvariant_hall` (trivial `Unit`-action)
embeds `X` in some `κ`-Hall subgroup `H` of `↥M`, and `exists_conj_eq_of_isHall_subgroupOf`
conjugates `H` to `K` (both `κ`-Hall of the solvable `M`). -/
theorem exists_conj_smul_le_isHall_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    {X : Subgroup G} (hXM : X ≤ M)
    (hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) (X.subgroupOf M)) :
    ∃ w ∈ M, MulAut.conj w • X ≤ K := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- Embed `X.subgroupOf M` in a `κ`-Hall subgroup `H` of `↥M` (trivial `Unit`-action).
  obtain ⟨H, hH_hall, -, hX_le_H⟩ :=
    OddOrder.BG.Ch1.S01.aInvariant_piSubgroup_le_aInvariant_hall
      (A := Unit) (φ := (1 : Unit →* MulAut ↥M))
      (by rw [Nat.card_unique]; exact Nat.coprime_one_left _)
      hXpi (fun _ => one_smul _ _)
  set HG : Subgroup G := H.map M.subtype with hHGdef
  have hHG_le_M : HG ≤ M := Subgroup.map_subtype_le _
  have hHG_hall : Ch03.IsHallSubgroup (S14.kappa M) (HG.subgroupOf M) := by
    rwa [hHGdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- Conjugate `HG` to `K` (both `κ`-Hall of the solvable `M`).
  obtain ⟨w, hwM, hw⟩ :=
    OddOrder.BG.Ch1.S06.exists_conj_eq_of_isHall_subgroupOf inferInstance hHG_le_M hKM
      hHG_hall hK
  have hXHG : X ≤ HG := by
    intro x hx
    rw [hHGdef]
    exact Subgroup.mem_map.mpr ⟨⟨x, hXM hx⟩, hX_le_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  exact ⟨w, hwM, (conj_smul_mono (MulAut.conj w) hXHG).trans hw.le⟩

/-- **`C_M(Q) ⊆ M_σ` from the prime-manner action** (BG Theorem 15.2, mmd L4196-4198): for a
type-`P₁` maximal subgroup `M = M_σ ⋊ K` with `K` acting in a prime manner on `M_σ`
(BG Prop 14.2(a)), the centralizer `C_M(Q)` of the normal `q`-subgroup `Q ⊴ M` (with `Q ≤ M_σ`,
`K* = C_{M_σ}(K) ⊊ Q`) lies in `M_σ`.

This *corrects an earlier misdiagnosis* (the `M = (C₇⋊C₃)×(C₃₁⋊C₅)` "counterexample" violates the
prime-manner action: there a `κ`-element centralizes all of `M_σ`, so `C_{M_σ}(x) ≠ K*`).  In the
genuine type-`P₁` setting the prime-manner action makes `C_M(Q) ⊆ M_σ` derivable.

Proof: it suffices to show `C := C_M(Q)` is a `σ(M)`-group (then
`sigma_subgroup_le_Msigma_of_isHall` gives `C ⊆ M_σ`).  Suppose a prime `r ∣ |C|` with
`r ∉ σ(M)`.  As `M` is type-`P₁`,
`κ(M) = π(M) ∖ σ(M)`, so `r ∈ κ(M)`; Cauchy gives a `κ`-element `c ∈ C` of order `r`.  By the Hall
machinery (`exists_conj_smul_le_isHall_kappa`) some `w ∈ M` conjugates `⟨c⟩` into `K`: `cʷ ∈ K`,
`cʷ ≠ 1`.  Since `Q ⊴ M` (`M ≤ N_G(Q)`) and `c` centralizes `Q`, `cʷ` centralizes `Qʷ = Q`, so
`Q ≤ C_{M_σ}(cʷ) = K*` (prime manner).  With `K* ≤ Q` this forces `Q = K*`, against `K* ≠ Q`.
Hence no such `r`, i.e. `C` is a `σ`-group. -/
theorem centralizer_le_Msigma_of_primeManner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Q Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hKM : K ≤ M) (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hprime : ∀ x ∈ K, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hKstarneQ : Kstar ≠ Q) :
    Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  set C : Subgroup G := Subgroup.centralizer (Q : Set G) ⊓ M with hCdef
  -- It suffices to show `C` is a `σ(M)`-group.
  refine OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) inf_le_right ?_
  -- `C` is a `σ(M)`-group: every prime `r ∣ |C|` lies in `σ(M)`.
  intro r hr
  by_contra hrσ
  have hr_prime : r.Prime := (Nat.mem_primeFactors.mp hr).1
  have : Fact r.Prime := ⟨hr_prime⟩
  -- `r ∈ π(M)` (since `r ∣ |C|` and `C ≤ M`), and `r ∉ σ(M)`, so `r ∈ κ(M)` (type-`P₁`).
  have hrπ : r ∈ S14.piSet M := by
    refine Nat.mem_primeFactors.mpr ⟨hr_prime, ?_, Nat.card_pos.ne'⟩
    exact (Nat.mem_primeFactors.mp hr).2.1.trans (Subgroup.card_dvd_of_le inf_le_right)
  have hrκ : r ∈ S14.kappa M := by
    rw [hP1.2]; exact ⟨hrπ, hrσ⟩
  -- A `κ`-element `c ∈ C` of order `r` (Cauchy in `↥C`).
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) r
    ((Nat.mem_primeFactors.mp hr).2.1)
  have hc_ne : (c : G) ≠ 1 := by
    intro hc1
    have h1 : orderOf c = 1 := by
      rw [show c = 1 from Subtype.ext hc1]; exact orderOf_one
    rw [hc_ord] at h1; exact hr_prime.ne_one h1
  -- `X := ⟨c⟩ ≤ M` is a `κ(M)`-group.
  have hcC : (c : G) ∈ C := c.2
  have hcC' : (c : G) ∈ Subgroup.centralizer (Q : Set G) ⊓ M := hCdef ▸ hcC
  have hcM : (c : G) ∈ M := (Subgroup.mem_inf.mp hcC').2
  set X : Subgroup G := Subgroup.zpowers (c : G) with hXdef
  have hXM : X ≤ M := by rw [hXdef]; exact Subgroup.zpowers_le.mpr hcM
  have hord_coe : orderOf (c : G) = r := by rw [Subgroup.orderOf_coe, hc_ord]
  have hXpi : Ch03.Subgroup.IsPiGroup (S14.kappa M) (X.subgroupOf M) := by
    intro s hs
    -- `|X.subgroupOf M| = |X| = orderOf c = r`, so its only prime factor is `r ∈ κ(M)`.
    have hcard : Nat.card ↥(X.subgroupOf M) = r := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv, hXdef,
        Nat.card_zpowers, hord_coe]
    rw [hcard, hr_prime.primeFactors, Finset.mem_singleton] at hs
    rw [hs]; exact hrκ
  -- Conjugate `X` into `K`: `cʷ ∈ K`, `cʷ ≠ 1`.
  obtain ⟨w, hwM, hwle⟩ := exists_conj_smul_le_isHall_kappa hG hM hKM hK hXM hXpi
  set cw : G := w * (c : G) * w⁻¹ with hcwdef
  have hcw_mem_smul : cw ∈ MulAut.conj w • X := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply,
      hcwdef]
    rw [hXdef, show w⁻¹ * (w * (c : G) * w⁻¹) * w = (c : G) by group]
    exact Subgroup.mem_zpowers _
  have hcwK : cw ∈ K := hwle hcw_mem_smul
  have hcw_ne : cw ≠ 1 := by
    intro h
    apply hc_ne
    have hconj : w⁻¹ * cw * w = (c : G) := by rw [hcwdef]; group
    rw [h, mul_one, inv_mul_cancel] at hconj
    exact hconj.symm
  -- `Q ≤ C_{M_σ}(cʷ) = K*`: `cʷ` centralizes `Qʷ = Q`, and `Q ≤ M_σ`.
  have hc_cent : (c : G) ∈ Subgroup.centralizer (Q : Set G) := (Subgroup.mem_inf.mp hcC').1
  have hQcent : Q ≤ Subgroup.centralizer ({cw} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg; subst hg
    -- `w⁻¹ y w ∈ Q` (`Q ⊴ M`, `w ∈ M`), and `c` centralizes it.
    have hwinvN : w⁻¹ ∈ Subgroup.normalizer (Q : Set G) := hMnormQ (M.inv_mem hwM)
    have hwinvyw : w⁻¹ * y * w ∈ Q := by
      have hmem : w⁻¹ * y * (w⁻¹)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp hwinvN y).mp hy
      rwa [inv_inv] at hmem
    have hcyc : (w⁻¹ * y * w) * (c : G) = (c : G) * (w⁻¹ * y * w) :=
      Subgroup.mem_centralizer_iff.mp hc_cent (w⁻¹ * y * w) hwinvyw
    -- Translate back: `cw * y = y * cw`.
    rw [hcwdef]
    calc w * (c : G) * w⁻¹ * y
        = w * ((c : G) * (w⁻¹ * y * w)) * w⁻¹ := by group
      _ = w * ((w⁻¹ * y * w) * (c : G)) * w⁻¹ := by rw [hcyc]
      _ = y * (w * (c : G) * w⁻¹) := by group
  have hQKstar : Q ≤ Kstar := by
    rw [← hprime cw hcwK hcw_ne]
    exact le_inf hQcent hQMσ
  exact hKstarneQ (le_antisymm hKstarQ hQKstar)

end OddOrder.BG.Ch4.S15



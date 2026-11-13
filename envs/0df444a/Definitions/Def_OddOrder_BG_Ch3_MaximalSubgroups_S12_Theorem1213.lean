-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1213
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1213
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:11:46.032989+00:00
-- url     : https://prove2.me/theorems/e048ab87-1d3a-41f7-9461-375c4d4a2ae0
-- title:
--   BG §12: Theorem 12.13, every nonabelian $p$-subgroup of $G$ lies in $\mathcal{U}$
-- statement:
--   Formalizes Theorem 12.13 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, the first uniqueness result on the $\sigma(M)$ side, derived from Proposition 12.4. The proof is by contradiction: a nonabelian $p$-subgroup in two distinct maximal subgroups $M$, $M^*$ forces $p\in\sigma(M)\cap\sigma(M^*)$ and $N_G(P)\subseteq M\cap M^*$ by Corollary 12.10(a)(d), and the Uniqueness Theorem is then used.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1213.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Theorem1213.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem1212c
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S10_BetaRadicalCore
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S01b_Prop116
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03d_Thm34

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- The nilpotent normalizer condition inside a `p`-group `S`: a proper subgroup `X < S` is
strictly contained in `N_G(X) ⊓ S`. (File-local; same statement as the private helper in
`S10_HallStructureCore`, replicated here for the BG 12.13 Sylow reduction.) -/
private theorem lt_inf_normalizer_of_lt_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {X S : Subgroup G} (hXS : X < S) (hS : IsPGroup p ↥S) :
    X < Subgroup.normalizer X ⊓ S := by
  have : Group.IsNilpotent ↥S := hS.isNilpotent
  have hNC : NormalizerCondition ↥S := Group.normalizerCondition_of_isNilpotent (G := ↥S)
  have hsub_lt : X.subgroupOf S < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hXS.ne (le_antisymm hXS.le htop)
  obtain ⟨t, ht_norm, ht_not⟩ := SetLike.exists_of_lt (hNC _ hsub_lt)
  rw [← Subgroup.subgroupOf_normalizer_eq hXS.le, Subgroup.mem_subgroupOf] at ht_norm
  rw [Subgroup.mem_subgroupOf] at ht_not
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hXS.le) (fun heq => ht_not ?_)
  exact heq ▸ Subgroup.mem_inf.mpr ⟨ht_norm, t.2⟩

/-- **BG 12.13 reduction step**: a Sylow `p`-subgroup `P` of a subgroup `K ≤ G`, whose image
`P̄ := P.map K.subtype` has `N_G(P̄) ≤ K`, is (as `P̄`) a Sylow `p`-subgroup of `G`.

Non-`σ` analogue of `S10.isSylow_sylowMap_of_mem_sigma` (same proof): take a Sylow `S ⊇ P̄` of `G`;
if `P̄ < S`, then `N_G(P̄) ⊓ S` is a `p`-subgroup of `K` (by `N_G(P̄) ≤ K`) strictly above `P̄`
(nilpotent normalizer condition in `S`), contradicting that `P` is Sylow in `↥K`. Used to enlarge
the nonabelian `P` to a Sylow `p`-subgroup of `G` inside `M ∩ M⋆`. -/
theorem exists_sylow_eq_map_of_normalizer_le [Finite G] {K : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p ↥K)
    (hN : Subgroup.normalizer (((P : Subgroup ↥K).map K.subtype) : Set G) ≤ K) :
    ∃ S : Sylow p G, (S : Subgroup G) = (P : Subgroup ↥K).map K.subtype := by
  set Pbar : Subgroup G := (P : Subgroup ↥K).map K.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    P.2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective)
  have hPbar_subOf : Pbar.subgroupOf K = (P : Subgroup ↥K) := by
    rw [hPbar, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
  obtain ⟨S, hPS⟩ := hPbar_pg.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : Pbar < (S : Subgroup G) := lt_of_le_of_ne hPS (Ne.symm hne)
  have hgrow : Pbar < Subgroup.normalizer Pbar ⊓ (S : Subgroup G) :=
    lt_inf_normalizer_of_lt_of_isPGroup hlt S.2
  set Y : Subgroup G := Subgroup.normalizer Pbar ⊓ (S : Subgroup G) with hY
  have hYK : Y ≤ K := le_trans inf_le_left hN
  have hYpg : IsPGroup p ↥Y :=
    S.2.of_injective (Subgroup.inclusion inf_le_right) (Subgroup.inclusion_injective _)
  have hPle : (P : Subgroup ↥K) ≤ Y.subgroupOf K :=
    hPbar_subOf ▸ Subgroup.comap_mono (f := K.subtype) hgrow.le
  have hYsubK_pg : IsPGroup p ↥(Y.subgroupOf K) :=
    hYpg.of_equiv (Subgroup.subgroupOfEquivOfLe hYK).symm
  have hYeq : Y.subgroupOf K = (P : Subgroup ↥K) := P.3 hYsubK_pg hPle
  have hYP : Y = Pbar := by
    have := congrArg (Subgroup.map K.subtype) hYeq
    rwa [Subgroup.map_subgroupOf_eq_of_le hYK, ← hPbar] at this
  exact absurd hYP hgrow.ne'

/-- A nonabelian `p`-subgroup `P` contained in two distinct maximal subgroups `M`, `M*` of `G`
satisfies `p ∈ σ(M) ∩ σ(M*)` and `N_G(P) ⊆ M ∩ M*` (Corollary 12.10(a),(d)). The membership
`p ∈ σ(M)` is the contrapositive of 12.10(a): a `σ(M)'`-`p`-subgroup is nilpotent, hence abelian.
The normalizer containment is 12.10(d) (nonabelian `⟹` noncyclic). -/
theorem mem_sigma_normalizer_le_of_two_maximals [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P M : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) (hM : M ∈ maximalSubgroups G) (hPM : P ≤ M) :
    p ∈ S10.sigma M ∧ Subgroup.normalizer (P : Set G) ≤ M := by
  obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := exists_subgroupESetup hG hM
  have : Group.IsNilpotent ↥P := hPp.isNilpotent
  have hcor := nilpotent_sigmaComplement_abelian hG hsetup
  -- `P` is a `σ(M)'`-`p`-subgroup only if `p ∉ σ(M)`; its primes are all `p`.
  have hPpi : p ∉ S10.sigma M → Subgroup.IsPiSubgroup ((S10.sigma M)ᶜ) P := by
    intro hpσ q hq
    obtain ⟨hqp, hqd, _⟩ := Nat.mem_primeFactors.mp hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    rw [hn] at hqd
    have : q = p := (Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp (hqp.dvd_of_dvd_pow hqd)
    rwa [this]
  have hpσM : p ∈ S10.sigma M := by
    by_contra hpσ
    exact hPnab (hcor.1 P hPM (hPpi hpσ) ‹_›)
  refine ⟨hpσM, ?_⟩
  -- `N_G(P) ⊆ M`: 12.10(d), `P` noncyclic.
  refine hcor.2.2.2.1 p hpσM P hPM hPp ?_
  intro hcyc
  have := hcyc
  exact hPnab (IsMulCommutative.of_comm (IsCyclic.commGroup (α := ↥P)).mul_comm)

/-- **Conjugates of a noncentral element cover its central coset** in an exponent-`p` extraspecial
group: for `a₀ ∉ Z(Q)` and any `z ∈ Z(Q)`, there is `q` with `q a₀ q⁻¹ = z · a₀`.

The map `φ : Q → Z(Q)`, `q ↦ ⁅q, a₀⁆`, is a homomorphism (commutators lie in `[Q,Q] = Z(Q)`,
which is central), nontrivial since `a₀ ∉ Z(Q)`, hence surjective onto the order-`p` group `Z(Q)`.
So every `z ∈ Z(Q)` is realized as `⁅q,a₀⁆`, i.e. `q a₀ q⁻¹ = z · a₀`. This is the conjugacy half of
the BG 12.13 Heisenberg line-conjugacy argument. -/
theorem exists_conj_eq_center_mul_of_expPExtraspecial {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsExpPExtraspecial p Q) {a₀ : Q} (ha₀ : a₀ ∉ Subgroup.center Q)
    {z : Q} (hz : z ∈ Subgroup.center Q) :
    ∃ q : Q, q * a₀ * q⁻¹ = z * a₀ := by
  classical
  have hes := hQ.isExtraspecial
  have hZcard : Nat.card (Subgroup.center Q) = p := hes.center_card
  have hZcomm : commutator Q = Subgroup.center Q := hes.commutator_eq_center
  -- (1) `⁅q, a₀⁆ ∈ Z(Q)` for all `q`.
  have hmemZ : ∀ q : Q, ⁅q, a₀⁆ ∈ Subgroup.center Q := fun q => by
    rw [← hZcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top q) (Subgroup.mem_top a₀)
  -- (2) `φ : Q →* Z(Q)`, `q ↦ ⁅q, a₀⁆` (homomorphism by centrality of commutators).
  have hcentral : ∀ z : Q, z ∈ Subgroup.center Q → ∀ w : Q, Commute z w :=
    fun z hz w => (Subgroup.mem_center_iff.mp hz w).symm
  let φ : Q →* Subgroup.center Q := MonoidHom.mk'
    (fun q => ⟨⁅q, a₀⁆, hmemZ q⟩) (fun x y => by
      apply Subtype.ext
      change ⁅x * y, a₀⁆ = ⁅x, a₀⁆ * ⁅y, a₀⁆
      have hc := hcentral ⁅y, a₀⁆ (hmemZ y)
      have e1 : ⁅x * y, a₀⁆ = x * ⁅y, a₀⁆ * x⁻¹ * ⁅x, a₀⁆ := by
        simp only [commutatorElement_def]; group
      have e2 : x * ⁅y, a₀⁆ * x⁻¹ = ⁅y, a₀⁆ := by rw [(hc x).symm.eq]; group
      rw [e1, e2, (hc ⁅x, a₀⁆).eq])
  -- (3) `φ` is surjective: its range is a nontrivial subgroup of the order-`p` group `Z(Q)`.
  have hφsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    have hdvd : Nat.card ↥φ.range ∣ p := hZcard ▸ Subgroup.card_subgroup_dvd_card φ.range
    have hne1 : Nat.card ↥φ.range ≠ 1 := by
      rw [ne_eq, Subgroup.card_eq_one]
      intro hbot
      refine ha₀ (Subgroup.mem_center_iff.mpr fun g => ?_)
      have hg1 : φ g = 1 := by rw [← Subgroup.mem_bot, ← hbot]; exact ⟨g, rfl⟩
      have h2 : ⁅g, a₀⁆ = 1 := Subtype.ext_iff.mp hg1
      exact commutatorElement_eq_one_iff_commute.mp h2
    have hcardr : Nat.card ↥φ.range = p :=
      (Nat.dvd_prime Fact.out).mp hdvd |>.resolve_left hne1
    exact Subgroup.eq_top_of_card_eq _ (by rw [hcardr, hZcard])
  -- (4) realize `z` as `⁅q, a₀⁆`, so `q a₀ q⁻¹ = z · a₀`.
  obtain ⟨q, hq⟩ := hφsurj ⟨z, hz⟩
  refine ⟨q, ?_⟩
  have hqz : ⁅q, a₀⁆ = z := Subtype.ext_iff.mp hq
  rw [commutatorElement_def] at hqz
  exact mul_inv_eq_iff_eq_mul.mp hqz

/-- **Non-central lines through a common rank-2 `A` are `Q`-conjugate** in an exp-`p` extraspecial
group `Q`: if `a ∉ Z(Q)`, `b ∉ Z(Q)`, and `b ∈ ⟨a⟩ ⊔ Z(Q)`, then `⟨b⟩ = q⟨a⟩q⁻¹` for some `q`.

Write `b = aⁱ·z` (`z ∈ Z(Q)`); `aⁱ ∉ Z(Q)` forces `p ∤ i`. Choosing `j := i⁻¹` in the field
`ZMod p` gives `i·j ≡ 1 (mod p)`, so (using `z^p = 1`) `z^{ij} = z`. Then
`exists_conj_eq_center_mul_of_expPExtraspecial` provides `q` with `q a q⁻¹ = zʲ·a`, whence
`q aⁱ q⁻¹ = (zʲa)ⁱ = z·aⁱ = b ∈ q⟨a⟩q⁻¹`; both sides have order `p`, so `⟨b⟩ = q⟨a⟩q⁻¹`.
This is the structural input to BG 12.13's final contradiction: the two lines `A₀, A₀⋆ ∈ ℰ¹(A)−{Z}`
are `Q`-conjugate, contradicting `ℳ(N_G(A₀)) = {M} ≠ {M⋆} = ℳ(N_G(A₀⋆))`. -/
theorem exists_conj_smul_zpowers_eq_of_expPExtraspecial {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (hQ : IsExpPExtraspecial p Q) {a b : Q} (ha : a ∉ Subgroup.center Q)
    (hb : b ∉ Subgroup.center Q) (hmem : b ∈ Subgroup.zpowers a ⊔ Subgroup.center Q) :
    ∃ q : Q, MulAut.conj q • Subgroup.zpowers a = Subgroup.zpowers b := by
  classical
  have hp : p.Prime := Fact.out
  -- `ord a = ord b = p`.
  have ha1 : a ≠ 1 := fun h => ha (h ▸ one_mem _)
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  have horda : orderOf a = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hQ.pow_eq_one a))).resolve_left
      (fun h => ha1 (orderOf_eq_one_iff.mp h))
  have hordb : orderOf b = p :=
    ((Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hQ.pow_eq_one b))).resolve_left
      (fun h => hb1 (orderOf_eq_one_iff.mp h))
  -- `b = aⁱ · z`, `z ∈ Z(Q)`.
  rw [Subgroup.mem_sup_of_normal_right] at hmem
  obtain ⟨y, hy, z, hz, hyz⟩ := hmem
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  -- `aⁱ ∉ Z(Q)`, so `p ∤ i`.
  have haiZ : a ^ i ∉ Subgroup.center Q := fun h => hb (hyz ▸ mul_mem h hz)
  have hpi : ¬ (p : ℤ) ∣ i := fun ⟨m, hm⟩ => haiZ (by
    rw [hm, zpow_mul, zpow_natCast, hQ.pow_eq_one, one_zpow]; exact one_mem _)
  -- `z ^ p = 1` (center has order `p`).
  have hzp : z ^ p = 1 := by
    have h1 : (⟨z, hz⟩ : Subgroup.center Q) ^ Nat.card (Subgroup.center Q) = 1 := pow_card_eq_one'
    rw [hQ.isExtraspecial.center_card] at h1
    have h2 := congrArg (Subgroup.subtype (Subgroup.center Q)) h1
    simpa using h2
  -- choose `j` with `i * j ≡ 1 (mod p)`.
  have : Fact p.Prime := ⟨hp⟩
  have hi0 : (i : ZMod p) ≠ 0 := fun h => hpi ((ZMod.intCast_zmod_eq_zero_iff_dvd i p).mp h)
  set j : ℤ := (((i : ZMod p)⁻¹).val : ℤ) with hjdef
  have hij1 : (p : ℤ) ∣ (i * j - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast [hjdef, ZMod.natCast_val, ZMod.cast_id]
    rw [mul_inv_cancel₀ hi0, sub_self]
  obtain ⟨m, hm⟩ := hij1
  have hijm : i * j = 1 + (p : ℤ) * m := by linarith
  -- `z ^ (i*j) = z`.
  have hzij : z ^ (i * j) = z := by
    rw [hijm, zpow_add, zpow_one, zpow_mul, zpow_natCast, hzp, one_zpow, mul_one]
  -- conjugate `a` to `zʲ·a` and raise to the `i`-th power: `q aⁱ q⁻¹ = b`.
  obtain ⟨q, hq⟩ := exists_conj_eq_center_mul_of_expPExtraspecial hQ ha (zpow_mem hz j)
  have hca : Commute z a := (Subgroup.mem_center_iff.mp hz a).symm
  have hcomm : Commute (z ^ j) a := hca.zpow_left j
  have hconjai : (MulAut.conj q) (a ^ i) = b := by
    rw [map_zpow, MulAut.conj_apply, hq, hcomm.mul_zpow, ← zpow_mul, mul_comm j i, hzij,
      (Subgroup.mem_center_iff.mp hz (a ^ i)).symm]
    exact hyz
  -- `b ∈ q⟨a⟩q⁻¹` and a cardinality count.
  have hbmem : b ∈ MulAut.conj q • Subgroup.zpowers a := by
    rw [mulAut_smul_eq_map]
    exact ⟨a ^ i, zpow_mem (Subgroup.mem_zpowers a) i, hconjai⟩
  have hinj : Function.Injective (MulAut.conj q).toMonoidHom := (MulAut.conj q).injective
  have hcardL : Nat.card (MulAut.conj q • Subgroup.zpowers a : Subgroup Q) = p := by
    have he : Nat.card (MulAut.conj q • Subgroup.zpowers a : Subgroup Q)
        = Nat.card (Subgroup.zpowers a) := by
      rw [mulAut_smul_eq_map]
      exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ hinj).toEquiv).symm
    rw [he, Nat.card_zpowers, horda]
  have hcardR : Nat.card (Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hordb]
  exact ⟨q, (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbmem)
    (le_of_eq (hcardL.trans hcardR.symm))).symm⟩

/-- **`G`-level Heisenberg line-conjugacy** (transport of
`exists_conj_smul_zpowers_eq_of_expPExtraspecial` to subgroups of `G`): for `a, b ∈ Q` (exp-`p`
extraspecial), with `a, b ∉ Z(Q)` and `b ∈ ⟨a⟩ ⊔ Z(Q)`, there is `g ∈ Q` with `g⟨a⟩g⁻¹ = ⟨b⟩`.
Lift `a, b` to `↥Q`, apply the type-level lemma, and transport the conjugacy back along
`Q.subtype`. -/
theorem exists_conj_smul_zpowers_eq_of_expPExtraspecial_le [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ_es : IsExpPExtraspecial p ↥Q) {a b : G} (haQ : a ∈ Q) (hbQ : b ∈ Q)
    (ha : a ∉ (Subgroup.center ↥Q).map Q.subtype) (hb : b ∉ (Subgroup.center ↥Q).map Q.subtype)
    (hmem : b ∈ Subgroup.zpowers a ⊔ (Subgroup.center ↥Q).map Q.subtype) :
    ∃ g ∈ Q, MulAut.conj g • Subgroup.zpowers a = Subgroup.zpowers b := by
  classical
  have hanc : (⟨a, haQ⟩ : ↥Q) ∉ Subgroup.center ↥Q :=
    fun h => ha (Subgroup.mem_map_of_mem Q.subtype h)
  have hbnc : (⟨b, hbQ⟩ : ↥Q) ∉ Subgroup.center ↥Q :=
    fun h => hb (Subgroup.mem_map_of_mem Q.subtype h)
  have hmem' : (⟨b, hbQ⟩ : ↥Q) ∈ Subgroup.zpowers (⟨a, haQ⟩ : ↥Q) ⊔ Subgroup.center ↥Q := by
    rw [← Subgroup.mem_map_iff_mem Q.subtype_injective, Subgroup.map_sup, MonoidHom.map_zpowers]
    exact hmem
  obtain ⟨q, hq⟩ := exists_conj_smul_zpowers_eq_of_expPExtraspecial hQ_es hanc hbnc hmem'
  refine ⟨Q.subtype q, q.2, ?_⟩
  have hmsc : (MulAut.conj q • Subgroup.zpowers (⟨a, haQ⟩ : ↥Q)).map Q.subtype
      = MulAut.conj (Q.subtype q) • (Subgroup.zpowers (⟨a, haQ⟩ : ↥Q)).map Q.subtype := by
    rw [mulAut_smul_eq_map, mulAut_smul_eq_map, Subgroup.map_map, Subgroup.map_map]; congr 1
  have ha_map : (Subgroup.zpowers (⟨a, haQ⟩ : ↥Q)).map Q.subtype = Subgroup.zpowers a := by
    rw [MonoidHom.map_zpowers]; rfl
  have hb_map : (Subgroup.zpowers (⟨b, hbQ⟩ : ↥Q)).map Q.subtype = Subgroup.zpowers b := by
    rw [MonoidHom.map_zpowers]; rfl
  have h2 := congrArg (Subgroup.map Q.subtype) hq
  rw [hmsc, ha_map, hb_map] at h2
  exact h2

/-- **Two non-central lines of a common `A ∈ ℰ²(Q)` are `Q`-conjugate** (subgroup form of the
Heisenberg line-conjugacy, BG 12.13 final step): for `A ∈ ℰ²(Q)` with `Z(Q) ≤ A` and `A₀, A₀⋆`
distinct-from-`Z(Q)` lines of `A`, there is `g ∈ Q` with `g A₀ g⁻¹ = A₀⋆`. Pick generators
`a₀, a₀⋆`; they avoid `Z(Q)` (a line `≠ Z(Q)` meets it trivially), and `A = ⟨a₀⟩ ⊔ Z(Q)` (a
`p`-group
strictly above `Z(Q)` inside the order-`p²` `A`), so `a₀⋆ ∈ ⟨a₀⟩ ⊔ Z(Q)`; apply
`exists_conj_smul_zpowers_eq_of_expPExtraspecial_le`. -/
theorem exists_conj_smul_eq_of_lines_of_expPExtraspecial [Finite G] {p : ℕ} [Fact p.Prime]
    {Q A A₀ A₀star : Subgroup G} (hQ_es : IsExpPExtraspecial p ↥Q)
    (hZA : (Subgroup.center ↥Q).map Q.subtype ≤ A) (hAmem : A ∈ elemAbelianOfRank G p 2)
    (hA_le_Q : A ≤ Q) (hA₀mem : A₀ ∈ elemAbelianOfRank G p 1) (hA₀_le : A₀ ≤ A)
    (hA₀_ne : A₀ ≠ (Subgroup.center ↥Q).map Q.subtype)
    (hA₀star_mem : A₀star ∈ elemAbelianOfRank G p 1) (hA₀star_le : A₀star ≤ A)
    (hA₀star_ne : A₀star ≠ (Subgroup.center ↥Q).map Q.subtype) :
    ∃ g ∈ Q, MulAut.conj g • A₀ = A₀star := by
  classical
  have hpp : p.Prime := Fact.out
  set Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hZdef
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, Subgroup.card_map_of_injective Q.subtype_injective, hQ_es.isExtraspecial.center_card]
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hAmem
  -- generators of the two lines.
  have getgen : ∀ {R : Subgroup G}, Nat.card ↥R = p → ∃ r : G, r ∈ R ∧ Subgroup.zpowers r = R := by
    intro R hR
    have : Nontrivial ↥R := Finite.one_lt_card_iff_nontrivial.mp (by rw [hR]; exact hpp.one_lt)
    obtain ⟨rbar, hrbar⟩ := exists_ne (1 : ↥R)
    exact ⟨rbar, rbar.2, OddOrder.BG.Ch1.S03d.zpowers_eq_of_prime_card (by rw [hR]; exact hpp)
      rbar.2 (fun h => hrbar (Subtype.ext h))⟩
  have hA₀card : Nat.card ↥A₀ = p := by rw [(mem_elemAbelianOfRank.mp hA₀mem).2, pow_one]
  have hA₀starcard : Nat.card ↥A₀star = p := by
    rw [(mem_elemAbelianOfRank.mp hA₀star_mem).2, pow_one]
  obtain ⟨a₀, ha₀A₀, hzpa₀⟩ := getgen hA₀card
  obtain ⟨a₀s, ha₀sA, hzpa₀s⟩ := getgen hA₀starcard
  have ha₀Q : a₀ ∈ Q := hA_le_Q (hA₀_le ha₀A₀)
  have ha₀sQ : a₀s ∈ Q := hA_le_Q (hA₀star_le ha₀sA)
  -- a line `≠ Z` avoids `Z` (both prime order, so meet `≤` line forces equality).
  have notZ : ∀ {B : Subgroup G} {b : G}, Nat.card ↥B = p → B ≠ Z → Subgroup.zpowers b = B →
      b ∈ B → b ∉ Z := by
    intro B b hBcard hBne hzpb hbB hbZ
    exact hBne (Subgroup.eq_of_le_of_card_ge (hzpb ▸ Subgroup.zpowers_le.mpr hbZ)
      (le_of_eq (hZcard.trans hBcard.symm)))
  have ha₀notZ : a₀ ∉ Z := notZ hA₀card hA₀_ne hzpa₀ ha₀A₀
  have ha₀snotZ : a₀s ∉ Z := notZ hA₀starcard hA₀star_ne hzpa₀s ha₀sA
  -- `A = A₀ ⊔ Z`, so `a₀⋆ ∈ ⟨a₀⟩ ⊔ Z`.
  have hsupA : A₀ ⊔ Z = A := by
    have hle : A₀ ⊔ Z ≤ A := sup_le hA₀_le hZA
    have hpg : IsPGroup p ↥(A₀ ⊔ Z) :=
      hAea.isPGroup.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    obtain ⟨j, hj⟩ := hpg.exists_card_eq
    have hdvd : p ∣ Nat.card ↥(A₀ ⊔ Z) := hZcard ▸ Subgroup.card_dvd_of_le le_sup_right
    have hne : Nat.card ↥(A₀ ⊔ Z) ≠ p := by
      intro hcp
      have hZeq : Z = A₀ ⊔ Z :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq (hcp.trans hZcard.symm))
      exact ha₀notZ (hZeq ▸ (le_sup_left (a := A₀) (hzpa₀ ▸ Subgroup.mem_zpowers a₀)))
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hAcard, hj]
    refine Nat.pow_le_pow_right hpp.pos ?_
    rw [hj] at hdvd hne
    have hj1 : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h, pow_zero] at hdvd
        exact absurd (Nat.le_of_dvd one_pos hdvd) (Nat.not_le.mpr hpp.one_lt)
      · exact h
    have hjne1 : j ≠ 1 := fun h => hne (by rw [h, pow_one])
    omega
  have hmem : a₀s ∈ Subgroup.zpowers a₀ ⊔ Z := by
    rw [hzpa₀, hsupA]; exact hA₀star_le ha₀sA
  obtain ⟨g, hgQ, hg⟩ :=
    exists_conj_smul_zpowers_eq_of_expPExtraspecial_le hQ_es ha₀Q ha₀sQ ha₀notZ ha₀snotZ hmem
  refine ⟨g, hgQ, ?_⟩
  rwa [hzpa₀, hzpa₀s] at hg

/-- **`ℳ(N_G(·))`-uniqueness blocks `M`-conjugacy**: if `A₀⋆ = g • A₀` (conjugation by some
`g ∈ M`), `ℳ(N_G(A₀)) = {M}`, and `ℳ(N_G(A₀⋆)) = {M⋆}`, then `M = M⋆`.

Conjugation by `g` commutes with `N_G(·)` (`normalizer_conj_smul`) and preserves coatomicity
(`isCoatom_conj_smul`), so `g • M` is a maximal subgroup containing `N_G(A₀⋆)`, hence the unique
such, namely `M⋆`; but `g ∈ M` fixes `M` (`conj_smul_eq_self_of_mem_normalizer`), whence `M = M⋆`.
This is the engine of the final contradiction in BG 12.13: `A₀` and `A₀⋆` are `Q`-conjugate, yet
their `ℳ(N_G(·))` are the distinct singletons `{M}` and `{M⋆}`. -/
theorem eq_of_conj_of_maximalContaining_normalizer_eq_singleton
    {A₀ A₀star M Mstar : Subgroup G} {g : G} (hgM : g ∈ M)
    (hconj : MulAut.conj g • A₀ = A₀star)
    (hM : maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M})
    (hMstar : maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) = {Mstar}) :
    M = Mstar := by
  -- `M ∈ ℳ(N_G(A₀))`, so `IsCoatom M` and `N_G(A₀) ≤ M`.
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [hM]; exact Set.mem_singleton_iff.mpr rfl
  obtain ⟨hMcoat, hMle⟩ := mem_maximalSubgroupsContaining.mp hMmem
  -- `g • M` is a coatom containing `N_G(A₀⋆)`, hence lies in `ℳ(N_G(A₀⋆)) = {M⋆}`.
  have hle' : Subgroup.normalizer (A₀star : Set G) ≤ MulAut.conj g • M := by
    rw [← hconj, ← normalizer_conj_smul]
    exact conj_smul_mono _ hMle
  have hmem' : MulAut.conj g • M
      ∈ maximalSubgroupsContaining (Subgroup.normalizer (A₀star : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨isCoatom_conj_smul hMcoat, hle'⟩
  rw [hMstar, Set.mem_singleton_iff] at hmem'
  -- `g ∈ M` fixes `M` under conjugation, so `M = M⋆`.
  rwa [conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hgM)] at hmem'

/-- **BG 12.13 reduction**: a nonabelian `p`-subgroup `P` lying in two distinct maximal subgroups
`M ≠ M⋆` yields a subgroup `Q ⊆ M ∩ M⋆` of order `p³` and exponent `p` (extraspecial).

Enlarge `P` to a Sylow `p`-subgroup `S` of `M ∩ M⋆`; since `N_G(S) ⊆ M ∩ M⋆`
(`mem_sigma_normalizer_le_of_two_maximals`, `S ⊇ P` still nonabelian), `S` is a Sylow `p`-subgroup
of `G` (`exists_sylow_eq_map_of_normalizer_le`). If `r(S) ≥ 3` the Uniqueness Theorem forces
`M = M⋆`; so `r(S) ≤ 2`, and `S` nonabelian, whence Corollary 10.7(b) (`sylow_structure`) provides
the extraspecial `Q ⊆ S ⊆ M ∩ M⋆`. -/
theorem exists_expPExtraspecial_le_of_two_maximals [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P M Mstar : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) (hM : M ∈ maximalSubgroups G)
    (hMstar : Mstar ∈ maximalSubgroups G) (hMne : M ≠ Mstar)
    (hPM : P ≤ M) (hPMstar : P ≤ Mstar) :
    ∃ (S : Sylow p G) (Q : Subgroup G),
      Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar ∧
      rank ↥(S : Subgroup G) ≤ 2 ∧ Q ≤ M ⊓ Mstar ∧
      IsExpPExtraspecial p ↥Q ∧ Nat.card ↥Q = p ^ 3 := by
  classical
  set K : Subgroup G := M ⊓ Mstar with hK
  have hPK : P ≤ K := le_inf hPM hPMstar
  -- enlarge `P` to a Sylow `p`-subgroup `Pbar` of `↥K`.
  have hPsubK_pg : IsPGroup p ↥(P.subgroupOf K) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPK).symm
  obtain ⟨SK, hSK⟩ := hPsubK_pg.exists_le_sylow
  set Pbar : Subgroup G := (SK : Subgroup ↥K).map K.subtype with hPbar
  have hPbar_pg : IsPGroup p ↥Pbar :=
    SK.2.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective)
  have hP_le_Pbar : P ≤ Pbar := by
    have h1 : (P.subgroupOf K).map K.subtype ≤ Pbar := Subgroup.map_mono hSK
    rwa [Subgroup.map_subgroupOf_eq_of_le hPK] at h1
  have hPbar_nab : ¬ IsMulCommutative ↥Pbar := fun h => hPnab (isMulCommutative_of_le h hP_le_Pbar)
  have hPbar_le_K : Pbar ≤ K := Subgroup.map_subtype_le _
  have hPbar_le_M : Pbar ≤ M := hPbar_le_K.trans inf_le_left
  have hPbar_le_Mstar : Pbar ≤ Mstar := hPbar_le_K.trans inf_le_right
  -- `N_G(Pbar) ≤ K`.
  have hN : Subgroup.normalizer (Pbar : Set G) ≤ K := le_inf
    (mem_sigma_normalizer_le_of_two_maximals hG hPbar_pg hPbar_nab hM hPbar_le_M).2
    (mem_sigma_normalizer_le_of_two_maximals hG hPbar_pg hPbar_nab hMstar hPbar_le_Mstar).2
  -- `Pbar` is a Sylow `p`-subgroup of `G`.
  obtain ⟨S, hS⟩ := exists_sylow_eq_map_of_normalizer_le SK (hPbar ▸ hN)
  rw [← hPbar] at hS
  have hSlt : (S : Subgroup G) < ⊤ := by
    rw [hS, lt_top_iff_ne_top]
    exact fun htop => hM.1 (top_le_iff.mp (htop ▸ hPbar_le_M))
  -- `r(S) ≤ 2` (else Uniqueness forces `M = M⋆`).
  have hrank2 : rank ↥(S : Subgroup G) ≤ 2 := by
    by_contra hr
    have huniq := Ch2.S09.uniquenessTheorem hG hSlt (by omega)
      (Or.inl (by omega : 3 ≤ rank ↥(S : Subgroup G)))
    exact hMne (huniq.2.unique ⟨hM, by rw [hS]; exact hPbar_le_M⟩
      ⟨hMstar, by rw [hS]; exact hPbar_le_Mstar⟩)
  -- `S` nonabelian, so Cor 10.7(b) gives the extraspecial `Q`.
  rcases (S10.sylow_structure hG S).2.1 hrank2 with
    habel | ⟨Q, _, hQ_le, _, hQ_es, hQ_card, _, _, _⟩
  · exact absurd habel (by rw [hS]; exact hPbar_nab)
  · exact ⟨S, Q, by rw [hS]; exact hN, hrank2,
      hQ_le.trans (by rw [hS]; exact hPbar_le_K), hQ_es, hQ_card⟩

/-- **`M_α ≠ 1`** (BG 12.13, mmd L3395): if a Sylow `p`-subgroup `S` of `G` has `N_G(S) ⊆ M ∩ M⋆`
for distinct maximals `M ≠ M⋆`, then `M_α ≠ 1`.

Corollary 10.9(b) (`beta_factorization_of_sylow_normalizer_in_intersection`) gives
`M = (M⋆ ∩ M) ⊔ M_β` and `α(M) = β(M)`, so `M_α = M_β`; were `M_β = 1`, then `M = M⋆ ∩ M ≤ M⋆`
would force `M = M⋆` (both coatoms), contradiction. -/
theorem Malpha_ne_bot_of_sylow_normalizer_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M Mstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G)
    (hMne : M ≠ Mstar) {p : ℕ} [Fact p.Prime] (S : Sylow p G)
    (hN : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar) :
    S10.Malpha M ≠ ⊥ := by
  obtain ⟨hfact, hab⟩ := S10.beta_factorization_of_sylow_normalizer_in_intersection hG hM hMstar
    (Ne.symm hMne) S (by rw [inf_comm]; exact hN)
  have hαβ : S10.Malpha M = S10.Mbeta M := by simp only [S10.Malpha, S10.Mbeta, hab]
  rw [hαβ]
  intro hbot
  rw [hbot, sup_bot_eq] at hfact
  have hMle : M ≤ Mstar := by rw [hfact]; exact inf_le_left
  rcases lt_or_eq_of_le hMle with hlt | heq
  · exact (mem_maximalSubgroups.mp hMstar).1 ((mem_maximalSubgroups.mp hM).2 Mstar hlt)
  · exact hMne heq

/-- **`p ∉ α(M)`** when a Sylow `p`-subgroup of `G` has rank `≤ 2`: since `α(M) = {p ∈ π(M) |
r_p(M) ≥ 3}` and `r_p(M) = pRank_p(M) ≤ pRank_p(G) = pRank_p(S) ≤ rank(S) ≤ 2`. In BG 12.13 this
supplies the coprimality `p ∤ |M_α|` (`M_α` is an `α(M)`-group) needed for the Lemma 6.5(b)
factorization of `N_M(Z)`. -/
theorem notMem_alpha_of_rank_sylow_le_two [Finite G] {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hrank2 : rank ↥(S : Subgroup G) ≤ 2) :
    p ∉ S10.alpha M := by
  intro hp
  have h3 : 3 ≤ pRank ↥M p := ((S10.mem_alpha_iff M p).mp hp).2
  have hle : pRank ↥M p ≤ 2 := calc
    pRank ↥M p ≤ pRank G p := pRank_mono_of_le M
    _ = pRank ↥(S : Subgroup G) p := (pRank_sylow_eq S).symm
    _ ≤ rank ↥(S : Subgroup G) := pRank_le_rank p
    _ ≤ 2 := hrank2
  omega

/-- **Proposition 12.4(b), contrapositive form**: for `A ∈ ℰ²_p(M)` with `A ≤ M`, if `M_α ≠ 1`
then some line `A₀ ∈ ℰ¹(A)` has `ℳ(N_G(A₀)) = {M}`.

This is the negation of the hypothesis of `mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne`
(whose conclusion includes `M_α = 1`): if every line had `ℳ(N_G(·)) ≠ {M}`, then `M_α = 1`. In
BG 12.13 (where `M_α ≠ 1` holds by `Malpha_ne_bot_of_sylow_normalizer_le`) this produces the
distinguished line `A₀` realizing `M`. -/
theorem exists_line_maximalContaining_eq_of_Malpha_ne_bot [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAM : A ≤ M) (hα : S10.Malpha M ≠ ⊥) :
    ∃ A₀ ∈ elemAbelianOfRank G p 1, A₀ ≤ A ∧
      maximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M} := by
  by_contra h
  push Not at h
  exact hα (mem_sigma_and_Malpha_eq_bot_of_forall_normalizer_ne hG hM hA hAM h).2.1

/-- **An exp-`p` extraspecial `Q ≤ G` contains `A ∈ ℰ²_p(G)`** (the `A ∈ ℰ²(Q)` of BG 12.13,
mmd L3391): `Q` is a non-cyclic `p`-group (`[Q,Q] = Z(Q) ≠ 1`), so it has an elementary abelian
subgroup of order `p²` (`exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic`), whose image
in `G` is the required `A` (`elemAbelianOfRank G p 2` asks only
`IsElementaryAbelian ∧ |A| = p²`). -/
theorem exists_elemAbelianOfRank_two_le_of_expPExtraspecial [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsExpPExtraspecial p ↥Q) :
    ∃ A : Subgroup G, A ≤ Q ∧ A ∈ elemAbelianOfRank G p 2 := by
  classical
  have hpp : p.Prime := Fact.out
  have hpG : p ∣ Nat.card G :=
    (hQ.isExtraspecial.center_card ▸
      Subgroup.card_subgroup_dvd_card (Subgroup.center ↥Q)).trans
      (Subgroup.card_subgroup_dvd_card Q)
  have hodd : Odd p := hG.odd.of_dvd_nat hpG
  -- `Q` is non-cyclic: cyclic ⟹ abelian ⟹ `[Q,Q]=⊥`, but `[Q,Q]=Z(Q)` has order `p`.
  have hQnc : ¬ IsCyclic ↥Q := by
    intro hcyc
    have := hcyc
    have hcomm : IsMulCommutative ↥Q :=
      IsMulCommutative.of_comm (IsCyclic.commGroup (α := ↥Q)).mul_comm
    have hbot : Subgroup.center ↥Q = ⊥ := by
      rw [← hQ.isExtraspecial.commutator_eq_center, commutator_eq_bot_iff]; exact hcomm
    have h1 : Nat.card ↥(Subgroup.center ↥Q) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hQ.isExtraspecial.center_card] at h1
    exact hpp.one_lt.ne' h1
  obtain ⟨E, hEea, hEcard⟩ :=
    OddOrder.BG.Ch1.S04.exists_isElementaryAbelian_card_prime_sq_of_not_isCyclic
      hQ.isExtraspecial.isPGroup hodd hQnc
  refine ⟨E.map Q.subtype, Subgroup.map_subtype_le _, mem_elemAbelianOfRank.mpr ⟨?_, ?_⟩⟩
  · exact hEea.map Q.subtype_injective
  · rw [Subgroup.card_map_of_injective Q.subtype_injective, hEcard]

/-- **`⟨a⟩ ⊔ Z(Q) ∈ ℰ²(Q)` for `a ∈ Q ∖ Z(Q)`** in an exp-`p` extraspecial `Q` with
`pRank_p(G) ≤ 2`:
`a` has order `p` and centralizes the (central) `Z(Q)`, so `⟨a⟩ ⊔ Z(Q)` is elementary abelian; it
strictly contains `Z(Q)` (order `p`) and has order `≤ p²` (by `pRank_p(G) ≤ 2`), hence order
`p²`. -/
theorem zpowers_sup_center_mem_elemAbelianOfRank_two [Finite G] {p : ℕ} [Fact p.Prime]
    {Q : Subgroup G} (hQ_es : IsExpPExtraspecial p ↥Q) (hpRank : pRank G p ≤ 2)
    {a : G} (haQ : a ∈ Q) (haZ : a ∉ (Subgroup.center ↥Q).map Q.subtype) :
    Subgroup.zpowers a ⊔ (Subgroup.center ↥Q).map Q.subtype ∈ elemAbelianOfRank G p 2 := by
  classical
  set Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hZdef
  have hpp : p.Prime := Fact.out
  have hZcard : Nat.card ↥Z = p := by
    rw [hZdef, Subgroup.card_map_of_injective Q.subtype_injective, hQ_es.isExtraspecial.center_card]
  have hap : a ^ p = 1 := by
    have : a = Q.subtype ⟨a, haQ⟩ := rfl
    rw [this, ← map_pow, hQ_es.pow_eq_one, map_one]
  have ha1 : a ≠ 1 := fun h => haZ (h ▸ one_mem _)
  have horda : orderOf a = p :=
    ((Nat.dvd_prime hpp).mp (orderOf_dvd_of_pow_eq_one hap)).resolve_left
      (fun h => ha1 (orderOf_eq_one_iff.mp h))
  have hzpea : (Subgroup.zpowers a).IsElementaryAbelian p :=
    OddOrder.BG.Ch1.S05.isElementaryAbelian_of_card_prime (by rw [Nat.card_zpowers, horda])
  have hZea : Z.IsElementaryAbelian p :=
    OddOrder.BG.Ch1.S05.isElementaryAbelian_of_card_prime hZcard
  have hzp_cent : Subgroup.zpowers a ≤ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro z hz
    rw [hZdef, SetLike.mem_coe, Subgroup.mem_map] at hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h2 := congrArg (Q.subtype) (Subgroup.mem_center_iff.mp hz' ⟨a, haQ⟩)
    rw [map_mul, map_mul] at h2; exact h2.symm
  have hAea : (Subgroup.zpowers a ⊔ Z).IsElementaryAbelian p :=
    hzpea.sup_of_le_centralizer hZea hzp_cent
  refine mem_elemAbelianOfRank.mpr ⟨hAea, ?_⟩
  obtain ⟨k, hk⟩ := hAea.isPGroup.exists_card_eq
  have hub : k ≤ 2 := by
    have hlog := hAea.log_card_le_pRank.trans (le_trans (pRank_mono_of_le _) hpRank)
    rwa [hk, Nat.log_pow hpp.one_lt] at hlog
  have hdvd : p ∣ Nat.card ↥(Subgroup.zpowers a ⊔ Z) :=
    hZcard ▸ Subgroup.card_dvd_of_le le_sup_right
  have hne : Nat.card ↥(Subgroup.zpowers a ⊔ Z) ≠ p := by
    intro hcp
    have heq : Z = Subgroup.zpowers a ⊔ Z :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (le_of_eq (hcp.trans hZcard.symm))
    have ha_in : a ∈ Subgroup.zpowers a ⊔ Z :=
      (le_sup_left : Subgroup.zpowers a ≤ _) (Subgroup.mem_zpowers a)
    rw [← heq] at ha_in
    exact haZ ha_in
  rw [hk] at hdvd hne ⊢
  have hlb : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hdvd
      exact absurd (Nat.le_of_dvd one_pos hdvd) (Nat.not_le.mpr hpp.one_lt)
    · exact h
  have : k = 2 := by
    rcases Nat.lt_or_ge k 2 with h | h
    · exact absurd (by rw [show k = 1 from by omega, pow_one]) hne
    · omega
  rw [this]

/-- **`Z(Q) ≤ A` for `A ∈ ℰ²(Q)`** in an exp-`p` extraspecial `Q` of order `p³` (mmd L3391/L3397,
so that `Z` is a line of `A` and `ℰ¹(A) − {Z}` is meaningful). For `z ∈ Z(Q)`: either `z = 1 ∈ A`,
or `⟨z⟩` has order `p` (`z^p = 1`), is elementary abelian, and centralizes `A`, so `A ⊔ ⟨z⟩` is
elementary abelian and `≤ Q`. It cannot be all of `Q` (`Q` is nonabelian), so by `|Q| = p³` it has
order `≤ p² = |A|`; with `A ≤ A ⊔ ⟨z⟩` this forces `A ⊔ ⟨z⟩ = A`, i.e. `z ∈ A`. -/
theorem center_map_le_of_mem_elemAbelianOfRank_two_le_expPExtraspecial [Finite G]
    {p : ℕ} [Fact p.Prime] {Q A : Subgroup G} (hQ : IsExpPExtraspecial p ↥Q)
    (hQcard : Nat.card ↥Q = p ^ 3) (hA : A ∈ elemAbelianOfRank G p 2) (hAQ : A ≤ Q) :
    (Subgroup.center ↥Q).map Q.subtype ≤ A := by
  classical
  have hpp : p.Prime := Fact.out
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  have hQnab : ¬ IsMulCommutative ↥Q := by
    intro hc
    have hbot : Subgroup.center ↥Q = ⊥ := by
      rw [← hQ.isExtraspecial.commutator_eq_center, commutator_eq_bot_iff]; exact hc
    have h1 : Nat.card ↥(Subgroup.center ↥Q) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hQ.isExtraspecial.center_card] at h1
    exact hpp.one_lt.ne' h1
  intro z hz
  rcases eq_or_ne z 1 with rfl | hz1
  · exact one_mem A
  have hzQ : z ∈ Q := by
    rw [Subgroup.mem_map] at hz; obtain ⟨z', _, rfl⟩ := hz; exact z'.2
  have hzp : z ^ p = 1 := by
    rw [Subgroup.mem_map] at hz; obtain ⟨z', _, heq⟩ := hz
    rw [← heq, ← map_pow, hQ.pow_eq_one z', map_one]
  have horderz : orderOf z = p :=
    ((Nat.dvd_prime hpp).mp (orderOf_dvd_of_pow_eq_one hzp)).resolve_left
      (fun h => hz1 (orderOf_eq_one_iff.mp h))
  have hzcard : Nat.card ↥(Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, horderz]
  have hzea : (Subgroup.zpowers z).IsElementaryAbelian p :=
    OddOrder.BG.Ch1.S05.isElementaryAbelian_of_card_prime hzcard
  -- `A` centralizes `⟨z⟩` (`z ∈ Z(Q)` commutes with `A ≤ Q`).
  have hAcent : A ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hcza : Commute z a := by
      rw [Subgroup.mem_map] at hz
      obtain ⟨z', hz', heq⟩ := hz
      have h2 := congrArg (Subgroup.subtype Q) (Subgroup.mem_center_iff.mp hz' ⟨a, hAQ ha⟩)
      rw [map_mul, map_mul, heq] at h2
      exact h2.symm
    exact hcza.zpow_left m
  have hsupea : (A ⊔ Subgroup.zpowers z).IsElementaryAbelian p :=
    hAea.sup_of_le_centralizer hzea hAcent
  have hsup_le : A ⊔ Subgroup.zpowers z ≤ Q :=
    sup_le hAQ (by rw [Subgroup.zpowers_le]; exact hzQ)
  have hne : A ⊔ Subgroup.zpowers z ≠ Q := by
    intro heq
    rw [heq] at hsupea
    exact hQnab (IsMulCommutative.of_comm hsupea.1)
  have hcard_dvd : Nat.card ↥(A ⊔ Subgroup.zpowers z) ∣ p ^ 3 :=
    hQcard ▸ Subgroup.card_dvd_of_le hsup_le
  have hcard_ne : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≠ p ^ 3 := fun hc =>
    hne (Subgroup.eq_of_le_of_card_ge hsup_le (le_of_eq (hQcard.trans hc.symm)))
  have hcard_le : Nat.card ↥(A ⊔ Subgroup.zpowers z) ≤ p ^ 2 := by
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hpp).mp hcard_dvd
    rw [hj] at hcard_ne ⊢
    refine Nat.pow_le_pow_right hpp.pos ?_
    by_contra h
    exact hcard_ne (by rw [show j = 3 from by omega])
  have heqA : A ⊔ Subgroup.zpowers z = A :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hAcard]; exact hcard_le)).symm
  have hle : Subgroup.zpowers z ≤ A := heqA ▸ le_sup_right
  exact hle (Subgroup.mem_zpowers z)

/-- **`ℳ(N_G(Z)) ≠ {M}`** (BG 12.13, mmd L3387-3395; `Z = Z(Q)` for the extraspecial `Q ⊆ M ∩ M⋆`).
`Q/Z` acts on `K = C_{M_α}(Z)`; Proposition 1.16 writes `K = ⟨C_K(Ā) | Ā ∈ ℰ¹(Q/Z)⟩`, and
Proposition
12.4(a) gives `C_K(A) = C_K(Ā) ⊆ M⋆` for the rank-2 `A ⊇ Z`, so `K ⊆ M⋆`. Then `M = (M ∩ M⋆)M_α`
(Corollary 10.9(b), using `α(M) = β(M)`) and Lemma 6.5(b) give `N_M(Z) ⊆ M⋆`; since `M⋆ ≠ M`, the
unique maximal over `N_G(Z)` (if any) is not `M`.

**The body is the remaining analytic core of BG 12.13** (the `cocyclicFixedByClosure` instantiation
for the `Q/Z`-action on `K = C_{M_α}(Z)`); the rest of the theorem is assembled around it. -/
theorem maximalContaining_normalizer_center_ne_of_two_maximals [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M Mstar Q : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hMstar : Mstar ∈ maximalSubgroups G) (hMne : M ≠ Mstar)
    (S : Sylow p G) (hN_S : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar)
    (hrank : rank ↥(S : Subgroup G) ≤ 2) (hQ_es : IsExpPExtraspecial p ↥Q)
    (_hQcard : Nat.card ↥Q = p ^ 3) (hQ_le : Q ≤ M ⊓ Mstar) :
    maximalSubgroupsContaining
        (Subgroup.normalizer (((Subgroup.center ↥Q).map Q.subtype) : Set G)) ≠ {M} := by
  set Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype with hZdef
  -- **Analytic core**: `N_M(Z) ⊆ M⋆`. `Q/Z` acts on `K = C_{M_α}(Z)`; Proposition 1.16 +
  -- Proposition 12.4(a) give `K ⊆ M⋆`, then `M = (M ∩ M⋆)M_α` (Cor 10.9(b)) + Lemma 6.5(b)
  -- (coprimality `p ∉ α(M)` from `r(S) ≤ 2`) give `N_M(Z) ⊆ M⋆`.
  have hNMZ : Subgroup.normalizer (Z : Set G) ⊓ M ≤ Mstar := by
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have hpp : p.Prime := Fact.out
    have hZ_le_inf : Z ≤ M ⊓ Mstar := (Subgroup.map_subtype_le _).trans hQ_le
    have hZM : Z ≤ M := hZ_le_inf.trans inf_le_left
    have hMα_le : S10.Malpha M ≤ M := S10.Malpha_le M
    have hZcard : Nat.card ↥Z = p := by
      rw [hZdef, Subgroup.card_map_of_injective Q.subtype_injective,
        hQ_es.isExtraspecial.center_card]
    -- **`C_{M_α}(Z) ⊆ M⋆`** — the `cocyclicFixedByClosure`/`Q/Z`-on-`K` analytic core (Prop 1.16 +
    -- 12.4a).
    have hK : Subgroup.centralizer (Z : Set G) ⊓ S10.Malpha M ≤ Mstar := by
      classical
      set K : Subgroup G := Subgroup.centralizer (Z : Set G) ⊓ S10.Malpha M with hKdef
      -- (1) `Q` normalizes `K = C_{M_α}(Z)` (it normalizes `Z` and `M_α`).
      have hQ_norm_Z : Q ≤ Subgroup.normalizer (Z : Set G) := by
        rw [hZdef]; exact le_normalizer_map_subtype_of_normal inferInstance
      have hQ_norm_Mα : Q ≤ Subgroup.normalizer ((S10.Malpha M : Subgroup G) : Set G) :=
        (hQ_le.trans inf_le_left).trans (le_normalizer_opiCoreInG (S10.alpha M) M)
      have hQK : Q ≤ Subgroup.normalizer (K : Set G) := by
        intro q hq
        refine mem_normalizer_of_conj_smul_eq_self ?_
        rw [hKdef, Subgroup.smul_inf, centralizer_conj_smul,
          conj_smul_eq_self_of_mem_normalizer (hQ_norm_Z hq),
          conj_smul_eq_self_of_mem_normalizer (hQ_norm_Mα hq)]
      -- (2) conjugation action of `Q` on `K`, factoring through `Q/Z(Q)`.
      let act : MulDistribMulAction ↥Q ↥K :=
        MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer (K : Set G))) ↥K
          (Subgroup.inclusion hQK)
      set ψ : ↥Q →* MulAut ↥K := MulDistribMulAction.toMulAut ↥Q ↥K with hψ
      have hψ_coe : ∀ (a : ↥Q) (x : ↥K),
          (K.subtype ((ψ a) x)) = (↑a) * (K.subtype x) * (↑a)⁻¹ := fun _ _ => rfl
      have hker : Subgroup.center ↥Q ≤ ψ.ker := by
        intro z hz
        rw [MonoidHom.mem_ker]
        apply MulEquiv.ext; intro x; apply Subtype.ext
        have hzZ : (z : G) ∈ (Z : Set G) := by
          rw [hZdef]; exact Subgroup.mem_map_of_mem _ hz
        have hcomm : (z : G) * (x : G) = (x : G) * (z : G) :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).1) (z : G) hzZ
        calc K.subtype ((ψ z) x) = (z : G) * (x : G) * (z : G)⁻¹ := hψ_coe z x
          _ = (x : G) := by rw [hcomm]; group
      set φ : (↥Q ⧸ Subgroup.center ↥Q) →* MulAut ↥K := QuotientGroup.lift _ ψ hker with hφ
      -- (3) `Q/Z(Q)` is noncyclic abelian acting coprimely on `K` ⟹ `cocyclicFixedByClosure φ = ⊤`.
      have hQZcomm : IsMulCommutative (↥Q ⧸ Subgroup.center ↥Q) := by
        refine ⟨⟨fun a b => ?_⟩⟩
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have hc : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          rw [commutatorElement_def]; group
        rw [hc, ← hQ_es.isExtraspecial.commutator_eq_center]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      have hcop : Nat.Coprime (Nat.card (↥Q ⧸ Subgroup.center ↥Q)) (Nat.card ↥K) := by
        have hQZpg : IsPGroup p (↥Q ⧸ Subgroup.center ↥Q) :=
          hQ_es.isExtraspecial.isPGroup.to_quotient _
        obtain ⟨k, hk⟩ := hQZpg.exists_card_eq
        rw [hk]
        refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr fun hpK => ?_)
        exact (notMem_alpha_of_rank_sylow_le_two S hrank) (S10.Malpha_isPiGroup M p
          (Nat.mem_primeFactors.mpr ⟨Fact.out,
            hpK.trans (Subgroup.card_dvd_of_le inf_le_right), Nat.card_pos.ne'⟩))
      have hNC : ¬ IsCyclic (↥Q ⧸ Subgroup.center ↥Q) := by
        intro hcyc
        have := hcyc
        have hcomm_Q : ∀ a b : ↥Q, a * b = b * a :=
          (MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
            (QuotientGroup.mk' (Subgroup.center ↥Q))
            (QuotientGroup.ker_mk' _).le).is_comm.comm
        have : IsMulCommutative ↥Q := ⟨⟨hcomm_Q⟩⟩
        have hbot : commutator ↥Q = ⊥ := commutator_eq_bot ↥Q
        rw [hQ_es.isExtraspecial.commutator_eq_center] at hbot
        have h1 : Nat.card ↥(Subgroup.center ↥Q) = 1 := by rw [hbot]; exact Subgroup.card_bot
        rw [hQ_es.isExtraspecial.center_card] at h1
        exact (Fact.out : p.Prime).one_lt.ne' h1
      have hgen := OddOrder.BG.Ch1.S01.cocyclicFixedByClosure_eq_top_of_not_isCyclic φ hcop hNC
      -- (4) each cocyclic generator `g` is centralized (in `G`) by a rank-2 `A_Y ∈ ℰ²(Q)`,
      --     so `↑g ∈ C_G(A_Y) ⊆ M⋆` by Proposition 12.4(a).
      have hle : OddOrder.BG.Ch1.S01.cocyclicFixedByClosure φ ≤ Mstar.comap K.subtype := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro g ⟨Y, ⟨a, hYa⟩, hfix⟩
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        have hpRank : pRank G p ≤ 2 := by
          rw [← pRank_sylow_eq S]; exact (pRank_le_rank p).trans hrank
        -- preimage `A_Y` of `Y` in `Q` (so `Z ≤ A_Y`); `↑g` centralizes it.
        set A_Y : Subgroup G := (Y.comap (QuotientGroup.mk' (Subgroup.center ↥Q))).map Q.subtype
          with hAYdef
        have hA_Y_le_Q : A_Y ≤ Q := Subgroup.map_subtype_le _
        have hgcent : K.subtype g ∈ Subgroup.centralizer (A_Y : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rw [SetLike.mem_coe, hAYdef, Subgroup.mem_map] at hx
          obtain ⟨yb, hyb, rfl⟩ := hx
          have hfixyb := hfix _ (Subgroup.mem_comap.mp hyb)
          rw [QuotientGroup.mk'_apply, hφ, QuotientGroup.lift_mk'] at hfixyb
          have h2 := congrArg K.subtype hfixyb
          rw [hψ_coe, mul_inv_eq_iff_eq_mul] at h2
          exact h2
        -- `Y ≠ ⊥` (else `Q/Z` is cyclic), so there is `a' ∈ A_Y ∖ Z`.
        have hY_ne : Y ≠ ⊥ := by
          intro hY1
          rw [hY1, bot_sup_eq] at hYa
          exact hNC (isCyclic_iff_exists_zpowers_eq_top.mpr ⟨a, hYa⟩)
        have : Nontrivial ↥Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hY_ne
        obtain ⟨⟨yb₀, hyb₀Y⟩, hyb₀ne⟩ := exists_ne (1 : ↥Y)
        have hyb₀1 : yb₀ ≠ 1 := fun h => hyb₀ne (Subtype.ext h)
        obtain ⟨q₀, rfl⟩ := QuotientGroup.mk_surjective yb₀
        have ha'AY : Q.subtype q₀ ∈ A_Y := by
          rw [hAYdef]
          refine Subgroup.mem_map_of_mem _ ?_
          rw [Subgroup.mem_comap, QuotientGroup.mk'_apply]; exact hyb₀Y
        have ha'Z : Q.subtype q₀ ∉ (Subgroup.center ↥Q).map Q.subtype := by
          rw [Subgroup.mem_map]
          rintro ⟨z', hz', hz'eq⟩
          exact hyb₀1 ((QuotientGroup.eq_one_iff q₀).mpr (Q.subtype_injective hz'eq ▸ hz'))
        have hZ_le_AY : (Subgroup.center ↥Q).map Q.subtype ≤ A_Y := by
          rw [hAYdef]
          apply Subgroup.map_mono
          intro w hw
          rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff w).mpr hw]
          exact one_mem Y
        -- `A := ⟨a'⟩ ⊔ Z ∈ ℰ²(Q)`, `A ≤ A_Y ≤ Q ≤ M⋆`, and `↑g ∈ C_G(A_Y) ≤ C_G(A) ⊆ M⋆`.
        have hA_mem := zpowers_sup_center_mem_elemAbelianOfRank_two hQ_es hpRank
          (hA_Y_le_Q ha'AY) ha'Z
        have hA_le_Mstar : Subgroup.zpowers (Q.subtype q₀) ⊔ (Subgroup.center ↥Q).map Q.subtype
            ≤ Mstar :=
          sup_le ((Subgroup.zpowers_le.mpr (hA_Y_le_Q ha'AY)).trans (hQ_le.trans inf_le_right))
            ((Subgroup.map_subtype_le _).trans (hQ_le.trans inf_le_right))
        have hgC : K.subtype g ∈ Subgroup.centralizer
            ((Subgroup.zpowers (Q.subtype q₀) ⊔ (Subgroup.center ↥Q).map Q.subtype :
              Subgroup G) : Set G) :=
          Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
            (sup_le (Subgroup.zpowers_le.mpr ha'AY) hZ_le_AY)) hgcent
        exact centralizer_le_of_elemAb_rank_two hG hMstar hA_mem hA_le_Mstar hgC
      intro x hx
      exact Subgroup.mem_comap.mp (hle (hgen ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥K)))
    -- Corollary 10.9(b): `M = (M ∩ M⋆) ⊔ M_α` (using `α(M) = β(M)`).
    obtain ⟨hfact, hab⟩ := S10.beta_factorization_of_sylow_normalizer_in_intersection hG hM hMstar
      (Ne.symm hMne) S (by rw [inf_comm]; exact hN_S)
    have hMαβ : S10.Malpha M = S10.Mbeta M := by simp only [S10.Malpha, S10.Mbeta, hab]
    have hMsup : S10.Malpha M ⊔ (M ⊓ Mstar) = M := by
      rw [hMαβ, sup_comm, inf_comm]; exact hfact.symm
    have hKU : (S10.Malpha M).subgroupOf M ⊔ (M ⊓ Mstar).subgroupOf M = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hMα_le inf_le_left, hMsup, Subgroup.subgroupOf_self]
    -- coprimality `(|Z|, |M_α|) = 1` from `p ∉ α(M)`.
    have hpMα : ¬ p ∣ Nat.card ↥(S10.Malpha M) := fun h =>
      (notMem_alpha_of_rank_sylow_le_two S hrank)
        (S10.Malpha_isPiGroup M p (Nat.mem_primeFactors.mpr ⟨hpp, h, Nat.card_pos.ne'⟩))
    have hcop : Nat.Coprime (Nat.card ↥(Z.subgroupOf M))
        (Nat.card ↥((S10.Malpha M).subgroupOf M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMα_le).toEquiv, hZcard]
      exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr hpMα
    -- Lemma 6.5(b) inside `↥M`: `N_{↥M}(Z) = C_{M_α}(Z) · N_{M∩M⋆}(Z)`.
    have hlem := OddOrder.BG.Ch1.S06.normalizer_eq_centralizerK_mul_normalizerU (G := ↥M)
      (K := (S10.Malpha M).subgroupOf M) (U := (M ⊓ Mstar).subgroupOf M) (H := Z.subgroupOf M)
      hKU (Subgroup.subgroupOf_mono M hZ_le_inf) hcop
    intro m hm
    rw [Subgroup.mem_inf] at hm
    have hmM : m ∈ M := hm.2
    have hmbar : (⟨m, hmM⟩ : ↥M) ∈ Subgroup.normalizer (Z.subgroupOf M) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hZM, Subgroup.mem_subgroupOf]; exact hm.1
    have hmbarc := SetLike.mem_coe.mpr hmbar
    rw [hlem] at hmbarc
    obtain ⟨c, hc, u, hu, hcu⟩ := Set.mem_mul.mp hmbarc
    -- `↑c ∈ C_{M_α}(Z) ⊆ M⋆`.
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hc
    have hcMstar : (M.subtype c) ∈ Mstar := by
      apply hK
      refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_subgroupOf.mp hc.2⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzM : z ∈ M := hZM hz
      have hcomm := (Subgroup.mem_centralizer_iff.mp hc.1) ⟨z, hzM⟩
        (Subgroup.mem_subgroupOf.mpr hz)
      have h2 := congrArg (M.subtype) hcomm
      rw [map_mul, map_mul] at h2
      exact h2
    -- `↑u ∈ M ∩ M⋆ ⊆ M⋆`.
    rw [SetLike.mem_coe, Subgroup.mem_inf] at hu
    have huMstar : (M.subtype u) ∈ Mstar :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hu.2)).2
    have hmem_star : (M.subtype c) * (M.subtype u) ∈ Mstar := Mstar.mul_mem hcMstar huMstar
    rwa [← map_mul, hcu] at hmem_star
  -- If `ℳ(N_G(Z)) = {M}`, then `N_G(Z) ≤ M`, so `N_G(Z) = N_M(Z) ⊆ M⋆`, forcing `M⋆ = M`.
  intro hsing
  have hMmem : M ∈ maximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) := by
    rw [hsing]; exact Set.mem_singleton_iff.mpr rfl
  have hNZM : Subgroup.normalizer (Z : Set G) ≤ M := (mem_maximalSubgroupsContaining.mp hMmem).2
  have hNZMstar : Subgroup.normalizer (Z : Set G) ≤ Mstar := fun x hx => hNMZ ⟨hx, hNZM hx⟩
  have hMstarmem : Mstar ∈ maximalSubgroupsContaining (Subgroup.normalizer (Z : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hMstar, hNZMstar⟩
  rw [hsing, Set.mem_singleton_iff] at hMstarmem
  exact hMne hMstarmem.symm

/-- **BG Theorem 12.13** (mmd L3347): every nonabelian `p`-subgroup of `G` (for every prime `p`)
lies in `𝒰`. -/
theorem nonabelian_pgroup_isUniquelyMaximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] {P : Subgroup G} (hPp : IsPGroup p ↥P)
    (hPnab : ¬ IsMulCommutative ↥P) :
    IsUniquelyMaximal P := by
  classical
  -- `P < ⊤` (else `G` is a `p`-group, hence solvable).
  have hPlt : P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hPtop
    have hGp : IsPGroup p G :=
      (hPtop ▸ hPp : IsPGroup p ↥(⊤ : Subgroup G)).of_equiv Subgroup.topEquiv
    have := hGp.isNilpotent
    exact hG.notSolvable IsNilpotent.to_isSolvable
  obtain ⟨M, hMcoatom, hPM⟩ := (IsCoatomic.eq_top_or_exists_le_coatom P).resolve_left hPlt.ne
  refine IsUniquelyMaximal.of_unique_maximal hPlt (mem_maximalSubgroups.mpr hMcoatom) hPM ?_
  intro Mstar hMstar hPMstar
  by_contra hne
  have hMmem : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMcoatom
  have hMne : M ≠ Mstar := fun h => hne h.symm
  -- enlarge `P` to a Sylow `p`-subgroup `S` of `G` inside `M ∩ M⋆`, with extraspecial `Q ⊆ M ∩ M⋆`.
  obtain ⟨S, Q, hN_S, hrankS, hQ_le, hQ_es, hQ_card⟩ :=
    exists_expPExtraspecial_le_of_two_maximals hG hPp hPnab hMmem hMstar hMne hPM hPMstar
  -- `A ∈ ℰ²(Q)` with `Z(Q) ≤ A`, and `A ⊆ M, M⋆`.
  obtain ⟨A, hA_le_Q, hA_mem⟩ := exists_elemAbelianOfRank_two_le_of_expPExtraspecial hG hQ_es
  have hZA : (Subgroup.center ↥Q).map Q.subtype ≤ A :=
    center_map_le_of_mem_elemAbelianOfRank_two_le_expPExtraspecial hQ_es hQ_card hA_mem hA_le_Q
  have hA_le_M : A ≤ M := (hA_le_Q.trans hQ_le).trans inf_le_left
  have hA_le_Mstar : A ≤ Mstar := (hA_le_Q.trans hQ_le).trans inf_le_right
  -- `M_α ≠ 1` and `M⋆_α ≠ 1`.
  have hMα : S10.Malpha M ≠ ⊥ :=
    Malpha_ne_bot_of_sylow_normalizer_le hG hMmem hMstar hMne S hN_S
  have hMstarα : S10.Malpha Mstar ≠ ⊥ :=
    Malpha_ne_bot_of_sylow_normalizer_le hG hMstar hMmem (Ne.symm hMne) S
      (by rw [inf_comm]; exact hN_S)
  -- distinguished lines `A₀` (realizing `M`) and `A₀⋆` (realizing `M⋆`) via Prop 12.4(b).
  obtain ⟨A₀, hA₀_mem, hA₀_le_A, hA₀_M⟩ :=
    exists_line_maximalContaining_eq_of_Malpha_ne_bot hG hMmem hA_mem hA_le_M hMα
  obtain ⟨A₀star, hA₀star_mem, hA₀star_le_A, hA₀star_Mstar⟩ :=
    exists_line_maximalContaining_eq_of_Malpha_ne_bot hG hMstar hA_mem hA_le_Mstar hMstarα
  -- `ℳ(N_G(Z)) ≠ {M}, {M⋆}`, hence `A₀, A₀⋆ ≠ Z`.
  have hZneM := maximalContaining_normalizer_center_ne_of_two_maximals hG hMmem hMstar hMne S hN_S
    hrankS hQ_es hQ_card hQ_le
  have hZneMstar := maximalContaining_normalizer_center_ne_of_two_maximals hG hMstar hMmem
    (Ne.symm hMne) S (by rw [inf_comm]; exact hN_S)
      hrankS hQ_es hQ_card (by rw [inf_comm]; exact hQ_le)
  have hA₀_ne_Z : A₀ ≠ (Subgroup.center ↥Q).map Q.subtype := fun heq => hZneM (heq ▸ hA₀_M)
  have hA₀star_ne_Z : A₀star ≠ (Subgroup.center ↥Q).map Q.subtype :=
    fun heq => hZneMstar (heq ▸ hA₀star_Mstar)
  -- `A₀` and `A₀⋆` are `Q`-conjugate, contradicting the distinct `ℳ(N_G(·))` singletons.
  obtain ⟨g, hgQ, hg⟩ := exists_conj_smul_eq_of_lines_of_expPExtraspecial hQ_es hZA hA_mem hA_le_Q
    hA₀_mem hA₀_le_A hA₀_ne_Z hA₀star_mem hA₀star_le_A hA₀star_ne_Z
  exact hne (eq_of_conj_of_maximalContaining_normalizer_eq_singleton
    ((hQ_le.trans inf_le_left) hgQ) hg hA₀_M hA₀star_Mstar).symm

end OddOrder.BG.Ch3.S12



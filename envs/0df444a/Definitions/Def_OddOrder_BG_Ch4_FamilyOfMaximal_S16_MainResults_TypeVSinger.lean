-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeVSinger
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeVSinger
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:37:00.480135+00:00
-- url     : https://prove2.me/theorems/c20be251-e9b3-4ef1-b76d-178d54688ddc
-- title:
--   BG §16: type-V Singer forward bridges
-- statement:
--   Assembles the type-V Singer structure and the forward bridge from the $M_F=M_\sigma$ type-$\mathcal{P}_1$ case to Peterfalvi type V, for Theorem A and Proposition 16.1(d) of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 6 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeVSinger.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeVSinger.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeP1Criteria

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`M_F` is non-abelian for a type-V maximal** (the abelian-`H` exclusion of Coq
`nonTI_Fitting_structure`, the `P1maxM` branch): a type-`P₁` maximal subgroup `M` with `M_F = M_σ`
has non-abelian `M_F`.  The type-`P` datum's `W₂ = C_{M'}(W₁#)` is nontrivial (`W2_nontrivial`) and
lies in `M''` (`W2_le`); but `M' = M_σ = M_F` here, so `M'' = (M_F)'`, whence `(M_F)' ⊇ W₂ ≠ ⊥`,
i.e. `M_F` is non-abelian.  (Equivalently: were `M_F` abelian, `M'' = ⊥` would force `W₂ = ⊥`.) -/
theorem not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    ¬ IsMulCommutative ↥(S15.MF M) := by
  intro hab
  have := hab
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  -- `M' = M_σ = M_F`, so `M'' = (M_F)' = ⊥` (were `M_F` abelian).
  have hM'MF : derivedInG M = S15.MF M :=
    (isTypeP1_derivedInG_eq_Msigma hG hM hP1).trans hmf.symm
  have hM''bot : secondDerivedInAmbient M = ⊥ := by
    rw [secondDerivedInAmbient, hM'MF,
      show derivedInG (S15.MF M) = (commutator ↥(S15.MF M)).map (S15.MF M).subtype from rfl,
      commutator_eq_bot, Subgroup.map_bot]
  exact data.W2_nontrivial (le_bot_iff.mp ((data.W2_le.trans inf_le_right).trans hM''bot.le))

/-- **`O_p(M_F)` is narrow once its `p`-rank reaches 3** (BG Theorem 15.7(e), the narrow input for
the `r(P) ≤ 2` step of the type-V Singer case).  For `P = O_p(M_F)` with
`pRank P ≥ 3`, the order-`p`
non-TI witness `X₁ ≤ M_F` whose `M_F`-centralizer has rank `< 3` (the `E1X_facts` rank bound from
`exists_inf_conj_fitting_orderP_witness`) realizes the narrow characterization
`narrow_iff_exists_card_prime_centralizer_pRank_le_two`: `X₁ ≤ P`
(`le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent`) and `C_P(X₁) = (C_G(X₁)).subgroupOf P` has
`pRank ≤ rank(M_F ⊓ C_G(X₁)) < 3` (it embeds into `M_F ⊓ C_G(X₁)` as `P ≤ M_F`).  No Sylow/`β`
plumbing is needed: the `pRank ≥ 3` hypothesis is exactly the contradiction branch of `r(P) ≤ 2`. -/
theorem isNarrow_opiCore_of_three_le_pRank [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (_hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    (h3 : 3 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p) :
    OddOrder.GroupTheory.IsNarrow p ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPMF : P ≤ S15.MF M := opiCoreInG_le _ _
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  rw [OddOrder.BG.Ch1.S05.narrow_iff_exists_card_prime_centralizer_pRank_le_two hpodd hPpg h3]
  refine ⟨X₁.subgroupOf P,
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₁P).toEquiv).trans hX₁card, ?_⟩
  -- `C_{↥P}(X₁.subgroupOf P) = (C_G(X₁)).subgroupOf P`.
  have himg_set : (P.subtype : ↥P → G) '' (↑(X₁.subgroupOf P) : Set ↥P) = (X₁ : Set G) := by
    rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hX₁P]
  have hcent : Subgroup.centralizer (↑(X₁.subgroupOf P) : Set ↥P)
      = (Subgroup.centralizer (X₁ : Set G)).subgroupOf P := by
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, himg_set]
  rw [hcent]
  -- `↥((C_G(X₁)).subgroupOf P)` embeds into `M_F ⊓ C_G(X₁)` (image is
  -- `P ⊓ C_G(X₁) ≤ M_F ⊓ C_G(X₁)`).
  have hsub : ((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype
      ≤ S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G) := by
    simp only [Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype]
    exact le_inf (inf_le_left.trans hPMF) inf_le_right
  calc pRank ↥((Subgroup.centralizer (X₁ : Set G)).subgroupOf P) p
      ≤ pRank ↥(((Subgroup.centralizer (X₁ : Set G)).subgroupOf P).map P.subtype) p :=
        pRank_le_of_injective
          (f := (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).toMonoidHom)
          (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).injective
    _ ≤ pRank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) p :=
        pRank_le_of_injective (Subgroup.inclusion_injective hsub)
    _ ≤ rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := pRank_le_rank p
    _ ≤ 2 := by omega

/-- **`r(O_p(M_F)) ≤ 2` for the type-V Singer case** (BG Theorem 15.7(e), Coq `rPle2`).  A
`κ`-Hall `K` (cyclic, `p'`, normalizing `P = O_p(M_F)`) that acts *faithfully* on `P`
(`K ⊓ C_G(P) = ⊥`) with `|K| ∤ p − 1` forces `pRank P ≤ 2`: were `pRank P ≥ 3`, `P` would be narrow
(`isNarrow_opiCore_of_three_le_pRank`), and BG Theorem 5.5(b) (`solvableAut_of_narrow`, applied to
the faithful `φ : K → MulAut P`) would give that every `p'`-element of `K` has order dividing
`p − 1`; the cyclic generator of `K` then yields `|K| ∣ p − 1`, contradicting `|K| ∤ p − 1`.

The faithfulness `K ⊓ C_G(P) = ⊥` is the `defZP`/`Kstar = Z(P)` content of the Singer case
(supplied separately). -/
theorem pRank_opiCore_le_two_of_kappaHall [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ K : Subgroup G} (hp : p.Prime) (hpodd : Odd p)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hrank3 : rank ↥(S15.MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3)
    [IsCyclic ↥K] (hKp' : ¬ p ∣ Nat.card ↥K)
    (hKnormP : K ≤ Subgroup.normalizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G))
    (hKfaithful : K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥)
    (hKp1 : ¬ Nat.card ↥K ∣ p - 1) :
    pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (q := p) (S15.MF M)
  have : Group.IsSolvable ↥K := by
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
    rw [← zpow_add, ← zpow_add, add_comm]
  by_contra hcon
  rw [not_le] at hcon
  have h3 : 3 ≤ pRank ↥P p := hcon
  have hPnarrow : OddOrder.GroupTheory.IsNarrow p ↥P :=
    isNarrow_opiCore_of_three_le_pRank hG hM hp hpodd hX₁card hX₁MF hrank3 h3
  -- The faithful conjugation action `φ : ↥K → MulAut ↥P`.
  set φ : ↥K →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKnormP) with hφdef
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro k hk
    rw [hφdef, MonoidHom.comp_apply] at hk
    have hkmem : (Subgroup.inclusion hKnormP k) ∈ (Subgroup.normalizerMonoidHom P).ker :=
      MonoidHom.mem_ker.mpr hk
    rw [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hkmem
    have hmem : (k : G) ∈ K ⊓ Subgroup.centralizer (↑P : Set G) :=
      Subgroup.mem_inf.mpr ⟨k.2, hkmem⟩
    rw [hKfaithful, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hKodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  obtain ⟨-, -, hb, -⟩ :=
    OddOrder.BG.Ch1.S05.solvableAut_of_narrow hpodd hPpg hPnarrow φ hφinj hKodd
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥K)
  have hKcard : Nat.card ↥K = orderOf g := (orderOf_eq_card_of_forall_mem_zpowers hg).symm
  have hgcop : Nat.Coprime (orderOf g) p := hKcard ▸ (hp.coprime_iff_not_dvd.mpr hKp').symm
  have hgdvd : orderOf g ∣ p - 1 := hb h3 g hgcop
  rw [← hKcard] at hgdvd
  exact hKp1 hgdvd

/-- **`|Z(O_p(M_F))| = p` in the type-V Singer case** (BG Theorem 15.7(e), Coq `defZP`/`oZ0`): the
centre of `P = O_p(M_F)` has order `p`.  The cyclic `κ`-Hall `K` (a `p′`-group acting on `P`)
centralizes `Ω₁(Z(P))` — it equals `K* = M_σ ⊓ C(K)` and `Ω₁(Z(P)) ≤ K*` (the `(e3)` Singer
hypothesis) — so by **BG Theorem 1.11** (`actsTrivially_on_of_fixes_omega1`, the coprime
`Ω₁`-rigidity)
`K` centralizes all of `Z(P)`.  Hence `Z(P) ≤ M_σ ⊓ C(K) = K* = Ω₁(Z(P)) ≤ Z(P)`, i.e.
`Z(P) = Ω₁(Z(P))`, whose order is `p`.  This is the `|Z(P)| = p` input to the central-product
collapse `mFT_rank2_Sylow_cprod` (`card_opiCore_eq_prime_cube_singer`).

The hypotheses `hZKstar`/`hZcard` are about the explicit `Ω₁(Z(P)) = omega1CenterInG P p`; in the
type-V branch they come from the witness `Z` (which equals `Ω₁(Z(P))`, exposed by
`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`) together with `Z ≤ K*`. -/
theorem card_center_opiCore_eq_prime_of_omega1Center_le_kstar [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hKp' : ¬ p ∣ Nat.card ↥K)
    (hKnormP : K ≤ Subgroup.normalizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G))
    (hZKstar : OddOrder.BG.Ch3.S10.omega1CenterInG (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ Kstar)
    (hZcard : Nat.card ↥(OddOrder.BG.Ch3.S10.omega1CenterInG
      (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p) = p) :
    Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  set Z : Subgroup G := OddOrder.BG.Ch3.S10.omega1CenterInG P p with hZdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (S15.MF M)
  -- `K* = Z` (= `Ω₁(Z(P))`): `|K*|` prime, `Z ≤ K*`, `|Z| = p`.
  have hKstarEqZ : Kstar = Z := by
    have hKstarPrime : (Nat.card ↥Kstar).Prime :=
      S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
    have hdvd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
    have hc : Nat.card ↥Kstar = p := ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hdvd).symm
    exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hc.trans hZcard.symm))).symm
  -- Conjugation action `φ : ↥K →* MulAut ↥P`.
  set φ : ↥K →* MulAut ↥P :=
    (Subgroup.normalizerMonoidHom P).comp (Subgroup.inclusion hKnormP) with hφdef
  have hp2 : p ≠ 2 := by rintro rfl; exact (by decide : ¬ Odd 2) hpodd
  -- `K` fixes `Z(P)` pointwise (Theorem 1.11): it fixes `Ω₁(Z(P)) = Z ≤ K* ≤ C(K)`.
  have htriv : ∀ a : ↥K, ∀ g ∈ Subgroup.center ↥P, φ a g = g := by
    refine OddOrder.BG.Ch1.S01.actsTrivially_on_of_fixes_omega1 hp2 hPpg hKp' φ
      (OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ) ?_
    intro a g hg hgp
    have hgZ : (g : G) ∈ Z := by
      rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map]
      exact ⟨g, mem_omega1OfAbelian.mpr ⟨hg, hgp⟩, rfl⟩
    have hgC : (g : G) ∈ Subgroup.centralizer (K : Set G) := by
      have hgKstar : (g : G) ∈ Kstar := by rw [hKstarEqZ]; exact hgZ
      rw [hKstar] at hgKstar; exact (Subgroup.mem_inf.mp hgKstar).2
    apply Subtype.ext
    change (a : G) * (g : G) * (a : G)⁻¹ = (g : G)
    have hcomm : (a : G) * (g : G) = (g : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hgC (a : G) a.2
    rw [hcomm, mul_inv_cancel_right]
  -- `Z(P) ≤ K* = Z`: `Z(P) ≤ M_σ` and `K` centralizes `Z(P)`.
  have hcent_le : (Subgroup.center ↥P).map P.subtype ≤ Z := by
    rw [← hKstarEqZ, hKstar]
    refine le_inf ((Subgroup.map_subtype_le _).trans
      ((opiCoreInG_le _ _).trans (hmf ▸ S15.maxNilpotentNormalHall_le_Msigma hG hM))) ?_
    intro x hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h2 : k * (g : G) * k⁻¹ = (g : G) := congrArg (fun z : ↥P => (z : G)) (htriv ⟨k, hk⟩ g hg)
    exact mul_inv_eq_iff_eq_mul.mp h2
  -- `Z = Ω₁(Z(P)) ≤ Z(P)`.
  have hZ_le_cent : Z ≤ (Subgroup.center ↥P).map P.subtype := by
    rw [hZdef, OddOrder.BG.Ch3.S10.omega1CenterInG]
    exact Subgroup.map_mono omega1OfAbelian_le
  have hcent_eq : (Subgroup.center ↥P).map P.subtype = Z := le_antisymm hcent_le hZ_le_cent
  have hmapcard : Nat.card ↥((Subgroup.center ↥P).map P.subtype) = Nat.card ↥(Subgroup.center ↥P) :=
    Subgroup.card_map_of_injective P.subtype_injective
  rw [hcent_eq] at hmapcard
  rw [← hmapcard, hZcard]

/-- **`|O_p(M_F)| = p³` in the type-V Singer case** (BG Theorem 15.7(e), Coq `dimP`/`oP`): the order
of `P = O_p(M_F)` is `p³`.  **Complete and axiom-clean** (`AxiomsCheck`); all four inputs are
discharged:

* `r(P) ≤ 2` (`hrPle2`, the `rPle2` step, via the faithfulness brick
  `kappaHall_inf_centralizer_opiCore_eq_bot` + `pRank_opiCore_le_two_of_kappaHall`),
* `P` non-abelian (`hPnab`),
* `P` Sylow of `G` (`exists_sylow_eq_opiCore_of_mf_eq_msigma`, Coq `sylP_G`),
* `|Z(P)| = p` (`hZPcard`, `card_center_opiCore_eq_prime_of_omega1Center_le_kstar`, Coq `defZP` via
  BG Theorem 1.11).

The **Blackburn rank-2 Sylow central-product structure** (BG Corollary 10.7(b), Coq
`mFT_rank2_Sylow_cprod`) enters through the public `S10.sylow_structure` (second conjunct, gated on
`rank ≤ 2`): `P` is abelian (excluded by `hPnab`) or a central product `P₁ ∘ P₂` with `P₁`
exponent-`p` extraspecial of order `p³` and `P₂` cyclic with `Ω₁(P₂) = Z(P₁)`.  Then `|Z(P)| = p`
collapses the cyclic factor — `P₂ ≤ Z(P)` forces `|P₂| = p`, so `P₂ = Ω₁(P₂) = Z(P₁) ≤ P₁` and
`P = P₁ ⊔ P₂ = P₁` — leaving `|P| = |P₁| = p³`. -/
theorem card_opiCore_eq_prime_cube_singer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (_hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M)
    {p : ℕ} (hp : p.Prime) (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M)
    (_hpπ : p ∈ (Nat.card ↥(S15.MF M)).primeFactors)
    (hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2)
    (hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)))
    (hZPcard : Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p) :
    Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- `P = O_p(M_F)` is a Sylow `p`-subgroup of `G` (`sylP_G`).
  obtain ⟨S, hS⟩ := exists_sylow_eq_opiCore_of_mf_eq_msigma hG hM hmf hp hpσ
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (S15.MF M)
  -- `rank P ≤ 2` from `pRank P p ≤ 2` (a `p`-group has `rank = pRank` at `p`).
  have hrankP : rank ↥P ≤ 2 := by
    by_contra hc
    exact absurd (OddOrder.BG.Ch2.S09.three_le_pRank_of_isPGroup_of_three_le_rank hPpg
      (by omega)) (by omega)
  -- **Blackburn rank-2 Sylow central-product dichotomy** (Cor 10.7(b), `sylow_structure`): `P` is
  -- abelian (excluded by `hPnab`) or a central product `P₁ ∘ P₂` with `P₁` exponent-`p`
  -- extraspecial of order `p³` and `P₂` cyclic with `Ω₁(P₂) = Z(P₁)`.
  have hrankS : rank ↥(S : Subgroup G) ≤ 2 := by rw [hS]; exact hrankP
  have hdich := (OddOrder.BG.Ch3.S10.sylow_structure hG S).2.1 hrankS
  rw [hS] at hdich
  rcases hdich with hab | ⟨P₁, P₂, hP₁P, hP₂P, hP₁es, hP₁card, hP₂cyc, hΩeq, hcp⟩
  · exact absurd hab hPnab
  · -- **Collapse** (Coq `dimP`): `P₂` is central in `P` (it centralizes `P₁` and is abelian), so
    -- `P₂ ≤ Z(P)` and `|P₂| ≤ |Z(P)| = p`; conversely `Ω₁(P₂) = Z(P₁)` has order `p` (`P₁`
    -- extraspecial), so `|P₂| ≥ p`.  Hence `|P₂| = p`, `P₂ = Ω₁(P₂) = Z(P₁) ≤ P₁`, and
    -- `P = P₁ ⊔ P₂ = P₁`, giving `|P| = |P₁| = p³`.
    have : IsCyclic ↥P₂ := hP₂cyc
    -- `|Z(P₁)| = p` (`P₁` extraspecial), and `|Ω₁(P₂).map| = |Z(P₁).map| = p` (`hΩeq`).
    have hΩcard : Nat.card ↥((Omega ↥P₂ p 1).map P₂.subtype) = p := by
      rw [hΩeq, Subgroup.card_map_of_injective P₁.subtype_injective,
        hP₁es.isExtraspecial.center_card]
    -- `P₂ ≤ C_G(P)`: `P₂` centralizes `P₁` (central product) and itself (cyclic ⟹ abelian).
    have hP₂cP : P₂ ≤ Subgroup.centralizer (P : Set G) := by
      rw [hcp.sup_eq]
      exact Subgroup.le_centralizer_iff.mpr (sup_le hcp.le_centralizer_right
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance))
    -- `P₂ ≤ Z(P)` (as a `G`-subgroup): `P₂ ≤ P` and `P₂ ≤ C_G(P)`.
    have hP₂_center : P₂ ≤ (Subgroup.center ↥P).map P.subtype := by
      intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hP₂P hx⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      exact fun z => Subtype.ext
        (Subgroup.mem_centralizer_iff.mp (hP₂cP hx) (z : G) z.2)
    -- `|P₂| = p`: `≤ |Z(P)| = p` (above) and `≥ |Ω₁(P₂).map| = p`.
    have hP₂card : Nat.card ↥P₂ = p := by
      refine le_antisymm ?_ ?_
      · calc Nat.card ↥P₂ ≤ Nat.card ↥((Subgroup.center ↥P).map P.subtype) :=
              Subgroup.card_le_of_le hP₂_center
          _ = Nat.card ↥(Subgroup.center ↥P) := Subgroup.card_map_of_injective P.subtype_injective
          _ = p := hZPcard
      · calc p = Nat.card ↥((Omega ↥P₂ p 1).map P₂.subtype) := hΩcard.symm
          _ ≤ Nat.card ↥P₂ := Subgroup.card_le_of_le (Subgroup.map_subtype_le _)
    -- `Ω₁(P₂) = ⊤` (every element of the order-`p` `P₂` satisfies `g^p = 1`), so
    -- `P₂ = Ω₁(P₂).map = Z(P₁).map ≤ P₁`.
    have hΩtop : Omega ↥P₂ p 1 = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact fun g => Omega.mem_of_pow_eq_one
        (by rw [pow_one]; exact orderOf_dvd_iff_pow_eq_one.mp (hP₂card ▸ orderOf_dvd_natCard g))
    have hP₂P₁ : P₂ ≤ P₁ := by
      have h := hΩeq
      rw [hΩtop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
      rw [h]; exact Subgroup.map_subtype_le _
    -- `P = P₁ ⊔ P₂ = P₁`, so `|P| = |P₁| = p³`.
    rw [hcp.sup_eq, sup_eq_left.mpr hP₂P₁, hP₁card]

/-- **Prop 16.1 forward bridge `hP1eqV`, reduced to the Peterfalvi (8.8) trichotomy residual** — a
type-`P₁` maximal subgroup with `M_F = M_σ` is of type V.

The type-`P` datum is the fully-constructed `typePData_of_isTypeP1_mf_eq_msigma` (`U = ⊥`,
`sorry`-free — the type-V carrier-constructibility milestone); `isTypeV_of_typePData` then reduces
to
the `alternative` disjunction on `H = M_F`.  As for the type-`F` bridge `isTypeI_of_isTypeF`, the
`FittingIsTI M` case is discharged directly (disjunct (a): `M_F#` is a `TI`-subset, via
`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).

The `¬FittingIsTI` case — **Peterfalvi (8.8) / BG Theorem 15.7(e)** (Coq `BGsection15`
`nonTI_Fitting_structure`) — is now discharged in full, so this theorem is complete and axiom-clean.
It splits on the Frobenius divisibility `|W₁| ∣ p − 1` (matching Coq's `Ks = Z₀ → |K| ∣ p.-1`
case analysis):

* `|W₁| ∣ p − 1` holds: disjunct (e2) directly, with `O_{p'}(M_F)` cyclic.
* otherwise the genuine **Singer / `SL₂(p)`** case (e3): `Z ⊓ K* ≠ ⊥` (else the Frobenius engine
  `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot` would give `|K| = |W₁| ∣ p − 1`), hence
  `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`/`defZP`), giving `|O_p(M_F)| = p³`
  (`card_opiCore_eq_prime_cube_singer`) and `|W₁| ∣ p + 1`
  (`card_dvd_succ_of_primeAction_extraspecial`, the symplectic/determinant-one step).

Both branches carry real proofs; this file has no live `sorry`.  (Until 2026-07-19 the two `(e3)`
steps were labelled `-- (sorry 1)` / `-- (sorry 2)` long after they had been discharged, which made
`grep sorry` report phantom gaps — the labels now name their actual content.)

(`hP1neIIIIV`, the sibling `M_F ≠ M_σ ⟹ III/IV` bridge, needs no trichotomy but instead the full
nilpotent `M_F`-complement `U ≠ ⊥`, gated on `M'/M_F` nilpotent.) -/
theorem isTypeV_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeV M := by
  set data := typePData_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf with hdata
  refine isTypeV_of_typePData data rfl ?_
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset (same as the type-`F` bridge).
    exact Or.inl (maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI)
  · -- `¬FittingIsTI` ⟹ disjuncts (e2)/(e3).  The non-TI witness `X₁` (order `p`, `C_G(X₁) ⊄ M`),
    -- the cyclic `O_{p'}(M_F)` (Coq `cycHp'`), and the `M`-normal order-`p` `Z = Ω₁(Z(O_p(M_F)))`
    -- (Coq `oZ`, `exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI`).
    have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
    have hnab := not_isMulCommutative_mf_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf
    obtain ⟨g, p, X₁, -, hp, hpσ, hX₁card, hX₁Mσ, -, hCGnotM, hrank3, -⟩ :=
      S15.exists_inf_conj_fitting_orderP_witness hG hM hTI
    have : Fact p.Prime := ⟨hp⟩
    have hX₁MF : X₁ ≤ S15.MF M := by
      rw [S15.mf_eq_msigma_of_not_fittingIsTI hG hM hTI]; exact hX₁Mσ
    obtain ⟨hpπ, hcyc⟩ :=
      S15.typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF hCGnotM hnab
    have hHMF : data.H = S15.MF M := data.H_eq
    -- Reconstruct a Hall `κ`-subgroup `K` (cyclic), the trivial `(κ ∪ σ)'`-Hall `U = ⊥`, and `K*`.
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro q hq
      simp only [Set.mem_compl_iff, not_not]
      by_cases hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hqσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hq, hqσ⟩)
    have hKcyc : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    -- `|W₁| = [M:M'] = |K|`.
    have hW1K : Nat.card ↥data.W1 = Nat.card ↥K :=
      (data.card_W1_eq_derived_index).trans
        (card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK).symm
    -- The `M`-normal order-`p` `Z ≤ M_F = M_σ` normalized by `K`.
    obtain ⟨Z, hZMF, hZcard, hZnorm, hX₁notZ, hZeq⟩ :=
      S15.exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF hCGnotM
        hrank3 hnab (q := p) hp hpπ
    -- `Z = Ω₁(Z(O_p(M_F)))` (Coq `Z0`), exposed for the type-V Singer `|Z(P)| = p` argument.
    have hZomega : Z = OddOrder.BG.Ch3.S10.omega1CenterInG
        (opiCoreInG ({p} : Set ℕ) (S15.MF M)) p := hZeq rfl
    have hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M := hmf ▸ hZMF
    have hKNZ : K ≤ Subgroup.normalizer (Z : Set G) := hKM.trans hZnorm
    set Kstar : Subgroup G :=
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) with hKstardef
    -- (e2) vs (e3) dichotomy on the Frobenius divisibility `|W₁| ∣ p − 1` (matching Coq's
    -- `Ks = Z₀ → |K| ∣ p-1` split): if it holds, disjunct (e2) directly; otherwise the genuine
    -- Singer/`SL₂(p)` case (e3), where the `K`-action on `Z` is *not* Frobenius so `Z ⊓ K* ≠ ⊥`,
    -- i.e. `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`).
    by_cases hdvd : Nat.card ↥data.W1 ∣ p - 1
    · -- (e2): `|W₁| ∣ p − 1` directly (the cyclic `O_{p'}(M_F)` is `hcyc`).
      exact Or.inr (Or.inl ⟨p, hp, hHMF ▸ hpπ, hdvd, hHMF ▸ hcyc⟩)
    · -- (e3): `¬(|W₁| ∣ p − 1)`, the genuine Singer case.  Then `Z ⊓ K* ≠ ⊥` (else the Frobenius
      -- engine `kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot` would give `|K| = |W₁| ∣ p − 1`),
      -- hence `Z ≤ K* = Z₀ = Z(P)` (Coq `defKs`/`defZP`/`rPle2`/`oZ0`, the genuinely-deep
      -- residual).
      have hZK : Z ⊓ Kstar ≠ ⊥ := fun h => hdvd
        (hW1K ▸ kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot hG hM hP1.1 hKM hK hKstardef hU
          hZMσ hZcard hKNZ h)
      -- `r(O_p(M_F)) ≤ 2` (Coq `rPle2`): faithfulness `K ⊓ C_G(P) = ⊥`
      -- (`kappaHall_inf_centralizer_opiCore_eq_bot`, brick 4) +
      -- `pRank_opiCore_le_two_of_kappaHall`.
      have hpodd : Odd p :=
        hG.odd.of_dvd_nat ((Nat.dvd_of_mem_primeFactors hpπ).trans
          (Subgroup.card_subgroup_dvd_card _))
      have hKp' : ¬ p ∣ Nat.card ↥K := by
        intro hdvdK
        have hpfK : p ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
          exact Nat.mem_primeFactors.mpr ⟨hp, hdvdK, Nat.card_pos.ne'⟩
        exact (S14.kappa_subset_sigmaCompl (hK.primeFactors_card_subset p hpfK)) hpσ
      have hKnormP : K ≤ Subgroup.normalizer
          (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) :=
        hKM.trans (le_normalizer_opiCoreInG_of_le_normalizer ({p} : Set ℕ)
          (S15.maxNilpotentNormalHall_le_normalizer M))
      have hZKstar : Z ≤ Kstar := by
        have hd : Nat.card ↥(Z ⊓ Kstar) ∣ p := hZcard ▸ Subgroup.card_dvd_of_le inf_le_left
        rcases (Nat.dvd_prime hp).mp hd with h1 | hpp
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hZK
        · exact inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left
            (le_of_eq (hZcard.trans hpp.symm)))
      have hrPle2 : pRank ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) p ≤ 2 :=
        pRank_opiCore_le_two_of_kappaHall hG hM hp hpodd hX₁card hX₁MF hrank3 hKp' hKnormP
          (kappaHall_inf_centralizer_opiCore_eq_bot hG hM hP1 hKM hK hKstardef hU hp hX₁card hX₁MF
            hZKstar hZcard hX₁notZ)
          (hW1K ▸ hdvd)
      -- `O_p(M_F)` is non-abelian (`opiCore_singleton_not_isMulCommutative_of_witness`).
      have hPnab : ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) :=
        S15.opiCore_singleton_not_isMulCommutative_of_witness hG hM hp hX₁card hX₁MF hCGnotM hnab
      -- `|Z(P)| = p` (Coq `defZP`, via BG Theorem 1.11): the witness `Z = Ω₁(Z(P))` (`hZomega`)
      -- lies in `K*` (`hZKstar`), so `K` centralizes `Z(P)`, forcing `Z(P) = Ω₁(Z(P))`.
      have hZPcard : Nat.card ↥(Subgroup.center ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M))) = p :=
        card_center_opiCore_eq_prime_of_omega1Center_le_kstar hG hM hP1 hmf hKM hK hKstardef
          hp hpodd hKp' hKnormP (hZomega ▸ hZKstar) (hZomega ▸ hZcard)
      refine Or.inr (Or.inr ⟨p, hp, hHMF ▸ hpπ, ?_, ?_, hHMF ▸ hcyc⟩)
      · -- (e3) conjunct 1: `|O_p(M_F)| = p³`.  All four inputs (`r(P) ≤ 2`, `P` non-abelian,
        -- `P` Sylow of `G`, `|Z(P)| = p`) are discharged, and the `mFT_rank2_Sylow_cprod`
        -- central-product structure (Coq §10.7b) enters via `S10.sylow_structure`.
        exact card_opiCore_eq_prime_cube_singer hG hM hP1 hmf hp hpσ hpπ hrPle2 hPnab hZPcard
      · -- (e3) conjunct 2: `|W₁| ∣ p + 1` via route B (Singer/`SL₂(p)` symplectic divisibility).
        have : Fact p.Prime := ⟨hp⟩
        have hPcard3 : Nat.card ↥(opiCoreInG ({p} : Set ℕ) (S15.MF M)) = p ^ 3 :=
          card_opiCore_eq_prime_cube_singer hG hM hP1 hmf hp hpσ hpπ hrPle2 hPnab hZPcard
        set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
        have hPextra : OddOrder.GroupTheory.IsExtraspecial p ↥P :=
          OddOrder.GroupTheory.IsExtraspecial.of_card_eq_prime_cube hPcard3 (fun h => hPnab ⟨⟨h⟩⟩)
        have hPMσ : P ≤ OddOrder.BG.Ch3.S10.Msigma M :=
          (opiCoreInG_le _ _).trans (S15.maxNilpotentNormalHall_le_Msigma hG hM)
        -- conjugation action `φ : K → Aut P`.
        let φ : ↥K →* MulAut ↥P :=
          (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKnormP)
        have hφ : ∀ (k : ↥K) (x : ↥P), ((φ k x : ↥P) : G) = (k : G) * (x : G) * (k : G)⁻¹ :=
          fun _ _ => rfl
        -- `K* = Z`.
        have hKstarEqZ : Kstar = Z := by
          have hKstarPrime : (Nat.card ↥Kstar).Prime :=
            S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstardef
          have hd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
          have hc : Nat.card ↥Kstar = p :=
            ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hd).symm
          exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hc.trans hZcard.symm))).symm
        -- `Z = Ω₁(Z(P))` as a subgroup of `↥P`-center mapped to `G`.
        have hZmem : ∀ {g : G}, g ∈ Z → ∃ z : ↥P, z ∈ Subgroup.center ↥P ∧ (z : G) = g := by
          intro g hg
          rw [hZomega] at hg
          simp only [OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map,
            Subgroup.coe_subtype] at hg
          obtain ⟨z, hzΩ, hzg⟩ := hg
          exact ⟨z, OddOrder.GroupTheory.omega1OfAbelian_le hzΩ, hzg⟩
        -- `hfpf`: `φ k x = x ⟹ x ∈ commutator P` (`x` centralizes `k`, so lands in `K* = Z`).
        have hfpf : ∀ k : ↥K, k ≠ 1 → ∀ x : ↥P, (φ k) x = x → x ∈ commutator ↥P := by
          intro k hk1 x hfix
          have hkne : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext h)
          have hcm : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
            have h := congrArg Subtype.val hfix; rwa [hφ k x] at h
          have hcomm : (k : G) * (x : G) = (x : G) * (k : G) := mul_inv_eq_iff_eq_mul.mp hcm
          have hxKstar : (x : G) ∈ Kstar := by
            rw [← centralizer_msigma_kappaElement_eq_kstar hG hM hP1.1 hKM hK hKstardef hU k.2 hkne]
            refine Subgroup.mem_inf.mpr ⟨hPMσ x.2, ?_⟩
            rw [Subgroup.mem_centralizer_iff]
            rintro g rfl
            exact hcomm
          obtain ⟨z, hzc, hzx⟩ := hZmem (hKstarEqZ ▸ hxKstar)
          have hzx' : z = x := Subtype.ext hzx
          rw [hPextra.commutator_eq_center, ← hzx']; exact hzc
        -- `hcentZ`: `K` centralizes `Z(P) = commutator P`.
        have hcentZ : ∀ k : ↥K, ∀ z : ↥P, z ∈ commutator ↥P → (φ k) z = z := by
          intro k z hz
          rw [hPextra.commutator_eq_center] at hz
          have hzZ : (z : G) ∈ Z := by
            rw [hZomega]
            simp only [OddOrder.BG.Ch3.S10.omega1CenterInG, Subgroup.mem_map, Subgroup.coe_subtype]
            refine ⟨z, (OddOrder.GroupTheory.mem_omega1OfAbelian).mpr ⟨hz, ?_⟩, rfl⟩
            have hdz : orderOf z ∣ p := by
              have h1 : orderOf (⟨z, hz⟩ : ↥(Subgroup.center ↥P)) ∣
                  Nat.card ↥(Subgroup.center ↥P) := orderOf_dvd_natCard _
              rw [hZPcard] at h1
              rwa [← orderOf_injective (Subgroup.center ↥P).subtype
                Subtype.coe_injective ⟨z, hz⟩] at h1
            exact orderOf_dvd_iff_pow_eq_one.mp hdz
          have hzcK : (z : G) ∈ Subgroup.centralizer (K : Set G) :=
            (hZKstar.trans (hKstardef ▸ inf_le_right)) hzZ
          have hcomm : (k : G) * (z : G) = (z : G) * (k : G) :=
            Subgroup.mem_centralizer_iff.mp hzcK (k : G) k.2
          apply Subtype.ext
          rw [hφ k z, hcomm, mul_inv_cancel_right]
        exact hW1K ▸ OddOrder.GroupTheory.card_dvd_succ_of_primeAction_extraspecial hpodd
          hPextra hPcard3 φ hfpf hcentZ hKcyc hKp' (hW1K ▸ hdvd)

end OddOrder.BG.Ch4.S16



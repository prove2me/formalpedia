-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeP1Criteria
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeP1Criteria
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:34:06.835512+00:00
-- url     : https://prove2.me/theorems/6983cf56-cd4b-4553-9294-73789c5f6087
-- title:
--   BG §16: type-$\mathcal{P}_1$ criteria
-- statement:
--   A part of the §16 type-bridges development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the type-bridges file. It consists of lemmas only, including `isTypeII_of_isTypeP2`, `isTypeV_of_typePData` and results on $\kappa$-Hall subgroups and centralizers of $M_\sigma$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeP1Criteria.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeP1Criteria.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeDataBridges

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **BG Proposition 16.1(b) forward bridge `hP2II`, complete and unconditional** — *every*
type-`P₂` maximal subgroup is of type II.  The two residuals of
`isTypeII_of_isTypeP2_of_derived_typeF` are discharged: `hderF` by `isTypeF_derivedInG_of_isTypeP2`,
and `hderfit` (`(M')_F = M_F`, both `= M_σ`) by
`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`.  No `τ₂(M) = ∅` gate (the earlier
reduction to BG Theorem 15.8 was unnecessary — and `τ₂(M) = ∅` is false for some type-`P₂` `M`,
cf. Corollary 15.9). -/
theorem isTypeII_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  -- `K` cyclic (Theorem A(2) / Lemma 15.1(b), `typeP_auxiliary_structure` conjunct 2).
  obtain ⟨_, hKcyc, _⟩ := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  have := hKcyc
  -- `hderfit`: `(M')_F = M_F` (both `= M_σ`).
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M := by
    rw [maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK, hMFMσ]
  -- `hderF`: `M'` is of type `F`.
  have hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M) :=
    isTypeF_derivedInG_of_isTypeP2 hG hM hP2 hKM hUM hKne hK hU hUne
  exact isTypeII_of_isTypeP2_of_derived_typeF hG hM hP2 hderF hderfit

/-- **Prop 16.1 forward bridge, type V last mile** (Peterfalvi (8.8)): a type-`P` datum with
`U = ⊥` and the Peterfalvi (8.8) trichotomy on `H = M_F` is of type V.  The `alternative`
disjunction is the deep named residual (BG §15.7(c) / Peterfalvi (8.8)). -/
theorem isTypeV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hUbot : data.U = ⊥)
    (halt :
      IsTISubset (sharpSubgroup data.H) (Subgroup.normalizer (data.H : Set G)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥data.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ data.H)) ∨
      (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
        Nat.card ↥(opiCoreInG {p} data.H) = p ^ 3 ∧ Nat.card ↥data.W1 ∣ p + 1 ∧
        IsCyclic ↥(opiCoreInG {p}ᶜ data.H))) :
    IsTypeV M :=
  ⟨{ typeP := data, U_eq_bot := hUbot, alternative := halt }⟩

/-- **`M_σ`-centralizer of a `κ`-element is `K*`** (the prime-action constancy of fixed points): for
a type-`P` maximal `M` with Hall `κ`-subgroup `K` and `K* = M_σ ⊓ C(K)`, every `k ∈ K#` has
`C_{M_σ}(k) = K*`.  `K` acts *primely* on `M_σ` (Proposition 14.2, `typeP_structure` conjunct 1,
`ActsPrimeOn (M_σ) K`), so the fixed subgroup `C_{M_σ}(k) = fixedByElement (M_σ) k` equals
`fixedBy (M_σ) K = M_σ ⊓ C(K) = K*` for every nonidentity `k ∈ K`. -/
theorem centralizer_msigma_kappaElement_eq_kstar [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K] {k : G} (hk : k ∈ K) (hk1 : k ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({k} : Set G) = Kstar := by
  have hprime : OddOrder.BG.Ch3.S13.ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) K :=
    (S14.typeP_structure hG hM hP hKM hK hKstar hU).1
  -- `fixedByElement (M_σ) k = fixedBy (M_σ) K`, both defeq to the centralizer forms.
  have heq := hprime k hk hk1
  rw [hKstar]
  exact heq

/-- **`|K| ∣ p - 1` from `K` acting Frobenius on an `M`-normal order-`p` subgroup** (the
divisibility engine for type-V disjunct (e2), Coq `regZq_dv_q1`): if the Hall `κ`-subgroup `K`
normalizes an order-`p` subgroup `Z ≤ M_σ` with `Z ⊓ K* = ⊥`, then `K` acts on `Z` as a Frobenius
group — every `k ∈ K#` centralizes only `1` in `Z`, since `C_{M_σ}(k) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`) and `Z ⊓ K* = ⊥` — so
`card_dvd_sub_one_of_isFrobeniusAction`
gives `|K| ∣ |Z| - 1 = p - 1`. -/
theorem kappaHall_card_dvd_sub_one_of_inf_kstar_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U Z : Subgroup G} {p : ℕ}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    (hZMσ : Z ≤ OddOrder.BG.Ch3.S10.Msigma M) (hZcard : Nat.card ↥Z = p)
    (hKNZ : K ≤ Subgroup.normalizer (Z : Set G)) (hZK : Z ⊓ Kstar = ⊥) :
    Nat.card ↥K ∣ p - 1 := by
  classical
  let : MulDistribMulAction ↥K ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hKNZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥K ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    have hconj : (u : G) * (z : G) * (u : G)⁻¹ = (z : G) := by
      rw [← h1]; exact congrArg Subtype.val hfix
    have hcomm : (u : G) * (z : G) = (z : G) * (u : G) := mul_inv_eq_iff_eq_mul.mp hconj
    have huK1 : (u : G) ≠ 1 := fun h => hu (Subtype.ext h)
    have hzKstar : (z : G) ∈ Kstar := by
      rw [← centralizer_msigma_kappaElement_eq_kstar hG hM hP hKM hK hKstar hU u.2 huK1]
      exact Subgroup.mem_inf.mpr ⟨hZMσ z.2,
        Subgroup.mem_centralizer_iff.mpr (fun x hx => by
          rw [Set.mem_singleton_iff] at hx; subst hx; exact hcomm)⟩
    have hz1 : (z : G) = 1 := by
      have hmem : (z : G) ∈ Z ⊓ Kstar := Subgroup.mem_inf.mpr ⟨z.2, hzKstar⟩
      rw [hZK, Subgroup.mem_bot] at hmem; exact hmem
    exact hz (Subtype.ext hz1)
  have hdvd := OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rwa [hZcard] at hdvd

/-- **`K` acts faithfully on `P = O_p(M_F)` in the type-V Singer case** (Coq `defKs`/`defZP`:
`K* = Z` forces `C_K(P) = 1`).  For a type-`P₁` maximal `M` with Hall `κ`-subgroup `K`,
`K* = M_σ ⊓ C(K)`, and an order-`p` subgroup `Z ≤ K*` with `X₁ ⊄ Z` (the non-TI witness `X₁` of
order
`p`, `X₁ ≤ M_F`), the centralizer of `P` in `K` is trivial.

A nonidentity `x ∈ K ⊓ C_G(P)` centralizes `P ⊇ X₁`, so `X₁ ≤ M_σ ⊓ C_G(x) = K*`
(`centralizer_msigma_kappaElement_eq_kstar`).  But `K* = Z`: `|K*|` is prime
(`kstar_card_prime_of_inputs`), `Z ≤ K*`, and `|Z| = p`, so `|K*| = p` and `Z = K*`.  Hence
`X₁ ≤ Z`, contradicting `X₁ ⊄ Z`.  This is the faithfulness input `K ⊓ C_G(P) = ⊥` to
`pRank_opiCore_le_two_of_kappaHall` (`rPle2`) for the type-V disjunct-3 (Singer/`SL₂(p)`) case. -/
theorem kappaHall_inf_centralizer_opiCore_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    [IsCyclic ↥K]
    {p : ℕ} {X₁ Z : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ S15.MF M)
    (hZKstar : Z ≤ Kstar) (hZcard : Nat.card ↥Z = p) (hX₁notZ : ¬ X₁ ≤ Z) :
    K ⊓ Subgroup.centralizer (↑(opiCoreInG ({p} : Set ℕ) (S15.MF M)) : Set G) = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (S15.MF M) with hPdef
  -- `K* = Z`: `|K*|` prime, `Z ≤ K*`, `|Z| = p`.
  have hKstarPrime : (Nat.card ↥Kstar).Prime :=
    S15.kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have hKstarEqZ : Kstar = Z := by
    have hdvd : p ∣ Nat.card ↥Kstar := hZcard ▸ Subgroup.card_dvd_of_le hZKstar
    have hcard : Nat.card ↥Kstar = p := ((Nat.prime_dvd_prime_iff_eq hp hKstarPrime).mp hdvd).symm
    exact (Subgroup.eq_of_le_of_card_ge hZKstar (le_of_eq (hcard.trans hZcard.symm))).symm
  -- `X₁ ≤ P` (`p`-subgroup of the nilpotent `M_F`).
  have hMFnil : Group.IsNilpotent ↥(S15.MF M) := S15.maxNilpotentNormalHall_isNilpotent M
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- A nonidentity `x ∈ K ⊓ C_G(P)` forces `X₁ ≤ K* = Z`, contradicting `X₁ ⊄ Z`.
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  by_contra hx1
  obtain ⟨hxK, hxCP⟩ := Subgroup.mem_inf.mp hx
  refine hX₁notZ ?_
  rw [← hKstarEqZ,
    ← centralizer_msigma_kappaElement_eq_kstar hG hM hP1.1 hKM hK hKstar hU hxK hx1]
  refine le_inf (hX₁MF.trans (S15.maxNilpotentNormalHall_le_Msigma hG hM)) (fun g hg => ?_)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (Subgroup.mem_centralizer_iff.mp hxCP g (hX₁P hg)).symm

end OddOrder.BG.Ch4.S16



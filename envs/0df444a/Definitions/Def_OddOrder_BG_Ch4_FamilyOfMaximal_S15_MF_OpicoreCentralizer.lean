-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizer
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:12:45.92336+00:00
-- url     : https://prove2.me/theorems/3cc59c88-68d0-43b7-95a3-5025b8aec9ef
-- title:
--   BG §15: $O_p$-core centralizer
-- statement:
--   A part of the TI-failure development of §15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the TI-failure file. It consists of lemmas only, including that the rank of $M_F$ is two when abelian and $F(M)$ is not TI, Hall-subgroup and coprimality-of-index lemmas, and that the $\kappa$-Hall subgroup has prime order for type $\mathcal{P}_2$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/OpicoreCentralizer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_PisetBetaDisjoint
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_OpicoreCentralizerBasic

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 15.7(e1), the rank claim** (mmd L4249, *"`H` is abelian of rank two"*): when
`F(M)` is not `TI` and `H = M_F` is abelian, `rank H = 2`.

`≤ 2`: the non-TI witness gives an order-`p` subgroup `X₁ ≤ M_F` with `rank (M_F ⊓ C_G(X₁)) < 3`
(BG's *"`C_H(X₁)` is abelian of rank less than 3"*), and `M_F` abelian makes `M_F ≤ C_G(X₁)`, so the
intersection is `M_F` itself.  `≥ 2`: `O_p(M_F)` is abelian (inside `M_F`) and **not** cyclic
(`not_isCyclic_opiCore_mf_of_orderP_le_conj`, Coq `not_cycMp`), so
`2 ≤ pRank_p O_p(M_F) ≤ rank M_F`.

Extracted from the inline argument of `S16`'s `isTypeI_of_isTypeF`, which now cites this. -/
theorem rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) (habel : IsMulCommutative ↥(MF M)) :
    rank ↥(MF M) = 2 := by
  classical
  obtain ⟨g, p, X₁, hgM, hp, -, hX₁card, hX₁Mσ, hX₁cMσ, -, hrank3, -⟩ :=
    exists_inf_conj_fitting_orderP_witness hG hM hnotTI
  have : Fact p.Prime := ⟨hp⟩
  have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hnotTI
  have hX₁MF : X₁ ≤ MF M := le_trans hX₁Mσ (le_of_eq hMFeq.symm)
  have hX₁cMF : X₁ ≤ MulAut.conj g • MF M := by rw [hMFeq]; exact hX₁cMσ
  -- `p` is odd (`p = |X₁|` divides the odd `|G|`).
  have hpOdd : Odd p := by
    have hpdvdG : p ∣ Nat.card G := hX₁card ▸ Subgroup.card_subgroup_dvd_card X₁
    rcases hp.eq_two_or_odd' with rfl | h
    · exact absurd (even_iff_two_dvd.mpr hpdvdG) (Nat.not_even_iff_odd.mpr hG.odd)
    · exact h
  have hcommMF : ∀ a b : ↥(MF M), a * b = b * a := isMulCommutative_iff.mp habel
  -- `≤ 2`: `M_F` abelian ⟹ `M_F ≤ C_G(X₁)`, so the witness bound applies to `M_F` itself.
  have hMFcentr : MF M ≤ Subgroup.centralizer (X₁ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    simpa using congrArg Subtype.val (hcommMF ⟨y, hX₁MF hy⟩ ⟨a, ha⟩)
  have hle3 : rank ↥(MF M) < 3 := (inf_eq_left.mpr hMFcentr) ▸ hrank3
  -- `≥ 2`: `O_p(M_F)` is abelian and noncyclic.
  have hOpMF : opiCoreInG ({p} : Set ℕ) (MF M) ≤ MF M := opiCoreInG_le {p} (MF M)
  have hcommOp : ∀ x y : ↥(opiCoreInG ({p} : Set ℕ) (MF M)), x * y = y * x := fun x y =>
    Subtype.ext (by
      simpa using congrArg Subtype.val (hcommMF ⟨(x : G), hOpMF x.2⟩ ⟨(y : G), hOpMF y.2⟩))
  have hOpnc : ¬ IsCyclic ↥(opiCoreInG ({p} : Set ℕ) (MF M)) :=
    not_isCyclic_opiCore_mf_of_orderP_le_conj hG hM hp hgM hX₁card hX₁MF hX₁cMF
  have h2pRank : 2 ≤ pRank ↥(opiCoreInG ({p} : Set ℕ) (MF M)) p :=
    two_le_pRank_of_comm_isPGroup_not_isCyclic hpOdd hcommOp
      (isPGroup_opiCoreInG_singleton (MF M)) hOpnc
  have hge2 : 2 ≤ rank ↥(MF M) :=
    le_trans (le_trans h2pRank (pRank_le_rank p))
      (rank_le_of_injective (Subgroup.inclusion_injective hOpMF))
  omega

/-- **`maxNilpotentNormalHall N` is `M`-normal when `N ◁ M`** (`N ≤ M`).  `maxNilpotentNormalHall N`
is a priori only normal in `N`; this upgrades it to normality in the larger `M`: each `g ∈ M`
conjugates `N` to itself (`N ◁ M`), and `maxNilpotentNormalHall_pointwise_smul` transports this to
`maxNilpotentNormalHall N`, so `M ≤ N_G(maxNilpotentNormalHall N)`. -/
theorem maxNilpotentNormalHall_subgroupOf_normal_of_le_of_normal [Finite G] {N M : Subgroup G}
    (hNM : N ≤ M) (hnorm : (N.subgroupOf M).Normal) :
    ((maxNilpotentNormalHall N).subgroupOf M).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((maxNilpotentNormalHall_le N).trans hNM)]
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hnorm hg
  have hNfix : N.map (MulAut.conj g).toMonoidHom = N :=
    OddOrder.BG.Ch1.S03f.map_conj_eq_self_of_mem_normalizer hgN
  have hNsmul : (MulAut.conj g) • N = N := by
    rw [pointwise_mulAut_smul_eq_map]; exact hNfix
  have key := maxNilpotentNormalHall_pointwise_smul (MulAut.conj g) N
  rw [hNsmul, pointwise_mulAut_smul_eq_map] at key
  exact OddOrder.BG.Ch1.S03f.mem_normalizer_of_map_conj_eq key

/-- **Coprime order/index ⟹ self-`primeFactors`-Hall**: if `H ≤ V` and `|H|` is coprime to the
relative index `[V : H]`, then `H` is a `π(H)`-Hall subgroup of `V` (the `π = π(H)` instance of
`IsHallSubgroup`).  This is the BG-side mirror of the Peterfalvi helper
`isHall_subgroupOf_primeFactors_of_coprime_index`. -/
theorem isHallSubgroup_primeFactors_of_coprime_index [Finite G] {V H : Subgroup G}
    (hHV : H ≤ V) (hcop : Nat.Coprime (Nat.card ↥H) ((H.subgroupOf V).index)) :
    Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors (H.subgroupOf V) := by
  have hcard : Nat.card ↥(H.subgroupOf V) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHV).toEquiv
  refine ⟨fun p hp => by rw [hcard] at hp; exact hp, fun p hp hpπ => ?_⟩
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (Nat.mem_primeFactors.mp hpπ).2.1
    (Nat.mem_primeFactors.mp hp).2.1
  exact absurd (Nat.dvd_one.mp hp1) (Nat.mem_primeFactors.mp hp).1.ne_one

/-- **Hall transitivity (coprime form)**: for `L ≤ Mid ≤ M`, if `|L|` is coprime to `[Mid : L]`
and `|Mid|` is coprime to `[M : Mid]`, then `|L|` is coprime to `[M : L]`.  The relative index is
multiplicative (`relIndex_mul_relIndex`), `|L| ∣ |Mid|`, and `|Mid|` coprime `[M:Mid]` transfers
to `|L|`. -/
theorem coprime_card_index_subgroupOf_trans [Finite G] {L Mid M : Subgroup G}
    (hLMid : L ≤ Mid) (hMidM : Mid ≤ M)
    (hL : Nat.Coprime (Nat.card ↥L) ((L.subgroupOf Mid).index))
    (hMid : Nat.Coprime (Nat.card ↥Mid) ((Mid.subgroupOf M).index)) :
    Nat.Coprime (Nat.card ↥L) ((L.subgroupOf M).index) := by
  have hmul : (L.subgroupOf Mid).index * (Mid.subgroupOf M).index = (L.subgroupOf M).index := by
    have h := Subgroup.relIndex_mul_relIndex L Mid M hLMid hMidM
    simpa only [Subgroup.relIndex] using h
  rw [← hmul]
  exact Nat.Coprime.mul_right hL (hMid.coprime_dvd_left (Subgroup.card_dvd_of_le hLMid))

/-- **`(M')_F = M_σ` for type-`P₂`, unconditional** (Coq `defM'F`, BGsection16.v l.1135; the
`M'`_\F = H` conjunct of `of_typeII`).  For a type-`P₂` maximal `M` with cyclic `κ`-Hall `K`, the
`F`-core of the derived subgroup `M' = M^{(1)}` is exactly `M_σ` — with **no** `τ₂(M) = ∅`
hypothesis.

The argument is elementary (and *avoids* the `τ₂(M) = ∅` route, which is moreover false for some
type-`P₂` `M`, cf. Corollary 15.9's `N ∈ ℳ_𝓟₂` with `r ∈ τ₂(N)`):

* `⊆`: `M' = M^{(1)}` complements the cyclic `κ`-Hall `K` in `M`
  (`typeP_derivedInG_isComplement_kappaHall`), so `M'` is a `κ(M)'`-Hall subgroup of `M`.  Hence
  `maxNilpotentNormalHall M'`, Hall in `M'` by `maxNilpotentNormalHall_isHall`, is — by Hall
  transitivity — a nilpotent normal Hall subgroup of `M`, so `≤ M_F = M_σ`
  (`le_maxNilpotentNormalHall`, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`).
* `⊇`: `M_σ` is a nilpotent normal Hall subgroup of `M'` (`[M':M_σ] ∣ [M:M_σ]`).

This discharges both the `hderfit` (`maxNilpotentNormalHall M' = maxNilpotentNormalHall M`) and the
`TypeFData.H_eq` inputs of the type-`P₂ ⟹ II` bridge. -/
theorem maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    maxNilpotentNormalHall (derivedInG M) = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have hMσM' : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMσnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    msigma_isNilpotent_of_isTypeP2 hG hM hP2
  have hMσnormM : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hM'normM : ((derivedInG M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hM'M]
    exact OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M
  -- `M_F = M_σ` for type-`P₂` (`M_σ` nilpotent).
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hMσnil
  -- `M' = M^{(1)}` complements the `κ`-Hall `K`, hence is `κ'`-Hall in `M`.
  have hcompl := typeP_derivedInG_isComplement_kappaHall hG hM (isTypeP_of_isTypeP2 hP2) hKM hK
  have hM'cop : Nat.Coprime (Nat.card ↥(derivedInG M)) (((derivedInG M).subgroupOf M).index) := by
    have hcop_BA : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
        (Nat.card ↥((derivedInG M).subgroupOf M)) := by
      have h := hK.coprime_index
      rwa [hcompl.index_eq_card] at h
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv, hcompl.symm.index_eq_card]
    exact hcop_BA.symm
  refine le_antisymm ?_ ?_
  · -- `⊆`: `maxNilpotentNormalHall M'` is nilpotent normal Hall in `M`, hence `≤ M_F = M_σ`.
    have hLM' : maxNilpotentNormalHall (derivedInG M) ≤ derivedInG M :=
      maxNilpotentNormalHall_le (derivedInG M)
    have hLM : maxNilpotentNormalHall (derivedInG M) ≤ M := hLM'.trans hM'M
    have : Group.IsNilpotent ↥(maxNilpotentNormalHall (derivedInG M)) :=
      maxNilpotentNormalHall_isNilpotent (derivedInG M)
    -- `maxNilpotentNormalHall M'` is coprime to `[M':·]` (Hall in `M'`).
    have hLcopMid : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (derivedInG M)))
        (((maxNilpotentNormalHall (derivedInG M)).subgroupOf (derivedInG M)).index) := by
      have h := (maxNilpotentNormalHall_isHall (derivedInG M)).coprime_index
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM').toEquiv] at h
    -- transitivity ⟹ coprime to `[M:·]`.
    have hLcopM : Nat.Coprime (Nat.card ↥(maxNilpotentNormalHall (derivedInG M)))
        (((maxNilpotentNormalHall (derivedInG M)).subgroupOf M).index) :=
      coprime_card_index_subgroupOf_trans hLM' hM'M hLcopMid hM'cop
    have hLnorm : ((maxNilpotentNormalHall (derivedInG M)).subgroupOf M).Normal :=
      maxNilpotentNormalHall_subgroupOf_normal_of_le_of_normal hM'M hM'normM
    have hLnil : Group.IsNilpotent ↥((maxNilpotentNormalHall (derivedInG M)).subgroupOf M) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLM).symm
    have hLhall := isHallSubgroup_primeFactors_of_coprime_index hLM hLcopM
    calc maxNilpotentNormalHall (derivedInG M)
        ≤ maxNilpotentNormalHall M := le_maxNilpotentNormalHall hLM hLnorm hLnil hLhall
      _ = OddOrder.BG.Ch3.S10.Msigma M := hMFMσ
  · -- `⊇` : `M_σ` is a nilpotent normal Hall subgroup of `M'`.
    refine le_maxNilpotentNormalHall hMσM' ?_ ?_ ?_
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hMσM']
      exact hM'M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hMσM).mp hMσnormM)
    · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMσM').symm
    · -- `M_σ` Hall in `M'`.
      have hHallM : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M)
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) :=
        OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
      have hcard' : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM').toEquiv
      have hcardM : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
          Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
      have hidxdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
        have e1 := Subgroup.card_mul_index
          ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M))
        have e2 := Subgroup.card_mul_index ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        rw [hcard'] at e1; rw [hcardM] at e2
        have hM'dvdM : Nat.card ↥(derivedInG M) ∣ Nat.card ↥M := by
          have h := Subgroup.card_subgroup_dvd_card ((derivedInG M).subgroupOf M)
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv] at h
        have hmul : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf (derivedInG M)).index ∣
            Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) *
            ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index := by
          rw [e1, e2]; exact hM'dvdM
        exact (mul_dvd_mul_iff_left (Nat.card_pos
          (α := ↥(OddOrder.BG.Ch3.S10.Msigma M))).ne').mp hmul
      refine ⟨fun p hp => by rwa [hcard'] at hp, fun p hp hpπ => ?_⟩
      have hpidxM : p ∈ (((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index).primeFactors := by
        obtain ⟨hpp, hpd, -⟩ := Nat.mem_primeFactors.mp hp
        exact Nat.mem_primeFactors.mpr ⟨hpp, hpd.trans hidxdvd, Subgroup.index_ne_zero_of_finite⟩
      have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := hHallM.1 p (by rw [hcardM]; exact hpπ)
      exact hHallM.2 p hpidxM hpσ

/-- **BG Theorem 14.7(f) / Proposition 14.2(g), type-`P₂` case** (mmd L4264, the first sentence of
Theorem 15.8's proof: *"By Theorem 14.7(f), `|K| = q`"*): for a type-`P₂` maximal subgroup `M` and a
Hall `κ(M)`-subgroup `K ≤ M`, the order `|K|` is prime.

This is the `∃ q, q.Prime ∧ |K| = q` half of the Proposition 14.2(g) clause packaged inside
`typeP_structure`, specialised to the *given* `K` (rather than the partner's `Kstar`, as in
`kstar_card_prime_of_inputs`).  Proof: build the required Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of the
solvable `M` by Hall's theorem (`Ch03.hall_E_exists`) and set `Kstar = C_{M_σ}(K)`; then the
`IsTypeP2 M →` conjunct of `typeP_structure` delivers `∃ q, q.Prime ∧ Nat.card ↥K = q`. -/
theorem card_kappaHall_prime_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) :
    ∃ q : ℕ, q.Prime ∧ Nat.card ↥K = q := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A Hall `(κ(M) ∪ σ(M))'`-subgroup `U` of the solvable `M` (Hall's theorem), lifted to an
  -- ambient `U' ≤ M` with `(U'.map).subgroupOf M` Hall (as in `exists_typeP_data`).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `typeP_structure` on `M` with the *given* `K`; its `IsTypeP2 M →` conjunct is
  -- `σ(M) = β(M) ∧ ∃ q, q.Prime ∧ Nat.card ↥K = q ∧ IsTISubset …`.
  obtain ⟨_hσβ, q, hq, hKq, _hTI⟩ :=
    (S14.typeP_structure hG hM hP2.1 hKM hK rfl hU).2.2.2.2.1 hP2
  exact ⟨q, hq, hKq⟩

/-- **Phase B foundation of BG Theorem 15.8** (Coq `Ptype_embedding` step): the type-`P₂`
maximal `M`'s partner `M*` — realized as any maximal `Mstar ∈ 𝓜(C(K))` — is type-`P`, has
`κ(Mstar)`-Hall `Ks := M_σ ⊓ C(K)`, and satisfies `K = Mstar_σ ⊓ C(Ks)`.

Proof: `typeP_duality` supplies the unique nonconjugate type-`P` partner `Mst` with exactly this
structure; `typeP_structure` (conjunct 6, with `K ∈ ℰ_q¹`) gives `𝓜(C(K)) = {Mst}`, so the
given `Mstar ∈ 𝓜(C(K))` equals `Mst`. -/
theorem typeP2_partner_structure_of_mem [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G))) :
    S14.IsTypeP Mstar ∧
      Ch03.IsHallSubgroup (S14.kappa Mstar)
        ((OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)).subgroupOf Mstar) ∧
      K = OddOrder.BG.Ch3.S10.Msigma Mstar ⊓ Subgroup.centralizer
        ((OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) :
          Subgroup G) : Set G) ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤ Mstar := by
  classical
  have hP : S14.IsTypeP M := hP2.1
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstardef
  obtain ⟨q, hqprime, hKcard⟩ := card_kappaHall_prime_of_isTypeP2 hG hM hP2 hKM hK
  have : Fact q.Prime := ⟨hqprime⟩
  have hKcyc : IsCyclic ↥K := isCyclic_of_prime_card hKcard
  have hKelemq : K ∈ elemAbelianOfRank G q 1 :=
    mem_elemAbelianOfRank.mpr
      ⟨Subgroup.IsElementaryAbelian.of_card_prime hKcard, by rw [hKcard, pow_one]⟩
  -- The unique nonconjugate type-`P` partner `Mst` (Theorem 14.7 / `typeP_duality`).
  obtain ⟨Mst, hMstprop, _hMstuniq⟩ := (S14.typeP_duality hG hM hP hKM hK hKstardef).2.2
  obtain ⟨hMstmax, hMstP, _hMnc, hMstpair, _hZcyc, _hZti, _hP2or, _hcover⟩ := hMstprop
  -- `𝓜(C(K)) = {Mst}` (`typeP_structure` conjunct 6 for `Mst`, rank-one `K ∈ ℰ_q¹`).
  have huniqMst : maximalSubgroupsContaining (Subgroup.centralizer (K : Set G)) = {Mst} := by
    have hMstsol : Group.IsSolvable ↥Mst := hG.isSolvable_of_mem_maximalSubgroups hMstmax
    obtain ⟨UMst, hUMsthall⟩ : ∃ UMst : Subgroup G, Ch03.IsHallSubgroup
        ((S14.kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (UMst.subgroupOf Mst) := by
      obtain ⟨U', hU'hall, -⟩ := Ch03.hall_D (G := ↥Mst)
        (π := (S14.kappa Mst ∪ OddOrder.BG.Ch3.S10.sigma Mst)ᶜ) (U := (⊥ : Subgroup ↥Mst))
        (fun p hp => by simp at hp)
      have hUeq : (U'.map Mst.subtype).subgroupOf Mst = U' :=
        Subgroup.comap_map_eq_self_of_injective Mst.subtype_injective U'
      exact ⟨U'.map Mst.subtype, by rw [hUeq]; exact hU'hall⟩
    exact (S14.typeP_structure hG hMstmax hMstP hMstpair.1 hMstpair.2.1 hMstpair.2.2
      hUMsthall).2.2.2.2.2.1 q hqprime K hKelemq le_rfl
  -- `Mstar = Mst`, so it inherits `Mst`'s partner structure.
  have hMstarEq : Mstar = Mst := by
    have hmem : Mstar ∈ ({Mst} : Set (Subgroup G)) := huniqMst ▸ hMstar
    exact Set.eq_of_mem_singleton hmem
  subst hMstarEq
  exact ⟨hMstP, hMstpair.2.1, hMstpair.2.2, hMstpair.1⟩

/-- **Phase A of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, up to `cKA`): from the
σ(H)′-Hall `E`-setup of a maximal `H` (the Corollary 14.12 signalizer neighbour supplied by
`typeP2_neighbor_is_typeF_of_mem`), a `κ`-Hall `K ⊆ F(E)`, and a prime `q₁ ∈ τ₂(H)`,
there is a rank-2 elementary abelian `A ≤ E` for `q₁` that centralizes `K`.

Proof (Coq `cKA`): extract `A ∈ ℰ²_{q₁}(E)` (`exists_elemAb_rank_two_le_E_of_tau2`); then
`A ⊴ E` (`elemAb_normal_in_E_of_tau2`) and `A` is a `q₁`-group, so `A ⊆ F(E)`
(`le_fittingInG_of_normal_isPiSubgroup_singleton`).  `F(E)` is a nilpotent σ(H)′-subgroup of `H`,
hence abelian (`nilpotent_sigmaComplement_abelian`, BG Cor 12.10).  As `A, K ⊆ F(E)` abelian,
`A ⊆ C(K)`. -/
theorem exists_rank2_elemAb_le_centralizer_kappa_of_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {H K E E₁ E₂ E₃ : Subgroup G}
    (hEsetup : SubgroupESetup H E E₁ E₂ E₃)
    (hKFE : K ≤ OddOrder.BG.Ch2.S08.fittingInG E)
    {q1 : ℕ} (hq1prime : q1.Prime) (hq1 : q1 ∈ tau2 H) :
    ∃ A : Subgroup G, A ∈ elemAbelianOfRank G q1 2 ∧ A ≤ E ∧
      A ≤ Subgroup.centralizer (K : Set G) := by
  classical
  have : Fact q1.Prime := ⟨hq1prime⟩
  obtain ⟨A, hA_elem, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hEsetup hq1
  refine ⟨A, hA_elem, hAE, ?_⟩
  -- `A ⊴ E` (Coq `nsAD`).
  have hEnA : E ≤ Subgroup.normalizer (A : Set G) :=
    ((elemAb_normal_in_E_of_tau2 hG hEsetup hq1 hA_elem hAE).1).1
  have hAnormE : (A.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mpr hEnA
  -- `A` is a `q₁`-group, so `A ⊆ F(E)`.
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA_elem
  have hApi : Subgroup.IsPiSubgroup ({q1} : Set ℕ) A :=
    isPiSubgroup_singleton_of_isPGroup hAea.isPGroup
  have hAFE : A ≤ OddOrder.BG.Ch2.S08.fittingInG E :=
    OddOrder.BG.Ch2.S08.le_fittingInG_of_normal_isPiSubgroup_singleton hAE hAnormE hApi
  -- `F(E)` is a nilpotent σ(H)′-subgroup of `H`, hence abelian (Coq `sigma'_nil_abelian`).
  have hFEnil : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent E
  have hFEleH : OddOrder.BG.Ch2.S08.fittingInG E ≤ H :=
    (OddOrder.BG.Ch2.S08.fittingInG_le E).trans hEsetup.E_le
  have hFEpi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma H)ᶜ)
      (OddOrder.BG.Ch2.S08.fittingInG E) := fun p hp =>
    hEsetup.isPiGroup_sigma_compl hG p
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (OddOrder.BG.Ch2.S08.fittingInG_le E))
        Nat.card_pos.ne' hp)
  have hFEab : IsMulCommutative ↥(OddOrder.BG.Ch2.S08.fittingInG E) :=
    (nilpotent_sigmaComplement_abelian hG hEsetup).1 _ hFEleH hFEpi hFEnil
  -- `A, K ⊆ F(E)` abelian ⟹ `A ⊆ C(K)`.
  exact le_centralizer_of_le_of_le hFEab hAFE hKFE

/-- **Phase D core of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, the `apply/pgroupP` step,
BGsection15.v:1383--1392): for a maximal `M` with an abelian Hall `(κ(M)∪σ(M))'`-subgroup `U ≤ M`
(Proposition 14.2(a); `κ`-Hall `K` normalizing `U`), *every* prime `r ∈ τ₂(M)` that divides `|U|`
has `C_G(U) ≤ M`.

This is the reusable per-prime heart of the final `τ₂(M) = ∅` argument: given the escape witness
`¬(C_G(U) ≤ M)`, it forces `τ₂(M)` to contain no such prime.

Proof (Coq): `r ∈ τ₂(M) ⊆ σ(M)'` and `r ∉ κ(M)` (κ-primes have `pRank ≤ 1`, `r` has `pRank 2`),
so `r ∈ (κ(M)∪σ(M))'`, the prime class of `U`.  Take a §12 `E`-setup with `M_σ`-complement `E ⊇ U`
(`exists_subgroupESetup_with_le`, `U` a `σ(M)'`-subgroup), and a rank-2 `B ∈ ℰ²_r(E)`
(`exists_elemAb_rank_two_le_E_of_tau2`).  Then `B ⊴ E` (`elemAb_normal_in_E_of_tau2`) and
`C_G(B) ≤ E ≤ M` (`centralizer_le_E_of_tau2`, = Corollary 12.6(b)).  Inside `↥E`, `B.subgroupOf E`
is a *normal* `(κ∪σ)'`-subgroup and `U.subgroupOf E` is a `(κ∪σ)'`-Hall (transferred from
`hU`), so `B ⊆ U` (`Subgroup.IsPiGroup.normal_le_hall`, Coq `normal_sub_max_pgroup`).  Hence
`C_G(U) ≤ C_G(B) ≤ M`. -/
theorem centralizer_kappaCompl_le_of_mem_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M U K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (_hKM : K ≤ M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (_hKNU : K ≤ Subgroup.normalizer (U : Set G))
    {r : ℕ} (hrprime : r.Prime) (hr : r ∈ tau2 M) (_hrU : r ∈ piSet U) :
    Subgroup.centralizer (U : Set G) ≤ M := by
  classical
  have : Fact r.Prime := ⟨hrprime⟩
  -- `r ∉ κ(M)`: κ-primes lie in `τ₁ ∪ τ₃` (`pRank ≤ 1`), but `r ∈ τ₂` has `pRank = 2`.
  have hrκ : r ∉ kappa M := by
    intro hrk
    rcases kappa_subset_tau1_union_tau3 hrk with h1 | h3
    · have := tau1_pRank_eq_one h1; have := tau2_pRank_eq_two hr; omega
    · have := tau3_pRank_eq_one h3; have := tau2_pRank_eq_two hr; omega
  have hrσ : r ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hr
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := fun h => h.elim hrκ hrσ
  -- `U` is a `σ(M)'`-subgroup (its prime class `(κ∪σ)'` is contained in `σ'`).
  have hU_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M)ᶜ) U := by
    intro p hp
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
    exact fun hpσ => hU.1 p hp (Or.inr hpσ)
  -- A §12 `E`-setup with `M_σ`-complement `E ⊇ U`.
  obtain ⟨E, E₁, E₂, E₃, hEsetup, hUE, _hEpi⟩ :=
    exists_subgroupESetup_with_le hG hM hUM hU_pi
  -- A rank-2 elementary abelian `B ∈ ℰ²_r(E)`.
  obtain ⟨B, hB_elem, hBE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG hEsetup hr
  -- `C_G(B) ≤ E ≤ M` (Cor 12.6(b)).
  have hCBE : Subgroup.centralizer (B : Set G) ≤ E :=
    (centralizer_le_E_of_tau2 hG hEsetup hr hB_elem hBE).1
  have hCBM : Subgroup.centralizer (B : Set G) ≤ M := hCBE.trans hEsetup.E_le
  -- `B ⊴ E` (Coq `nsBUK`).
  have hEnB : E ≤ Subgroup.normalizer (B : Set G) :=
    ((elemAb_normal_in_E_of_tau2 hG hEsetup hr hB_elem hBE).1).1
  have hBnormE : (B.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mpr hEnB
  -- `B ⊆ U`: `B.subgroupOf E` is a normal `(κ∪σ)'`-subgroup of `↥E`, and `U.subgroupOf E` is a
  -- `(κ∪σ)'`-Hall of `↥E`, so the normal π-subgroup lands inside the Hall.
  have hBU : B ≤ U := by
    -- `B` is a `{r}`-group with `r ∈ (κ∪σ)'`, hence a `(κ∪σ)'`-group.
    have hB_pi : Ch03.Subgroup.IsPiGroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) B := by
      intro p hp
      obtain ⟨hae, hcard⟩ := mem_elemAbelianOfRank.mp hB_elem
      have hpr : p = r := by
        have hpd : p ∈ (r ^ 2).primeFactors := hcard ▸ hp
        rw [Nat.primeFactors_prime_pow (by norm_num) hrprime, Finset.mem_singleton] at hpd
        exact hpd
      exact hpr ▸ hrκσ
    have hB_piE : Ch03.Subgroup.IsPiGroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        (B.subgroupOf E) := Ch03.Subgroup.IsPiGroup.subgroupOf hBE hB_pi
    -- `U.subgroupOf E` is a `(κ∪σ)'`-Hall of `↥E`: prime factors of `|U|` stay in the class, and
    -- `[E : U] ∣ [M : U]` has no primes in the class.
    have hUhallE : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        (U.subgroupOf E) := by
      refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUE).toEquiv] at hp
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at hp
        exact hU.1 p hp
      · have hdvd : (U.subgroupOf E).index ∣ (U.subgroupOf M).index := by
          have hmul : U.relIndex E * E.relIndex M = U.relIndex M :=
            Subgroup.relIndex_mul_relIndex U E M hUE hEsetup.E_le
          exact ⟨E.relIndex M, hmul.symm⟩
        refine hU.2 p ?_ hpπ
        rw [Nat.mem_primeFactors] at hp ⊢
        exact ⟨hp.1, hp.2.1.trans hdvd, Subgroup.index_ne_zero_of_finite⟩
    have := (hB_piE.normal_le_hall hUhallE)
    intro x hx
    have hxE : x ∈ E := hBE hx
    have : (⟨x, hxE⟩ : ↥E) ∈ U.subgroupOf E := this (Subgroup.mem_subgroupOf.mpr hx)
    exact Subgroup.mem_subgroupOf.mp this
  -- `C_G(U) ≤ C_G(B) ≤ M`.
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBU)).trans hCBM

/-- **BG Theorem 15.8, final `τ₂(M) = ∅` step for primes** (Coq `tau2_P2type_signalizer`,
BGsection15.v:1383, the `pgroupP` conclusion): under the signalizer escape witness
`¬(C_G(U) ≤ M)`, no *prime* lies in `τ₂(M)`.

Proof: for a prime `r ∈ τ₂(M)`, `r ∣ |M|` (positive `pRank`) and `r ∈ (κ(M)∪σ(M))'`, so `r ∣ |U|`
(`U` is the `(κ∪σ)'`-Hall of `M`, whose order carries the full `r`-part of `|M|`); then
`centralizer_kappaCompl_le_of_mem_tau2` gives `C_G(U) ≤ M`, contradicting the escape witness.

(Stated in prime form `∀ r, r.Prime → r ∉ τ₂(M)`, matching how the repo threads `τ₂` primality
throughout §12; the literal set-equality `τ₂(M) = ∅` additionally rules out composite labels via
the `pRank`-of-non-prime degeneracy, handled where the full theorem is assembled.) -/
theorem not_prime_mem_tau2_of_centralizer_kappaCompl_not_le [Finite G] (hG : IsMinimalSimpleOdd G)
    {M U K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hU : Ch03.IsHallSubgroup ((kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKNU : K ≤ Subgroup.normalizer (U : Set G))
    (hesc : ¬ (Subgroup.centralizer (U : Set G) ≤ M)) :
    ∀ r : ℕ, r.Prime → r ∉ tau2 M := by
  intro r hrprime hr
  have : Fact r.Prime := ⟨hrprime⟩
  -- `r ∈ (κ(M)∪σ(M))'` (as in `centralizer_kappaCompl_le_of_mem_tau2`).
  have hrκ : r ∉ kappa M := by
    intro hrk
    rcases kappa_subset_tau1_union_tau3 hrk with h1 | h3
    · have := tau1_pRank_eq_one h1; have := tau2_pRank_eq_two hr; omega
    · have := tau3_pRank_eq_one h3; have := tau2_pRank_eq_two hr; omega
  have hrσ : r ∉ OddOrder.BG.Ch3.S10.sigma M := tau2_subset_sigma_compl M hr
  have hrκσ : r ∈ (kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ := fun h => h.elim hrκ hrσ
  -- `r ∣ |M|` (positive `pRank`), and `r ∤ [M : U]` (Hall), so `r ∣ |U| = |U.subgroupOf M|`.
  have hrM : r ∈ (Nat.card ↥M).primeFactors :=
    OddOrder.BG.Ch2.S09.mem_primeFactors_card_of_pos_pRank
      (by rw [tau2_pRank_eq_two hr]; norm_num)
  have hrUsub : r ∈ (Nat.card ↥(U.subgroupOf M)).primeFactors := by
    have hlag : Nat.card ↥(U.subgroupOf M) * (U.subgroupOf M).index = Nat.card ↥M :=
      Subgroup.card_mul_index _
    have hridx : ¬ r ∣ (U.subgroupOf M).index := fun hd =>
      hU.2 r (Nat.mem_primeFactors.mpr ⟨hrprime, hd, Subgroup.index_ne_zero_of_finite⟩) hrκσ
    have hrdvdM : r ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors hrM
    have hrU : r ∣ Nat.card ↥(U.subgroupOf M) :=
      ((Nat.Prime.dvd_mul hrprime).mp (by rw [hlag]; exact hrdvdM)).resolve_right hridx
    exact Nat.mem_primeFactors.mpr ⟨hrprime, hrU, Nat.card_pos.ne'⟩
  have hrU : r ∈ piSet U := by
    rwa [piSet, Set.mem_ofPred_eq, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  exact hesc (centralizer_kappaCompl_le_of_mem_tau2 hG hM hKM hUM hU hKNU hrprime hr hrU)

/-- **Phase B/C step 1 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1300--1307,
the `sKLs`/`sLq` block): from the partner structure of the type-`P₂` maximal `M` (via
`typeP2_partner_structure_of_mem`), the `κ`-Hall `K` embeds into `M*_σ`, and `q := |K|` (prime)
lies in `σ(M*)`.

Proof (Coq `sKLs`, `sLq`): the partner structure gives `K = M*_σ ⊓ C(Ks)` (with
`Ks = M_σ ⊓ C(K)`), so `K ≤ M*_σ` (`inf_le_left`).  As `|K| = q` is prime and `q ∣ |M*_σ|`
(`K ≤ M*_σ`), and `M*_σ` is a `σ(M*)`-group (`Msigma_isPiGroup`), we get `q ∈ σ(M*)`. -/
theorem partner_kappaHall_le_Msigma_of_isTypeP2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Mstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hMstar : Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (K : Set G))) :
    K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar ∧
      ∀ q : ℕ, q.Prime → Nat.card ↥K = q → q ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
  obtain ⟨_hMstP, _hKsHall, hKeq, _⟩ :=
    typeP2_partner_structure_of_mem hG hM hP2 hKM hK hMstar
  -- `K = M*_σ ⊓ C(Ks) ≤ M*_σ`.
  have hKMσstar : K ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by rw [hKeq]; exact inf_le_left
  refine ⟨hKMσstar, fun q hqprime hKcard => ?_⟩
  -- `q ∣ |M*_σ|`, and `M*_σ` is a `σ(M*)`-group.
  have hqdvd : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma Mstar) := by
    rw [← hKcard]; exact Subgroup.card_dvd_of_le hKMσstar
  exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup Mstar q
    (Nat.mem_primeFactors.mpr ⟨hqprime, hqdvd, Nat.card_pos.ne'⟩)

/-- **`sigma'2Elem_tau2`** (BG §12, Coq BGsection12.v:209; converse to
`exists_elemAb_rank_two_le_E_of_tau2`): a rank-2 elementary abelian `p`-subgroup `A ≤ E` inside a
`σ(M)'`-Hall `E`-setup forces `p ∈ τ₂(M)` (for `p` prime).

Proof (Coq): `A ≤ E` is a nontrivial `p`-group, so `p ∈ π(E)`; then `p ∈ τ₁(M) ∪ τ₂(M) ∪ τ₃(M)`
(`SubgroupESetup.mem_tau_union_of_mem_primeFactors`).  Since `A ∈ ℰ²_p(E)` and `A ≤ E ≤ M`,
`pRank ↥M p ≥ 2` (`le_pRank`), but `τ₁`/`τ₃` primes have `pRank = 1`; so `p ∈ τ₂(M)`.

This is the missing converse used in the `sLq1` step of `tau2_P2type_signalizer` (proving
`q₁ ∈ σ(M*)` by contradiction: were `q₁ ∉ σ(M*)`, `A` would be a `τ₂(M*)` witness). -/
theorem mem_tau2_of_elemAb_rank_two_le_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (hEsetup : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} (hpprime : p.Prime)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    p ∈ tau2 M := by
  have : Fact p.Prime := ⟨hpprime⟩
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  -- `p ∈ π(E)`: `p ∣ |A| = p² ∣ |E|`.
  have hpE : p ∈ (Nat.card ↥E).primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hpprime, ?_, Nat.card_pos.ne'⟩
    refine (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans ?_
    rw [← hAcard]; exact Subgroup.card_dvd_of_le hAE
  -- `p ∈ τ₁ ∪ τ₂ ∪ τ₃`; rule out `τ₁`/`τ₃` by `pRank ↥M p ≥ 2`.
  have hpτ : p ∈ tau1 M ∪ tau2 M ∪ tau3 M :=
    hEsetup.mem_tau_union_of_mem_primeFactors hG hpE
  have hAM : A ≤ M := hAE.trans hEsetup.E_le
  have hpRank2 : 2 ≤ pRank ↥M p := by
    have hAsubEA : (A.subgroupOf M).IsElementaryAbelian p :=
      IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM).symm hAea
    have hle := le_pRank (A.subgroupOf M) hAsubEA
    have hcard : Nat.card ↥(A.subgroupOf M) = p ^ 2 :=
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv).trans hAcard
    rw [hcard, Nat.log_pow hpprime.one_lt] at hle
    exact hle
  rcases hpτ with (h1 | h2) | h3
  · exact absurd (tau1_pRank_eq_one h1) (by omega)
  · exact h2
  · exact absurd (tau3_pRank_eq_one h3) (by omega)

/-- **Phase B/C step 2 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1307--1316,
the `sLq1`/`sALs` block): with the partner `M*` type-`P`, `K ≤ M*_σ`, `q := |K| ∈ σ(M*)`, and a
rank-2 elementary abelian `A ∈ ℰ²_{q₁}(G)` (`q₁` prime) with `A ≤ C(K)` and `A ≤ M*`, one has
`q₁ ∈ σ(M*)` and `A ≤ M*_σ`.

Proof (Coq `sLq1`): by contradiction — if `q₁ ∉ σ(M*)`, then `A` is a `σ(M*)'`-group, so it lies in
a `σ(M*)'`-Hall `E`-setup (`exists_subgroupESetup_with_le`).  Then `q₁ ∈ τ₂(M*)`
(`mem_tau2_of_elemAb_rank_two_le_E`), so `C_G(A) ≤ E` (Cor 12.6(b), `centralizer_le_E_of_tau2`).
But `K ≤ C_G(A)` (`A ≤ C(K)` symmetrised), so `K ≤ E`, a `σ(M*)'`-group; yet `q = |K| ∈ σ(M*)`
divides `|K|` — contradiction.  Then `A ⊆ M*_σ` (`sALs`): `A` is a `σ(M*)`-group (`q₁ ∈ σ(M*)`) in
`M*`, absorbed by the normal `σ(M*)`-Hall `M*_σ` (`isPiGroup_le_of_normal_isHallSubgroup`). -/
theorem mem_sigma_and_le_Msigma_of_rank2_centralizer_kappa [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {Mstar K A : Subgroup G} {q q1 : ℕ}
    (hMstar : Mstar ∈ maximalSubgroups G) (hqprime : q.Prime) (hKcard : Nat.card ↥K = q)
    (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma Mstar)
    (hq1prime : q1.Prime) (hA : A ∈ elemAbelianOfRank G q1 2)
    (hACK : A ≤ Subgroup.centralizer (K : Set G)) (hAMstar : A ≤ Mstar) :
    q1 ∈ OddOrder.BG.Ch3.S10.sigma Mstar ∧ A ≤ OddOrder.BG.Ch3.S10.Msigma Mstar := by
  classical
  have : Fact q1.Prime := ⟨hq1prime⟩
  obtain ⟨hAea, hAcard⟩ := mem_elemAbelianOfRank.mp hA
  -- `K ≤ C_G(A)` (symmetrise `A ≤ C_G(K)`).
  have hKCA : K ≤ Subgroup.centralizer (A : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hACK ha) k hk).symm
  -- `q₁ ∈ σ(M*)`, by contradiction.
  have hq1σ : q1 ∈ OddOrder.BG.Ch3.S10.sigma Mstar := by
    by_contra hq1nσ
    -- `A` is a `σ(M*)'`-subgroup (a `q₁`-group with `q₁ ∉ σ(M*)`).
    have hApi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ) A := by
      intro p hp
      have hpq1 : p = q1 := by
        have hpd : p ∈ (q1 ^ 2).primeFactors := hAcard ▸ hp
        rw [Nat.primeFactors_prime_pow (by norm_num) hq1prime, Finset.mem_singleton] at hpd
        exact hpd
      exact hpq1 ▸ hq1nσ
    -- a `σ(M*)'`-Hall `E`-setup with `A ≤ E`.
    obtain ⟨E, E₁, E₂, E₃, hEsetup, hAE, _hEpi⟩ :=
      exists_subgroupESetup_with_le hG hMstar hAMstar hApi
    -- `q₁ ∈ τ₂(M*)`, so `C_G(A) ≤ E`.
    have hq1τ2 : q1 ∈ tau2 Mstar := mem_tau2_of_elemAb_rank_two_le_E hG hEsetup hq1prime hA hAE
    have hCAE : Subgroup.centralizer (A : Set G) ≤ E :=
      (centralizer_le_E_of_tau2 hG hEsetup hq1τ2 hA hAE).1
    -- `K ≤ C_G(A) ≤ E`, so `q ∣ |K|` lies in `π(E) ⊆ σ(M*)'` — contradicting `q ∈ σ(M*)`.
    have hKE : K ≤ E := hKCA.trans hCAE
    have hqπE : q ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqprime, (hKcard ▸ Subgroup.card_dvd_of_le hKE), Nat.card_pos.ne'⟩
    exact hEsetup.not_mem_sigma_of_mem_primeFactors hG hqπE hqσ
  refine ⟨hq1σ, ?_⟩
  -- `A ⊆ M*_σ`: `A` a `σ(M*)`-group in `M*`, absorbed by the normal `σ(M*)`-Hall `M*_σ`.
  have hMσHall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma Mstar)
      ((OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar) :=
    OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hMstar
  have hApiσ : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma Mstar) (A.subgroupOf Mstar) := by
    intro p hp
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAMstar).toEquiv, hAcard,
      Nat.primeFactors_prime_pow (by norm_num) hq1prime, Finset.mem_singleton] at hp
    exact hp ▸ hq1σ
  have : ((OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hAsubMσ : A.subgroupOf Mstar ≤ (OddOrder.BG.Ch3.S10.Msigma Mstar).subgroupOf Mstar :=
    OddOrder.BG.Ch3.S10.isPiGroup_le_of_normal_isHallSubgroup hMσHall hApiσ
  have hmap := Subgroup.map_mono (f := Mstar.subtype) hAsubMσ
  rwa [Subgroup.map_subgroupOf_eq_of_le hAMstar,
    Subgroup.map_subgroupOf_eq_of_le (OddOrder.BG.Ch3.S10.Msigma_le Mstar)] at hmap

/-- **Phase B/C step 4 of BG Theorem 15.8** (Coq `tau2_P2type_signalizer`, BGsection15.v:1358--1367,
the `not_cQQ` block): with the partner `L` type-`P₁` (so `L_σ` nilpotent, `L' = L_σ`), `q ∈ σ(L)`,
the `q`-core `Q = O_q(L)` a Sylow `q`-subgroup of `L` (Step 3), and the `κ`-Hall `K` with `|K| = q`
prime, `K ≤ Q` and `K ≤ (L_σ)'`, the Sylow `Q` is **nonabelian**.

Proof (Coq `not_cQQ`, working inside `↥(L_σ)`): the nilpotent `L_σ` factors as
`L_σ = O_{q'}(L_σ)·Q` (`oPiCore_sup_compl_eq_top`, since `Q.subgroupOf L_σ = O_q(↥L_σ)`).  BG Lemma
6.5(a) (`inf_commutator_eq_of_coprime`) with the normal `q'`-part `O_{q'}(↥L_σ)`, `U = Q`, `H = K`
gives `K ⊓ (L_σ)' = K ⊓ ⁅Q, Q⁆`.  If `Q` were abelian, `⁅Q, Q⁆ = ⊥`, so `K ⊓ (L_σ)' = ⊥`; but
`K ≤ (L_σ)'` gives `K ⊓ (L_σ)' = K`, forcing `K = ⊥`, contradicting `|K| = q > 1`. -/
theorem partner_opiCore_nonabelian [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {L K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (_hL : L ∈ maximalSubgroups G) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma L)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma L))
    (hKcard : Nat.card ↥K = q)
    (hKQ : K ≤ opiCoreInG ({q} : Set ℕ) L)
    (hKderiv : K ≤ derivedInG (OddOrder.BG.Ch3.S10.Msigma L)) :
    ¬ IsMulCommutative ↥(opiCoreInG ({q} : Set ℕ) L) := by
  classical
  intro hQab
  set Ls : Subgroup G := OddOrder.BG.Ch3.S10.Msigma L with hLsdef
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) L with hQdef
  have hMσM : Ls ≤ L := OddOrder.BG.Ch3.S10.Msigma_le L
  have hMnormMσ : L ≤ Subgroup.normalizer (Ls : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG _ L
  -- `Q ≤ L_σ` and `Q = O_q(L_σ)`.
  have hQMσ : Q ≤ Ls := by
    rw [hQdef, hLsdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hQeqMσ : Q = opiCoreInG ({q} : Set ℕ) Ls := by
    rw [hQdef, hLsdef]
    exact opiCoreInG_eq_of_normal_le hMσM hMnormMσ (hQdef ▸ hLsdef ▸ hQMσ)
  have : Group.IsNilpotent ↥Ls := hLsdef ▸ hnil
  -- Inside `↥(L_σ)`: `Q̄ = O_q(↥L_σ)`, `Ō = O_{q'}(↥L_σ)`, with `Ō ⊔ Q̄ = ⊤`.
  have hQsub_eq : Q.subgroupOf Ls = Ch03.oPiCore ({q} : Set ℕ) ↥Ls := by
    rw [hQeqMσ, OddOrder.BG.Ch3.S10.opiCoreInG_subgroupOf]
  have hKMσ : K ≤ Ls := hKQ.trans hQMσ
  set Qbar : Subgroup ↥Ls := Q.subgroupOf Ls with hQbardef
  set Obar : Subgroup ↥Ls := Ch03.oPiCore ({q}ᶜ : Set ℕ) ↥Ls with hObardef
  set Kbar : Subgroup ↥Ls := K.subgroupOf Ls with hKbardef
  have hObarN : Obar.Normal := hObardef ▸ Ch03.oPiCore.normal _ _
  have hsup : Obar ⊔ Qbar = ⊤ := by
    have h := oPiCore_sup_compl_eq_top (K := ↥Ls) ({q}ᶜ : Set ℕ)
    rw [compl_compl] at h
    rw [hObardef, hQsub_eq]; exact h
  -- `K̄ = K.subgroupOf L_σ ≤ Q̄`; coprime `(|K̄|, |Ō|)` (`q`-group vs `q'`-group).
  have hKbarQ : Kbar ≤ Qbar := Subgroup.subgroupOf_mono Ls hKQ
  have hKbarcard : Nat.card ↥Kbar = q := by
    rw [hKbardef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKMσ).toEquiv]; exact hKcard
  have hObarpi : Ch03.Subgroup.IsPiGroup ({q}ᶜ : Set ℕ) Obar :=
    hObardef ▸ Ch03.oPiCore.isPiGroup ({q}ᶜ : Set ℕ)
  have hcop : Nat.Coprime (Nat.card ↥Kbar) (Nat.card ↥Obar) := by
    refine coprime_of_forall_prime_not_dvd (fun r hr hrK hrO => ?_)
    have hrq : r = q := by
      have hmem : r ∈ (q : ℕ).primeFactors := by
        rw [hKbarcard] at hrK
        exact Nat.mem_primeFactors.mpr ⟨hr, hrK, (Fact.out : q.Prime).ne_zero⟩
      rw [(Fact.out : q.Prime).primeFactors, Finset.mem_singleton] at hmem; exact hmem
    have hrOmem : r ∈ ({q}ᶜ : Set ℕ) :=
      hObarpi r (Nat.mem_primeFactors.mpr ⟨hr, hrO, Nat.card_pos.ne'⟩)
    exact hrOmem (by rw [hrq]; rfl)
  -- BG Lemma 6.5(a): `K̄ ⊓ commutator ↥L_σ = K̄ ⊓ ⁅Q̄, Q̄⁆`.
  have hfocal := OddOrder.BG.Ch1.S06.inf_commutator_eq_of_coprime (K := Obar) (U := Qbar)
    (H := Kbar) hsup hKbarQ hcop
  -- `Q` abelian ⟹ `Q̄` abelian ⟹ `⁅Q̄, Q̄⁆ = ⊥`, so RHS `= ⊥`.
  have hQbarab : IsMulCommutative ↥Qbar :=
    OddOrder.BG.Ch3.S11.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hQMσ).symm hQab
  have hQQbot : ⁅Qbar, Qbar⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx; rw [Subgroup.mem_centralizer_iff]; intro y hy
    exact congrArg Subtype.val (hQbarab.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  -- `K̄ ≤ commutator ↥L_σ` (from `K ≤ (L_σ)'`).
  have hKbarComm : Kbar ≤ commutator ↥Ls := by
    have hid : (derivedInG Ls).subgroupOf Ls = commutator ↥Ls :=
      Subgroup.comap_map_eq_self_of_injective Ls.subtype_injective (commutator ↥Ls)
    rw [hKbardef, ← hid]
    exact Subgroup.subgroupOf_mono Ls (hLsdef ▸ hKderiv)
  -- `K̄ = K̄ ⊓ commutator = K̄ ⊓ ⁅Q̄,Q̄⁆ = K̄ ⊓ ⊥ = ⊥`, contradicting `|K̄| = q > 1`.
  have hKbot : Kbar = ⊥ := by
    have h1 : Kbar ⊓ commutator ↥Ls = Kbar := inf_eq_left.mpr hKbarComm
    rw [hfocal, hQQbot, inf_bot_eq] at h1
    exact h1.symm
  rw [hKbot, Subgroup.card_bot] at hKbarcard
  exact (Fact.out : q.Prime).one_lt.ne' hKbarcard.symm

end OddOrder.BG.Ch4.S15



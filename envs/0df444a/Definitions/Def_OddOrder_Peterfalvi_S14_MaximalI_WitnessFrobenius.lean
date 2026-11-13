-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_WitnessFrobenius
-- name    : OddOrder_Peterfalvi_S14_MaximalI_WitnessFrobenius
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:48:55.176613+00:00
-- url     : https://prove2.me/theorems/e19d90ff-e459-4339-b4c3-d0e7c27f6107
-- title:
--   Peterfalvi §14: witness Frobenius and intersection structure
-- statement:
--   Proves that the witness subgroup is Frobenius and develops its intersection structure (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 14, pp. 69-74, (12.10)–(12.11)). The bundle consists of lemmas only.
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/WitnessFrobenius.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/WitnessFrobenius.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowCyclic

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (12.10) obligation B, minimality core** (§8/(12.8) obligation pinned as an
explicit hypothesis, hub 9003 Cluster A; the upstream has since been proved): for the type-I
witness `L` of (12.9), every Sylow `q`-subgroup of `L` at a prime
`q` dividing `|U|` (`U =` the complement of `H = L_F`) is **cyclic**.

Peterfalvi's argument: a prime `q ∣ |L/H|` has `q < p` — in case (8.3.c) `q ∣ p−1`; in case
(8.3.b) a Sylow `p`-subgroup `P` of `H` is of rank `2` and (8.1.c) yields an order-`q` element of
`L` acting fixed-point-freely on `Ω₁(P)`, so `q ∣ p²−1`, hence `q ∣ p−1` or `q ∣ p+1`, giving
`q < p`.  By the minimality of `p` in (12.8) (no type-I maximal has a noncyclic Sylow `q`-subgroup
of its `M/M_F` for `q < p`), a Sylow `q`-subgroup of `L` is cyclic.

**Assembly** (proven): case (a) of the (8.3) alternative is excluded by
`witness_H_sharp_not_isTISubset_of_typeI`; case (b) is the counting core
`TypeFData.prime_dvd_sq_sub_one_of_abelian_kernel` (`q ∣ p² − 1`) followed by
`prime_lt_of_odd_dvd_sq_sub_one` (`q < p`, using that `p`, `q` are odd); case (c) pairs the
exponent bound `exp U ∣ p − 1` at the prime `p ∣ |H|` with a Cauchy order-`q` element of `U`.
With `q < p`, a noncyclic Sylow `q`-subgroup `Q` of `L` would witness `InPi q` (its `L`-image has
full `q`-order, and `q ∣ [L : L_F] = |U|`), contradicting the (12.8) minimality `minimal_p`. -/
theorem witness_L_sylow_cyclic_of_dvd_complement [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) {q : ℕ} (hq : q.Prime)
    (hqU : q ∣ Nat.card ↥typeI.typeF.U) (Q : Sylow q ↥data.L) :
    IsCyclic ↥(Q : Subgroup ↥data.L) := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  -- `P₀ ≤ H`, so `p ∣ |H|`.
  have hP0H : ctr.P0 ≤ typeI.typeF.H := by
    rw [typeI.typeF.H_eq]; exact witness_P0_le_kernel hG hnoV data
  have hP0ne : ctr.P0 ≠ ⊥ := fun h => ctr.P0_noncyclic (h ▸ inferInstance)
  have hpH : ctr.p ∣ Nat.card ↥typeI.typeF.H := by
    obtain ⟨k, hk⟩ := ctr.P0_pGroup.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hP0ne (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
    exact (dvd_pow_self ctr.p hk0).trans (hk ▸ Subgroup.card_dvd_of_le hP0H)
  -- `p` and `q` are odd (divisors of the odd `|G|`).
  have hq_odd : Odd q :=
    hG.odd.of_dvd_nat (hqU.trans (Subgroup.card_subgroup_dvd_card _))
  have hp_odd : Odd ctr.p :=
    hG.odd.of_dvd_nat (hpH.trans (Subgroup.card_subgroup_dvd_card _))
  -- Step A: `q < p`, by the (8.3) alternative for the type-I witness `L`.
  have hqp : q < ctr.p := by
    rcases typeI.alternative with hTI | ⟨hab, hrank⟩ | ⟨hexp, _⟩
    · exact absurd hTI (witness_H_sharp_not_isTISubset_of_typeI hG hnoV data typeI)
    · exact prime_lt_of_odd_dvd_sq_sub_one ctr.p_prime hq hp_odd hq_odd
        (typeI.typeF.prime_dvd_sq_sub_one_of_abelian_kernel hab hrank.le hq hpH hqU)
    · have hpmem : ctr.p ∈ (Nat.card ↥typeI.typeF.H).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpH, Nat.card_pos.ne'⟩
      have : Fintype ↥typeI.typeF.U := Fintype.ofFinite _
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥typeI.typeF.U) q
        (by rwa [← Nat.card_eq_fintype_card])
      have hqp1 : q ∣ ctr.p - 1 :=
        (hu ▸ Monoid.order_dvd_exponent u).trans (hexp ctr.p ctr.p_prime hpmem)
      have hp2 := ctr.p_prime.two_le
      have := Nat.le_of_dvd (by omega) hqp1
      omega
  -- Step B: minimality of `p` (12.8) — a noncyclic Sylow `q` of `L` would put `q ∈ π`.
  by_contra hnc
  refine absurd (ctr.minimal_p q hq ⟨data.L, data.L_maximal, ⟨typeI⟩,
    (Q : Subgroup ↥data.L).map data.L.subtype, Subgroup.map_subtype_le _,
    Q.2.map data.L.subtype, ?_, ?_, ?_⟩) (not_le.mpr hqp)
  · -- The image has full `q`-order in `L`: `¬ q ∣ [L : Q]`.
    rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective data.L.subtype_injective]
    exact Q.not_dvd_index
  · -- Noncyclicity transfers along `Q ≅ Q.map L.subtype`.
    intro hc
    have := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (Q : Subgroup ↥data.L) data.L.subtype
        data.L.subtype_injective).symm.surjective)
  · -- `q ∣ [L : L_F] = |U|`.
    rw [← typeI.typeF.H_eq, Subgroup.relIndex, typeI.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe typeI.typeF.U_le).toEquiv]
    exact hqU

/-- **Peterfalvi (12.10) obligation B**: the type-I witness `L`'s complement `U` is a Z-group.

**Assembly** (`sorry`-free modulo the (8.3)/(8.1.c)/(12.8) minimality core): to show every Sylow
`q`-subgroup `P` of `U` is cyclic, distinguish `q ∣ |U|` from `q ∤ |U|`.  If `q ∤ |U|` then `P` is
trivial (its order is a `q`-power dividing `|U|`, forcing order `1`), hence cyclic.  If `q ∣ |U|`,
embed `U ↪ L` (via `U_le`): `P` becomes a `q`-subgroup of `L`, contained in a Sylow `q`-subgroup `Q`
of `L`, which is cyclic by the minimality core `witness_L_sylow_cyclic_of_dvd_complement`; a
subgroup
of a cyclic group is cyclic, so `P` is cyclic. -/
theorem witness_L_complement_isZGroup [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (typeI : TypeIData data.L) :
    _root_.IsZGroup ↥typeI.typeF.U := by
  classical
  rw [isZGroup_iff]
  intro q hq P
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqU : q ∣ Nat.card ↥typeI.typeF.U
  · -- `q ∣ |U|`: embed `P` into `L`, contain it in a cyclic Sylow `q`-subgroup of `L`.
    -- `P`, pushed along `U ↪ L`, is a `q`-subgroup of `L`.
    have hincl : Function.Injective (Subgroup.inclusion typeI.typeF.U_le) :=
      Subgroup.inclusion_injective _
    set PL : Subgroup ↥data.L :=
      (P : Subgroup ↥typeI.typeF.U).map (Subgroup.inclusion typeI.typeF.U_le) with hPL
    have hPLpg : IsPGroup q ↥PL :=
      (P.2.map (Subgroup.inclusion typeI.typeF.U_le))
    obtain ⟨Q, hQle⟩ := hPLpg.exists_le_sylow
    -- The containing Sylow `q`-subgroup of `L` is cyclic (minimality core).
    have hQcyc : IsCyclic ↥(Q : Subgroup ↥data.L) :=
      witness_L_sylow_cyclic_of_dvd_complement hG hnoV data typeI hq hqU Q
    -- A subgroup of a cyclic group is cyclic; `PL ≤ Q ≅ P`.
    have : IsCyclic ↥PL := Subgroup.isCyclic_of_le hQle
    exact isCyclic_of_surjective _
      (Subgroup.equivMapOfInjective (P : Subgroup ↥typeI.typeF.U)
        (Subgroup.inclusion typeI.typeF.U_le) hincl).symm.surjective
  · -- `q ∤ |U|`: the Sylow `q`-subgroup is trivial, hence cyclic.
    have hcard : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) ∣ Nat.card ↥typeI.typeF.U :=
      (P : Subgroup ↥typeI.typeF.U).card_subgroup_dvd_card
    obtain ⟨k, hk⟩ := P.2.exists_card_eq
    have hqk : q ^ k ∣ Nat.card ↥typeI.typeF.U := hk ▸ hcard
    have hk0 : k = 0 := by
      by_contra hk0
      exact hqU ((dvd_pow_self q hk0).trans hqk)
    have hcard1 : Nat.card ↥(P : Subgroup ↥typeI.typeF.U) = 1 := by rw [hk, hk0, pow_zero]
    have : Subsingleton ↥(P : Subgroup ↥typeI.typeF.U) :=
      (Finite.card_le_one_iff_subsingleton).mp (by omega)
    infer_instance

/-- **Peterfalvi (12.10)**: the maximal subgroup `L` supplied by (12.9) is Frobenius with kernel
`L_F`.  **Assembly** (`sorry`-free modulo the two (12.10) obligations): `L` is Type I
(`witness_L_isTypeI`) and its complement `U` is a Z-group (`witness_L_complement_isZGroup`), so the
(8.2.b) bridge `typeI_frobenius_of_isZGroup_complement` yields the Frobenius structure with kernel
`H = L_F` (`typeF.H_eq`). -/
theorem witness_L_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ frob : TypeIFrobeniusData data.L, frob.kernel_eq_MF := by
  obtain ⟨typeI⟩ := witness_L_isTypeI hG hnoV data
  exact ⟨{ typeI := typeI
           complement := typeI.typeF.U.subgroupOf data.L
           kernel_eq_MF := typeI.typeF.H = maxNilpotentNormalHall data.L
           kernel_eq_MF_holds := typeI.typeF.H_eq
           frobenius := typeI_frobenius_of_isZGroup_complement typeI
             (witness_L_complement_isZGroup hG hnoV data typeI) },
         typeI.typeF.H_eq⟩

/-- **Peterfalvi (12.11), first assertion**: `M ∩ L` complements `K = M_F` in `M`.  This is the
"first assertion follows from (12.9) and (8.13.c1)" step, with the (8.13)/BG roles swapped from
the (12.11) notation: the witness `x ∈ Ω₁(P₀)^# ⊆ L_F = L_σ` (type I) is a `σ`-sharp element of
`L` **escaping `L`** (`C_G(x) ⊄ L`), and its supporting maximal is `M` (`C_G(x) ≤ N_G(⟨x⟩) ≤ M`
pins `M` in the singleton `𝓜(C_G(x))`).

**Assembly** (proven): BG Theorem D(4) tail — "`M ∩ N` is a complement of `N_σ` in `N`" — is the
`IsComplement'` conjunct of `signalizer_structure_of_mem_sigmaSharp` (its unique `N` is `M` by the
singleton), applied at `M' := L ∈ 𝓜_σ(x)`; `N_σ = M_σ = M_F = K` is the type-I identification
`MF_eq_Msigma`. -/
theorem intersection_complements_K [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) := by
  classical
  -- The witness `L` is type I with `L_F = L_σ`, so `x ∈ P₀ ⊆ L_F` is `σ`-sharp in `L`.
  have hLtypeI : IsTypeI data.L := witness_L_isTypeI hG hnoV data
  have hLF_eq : maxNilpotentNormalHall data.L = OddOrder.BG.Ch3.S10.Msigma data.L :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG data.L_maximal).2.2.2.2.2.mpr
      (Or.inl hLtypeI)
  have hxLσ : data.x ∈ OddOrder.BG.Ch3.S10.Msigma data.L :=
    hLF_eq ▸ witness_P0_le_kernel hG hnoV data data.x_mem_P0
  have hxσ : data.x ∈ OddOrder.BG.Ch4.S14.sigmaSharp data.L :=
    ⟨hxLσ, by simpa using data.x_ne_one⟩
  -- `C_G(x) ≤ M` (via `N_G(⟨x⟩) ≤ M`), so `M` is THE maximal subgroup over `C_G(x)`.
  have hCM : Subgroup.centralizer ({data.x} : Set G) ≤ ctr.M := by
    refine le_trans ?_ data.normalizer_closure_x_le_M
    rw [← Subgroup.centralizer_closure]
    exact Subgroup.centralizer_le_normalizer _
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG data.L_maximal hxσ data.centralizer_x_not_le_L
  have hMN₀ : ctr.M = N₀ := by
    have hMin : ctr.M ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨ctr.M_maximal, hCM⟩
    rw [hN₀] at hMin
    exact hMin
  -- The signalizer structure at the escaping `σ`-sharp `x`; its unique `N` is `M`.
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x).ncard := by
    by_contra h
    push Not at h
    exact data.centralizer_x_not_le_L
      (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG data.L_maximal hxLσ
        data.x_ne_one h)
  obtain ⟨N, ⟨hNmax, hCN, -, -, -, -, hforall⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG data.L_maximal hxσ hgt
  have hNM : N = ctr.M := by
    have hNin : N ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({data.x} : Set G)) := ⟨hNmax, hCN⟩
    rw [hN₀] at hNin
    rw [hNin, ← hMN₀]
  -- `L ∈ 𝓜_σ(x)`: apply the Theorem D(4) complement conjunct at `M' = L`.
  have hLin : data.L ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement data.x :=
    ⟨data.L_maximal, hxLσ⟩
  obtain ⟨-, -, hcompl, -⟩ := hforall data.L hLin
  rw [hNM, ← MF_eq_Msigma hG ctr,
    show data.L ⊓ ctr.M = ctr.M ⊓ data.L from inf_comm .. ] at hcompl
  exact hcompl

/-- **`|M ∩ L|` is coprime to `|K|`** (from the first assertion (12.11) + `M_F` Hall).  `M ∩ L`
complements `K = M_F` in `M` (`intersection_complements_K`), so `|M ∩ L| = [M : K]`, which is
coprime to `|K|` because `K = M_F` is a Hall subgroup of `M`. -/
theorem card_MinfL_coprime_card_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Nat.Coprime (Nat.card ↥(ctr.M ⊓ data.L)) (Nat.card ↥ctr.K) := by
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hcompl := intersection_complements_K hG hnoV data
  have hHall := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M).coprime_index
  rw [← ctr.K_eq_MF] at hHall
  -- `hHall : Coprime |K| [M : K]`;  `[M : K] = |M ∩ L|` by the complement.
  have hidx : (ctr.K.subgroupOf ctr.M).index = Nat.card ↥((ctr.M ⊓ data.L).subgroupOf ctr.M) :=
    hcompl.symm.index_eq_card
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at hHall
  exact hHall.symm

/-- **Peterfalvi (12.11), core of the second assertion**: a subgroup `A ≤ M ∩ L` meeting the
witness kernel `H = L_F` trivially (`A ⊓ H = ⊥`, i.e. of order prime to `|H|`) is trivial.

The genuine (12.11) argument, now fully assembled from the landed infrastructure.  Put
`P = O_p(H) ∩ M` (an `A`-invariant `p`-subgroup of `H` containing `P₀`, via the nilpotent core
`opiCoreInG`); then:
* `P` does not centralize `K` (`P₀_not_le_centralizer_K`, `P₀ ≤ P`);
* `P ⊔ A` is Frobenius with kernel `P` (from `L`'s Frobenius structure), acts coprimely on `K`
  (`P ⊔ A ≤ M ∩ L`, coprime to `|K|`), so by Wielandt (9.1)
  `exists_ne_one_centralized_by_complement_of_kernel_not_centralizes` gives `C_K(A) ≠ 1`;
* `C_K(x) ≠ 1` by (12.9) (`ctr.CKx_not_le_Kprime`);
* since `M ∩ L` complements `K` in `M` (first assertion), `A` and `x` land in a common abelian
  subgroup `W` (`exists_abelian_centralizer_le_of_isComplement` with `V = M ∩ L`), so `A`
  centralizes `x`;
* by `L`'s Frobenius condition (4) (`centralizer_kernel_le`, `x ∈ H^#`), `A ≤ C_L(x) ⊆ H`, so
  `A ⊆ H`, forcing `A = A ⊓ H = ⊥`. -/
theorem witness_MinfL_pprime_subgroup_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) {A : Subgroup G}
    (hAML : A ≤ ctr.M ⊓ data.L) (hAH : A ⊓ maxNilpotentNormalHall data.L = ⊥) (hAne : A ≠ ⊥) :
    False := by
  classical
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hAM : A ≤ ctr.M := hAML.trans inf_le_left
  have hAL : A ≤ data.L := hAML.trans inf_le_right
  have hHnilp : Group.IsNilpotent ↥H := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent
      data.L
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hHnorm : data.L ≤ Subgroup.normalizer (H : Set G) :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer data.L
  -- Frobenius structure of `L` with kernel `H` (upstream of this theorem).
  obtain ⟨frob, _⟩ := witness_L_frobenius hG hnoV data
  have hHfrob : frob.typeI.typeF.H = H := frob.typeI.typeF.H_eq
  have hFrobL : ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (H.subgroupOf data.L) C :=
    ⟨frob.complement, hHfrob ▸ frob.frobenius⟩
  -- `x ∈ H^#` and `x ∈ M ∩ L`.
  have hxH : data.x ∈ H := witness_P0_le_kernel hG hnoV data data.x_mem_P0
  have hxML : data.x ∈ ctr.M ⊓ data.L := ⟨ctr.P0_le_M data.x_mem_P0, hHL hxH⟩
  -- `P = O_p(H) ∩ M` contains `P₀`, sits inside `H` and `M`.
  set P : Subgroup G := opiCoreInG ({ctr.p} : Set ℕ) H ⊓ ctr.M with hPdef
  have hP0_le_P : ctr.P0 ≤ P :=
    le_inf (pGroup_le_opiCoreInG_of_le_of_isNilpotent ctr.P0_pGroup (witness_P0_le_kernel hG hnoV
        data))
      ctr.P0_le_M
  have hP_le_H : P ≤ H := inf_le_left.trans (opiCoreInG_le _ _)
  have hP_le_M : P ≤ ctr.M := inf_le_right
  have hP0ne : ctr.P0 ≠ ⊥ := fun hb => ctr.P0_noncyclic (hb ▸ isCyclic_of_subsingleton)
  have hPne : P ≠ ⊥ := fun hb => hP0ne (le_bot_iff.mp (hb ▸ hP0_le_P))
  -- `A` normalises `P` (normalises `O_p(H)` and `M`).
  have hAnorm_opi : A ≤ Subgroup.normalizer (opiCoreInG ({ctr.p} : Set ℕ) H) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ (hAL.trans hHnorm)
  have hAnorm_M : A ≤ Subgroup.normalizer (ctr.M : Set G) := hAM.trans Subgroup.le_normalizer
  have hAP : A ≤ Subgroup.normalizer (P : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hOpi := (Subgroup.mem_normalizer_iff.mp (hAnorm_opi ha)) y
    have hM := (Subgroup.mem_normalizer_iff.mp (hAnorm_M ha)) y
    simp only [hPdef, Subgroup.mem_inf]
    rw [hOpi, hM]
  -- `P ⊔ A ≤ N_G(K)` and `≤ M ∩ L`.
  have hMnorm_K : ctr.M ≤ Subgroup.normalizer (ctr.K : Set G) :=
    ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer ctr.M
  have hPAK : P ⊔ A ≤ Subgroup.normalizer (ctr.K : Set G) :=
    sup_le (hP_le_M.trans hMnorm_K) (hAM.trans hMnorm_K)
  have hPA_ML : P ⊔ A ≤ ctr.M ⊓ data.L :=
    sup_le (le_inf hP_le_M (hP_le_H.trans hHL)) hAML
  -- `K` is solvable (subgroup of the solvable maximal `M`).
  have hKM : ctr.K ≤ ctr.M := ctr.K_eq_MF ▸ OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le ctr.M
  have hMsolv : Group.IsSolvable ↥ctr.M := hG.isSolvable_of_mem_maximalSubgroups ctr.M_maximal
  have hKsolv : Group.IsSolvable ↥ctr.K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
  -- Coprimality of the `P ⊔ A`-action on `K`.
  have hcop : Nat.Coprime (Nat.card ↥ctr.K) (Nat.card ↥(P ⊔ A)) :=
    (card_MinfL_coprime_card_K hG hnoV data).symm.coprime_dvd_right (Subgroup.card_dvd_of_le hPA_ML)
  -- `P` does not centralize `K`.
  have hPnc : ¬ P ≤ Subgroup.centralizer (ctr.K : Set G) := fun hPc =>
    P0_not_le_centralizer_K hG ctr (hP0_le_P.trans hPc)
  -- **`C_K(A) ≠ 1`** (Wielandt (9.1) via the sub-Frobenius engine).
  obtain ⟨n, hnK, hn1, hnA⟩ := exists_ne_one_centralized_by_complement_of_kernel_not_centralizes
    hHL hFrobL hP_le_H hPne hAL hAH hAne hAP hPAK hKsolv hcop hPnc
  -- **`C_K(x) ≠ 1`** (Peterfalvi (12.9)).
  obtain ⟨n', hn'mem, hn'K'⟩ := SetLike.not_le_iff_exists.mp data.CKx_not_le_Kprime
  obtain ⟨hn'C, hn'K⟩ := Subgroup.mem_inf.mp hn'mem
  have hn'1 : n' ≠ 1 := fun h => hn'K' (by rw [h]; exact Subgroup.one_mem _)
  -- **`A` and `x` in a common abelian `W ≤ M ∩ L`** (step (8.1.b), `V = M ∩ L`).
  obtain ⟨typeIM⟩ := ctr.M_typeI
  have htypeFH : typeIM.typeF.H = ctr.K := ctr.K_eq_MF ▸ typeIM.typeF.H_eq
  obtain ⟨W, hWab, hWle⟩ := exists_abelian_centralizer_le_of_isComplement hMsolv typeIM.typeF
    (V := ctr.M ⊓ data.L) inf_le_left (htypeFH ▸ intersection_complements_K hG hnoV data)
  have hnFH : n ∈ typeIM.typeF.H := by rw [htypeFH]; exact hnK
  have hn'FH : n' ∈ typeIM.typeF.H := by rw [htypeFH]; exact hn'K
  have hA_W : A ≤ W := by
    intro a haA
    have haC : (a : G) ∈ Subgroup.centralizer ({n} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp (hnA a haA))
    exact hWle n hnFH hn1 ⟨hAML haA, haC⟩
  have hx_W : data.x ∈ W := by
    have hxC : data.x ∈ Subgroup.centralizer ({n'} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp hn'C).symm
    exact hWle n' hn'FH hn'1 ⟨hxML, hxC⟩
  -- **`A` centralizes `x`** (both in abelian `W`), then **`A ⊆ H`** by Frobenius condition (4).
  have hA_H : A ≤ H := by
    intro a haA
    have hax : (a : G) * data.x = data.x * a :=
      congrArg Subtype.val (hWab.is_comm.comm ⟨a, hA_W haA⟩ ⟨data.x, hx_W⟩)
    have hxHfrob : (⟨data.x, hHL hxH⟩ : ↥data.L) ∈ frob.typeI.typeF.H.subgroupOf data.L := by
      rw [Subgroup.mem_subgroupOf, hHfrob]; exact hxH
    have hx1 : (⟨data.x, hHL hxH⟩ : ↥data.L) ≠ 1 :=
      fun h => data.x_ne_one (by simpa using congrArg Subtype.val h)
    have hcent := frob.frobenius.centralizer_kernel_le _ hxHfrob hx1
    have haC : (⟨a, hAL haA⟩ : ↥data.L) ∈
        Subgroup.centralizer ({(⟨data.x, hHL hxH⟩ : ↥data.L)} : Set ↥data.L) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (by simpa using hax)
    have haH := hcent haC
    rw [Subgroup.mem_subgroupOf, hHfrob] at haH
    exact haH
  exact hAne (le_bot_iff.mp (hAH ▸ le_inf le_rfl hA_H))

/-- **Peterfalvi (12.11), second assertion**: `M ∩ L ⊆ H = L_F`.  `M ∩ L` has no nontrivial
subgroup meeting `H` trivially (`witness_MinfL_pprime_subgroup_eq_bot`), so its order is coprime to
`[L : H]` (any common prime would give a nontrivial Sylow subgroup meeting `H` trivially), and the
normal-Hall reduction `le_of_coprime_card_index_of_normal` places `M ∩ L` inside `H`. -/
theorem intersection_le_kernel [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall data.L with hHdef
  have hHL : H ≤ data.L := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le data.L
  have hMLL : ctr.M ⊓ data.L ≤ data.L := inf_le_right
  have hHnorm : (H.subgroupOf data.L).Normal :=
    OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal data.L
  -- `|M ∩ L|` is coprime to `[L : H]`.
  have hcop : Nat.Coprime (Nat.card ↥((ctr.M ⊓ data.L).subgroupOf data.L))
      (H.subgroupOf data.L).index := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMLL).toEquiv, Nat.coprime_iff_gcd_eq_one]
    by_contra hgcd
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hgcd
    have : Fact q.Prime := ⟨hq⟩
    rw [Nat.dvd_gcd_iff] at hqdvd
    obtain ⟨hqML, hqidx⟩ := hqdvd
    -- A Sylow `q`-subgroup `Q` of `M ∩ L` is nontrivial, meets `H` trivially, contradicts the core.
    obtain ⟨Q⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥(ctr.M ⊓ data.L)))
    set A : Subgroup G := (Q : Subgroup ↥(ctr.M ⊓ data.L)).map (ctr.M ⊓ data.L).subtype with hAdef
    have hApg : IsPGroup q ↥A := Q.2.map _
    have hAML : A ≤ ctr.M ⊓ data.L := Subgroup.map_subtype_le _
    -- `q ∉ π(H)` (as `q ∣ [L : H]` and `H` is Hall in `L`), so `A ⊓ H = ⊥`.
    have hqH : ¬ q ∣ Nat.card ↥H := by
      have hHallL := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall data.L).coprime_index
      intro hdvd
      have hdvd' : q ∣ Nat.card ↥(H.subgroupOf data.L) := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv]; exact hdvd
      have hg : q ∣ Nat.gcd (Nat.card ↥(H.subgroupOf data.L)) (H.subgroupOf data.L).index :=
        Nat.dvd_gcd hdvd' hqidx
      rw [hHallL] at hg
      exact hq.one_lt.ne' (Nat.dvd_one.mp hg)
    have hAH : A ⊓ H = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzA, hzH⟩ := Subgroup.mem_inf.mp hz
      rw [Subgroup.mem_bot]
      by_contra hzne
      apply hqH
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hApg) ⟨z, hzA⟩
      have hoz : orderOf z = q ^ k := by
        rw [← hk]; exact orderOf_injective A.subtype A.subtype_injective ⟨z, hzA⟩
      have hk0 : k ≠ 0 := fun h => hzne (orderOf_eq_one_iff.mp (by rw [hoz, h, pow_zero]))
      have hqoz : q ∣ Nat.card ↥(Subgroup.zpowers z) := by
        rw [Nat.card_zpowers, hoz]; exact dvd_pow_self q hk0
      exact hqoz.trans (Subgroup.card_dvd_of_le ((Subgroup.zpowers_le).mpr hzH))
    have hAne : A ≠ ⊥ := by
      have hqQ : q ∣ Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) := by
        have hmul := Subgroup.card_mul_index (Q : Subgroup ↥(ctr.M ⊓ data.L))
        rcases (Nat.Prime.dvd_mul hq).mp (hmul ▸ hqML) with h | h
        · exact h
        · exact absurd h Q.not_dvd_index
      intro hb
      have hA1 : Nat.card ↥A = Nat.card ↥(Q : Subgroup ↥(ctr.M ⊓ data.L)) :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ _
          (ctr.M ⊓ data.L).subtype_injective).toEquiv).symm
      rw [hb, Subgroup.card_bot] at hA1
      rw [← hA1] at hqQ
      exact hq.one_lt.ne' (Nat.dvd_one.mp hqQ)
    exact witness_MinfL_pprime_subgroup_eq_bot hG hnoV data hAML hAH hAne
  -- Apply the normal-Hall reduction.
  have hle := Subgroup.le_of_coprime_card_index_of_normal hcop
  intro z hz
  have : (⟨z, hMLL hz⟩ : ↥data.L) ∈ H.subgroupOf data.L :=
    hle (Subgroup.mem_subgroupOf.mpr hz)
  exact Subgroup.mem_subgroupOf.mp this

/-- **Peterfalvi (12.11)**: `M ∩ L` complements `K` in `M` and lies in the Fitting kernel
`H = L_F` of the witness subgroup `L`.

**Assembly**: the two textbook assertions of (12.11) are `intersection_complements_K` (from (12.9)
and (8.13.c1)) and `intersection_le_kernel` (the (8.1.b/c)+(9.1)+(12.10) `A = 1` argument),
combined here. -/
theorem intersection_complement_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    Subgroup.IsComplement' (ctr.K.subgroupOf ctr.M) ((ctr.M ⊓ data.L).subgroupOf ctr.M) ∧
      ctr.M ⊓ data.L ≤ maxNilpotentNormalHall data.L :=
  ⟨intersection_complements_K hG hnoV data, intersection_le_kernel hG hnoV data⟩

/-- **Peterfalvi (12.10), non-TI clause**: for the (12.9) witness `L`, its Frobenius kernel
`H = L_F` has `H^#` **not** a TI-subset of `G`.  This is the "By (12.9), `H^#` is not a TI-subset"
step of (12.10): the rank-two witness `x ∈ Ω₁(P₀)^#` has `C_G(x) ⊄ L`
(`data.centralizer_x_not_le_L`)
while `N_G(H) = L` (maximality of `L` + `H = L_F` normal); pick `g ∈ C_G(x) ∖ L`, then `g ∉ N_G(H)`
yet `g x g⁻¹ = x ∈ H^#`, witnessing the TI failure (`x ∈ H^# ∩ (H^#)^g`).

This is the honest (12.9)/(12.10) prerequisite of the *witness* coherence route: with it,
`witness_L_coherent` dispatches only through the (b)/(c) cases of (12.6) (which are `sorry`-free),
never the TI-only case (a) — so the witness coherence depends on this genuine (12.9) fact rather
than on the (8.18.c) geometry that case (a) (`sibleyTarget_frobI`) transitively needs.

Specialization of the `TypeIData`-form `witness_H_sharp_not_isTISubset_of_typeI` to the
Frobenius witness (whose `x ∈ H` route is the upstream `witness_P0_le_kernel`, not (12.11)). -/
theorem witness_H_sharp_not_isTISubset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr)
    (frob : TypeIFrobeniusData data.L) :
    ¬ OddOrder.GroupTheory.IsTISubset
        (OddOrder.GroupTheory.sharpSubgroup frob.typeI.typeF.H)
        (Subgroup.normalizer (frob.typeI.typeF.H : Set G)) :=
  witness_H_sharp_not_isTISubset_of_typeI hG hnoV data frob.typeI

/-- **Peterfalvi (12.1) for the witness subgroup `L`, with its Frobenius witness**: the second
maximal subgroup `L` of (12.9) carries the (12.1) Hypothesis together with an explicit Frobenius
decomposition of its kernel `H = L_F`.  Since `L` is type I (Frobenius, by (12.10)
`witness_L_frobenius`), `hypothesis_of_typeIData` applied to the recovered `TypeIData` yields the
Hypothesis whose `typeI` is that very data, so the Frobenius group structure `frob.frobenius`
transfers to `hyp.H`.  This Frobenius witness is the structural input to coherence (12.6). -/
theorem witness_L_hypothesis_frobenius [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {ctr : CounterexampleHypothesis (G := G)} (data : RankTwoWitnessData ctr) :
    ∃ hyp : Hypothesis data.L, ∃ C : Subgroup ↥data.L,
      OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥data.L (hyp.H.subgroupOf data.L) C ∧
      ¬ OddOrder.GroupTheory.IsTISubset
          (OddOrder.GroupTheory.sharpSubgroup hyp.typeI.typeF.H)
          (Subgroup.normalizer (hyp.typeI.typeF.H : Set G)) := by
  obtain ⟨frob, hker⟩ := witness_L_frobenius hG hnoV data
  obtain ⟨hyp, hhyp⟩ := hypothesis_of_typeIData hG data.L_maximal frob.typeI
  have hH : hyp.typeI.typeF.H = frob.typeI.typeF.H := by rw [hhyp]
  refine ⟨hyp, frob.complement, ?_, ?_⟩
  · rw [show hyp.H = hyp.typeI.typeF.H from rfl, hH]
    exact frob.frobenius
  · rw [hH]
    exact witness_H_sharp_not_isTISubset hG hnoV data frob

end OddOrder.Peterfalvi.S14



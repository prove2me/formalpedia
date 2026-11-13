-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_Noncoherence
-- name    : OddOrder_Peterfalvi_S12_Noncoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:28:48.566274+00:00
-- url     : https://prove2.me/theorems/1d8ea611-f6e6-4002-a115-0640d23718a3
-- title:
--   Peterfalvi (10.8): the unconditional noncoherence theorem
-- statement:
--   Formalizes the unconditional form of Theorem (10.8) (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 10, pp. 59-60): under Hypothesis (10.1), the character family is not coherent.
--
--   Main declarations: `S_not_coherent_unconditional` (Peterfalvi (10.8), unconditional); `induce_linear_isIrreducible` (Type-V irreducibility bridge); `inducedKernelFamily_commutator_eq_SHCSet` (`S(M″) = SHCSet`); `typeV_sixFiveA_bound` (Peterfalvi (6.5.a) for `(L, K, M) := (M, M′, 1)`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_Noncoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_Noncoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIICrossIsometryPair
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeVCaseC
import Definitions.Def_OddOrder_Peterfalvi_S13_Lemmas113To115
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_CentralizerContainment

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.8), unconditional**: under Hypothesis (10.1), the character family `𝒮`
is not coherent — with the type-II partner supply assembled internally (issue 1020 Phase 3).
Every ingredient is axiom-clean; this is the honest heir of `S_not_coherent`. -/
theorem S_not_coherent_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) :
    ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  rintro ⟨hcoh⟩
  obtain ⟨params, -⟩ := w2_prime_and_parameter_independence hG hyp
  let coh : CoherentHypothesis hyp params := ⟨hcoh⟩
  -- the `M`-seeded order-free pair and the reconciled partner datum
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M := hyp.bgTypeP hG
  have hnotP2 := not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt
  obtain ⟨mp₀, hT₀, hK₀⟩ := exists_section16MaximalPairCore_around hG hyp.maximal hP hnotP2
    hyp.typeP.W1_le (typePData_W1_isHallSubgroup_kappa hG hyp.maximal hP hyp.typeP)
  obtain ⟨dII₀⟩ := section16_S_isTypeII hG mp₀
  obtain ⟨mp, u, dataS, hT, hKstar, huS, hSW1, hSW2, hH, hU⟩ :=
    exists_reconciled_conj_typePData_S hG hyp mp₀.S_maximal
      (section16_S_isTypeII hG mp₀) dII₀.typeP
  have hSmax := mp.S_maximal
  have hSII : IsTypeII mp.S := section16_S_isTypeII hG mp
  -- `K = W₂(M)`: the pair-linkage card identities
  have hKW2 : mp.K = hyp.typeP.W2 := by
    rw [mp.K_eq, hT, hKstar]
    exact typePData_Msigma_inf_centralizer_W1_eq_W2 hG hyp.maximal hyp.typeP
  have hKcard : Nat.card ↥mp.K = hyp.w2 := by rw [hKW2]; rfl
  have hKstarcard : Nat.card ↥mp.Kstar = hyp.w1 := by rw [hKstar]; rfl
  -- supply: the derived index of the partner is `w₂`
  have hSidx : ((derivedInG mp.S).subgroupOf mp.S).index = hyp.w2 := by
    rw [← dataS.card_W1_eq_derived_index, hSW1, hKcard]
  have hW1card : Nat.card ↥dataS.W1 = hyp.w2 := by rw [hSW1, hKcard]
  -- supply: `|U| ≥ 7` (the odd-order forcing on the reconciled datum)
  have hUcard : Nat.card ↥dataS.U = Nat.card ↥dII₀.typeP.U := by
    rw [hU, pointwise_mulAut_smul_eq_map]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective dII₀.typeP.U
      (MulAut.conj u).toMonoidHom (MulAut.conj u).injective).toEquiv).symm
  have hUne : dataS.U ≠ ⊥ := by
    intro hbot
    have h1 : 1 < Nat.card ↥dII₀.typeP.U :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr dII₀.common.1
    rw [← hUcard, hbot, Subgroup.card_bot] at h1
    omega
  have hU7 : 7 ≤ Nat.card ↥dataS.U := by
    have hUlt : 1 < Nat.card ↥dataS.U := (Subgroup.one_lt_card_iff_ne_bot _).mpr hUne
    have hfrobUW := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius dataS hUne
    have hmod := hfrobUW.card_kernel_modEq_one
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hmod
    have hdvd : Nat.card ↥dataS.W1 ∣ Nat.card ↥dataS.U - 1 :=
      (Nat.modEq_iff_dvd' hUlt.le).mp hmod.symm
    have hUodd : Odd (Nat.card ↥dataS.U) :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dataS.U)
    have hW1odd : Odd (Nat.card ↥dataS.W1) :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card dataS.W1)
    have hge := OddOrder.Peterfalvi.S08.two_mul_add_one_le_of_odd_dvd hW1odd hUodd hdvd hUlt
    rw [hW1card] at hge
    have hw2prime : (hyp.w2).Prime := hyp.w2_prime hG
    have hw2odd : Odd hyp.w2 := hW1card ▸ hW1odd
    have hw2ge : 3 ≤ hyp.w2 := by
      have h2 := hw2prime.two_le
      obtain ⟨k, hk⟩ := hw2odd; omega
    omega
  -- supply: `|W₁(S)|` prime, coprime to `|[S,S]|`
  have hprime : (Nat.card ↥dataS.W1).Prime := by
    rw [hW1card]; exact hyp.w2_prime hG
  have hcop := typePData_W1_hall_coprime hG hSmax mp.S_typeP dataS
  -- supply: (8.11) — `H = S_F` is a Hall subgroup of `G`
  have hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      (Nat.card ↥dataS.H).primeFactors dataS.H := by
    have h := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hSmax
      (show HasPeterfalviType PeterfalviType.II mp.S from hSII)).1
    rw [dataS.H_eq]
    exact h
  -- supply: (8.16)/(8.6.a) — centralizers of `H#`-elements land in `S`
  have hcent : ∀ b ∈ dataS.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ mp.S := by
    intro b hb hb1
    refine OddOrder.Peterfalvi.S14.typeII_centralizer_le_of_mem_mainSubgroup hG hSmax hSII
      ?_ hb1
    show b ∈ mainSubgroup mp.S PeterfalviType.II
    have : mainSubgroup mp.S PeterfalviType.II = maxNilpotentNormalHall mp.S := rfl
    rw [this, ← dataS.H_eq]
    exact hb
  -- supply: the (10.7) Frobenius-kernel capture
  have hfrobcap : ∀ b ∈ dataS.H, b ≠ 1 → ∀ y ∈ derivedInG mp.S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ dataS.H := by
    have hfrob := typeII_HU_frobenius_of_coherent' hG coh
      (data := { maximal := hSmax
                 typeP := dataS
                 nontrivial := hSII.some.common.transfer dataS
                 type_alt := Or.inl hSII }) hSII
    intro b hb hb1 y hy hyc
    have hbS' : b ∈ derivedInG mp.S := dataS.H_le hb
    have hbmem : (⟨b, hbS'⟩ : ↥(derivedInG mp.S)) ∈ dataS.H.subgroupOf (derivedInG mp.S) :=
      Subgroup.mem_subgroupOf.mpr hb
    have hbne : (⟨b, hbS'⟩ : ↥(derivedInG mp.S)) ≠ 1 := by
      intro h; exact hb1 (congrArg Subtype.val h)
    have hyC : (⟨y, hy⟩ : ↥(derivedInG mp.S))
        ∈ Subgroup.centralizer ({(⟨b, hbS'⟩ : ↥(derivedInG mp.S))} : Set ↥(derivedInG mp.S)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc b rfl).symm
    have := hfrob.centralizer_kernel_le _ hbmem hbne hyC
    exact Subgroup.mem_subgroupOf.mp this
  -- supply: the pair-linkage card identities for `W₂` and `W`
  have hW2card : Nat.card ↥dataS.W2 = hyp.w1 := by rw [hSW2, hKstarcard]
  have hWcard : Nat.card ↥dataS.W = hyp.w1 * hyp.w2 := by
    have hinf : mp.K ⊓ mp.Kstar = ⊥ := by
      rw [← hSW1, ← hSW2]
      exact disjoint_iff.mp (typePData_disjoint_W1_W2 dataS)
    have hmul := card_mul_eq_of_disjoint_sup_le_isCyclic (W := mp.K ⊔ mp.Kstar)
      mp.Z_cyclic le_sup_left le_sup_right rfl hinf
    have hWKK : dataS.W = mp.K ⊔ mp.Kstar := by rw [dataS.W_eq, hSW1, hSW2]
    rw [hWKK, ← hmul, hKcard, hKstarcard, Nat.mul_comm]
  -- the partner-supplied estimate and the arithmetic contradiction
  have hw1odd : Odd hyp.w1 :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hw1gt : 1 < hyp.w1 :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hw1 : 3 ≤ hyp.w1 := by
    obtain ⟨k, hk⟩ := hw1odd; omega
  have hw2 : 1 ≤ hyp.w2 := Nat.card_pos
  have hMp : (2 * hyp.w1 + 1) * hyp.w2 ≤ Nat.card ↥(derivedInG M) := hyp.card_derived_ge hG
  obtain ⟨u', hu7', hbound⟩ := typeII_coherence_contradiction_estimate_of_partner hG coh dataS
    hSidx hU7 hprime hcop hHall hcent hfrobcap hW2card hWcard
  exact typeII_noncoherence_arithmetic hw1 hu7' hw2 hMp hbound

open scoped Classical FiniteInduce in
/-- **Type-V irreducibility bridge** (the `hcoh` sub-piece of `typeV_sixFiveA_bound`): a
nonprincipal *linear* irreducible character `θ` of `M′ = (derivedInG M).subgroupOf M` induces
irreducibly to `M`.  Generalizes the single-`ζ` `havoid` computation of
`exists_zeta_in_inducedFamily_degree_w1` to *every* linear `θ` (the argument uses only `θ ≠ 1` and
`θ(1) = 1`): the trivial column gives `chiRestrict 1 = 1_{M′} ≠ θ`, and a nontrivial column `χ₂`
gives `chiRestrict χ₂ = Res_{M′} μ_{0j}` of degree `μ_{0j}(1) > 1 ≠ θ(1) = 1` (else `μ_{0j}` is a
column-`0` character, contradicting `columnFamily_mu_ne`).  Hence `θ` avoids every `chiRestrict χ₂`
and `Ind_{M′}^M θ` is irreducible by `induce_isIrreducible_of_forall_chiRestrict_ne`. -/
theorem induce_linear_isIrreducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M))
    (hθne : θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
    (hθ1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) :
    IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) := by
  classical
  let h : OddOrder.Peterfalvi.S06.Hypothesis ↥M :=
    typePData_toS06Hypothesis hyp.typeP hG.odd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  have hNeZ : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  refine h.induce_isIrreducible_of_forall_chiRestrict_ne (χ := θ) ?_
  intro χ₂ heq
  by_cases hχ₂ : χ₂ = 1
  · subst hχ₂
    refine hθne ?_
    rw [← heq]
    apply IrreducibleCharacter.ext
    rw [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict,
      (h.certainType_zero_column_anchor).2,
      OddOrder.Peterfalvi.S03.restrict_trivialClassFunction]
    rfl
  · have hmu1 : ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) (1 : ↥M) = 1 := by
      have hval := congrArg
        (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) (1 : ↥h.K)) heq
      simp only [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
        Subgroup.coe_one] at hval
      rw [hval]; exact hθ1
    have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
        ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) := by
      intro x hx
      have hx1 := ((h.columnFamily χ₂).mu 0).isIrreducible
        |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
        OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
    obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
    exact h.columnFamily_mu_ne hχ₂ 0 i hi.symm

open scoped Classical FiniteInduce in
/-- **`S(M″) = SHCSet`**: the kernel-filter family `S(⁅M′,M′⁆)` equals the degree-`w₁` irreducible
subfamily `SHCSet = {φ ∈ 𝒮 | φ irreducible, φ(1) = w₁}`.

`⊆`: a member `Ind_{M′}^M θ` (`θ` trivial on `M″ = ⁅M′,M′⁆`, i.e. *linear*, `θ ≠ 1`) is irreducible
(`induce_linear_isIrreducible`) of degree `[M:M′]·θ(1) = w₁·1 = w₁` (`induce_apply_one`,
`card_W1_eq_derived_index`); linearity `θ(1) = 1` from the commutator kernel via
`apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient`.  `⊇`: a degree-`w₁`
member `Ind θ` has `θ(1) = 1` (as `w₁·θ(1) = w₁`), so `θ` is linear, hence trivial on `M″`
(`apply_eq_one_of_mem_commutator_of_apply_one_eq_one`).  Feeds the (5.7) coherence
`SHC_isCoherent` into the `hcoh` input of `typeV_sixFiveA_bound` and the non-abelian branch of
`typeV_sixFiveB_pGroup`. -/
theorem inducedKernelFamily_commutator_eq_SHCSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆) = hyp.SHCSet := by
  have : IsMulCommutative (↥((derivedInG M).subgroupOf M)
      ⧸ commutator ↥((derivedInG M).subgroupOf M)) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr le_rfl
  have hw1pos : (hyp.w1 : ℂ) ≠ 0 := by
    have h0 : 0 < hyp.w1 := Nat.card_pos
    exact_mod_cast h0.ne'
  have hidxw1 : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  ext φ
  constructor
  · -- `Ind θ` with `θ` linear (trivial on `M″`), `θ ≠ 1` ⟹ irreducible of degree `w₁`
    rintro ⟨θ, hθne, hker, rfl⟩
    have hkerc : (commutator ↥((derivedInG M).subgroupOf M) :
          Set ↥((derivedInG M).subgroupOf M)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := by
      rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
      exact hker
    have hθ1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 :=
      apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
        (N := commutator ↥((derivedInG M).subgroupOf M)) θ hkerc
    have hirr := induce_linear_isIrreducible hG hyp θ hθne hθ1
    have hdeg : (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) : ↥M → ℂ) 1
        = (hyp.w1 : ℂ) := by
      rw [ClassFunction.induce_apply_one, hθ1, mul_one, hidxw1]
    refine ⟨?_, hirr, hdeg⟩
    rw [inducedFamily_eq_inducedKernelFamily_bot]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le ⟨θ, hθne, hker, rfl⟩
  · -- degree-`w₁` irreducible member ⟹ source `θ` linear ⟹ trivial on `M″`
    rintro ⟨hmem, -, hdeg⟩
    rw [inducedFamily_eq_inducedKernelFamily_bot,
      OddOrder.Peterfalvi.S08.mem_inducedKernelFamily] at hmem
    obtain ⟨θ, hθne, -, rfl⟩ := hmem
    have hθ1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 := by
      have hd := hdeg
      rw [ClassFunction.induce_apply_one, hidxw1] at hd
      have h2 : (hyp.w1 : ℂ) * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1
          = (hyp.w1 : ℂ) * 1 := by rw [mul_one]; exact hd
      exact mul_left_cancel₀ hw1pos h2
    refine ⟨θ, hθne, ?_, rfl⟩
    rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
    intro x hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ1]
    exact θ.isIrreducible.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hθ1 hx

open scoped FiniteInduce in
/-- **Peterfalvi (6.5.a) for `(L, K, M) := (M, M′, 1)`** — the (10.10.1) index bound.

Book (p. 33): "**(6.5)** Assume Hypothesis (6.4) and that `𝒮(M)` is not coherent.
**(a)** `K/H₁` is a chief factor of `L` and `|K : H₁| ≤ 4|L : K|² + 1`."  Here
"**(6.4) Hypothesis.** (a) Assume that Hypothesis (6.1) holds and that `|L|` is odd.
(b) Let `M` be a normal subgroup of `L` contained in `K` such that `K/M` is nilpotent.
(c) Let `H₁/M` be the commutator subgroup of `K/M`.  Assume that `L/H₁` is a Frobenius group
with kernel `K/H₁`."

Instantiated at `(L, K, M) := (M, M′, 1)` for a type-V maximal `M` of the (10.1)
`Hypothesis` ((8.4.d)+(8.15) supply Hypothesis (6.4): type V makes `K = M′ = M_F` nilpotent
and `L/H₁ = M/M″` Frobenius with kernel `M′/M″`): `H₁ = [M′, M′] = M″`, so
`|K : H₁| = |M′ : M″|` is the abelianization order of `M′` and `|L : K| = |M : M′| = w₁`;
noncoherence of `𝒮(1) = 𝒮` yields `|M′ : M″| ≤ 4w₁² + 1` — the input of the (10.10.1)
parameter calculation `p = 2w₁ − 1` (`typeV_param_arithmetic`, with `|M′ : M″| = p²` from
`card_abelianization_eq_prime_sq_of_card_eq_prime_cube`).

**Now landed** (issue 9089, lane a): the six-two decomposition chain
(`exists_source_index_le_two_psi_of_ne_top` + `sixTwoDecompositionData`) was generalized to be
htype/chief-free (commits 6ce607ce, 5065c1ea), so it applies to type V's base `Hypothesis M`
directly.  The proof is the contrapositive of the (6.3) oracle
`S08.six_three_of_six_two_oracle` at `(L, K, H, M, H₁) = (M, M', M', 1, M'')` (`K = H = M'`,
`H₁ = ⁅M', M'⁆ = M''`); see `S13.coherent_S_of_coherent_SH0C` for the type III/IV template.  The
`hcoh` input (coherence of `𝒮(M'') = S(⁅M',M'⁆)`, the uniform degree-`w₁` irreducible family) is
the (5.7) coherence `SHC_isCoherent` after the identification
`inducedKernelFamily M' ⁅M',M'⁆ = SHCSet`. -/
theorem typeV_sixFiveA_bound [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hV : IsTypeV M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) ≤ 4 * hyp.w1 ^ 2 + 1 := by
  classical
  by_contra hgt
  rw [not_le] at hgt
  apply hnc
  obtain ⟨dV⟩ := hV
  obtain ⟨params, hmu, -, hζS, hζ1, hζne, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  -- instances on `K = M' = (derivedInG M).subgroupOf M`
  have hKnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hKnil : Group.IsNilpotent ↥((derivedInG M).subgroupOf M) :=
    TypeVData.isNilpotent_derivedInG_subgroupOf dV
  have hKsolv : Group.IsSolvable ↥((derivedInG M).subgroupOf M) := IsNilpotent.to_isSolvable
  -- `𝒮 = SOf ⊥`
  have hSset : hyp.Sset = OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    unfold OddOrder.Peterfalvi.S12.Hypothesis.Sset
    exact inducedFamily_eq_inducedKernelFamily_bot
  -- `⁅K,K⁆ < K` from the nontrivial abelianization (`|Ab K| > 4w₁²+1 ≥ 1`)
  have hcard_ab : 1 < Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) := by omega
  have hH₁H : (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ : Subgroup ↥M)
      < (derivedInG M).subgroupOf M := by
    refine lt_of_le_of_ne (Subgroup.commutator_le_left _ _) ?_
    intro heq
    have hcomm_top : commutator ↥((derivedInG M).subgroupOf M) = ⊤ := by
      rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self, heq, Subgroup.subgroupOf_self]
    have : Subsingleton (Abelianization ↥((derivedInG M).subgroupOf M)) := by
      change Subsingleton (↥((derivedInG M).subgroupOf M)
        ⧸ commutator ↥((derivedInG M).subgroupOf M))
      rw [hcomm_top]
      exact QuotientGroup.subsingleton_quotient_top
    have hcard1 : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = 1 :=
      Nat.card_unique
    omega
  -- ★ the (5.7) coherence of `𝒮(M″) = S(⁅K,K⁆)` — the uniform degree-`w₁` irreducible family
  have hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆)) hyp.A0) := by
    rw [inducedKernelFamily_commutator_eq_SHCSet hG hyp]
    exact ⟨hyp.SHC_isCoherent hG⟩
  rw [hSset]
  by_cases hcomm : (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ : Subgroup ↥M) = ⊥
  · -- `M'` abelian: `SOf ⊥ = SOf ⁅K,K⁆` is the whole family, coherent by `hcoh`
    rw [← hcomm]; exact hcoh
  · -- the (6.3) oracle: `SOf ⁅K,K⁆` coherent + the index bound ⟹ `SOf ⊥` coherent
    have hbound : 4 * ((derivedInG M).subgroupOf M).index ^ 2 + 1
        < Nat.card (↥((derivedInG M).subgroupOf M)
            ⧸ (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆).subgroupOf
              ((derivedInG M).subgroupOf M)) := by
      rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
      have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
        hyp.typeP.card_W1_eq_derived_index.symm
      rw [hidx]
      exact hgt
    refine OddOrder.Peterfalvi.S08.six_three_of_six_two_oracle
      (L := M) (K := (derivedInG M).subgroupOf M) (H := (derivedInG M).subgroupOf M)
      (M := ⊥) (H₁ := ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆)
      hKnorm bot_le hH₁H le_rfl hyp.tau hyp.A0
      (fun X => OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) X)
      ?_ hcoh hbound
    -- the (5.6) break-member oracle `h56` = the generalized §11/§13 dichotomy producer
    intro A B hAnorm hBnorm hBA hAH₁ _hcentral hAcoh hBncoh
    have := hAnorm
    have := hBnorm
    have : (A.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hAnorm.subgroupOf _
    have : (B.subgroupOf ((derivedInG M).subgroupOf M)).Normal := hBnorm.subgroupOf _
    have hAne : A.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd ((Subgroup.subgroupOf_eq_top.mp htop).trans hAH₁) (not_le_of_gt hH₁H)
    have hBne : B.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
      intro htop
      exact absurd ((Subgroup.subgroupOf_eq_top.mp htop).trans (hBA.trans hAH₁))
        (not_le_of_gt hH₁H)
    have hAcoh' : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A)
        hyp.A0) := hAcoh
    have hBncoh' : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
        hyp.A0) := fun h => hBncoh h
    exact hyp.exists_source_index_le_two_psi_of_ne_top hG hAne hBne
      (hyp.sixTwoDecompositionData hG hmu hδpm hδj hζS hζ1 A B) hAcoh' hBncoh'

open scoped FiniteInduce in
/-- **Peterfalvi (6.5.b) for `(L, K, M) := (M, M′, 1)`** — the not-(a) `p`-group reduction.

Book (p. 33): "**(6.5)** Assume Hypothesis (6.4) and that `𝒮(M)` is not coherent. …
**(b)** There is a prime number `p` such that `K/M` is a non-abelian `p`-group."

Instantiated at `(L, K, M) := (M, M′, 1)` (see `typeV_sixFiveA_bound` for the (6.4)
instantiation): if `𝒮` is not coherent then `M′` is a non-abelian `p`-group.  The prime is
folded to `p = w₂` following the (10.10) proof ("then `p = w₂` because `w₂` is a prime
divisor of `|H|`" — `W₂ ≤ M″ ≤ M′` with `w₂` prime, `Hypothesis.w2_prime`), so the
conclusion is stated with `hyp.w2` directly.

**Now landed** (issue 9089, lane a).  Non-abelian: if `M′` were abelian then `⁅M′,M′⁆ = ⊥`, so
`𝒮 = S(⁅M′,M′⁆) = SHCSet` (`inducedKernelFamily_commutator_eq_SHCSet`) is coherent
(`SHC_isCoherent`), contradicting `hnc`.  `p`-group: the `W₁`-conjugation action on `M′` has its
fixed points in `M″` (`TypePData.centralizer_W1`: `C_{M′}(w) = W₂ ⊆ M″`), so
`isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` fires with the (6.5.a) index bound
(`typeV_sixFiveA_bound`) to make the nilpotent `M′` a `p`-group; `p = w₂` since `w₂ ∣ |M′| = p^n`
with `w₂` prime. -/
theorem typeV_sixFiveB_pGroup [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hV : IsTypeV M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)) :
    IsPGroup hyp.w2 ↥(derivedInG M) ∧ ¬ IsMulCommutative ↥(derivedInG M) := by
  classical
  obtain ⟨dV⟩ := hV
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hKnorm : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hKnil : Group.IsNilpotent ↥((derivedInG M).subgroupOf M) :=
    TypeVData.isNilpotent_derivedInG_subgroupOf dV
  -- `⁅M′,M′⁆.map subtype = M″`
  have hmapcomm : Subgroup.map M.subtype
      (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ : Subgroup ↥M)
      = secondDerivedInAmbient M := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (show derivedInG M ≤ M from Subgroup.map_subtype_le _)]
    exact (Subgroup.map_subtype_commutator (derivedInG M)).symm
  -- ★ non-abelian
  have hnonab : ¬ IsMulCommutative ↥(derivedInG M) := by
    intro habel
    apply hnc
    have hKcomm : IsMulCommutative ↥((derivedInG M).subgroupOf M) :=
      ⟨⟨fun a b => (Subgroup.subgroupOfEquivOfLe hM'le).injective
        (by rw [map_mul, map_mul]; exact habel.is_comm.comm _ _)⟩⟩
    have hcommbot : (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ :
        Subgroup ↥M) = ⊥ := by
      have h1 : (⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆ :
          Subgroup ↥M).subgroupOf ((derivedInG M).subgroupOf M) = ⊥ := by
        rw [OddOrder.Peterfalvi.S08.commutator_subgroupOf_self]
        exact (commutator_eq_bot_iff _).mpr hKcomm
      exact (Subgroup.subgroupOf_eq_bot.mp h1).eq_bot_of_le (Subgroup.commutator_le_left _ _)
    have hSeq := inducedKernelFamily_commutator_eq_SHCSet hG hyp
    rw [hcommbot] at hSeq
    have hSset : hyp.Sset = OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
      unfold OddOrder.Peterfalvi.S12.Hypothesis.Sset
      exact inducedFamily_eq_inducedKernelFamily_bot
    rw [hSset, hSeq]
    exact ⟨hyp.SHC_isCoherent hG⟩
  refine ⟨?_, hnonab⟩
  -- ★ p-group: fixed-point-free `W₁`-action on `Ab(M′)` + the (6.5.a) bound
  let actH : MulDistribMulAction ↥(hyp.W1.subgroupOf M) ↥((derivedInG M).subgroupOf M) :=
    MulDistribMulAction.compHom ((derivedInG M).subgroupOf M)
      ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)).comp (hyp.W1.subgroupOf M).subtype)
  have hsmul : ∀ (a : ↥(hyp.W1.subgroupOf M)) (x : ↥((derivedInG M).subgroupOf M)),
      ((a • x : ↥((derivedInG M).subgroupOf M)) : ↥M)
        = (a : ↥M) * (x : ↥M) * (a : ↥M)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥((derivedInG M).subgroupOf M))
        = (MulDistribMulAction.toMulAut ↥(hyp.W1.subgroupOf M)
            ↥((derivedInG M).subgroupOf M) a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    change ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)
      ((hyp.W1.subgroupOf M).subtype a)) x : ↥M) = _
    rw [MulAut.conjNormal_apply]; rfl
  have hW1card : Nat.card ↥(hyp.W1.subgroupOf M) = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf M))
      (Nat.card ↥((derivedInG M).subgroupOf M)) := by
    rw [hW1card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv]
    exact (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP).symm
  have hfix : ∀ w : ↥(hyp.W1.subgroupOf M), w ≠ 1 → ∀ x : ↥((derivedInG M).subgroupOf M),
      w • x = x → x ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    intro a ha x hx
    have hc := hsmul a x
    rw [hx] at hc
    have hcommM : (a : ↥M) * (x : ↥M) = (x : ↥M) * (a : ↥M) :=
      mul_inv_eq_iff_eq_mul.mp hc.symm
    have haW1G : ((a : ↥M) : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp a.2
    have hane : ((a : ↥M) : G) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have hxM'G : ((x : ↥M) : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp x.2
    have hcommG : ((x : ↥M) : G) * ((a : ↥M) : G) = ((a : ↥M) : G) * ((x : ↥M) : G) := by
      simpa using (congrArg (fun t : ↥M => (↑t : G)) hcommM).symm
    have hxW2 : ((x : ↥M) : G) ∈ hyp.typeP.W2 := by
      rw [← hyp.typeP.centralizer_W1 _ haW1G hane]
      exact Subgroup.mem_inf.mpr ⟨hxM'G, Subgroup.mem_centralizer_singleton_iff.mpr hcommG⟩
    have hxsd : ((x : ↥M) : G) ∈ secondDerivedInAmbient M :=
      (hyp.typeP.W2_le.trans inf_le_right) hxW2
    have key : (x : ↥M) ∈ (⁅(derivedInG M).subgroupOf M,
        (derivedInG M).subgroupOf M⁆ : Subgroup ↥M) := by
      refine (Subgroup.mem_map_iff_mem M.subtype_injective).mp ?_
      rw [hmapcomm]; exact hxsd
    exact OddOrder.Peterfalvi.S08.commutator_subgroupOf_self ((derivedInG M).subgroupOf M) ▸
      Subgroup.mem_subgroupOf.mpr key
  have hWodd : Odd (Nat.card ↥(hyp.W1.subgroupOf M)) := by
    rw [hW1card]
    exact hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hHodd : Odd (Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))) :=
    hG.odd.of_dvd_nat
      (((Subgroup.card_quotient_dvd_card
          (commutator ↥((derivedInG M).subgroupOf M))).trans
        (Subgroup.card_subgroup_dvd_card ((derivedInG M).subgroupOf M))).trans
        (Subgroup.card_subgroup_dvd_card M))
  have hbound' : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      ≤ 4 * Nat.card ↥(hyp.W1.subgroupOf M) ^ 2 + 1 := by
    rw [hW1card]
    exact typeV_sixFiveA_bound hG hyp ⟨dV⟩ hnc
  obtain ⟨p, hp, hHp⟩ :=
      OddOrder.Peterfalvi.S08.isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator
    hcop hfix hHodd hWodd hbound'
  have : Fact p.Prime := ⟨hp⟩
  have hHp' : IsPGroup p ↥(derivedInG M) := hHp.of_equiv (Subgroup.subgroupOfEquivOfLe hM'le)
  have hw2prime : hyp.w2.Prime := hyp.w2_prime hG
  have hW2der : hyp.W2 ≤ derivedInG M :=
    (hyp.typeP.W2_le.trans inf_le_right).trans (Subgroup.map_subtype_le _)
  have hw2dvd : hyp.w2 ∣ Nat.card ↥(derivedInG M) := by
    have h := Subgroup.card_subgroup_dvd_card (hyp.W2.subgroupOf (derivedInG M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2der).toEquiv] at h
  obtain ⟨n, hn⟩ := hHp'.exists_card_eq
  have hpw2 : hyp.w2 = p :=
    (Nat.prime_dvd_prime_iff_eq hw2prime hp).mp (hw2prime.dvd_of_dvd_pow (hn ▸ hw2dvd))
  rw [hpw2]; exact hHp'

open scoped FiniteInduce in
/-- **Peterfalvi (6.5.c) for `(L, K, M) := (M, M′, 1)`** — the case-(b) killer.

Book (p. 33): "**(6.5)** Assume Hypothesis (6.4) and that `𝒮(M)` is not coherent. …
**(c)** `|L : K|` does not divide `p − 1`."

Instantiated at `(L, K, M) := (M, M′, 1)`: `|L : K| = w₁` and `p = w₂`
(`typeV_sixFiveB_pGroup`), so `w₁ ∤ w₂ − 1` (natural subtraction; `w₂ ≥ 3`).  In the (10.10)
proof this refutes case (b) of Definition (8.7): its prime `p′` with `w₁ ∣ p′ − 1` lies in
`(Nat.card ↥M′).primeFactors` of the `w₂`-group `M′`, so `p′ = w₂` — contradiction.

**Now landed** (issue 9089, lane a): the (6.5.c) arithmetic `S08.six_five_c_arith`.  If
`w₁ ∣ w₂ − 1`, then the non-abelian `w₂`-group `M′` (`typeV_sixFiveB_pGroup`) has
`w₂² ≤ |Ab M′|` (`sq_le_card_abelianization_of_isPGroup_of_noncomm`) while the (6.5.a) bound
(`typeV_sixFiveA_bound`) gives `|Ab M′| ≤ 4w₁² + 1`; with `w₁, w₂` odd and `w₂` prime, the
divisor gap `w₂ ≥ 2w₁ + 1` forces `w₂² ≥ (2w₁+1)² > 4w₁² + 1` — contradiction. -/
theorem typeV_sixFiveC_not_dvd [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hV : IsTypeV M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)) :
    ¬ (hyp.w1 ∣ hyp.w2 - 1) := by
  intro hdvd
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  obtain ⟨hpgrp, hnonab⟩ := typeV_sixFiveB_pGroup hG hyp hV hnc
  have hw2prime : hyp.w2.Prime := hyp.w2_prime hG
  have hw2odd : Odd hyp.w2 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W2)
  have hw1odd : Odd hyp.w1 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hnc' : ¬ ∀ a b : ↥(derivedInG M), a * b = b * a := fun h => hnonab ⟨⟨h⟩⟩
  -- `|Ab M′|` in the two coordinates (`↥M′ ≃* ↥(M′.subgroupOf M)`)
  have hcardeq : Nat.card (Abelianization ↥(derivedInG M))
      = Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) :=
    Nat.card_congr (MulEquiv.abelianizationCongr
      (Subgroup.subgroupOfEquivOfLe hM'le).symm).toEquiv
  have hpsq : hyp.w2 ^ 2 ≤ Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) :=
    hcardeq ▸ OddOrder.Peterfalvi.S08.sq_le_card_abelianization_of_isPGroup_of_noncomm
      hw2prime hpgrp hnc'
  have hbound : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      ≤ 4 * hyp.w1 ^ 2 + 1 := typeV_sixFiveA_bound hG hyp hV hnc
  exact OddOrder.Peterfalvi.S08.six_five_c_arith hw2prime hw2odd hw1odd hdvd hpsq hbound

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.10.1)–(10.10.4): a type-V maximal forces `𝒮` coherent** — the honest
three-branch assembly (issue 1021; supersedes the bare-sorry `typeV_forces_coherence` of
`S12_MaximalIII_IV_V`).

If `𝒮` is coherent there is nothing to prove; otherwise the (8.7) trichotomy of the type-V
datum (`TypeVData.alternative_transfer`, moved onto `hyp.typeP`) splits:

* **case (a)** (`H^# = (M′)^#` TI in `N_G(H)`): coherent by Theorem (6.8) — the landed
  sorry-free `S13.typeV_caseA_coherence`;
* **not (a)**: the (6.5) gates fire on the noncoherence — `M′` is a non-abelian `w₂`-group
  (`typeV_sixFiveB_pGroup`), so **case (b)** is refuted: its prime `p′` divides `|M′| = w₂^m`,
  hence `p′ = w₂` and `w₁ ∣ w₂ − 1` contradicts `typeV_sixFiveC_not_dvd`;
* **case (c)**: `O_p(H) = H` (a `p`-group is its own `p`-core), so `|M′| = p³` with `p = w₂`
  and `w₁ ∣ p + 1`; the (6.5.a) bound (`typeV_sixFiveA_bound`) with `|M′ : M″| = p²` (P1)
  runs (10.10.1) (`typeV_param_arithmetic`): `p = 2w₁ − 1`, `w₁ < w₂`; the grid parameter is
  pinned `d = p` (`muGrid_degree_eq_prime_of_card_eq_prime_cube`), whence `δ = −1`, `n = 2`
  (`delta_eq_neg_one` / `n_eq_two`); P2 supplies `|S₁| ≥ 8`, P4 the structure
  `S = S₁ ∪ {μ_j}`, and the (5.7) coherence `SHC_isCoherent` of `S₁` feeds the sorry-free
  (10.10.4) engine `typeV_caseC_coherence_engine`.

The assembly and the whole case-(c) package are `sorry`-free, as are the three (6.5) gate
lemmas this theorem used to be gated on (issue 2022, since closed). -/
theorem typeV_forces_coherence_v2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (hV : IsTypeV M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0) := by
  by_cases hnc : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0)
  · exact hnc
  -- `𝒮` not coherent: run the (8.7) trichotomy of the type-V datum on `hyp.typeP`
  obtain ⟨dV⟩ := hV
  have hHeq : derivedInG M = hyp.typeP.H := TypeVData.derivedInG_eq_H dV hyp.typeP
  have hw1eq : hyp.w1 = Nat.card ↥hyp.typeP.W1 := rfl
  rcases TypeVData.alternative_transfer dV hyp.typeP with hTI | hbc
  · -- case (a): `(M′)^#` is TI — Theorem (6.8) via the Sibley route
    exact ⟨OddOrder.Peterfalvi.S13.typeV_caseA_coherence hG hyp dV hTI⟩
  -- not-(a): the (6.5) gates fire on the noncoherence hypothesis
  obtain ⟨hpgrp, hnonab⟩ := typeV_sixFiveB_pGroup hG hyp ⟨dV⟩ hnc
  have hnd := typeV_sixFiveC_not_dvd hG hyp ⟨dV⟩ hnc
  have hw2prime : hyp.w2.Prime := hyp.w2_prime hG
  have : Fact hyp.w2.Prime := ⟨hw2prime⟩
  obtain ⟨m, hm⟩ := hpgrp.exists_card_eq
  rcases hbc with ⟨p', hp', hp'mem, hw1dvd, -⟩ | ⟨p, hp, hpmem, hOp, hdvdp1, -⟩
  · -- case (b) refuted: `p′ ∣ |M′| = w₂^m` gives `p′ = w₂`, so `w₁ ∣ w₂ − 1` — against (6.5.c)
    have hp'w2 : p' = hyp.w2 := by
      have hdvdH : p' ∣ Nat.card ↥(derivedInG M) := by
        rw [hHeq]
        exact (Nat.mem_primeFactors.mp hp'mem).2.1
      rw [hm] at hdvdH
      exact (Nat.prime_dvd_prime_iff_eq hp' hw2prime).mp (hp'.dvd_of_dvd_pow hdvdH)
    rw [hp'w2, ← hw1eq] at hw1dvd
    exact absurd hw1dvd hnd
  · -- case (c): `|M′| = p³`, `w₁ ∣ p + 1` — the (10.10.1)–(10.10.4) engine
    have : Fact p.Prime := ⟨hp⟩
    have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
    -- `p = w₂` (a prime divisor of the `w₂`-group `M′`)
    have hpw2 : p = hyp.w2 := by
      have hdvdH : p ∣ Nat.card ↥(derivedInG M) := by
        rw [hHeq]
        exact (Nat.mem_primeFactors.mp hpmem).2.1
      rw [hm] at hdvdH
      exact (Nat.prime_dvd_prime_iff_eq hp hw2prime).mp (hp.dvd_of_dvd_pow hdvdH)
    -- `M′` is a `p`-group, so `O_p(M′) = M′` and the case-(c) datum reads `|M′| = p³`
    have hHp : IsPGroup p ↥hyp.typeP.H := by
      rw [hpw2, ← hHeq]
      exact hpgrp
    have hcore : opiCoreInG ({p} : Set ℕ) hyp.typeP.H = hyp.typeP.H :=
      le_antisymm (opiCoreInG_le _ _)
        (le_opiCoreInG_of_normal_of_isPiSubgroup le_rfl
          (by rw [Subgroup.subgroupOf_self]; infer_instance)
          (isPiSubgroup_singleton_of_isPGroup hHp))
    have hcardH : Nat.card ↥((derivedInG M).subgroupOf M) = p ^ 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv, hHeq, ← hcore]
      exact hOp
    -- non-abelianness in the `subgroupOf` coordinate (P1/P2/P4 speak `(M′).subgroupOf M`)
    have hnonab' : ¬ IsMulCommutative ↥((derivedInG M).subgroupOf M) := by
      intro hcomm
      refine hnonab ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨x, rfl⟩ := (Subgroup.subgroupOfEquivOfLe hM'le).surjective a
      obtain ⟨y, rfl⟩ := (Subgroup.subgroupOfEquivOfLe hM'le).surjective b
      rw [← map_mul, ← map_mul, hcomm.is_comm.comm x y]
    -- (10.10.1): `p = 2w₁ − 1` and `w₁ < w₂` from the (6.5.a) bound and `|M′ : M″| = p²`
    have hbound := typeV_sixFiveA_bound hG hyp ⟨dV⟩ hnc
    have hab : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = p ^ 2 :=
      card_abelianization_eq_prime_sq_of_card_eq_prime_cube hp hcardH hnonab'
    have hboundp : p ^ 2 ≤ 4 * hyp.w1 ^ 2 + 1 := by
      rw [← hab]
      exact hbound
    have hpodd : Odd p := by
      rw [hpw2]
      exact hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W2)
    have hw1odd : Odd hyp.w1 :=
      hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
    have hw1gt : 1 < hyp.w1 :=
      (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    have hw13 : 3 ≤ hyp.w1 := by obtain ⟨k, hk⟩ := hw1odd; omega
    have hdvd : hyp.w1 ∣ p + 1 := by
      rw [hw1eq]
      exact hdvdp1
    obtain ⟨hp2w1, hw1ltp⟩ := typeV_param_arithmetic hpodd hw1odd hw1gt hdvd hboundp
    have hw12 : hyp.w1 < hyp.w2 := by omega
    have hp2w1Z : (p : ℤ) = 2 * (hyp.w1 : ℤ) - 1 := by omega
    -- the (10.2)/(10.3) parameter package with the (10.3) facts exposed
    obtain ⟨params, hmu, -, hζS, hζ1, hζne, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
    have hdeg : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ) := by
      intro i j hj
      rw [← hmu]
      exact params.degree_independent i j hj
    -- (10.10.2) numeric pins: `d = p`, `δ = −1`, `n = 2`
    have hdp : params.d = p :=
      hyp.muGrid_degree_eq_prime_of_card_eq_prime_cube hG hG.odd hp hcardH
        params.d_gt_one hdeg
    have hdZ : (params.d : ℤ) = 2 * (hyp.w1 : ℤ) - 1 := by
      rw [hdp]
      exact hp2w1Z
    have hδ : params.delta = -1 := params.delta_eq_neg_one hw13 hδpm hdZ
    have hn2 : params.n = 2 := params.n_eq_two (by omega) hdZ hδ
    -- grid degree data: zero column has degree `1`, both degrees avoid `ζ(1) = w₁`
    have hμ0 : ∀ i, hyp.muGrid hG hG.odd i 0 1 = 1 := fun i =>
      hyp.muGrid_zero_column_apply_one hG hG.odd i
    have hdζ : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
        hyp.muGrid hG hG.odd i j 1 ≠ params.zeta 1 := by
      intro i j hj
      rw [hdeg i j hj, hζ1]
      have hne : params.d ≠ hyp.w1 := by omega
      exact fun h => hne (by exact_mod_cast h)
    have h0ζ : ∀ i, hyp.muGrid hG hG.odd i 0 1 ≠ params.zeta 1 := by
      intro i
      rw [hμ0 i, hζ1]
      intro h
      have h1 : (1 : ℕ) = hyp.w1 := by exact_mod_cast h
      omega
    -- (10.10.2) structure package: the `h8` count and the dichotomy `S = S₁ ∪ {μ_j}`
    have h8 := hyp.eight_le_SHCcount_of_card_eq_prime_cube hG hp hcardH hnonab' hp2w1Z hw13
    have hstruct := hyp.mem_SHCSet_or_eq_muGrid_columnSum_of_card_eq_prime_cube hG hG.odd
      hp hpw2 hcardH hnonab'
    -- (5.7): `S₁ = S(HC)` is coherent; fire the (10.10.4) engine
    exact ⟨hyp.typeV_caseC_coherence_engine hG (hyp.SHC_isCoherent hG) hG.odd hζS
      params.zeta_irreducible hζ1 hζne hdeg hμ0 params.n_formula hδj hdζ h0ζ hδpm hn2 h8
      hw12 hstruct⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.10), unconditional**: `G` has no maximal subgroup of type V — the
`S12.no_typeV_maximal` conclusion re-founded on the unconditional (10.8)
(`S_not_coherent_unconditional`) and the three-branch (10.10.1)–(10.10.4) assembly
`typeV_forces_coherence_v2` (issue 1021); the (6.5) gate lemmas it was once gated on
(issue 2022) are proved. -/
theorem no_typeV_maximal_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M := by
  rintro ⟨M, hMmax, hMV⟩
  obtain ⟨hyp⟩ := exists_hypothesis_of_typeIIIorIVorV hG hMmax (Or.inr (Or.inr hMV))
  exact S_not_coherent_unconditional hG hyp (typeV_forces_coherence_v2 hG hyp hMV)

/-- **Peterfalvi (10.10) type dichotomy, unconditional**: the §11 hypothesis on a maximal `M`
forces type III or IV — the honest heir of `S12.Hypothesis.isTypeIIIorIV` (`S13_SixTwoBridge`),
with the type-V branch excluded by the axiom-clean `no_typeV_maximal_unconditional` instead of the
legacy `no_typeV_maximal` (whose `typeV_forces_coherence` was a bare `sorry`).  This is
`#print axioms`-clean and is the type-determination input threaded into the
`card_kappaHall_lt_of_isTypeIIIorIV` spine (issue 1025). -/
theorem isTypeIIIorIV_unconditional [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) : IsTypeIII M ∨ IsTypeIV M := by
  have : Fintype G := Fintype.ofFinite _
  rcases hyp.type_alt with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd ⟨M, hyp.maximal, h⟩ (no_typeV_maximal_unconditional hG)

end OddOrder.Peterfalvi.S12



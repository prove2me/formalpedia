-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_TypeIIIGalois
-- name    : OddOrder_Peterfalvi_S13_TypeIIIGalois
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:12:38.094198+00:00
-- url     : https://prove2.me/theorems/8ac0bbe9-2a29-45ab-bb4c-2af562d70306
-- title:
--   Peterfalvi (11.9): the row-0 projection, Galois constancy layer
-- statement:
--   Formalizes the Galois-transport layer of Peterfalvi (11.9) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §11, pp. 66-67).
--
--   Main declarations: `Hypothesis.mapRingEquiv_mem_SHC_stratum` (The Galois twist of `ζ` stays in the `S(HC)` stratum); `Hypothesis.tau_zeta_sub_mapRingEquiv_eq_SHC_extension` (The `S(HC)`-coherent `τ₁` computes the Galois-twist difference); `Hypothesis.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero` (The Galois-twist correction is orthogonal to the aligned `σ`-grid); `Hypothesis.mapRingEquiv_tau_muColumnZero_sub_zeta` (The Galois bridge for the Dade image of `μ₀ − ζ`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_TypeIIIGalois.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_TypeIIIGalois.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S12_Props109To1011
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **The Galois twist of `ζ` stays in the `S(HC)` stratum**: for `ζ ∈ S = inducedFamily M`
irreducible of degree `w₁` and a coefficient automorphism `u`, the twist `σζ` is again an
irreducible member of degree `w₁` (`inducedFamily_closedUnderMapRingEquiv`, `galoisMap`,
and `σ`-fixedness of the rational degree). -/
theorem Hypothesis.mapRingEquiv_mem_SHC_stratum [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.mapRingEquiv u ζ ∈ inducedFamily M ∧
      IsIrreducibleCharacter (ClassFunction.mapRingEquiv u ζ) ∧
      ClassFunction.mapRingEquiv u ζ 1 = (hyp.w1 : ℂ) := by
  refine ⟨inducedFamily_closedUnderMapRingEquiv M u hζS, ?_, ?_⟩
  · have h := (IrreducibleCharacter.galoisMap u ⟨ζ, hζirr⟩).isIrreducible
    rwa [IrreducibleCharacter.galoisMap_apply_coe] at h
  · rw [ClassFunction.mapRingEquiv_apply, hζ1, map_natCast]

open scoped FiniteInduce in
/-- **The `S(HC)`-coherent `τ₁` computes the Galois-twist difference** (the `σ`-generalization of
`tau_zeta_sub_conj_eq_SHC_extension`): `τ(ζ − σζ) = ζ^{τ₁} − (σζ)^{τ₁}`.  The difference is a
degree-`0` `ℤ`-combination of `S(HC)`-members, hence `A₀`-supported
(`SHC_zSpan_vanish_support`), where the coherent extension agrees with `τ`. -/
theorem Hypothesis.tau_zeta_sub_mapRingEquiv_eq_SHC_extension [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ)
      = coh.extension ζ - coh.extension (ClassFunction.mapRingEquiv u ζ) := by
  obtain ⟨hζuS, hζuirr, hζu1⟩ := hyp.mapRingEquiv_mem_SHC_stratum u hζS hζirr hζ1
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanζu : ClassFunction.mapRingEquiv u ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζuS, hζuirr, hζu1⟩
  have hsub1 : (ζ - ClassFunction.mapRingEquiv u ζ) 1 = 0 := by
    rw [ClassFunction.sub_apply, hζ1, hζu1, sub_self]
  have hmem : (ζ - ClassFunction.mapRingEquiv u ζ) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζu,
      hyp.SHC_zSpan_vanish_support hG (Submodule.sub_mem _ hspanζ hspanζu) hsub1⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

open scoped FiniteInduce in
/-- **The Galois-twist correction is orthogonal to the aligned `σ`-grid**:
`⟨τ(ζ − σζ), ω_{ij}^σ⟩ = 0`.  Both `τ₁`-images are `⊥`-grid by (5.3.b)
(`SHC_extension_inner_alignedOmegaSigma_eq_zero`, the non-reality inputs coming from the
odd order via `inducedFamily_hasNoRealCharacters`).  This is the `hcorrection` input of the
`a_aut` engine for the (11.9.a) row/column constancy. -/
theorem Hypothesis.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    (hodd : Odd (Nat.card G)) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      (hyp.alignedOmegaSigmaGrid hG hodd i j) = 0 := by
  have := hyp.finiteG
  obtain ⟨hζuS, hζuirr, hζu1⟩ := hyp.mapRingEquiv_mem_SHC_stratum u hζS hζirr hζ1
  have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hζne : ζ.conj ≠ ζ := fun h =>
    inducedFamily_hasNoRealCharacters hoddM hζS h
  have hζune : (ClassFunction.mapRingEquiv u ζ).conj ≠ ClassFunction.mapRingEquiv u ζ := fun h =>
    inducedFamily_hasNoRealCharacters hoddM hζuS h
  rw [hyp.tau_zeta_sub_mapRingEquiv_eq_SHC_extension hG coh u hζS hζirr hζ1,
    ClassFunction.inner_sub_left,
    hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζS hζirr hζ1 hζne i j,
    hyp.SHC_extension_inner_alignedOmegaSigma_eq_zero hG coh hodd hζuS hζuirr hζu1 hζune i j,
    sub_zero]

/-- **`w₁` is prime for a type-III/IV maximal subgroup**: the `TypePNontrivialCore` of the
type-III/IV data carries `(|W₁'|).Prime` for *its* type-`P` structure, and `|W₁| = [M : M']`
is independent of the choice (`card_W1_eq_derived_index`), so `hyp.w1` inherits primality. -/
theorem Hypothesis.w1_prime_of_typeIIIorIV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    (hyp.w1).Prime := by
  have hbase : hyp.w1 = Nat.card ↥hyp.typeP.W1 := rfl
  rcases htype with h3 | h4
  · obtain ⟨data⟩ := h3
    refine (show Nat.card ↥data.typeP.W1 = hyp.w1 from ?_) ▸ data.common.2.1
    rw [data.typeP.card_W1_eq_derived_index, hbase, hyp.typeP.card_W1_eq_derived_index]
  · obtain ⟨data⟩ := h4
    refine (show Nat.card ↥data.typeP.W1 = hyp.w1 from ?_) ▸ data.common.2.1
    rw [data.typeP.card_W1_eq_derived_index, hbase, hyp.typeP.card_W1_eq_derived_index]

open scoped FiniteInduce in
/-- **The Galois bridge for the Dade image of `μ₀ − ζ`** (Coq `aut_phi`):
`σ(τ(μ₀ − ζ)) = τ(μ₀ − ζ) + τ(ζ − σζ)`.  The Dade map commutes with `σ` on the `A₀`-supported
`μ₀ − ζ` (`tau_mapRingEquiv_comm`), the anchor `μ₀` is `σ`-fixed
(`mapRingEquiv_muColumnZero_sum`), and `τ` is additive.  This is the `hφ` input of the `a_aut`
engine (`inner_eq_intCast_of_mapRingEquiv_eq_add`) for the (11.9.a) constancy. -/
theorem Hypothesis.mapRingEquiv_tau_muColumnZero_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (u : ℂ ≃+* ℂ) {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.mapRingEquiv u
        (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ))
      = hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ)
        + hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ) := by
  have := hyp.finiteG
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  rw [← hyp.tau_mapRingEquiv_comm u hsupp, ← map_add]
  congr 1
  rw [ClassFunction.mapRingEquiv_sub, hyp.mapRingEquiv_muColumnZero_sum hG hodd u]
  abel

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.a), the column-`0` Galois constancy** (`a_{i'0} = a_{i0}` for
`i, i' ≠ 0`): the `σ`-grid coefficients of `ψ = τ(μ₀ − ζ)` along the punctured column `0` are
constant.  The `a_aut` engine (`inner_eq_intCast_of_mapRingEquiv_eq_add`) at the (3.9.b) grid
move `σ(ω_{i0}^σ) = ω_{i'0}^σ` (`exists_mapRingEquiv_chiFam_left_move`, `|W₁|` prime), with the
Galois bridge (`mapRingEquiv_tau_muColumnZero_sub_zeta`) and the correction orthogonality
(`tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero`). -/
theorem Hypothesis.inner_tau_muColumnZero_sub_zeta_columnZero_const [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {i i' : Fin hyp.w1} (hi : i ≠ 0) (hi' : i' ≠ 0) :
    ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
      = ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i 0) := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  have hchi := (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)
  -- the `(ρ 0, κ 0) = (1, 1)` anchor, from the trivial corner and orthonormality
  have h00 : (ρ 0, κ 0)
      = ((1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
        (1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)) := by
    by_contra hne
    have h0 := hchi.2.2.1 (ρ 0, κ 0) (1, 1)
    rw [if_neg hne, ← hprod 0 0, hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hchi.1] at h0
    have htmem : trivialClassFunction G ∈ irreducibleCharacters G :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner htmem htmem, if_pos rfl] at h0
    exact one_ne_zero h0
  have hρ0 : ρ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.1
  have hκ0 : κ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.2
  -- nontriviality of the moved indices
  have hpne : ρ i ≠ 1 := fun h => hi (hρinj (h.trans hρ0.symm))
  have hp'ne : ρ i' ≠ 1 := fun h => hi' (hρinj (h.trans hρ0.symm))
  -- `ψ` is a virtual character
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hμ0Z : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.muGrid_isIrreducible hG hodd r 0).mem_ZIrr)
  have hψZ : hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  -- the Galois move on the punctured column `0`
  have hprime : (Nat.card (typePData_toTICyclicHypothesis hyp.typeP hodd).W1).Prime :=
    hyp.w1_prime_of_typeIIIorIV htype
  obtain ⟨u, hmove⟩ :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).exists_mapRingEquiv_chiFam_left_move rfl
      (hyp.canonicalFullDadeApp hG hodd) hprime hpne hp'ne
  -- the integral coefficient at the source index
  have hηZ : (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
      (hyp.canonicalFullDadeApp hG hodd) (ρ i, 1) ∈ ZIrr G := hchi.2.1 _
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hψZ hηZ
  -- the correction orthogonality at the target index
  have hcorr : ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
        (hyp.canonicalFullDadeApp hG hodd) (ρ i', 1)) = 0 := by
    rw [← hκ0, ← hprod i' 0]
    exact hyp.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero hG coh hodd u
      hζS hζirr hζ1 i' 0
  -- the `a_aut` transport
  have htransport := ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add u m hψZ hηZ
    (hyp.mapRingEquiv_tau_muColumnZero_sub_zeta hG hodd u hζS hζ1) hmove.symm hm hcorr
  rw [hprod i' 0, hprod i 0, hκ0, htransport, hm]

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.a), the row-`0` Galois constancy** (`a_{0j'} = a_{0j}` for `j, j' ≠ 0`):
the `W₂`-side mirror of `inner_tau_muColumnZero_sub_zeta_columnZero_const`, via
`exists_mapRingEquiv_chiFam_right_move` and `|W₂|` prime (`w2_prime`). -/
theorem Hypothesis.inner_tau_muColumnZero_sub_zeta_rowZero_const [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {j j' : Fin hyp.w2} (hj : j ≠ 0) (hj' : j' ≠ 0) :
    ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd 0 j')
      = ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd 0 j) := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  have hchi := (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)
  have h00 : (ρ 0, κ 0)
      = ((1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
        (1 : ((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
          (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)) := by
    by_contra hne
    have h0 := hchi.2.2.1 (ρ 0, κ 0) (1, 1)
    rw [if_neg hne, ← hprod 0 0, hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hchi.1] at h0
    have htmem : trivialClassFunction G ∈ irreducibleCharacters G :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner htmem htmem, if_pos rfl] at h0
    exact one_ne_zero h0
  have hρ0 : ρ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.1
  have hκ0 : κ 0 = 1 := (Prod.mk.injEq _ _ _ _).mp h00 |>.2
  have hqne : κ j ≠ 1 := fun h => hj (hκinj (h.trans hκ0.symm))
  have hq'ne : κ j' ≠ 1 := fun h => hj' (hκinj (h.trans hκ0.symm))
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hμ0Z : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.muGrid_isIrreducible hG hodd r 0).mem_ZIrr)
  have hψZ : hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  have hprime : (Nat.card (typePData_toTICyclicHypothesis hyp.typeP hodd).W2).Prime :=
    hyp.w2_prime hG
  obtain ⟨u, hmove⟩ :=
    (typePData_toTICyclicHypothesis hyp.typeP hodd).exists_mapRingEquiv_chiFam_right_move rfl
      (hyp.canonicalFullDadeApp hG hodd) hprime hqne hq'ne
  have hηZ : (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
      (hyp.canonicalFullDadeApp hG hodd) (1, κ j) ∈ ZIrr G := hchi.2.1 _
  obtain ⟨m, hm⟩ := ClassFunction.inner_mem_ZIrr_int hψZ hηZ
  have hcorr : ClassFunction.inner (hyp.tau (ζ - ClassFunction.mapRingEquiv u ζ))
      ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
        (hyp.canonicalFullDadeApp hG hodd) (1, κ j')) = 0 := by
    rw [← hρ0, ← hprod 0 j']
    exact hyp.tau_zeta_sub_mapRingEquiv_inner_alignedOmegaSigma_eq_zero hG coh hodd u
      hζS hζirr hζ1 0 j'
  have htransport := ClassFunction.inner_eq_intCast_of_mapRingEquiv_eq_add u m hψZ hηZ
    (hyp.mapRingEquiv_tau_muColumnZero_sub_zeta hG hodd u hζS hζ1) hmove.symm hm hcorr
  rw [hprod 0 j', hprod 0 j, hρ0, htransport, hm]

open scoped FiniteInduce in
/-- The aligned column-`0` grid sum pairs with a grid vector by the column-`0` indicator:
`⟨∑_r ω_{r0}^σ, ω_{ij}^σ⟩ = δ_{j0}` (orthonormality, single surviving term `r = i`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_columnZero_sum_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    ClassFunction.inner (∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hodd r 0)
      (hyp.alignedOmegaSigmaGrid hG hodd i j) = (if j = 0 then (1 : ℂ) else 0) := by
  have := hyp.finiteG
  classical
  rw [inner_sum_left, Finset.sum_eq_single i]
  · rw [hyp.alignedOmegaSigmaGrid_inner hG hodd i i 0 j]
    by_cases hj : j = 0
    · rw [if_pos ⟨rfl, hj.symm⟩, if_pos hj]
    · rw [if_neg (fun hh => hj hh.2.symm), if_neg hj]
  · intro r _ hri
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd r i 0 j, if_neg (fun hh => hri hh.1)]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.a)**: for an irreducible `ζ ∈ S` of degree `w₁` whose column-`0` residual
is **not** orthogonal to the grid (the (11.8) input `h118`), the `σ`-grid coefficients of
`ψ = τ(μ₀ − ζ)` are the **row-`0` indicator**: `⟨ψ, ω_{ij}^σ⟩ = δ_{i0}`; equivalently
`ψ − ∑_j ω_{0j}^σ ⊥ (Irr W)^σ`.

The proof mirrors the book: `a₀₀ = 1` (Dade reciprocity), Galois constancy along the punctured
row/column (`inner_tau_muColumnZero_sub_zeta_columnZero_const`/`rowZero_const`), the (3.7)
separability (`sigmaCoeff_add_eq`), and the norm budget `∑ a² ≤ ‖ψ‖² = w₁ + 1`
(`sum_sq_inner_le_of_orthonormal`).  The integer case split then forces
`a_{11} = 0`, and `a_{10} ≠ 0` would make the grid part the column-`0` sum — refuted by `h118` —
so `a_{10} = 0` and `a_{01} = 1`. -/
theorem Hypothesis.inner_tau_muColumnZero_sub_zeta_rowZero_of_residual_not_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ}
    (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (h118 : ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
          - ∑ r : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd r 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner (hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hG.odd r 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = (if i = 0 then (1 : ℂ) else 0) := by
  have := hyp.finiteG
  classical
  have hodd : Odd (Nat.card G) := hG.odd
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  have : Fintype ((tic.W1.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ((tic.W2.subgroupOf tic.W) →* ℂˣ) := Fintype.ofFinite _
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    hyp.canonicalFullDadeApp hG hodd
  have hVeq : tic.V = tic.Vdiff := rfl
  have hcardW1 : Nat.card ↥tic.W1 = hyp.w1 := rfl
  have hcardW2 : Nat.card ↥tic.W2 = hyp.w2 := rfl
  have h3w1 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
  have h3w2 : (3 : ℕ) ≤ hyp.w2 := hcardW2 ▸ tic.three_le_card_W2
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  have hchi := tic.chiFam_spec hVeq app
  set ψ : ClassFunction G ℂ :=
    hyp.tau ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ) with hψ
  -- `μ₀ − ζ` is `A₀`-supported; `ψ` is a virtual character of norm `w₁ + 1`
  have hsupp : ((∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hζS hζ1
  have hμ0Z : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun r _ => (hyp.muGrid_isIrreducible hG hodd r 0).mem_ZIrr)
  have hψZ : ψ ∈ ZIrr G := by
    rw [hψ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp (Submodule.sub_mem _ hμ0Z hζirr.mem_ZIrr)
  have hψnorm : ClassFunction.inner ψ ψ = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hψ, hyp.tau_inner_eq_of_supported hsupp hsupp,
      inner_muColumnZero_sub_zeta_self hG hyp hζirr hζ1]
  -- `a₀₀ = 1`
  have hzeta_triv : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hζirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hζ1, trivialClassFunction_apply] at h1
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  have ha00 : ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd 0 0) = 1 := by
    rw [hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hψ, hyp.tau_inner_trivial hsupp,
      ClassFunction.inner_sub_left, hyp.muColumnZero_inner_trivial hG hodd, hzeta_triv, sub_zero]
  -- `ψ` vanishes on `V` (for the (3.7) separability)
  have hpsiV : ∀ v ∈ tic.V, ψ v = 0 := by
    intro v hv
    have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
    rw [hψ, hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hζv : ζ ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    have hμv : (∑ r : Fin hyp.w1, hyp.muGrid hG hodd r 0) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hnotmem
    rw [ClassFunction.sub_apply, hμv, hζv, sub_zero]
  -- integer grid coefficients
  have hgridZ : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      hyp.alignedOmegaSigmaGrid hG hodd i j ∈ ZIrr G := by
    intro i j
    rw [hprod i j]
    exact hchi.2.1 _
  have hint : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), ∃ m : ℤ,
      ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j) = (m : ℂ) := fun i j =>
    ClassFunction.inner_mem_ZIrr_int hψZ (hgridZ i j)
  choose n hn using hint
  have hn00 : n 0 0 = 1 := by
    have := (hn 0 0).symm.trans ha00
    exact_mod_cast this
  -- the punctured-row/column constancy (the Galois layer)
  have hi₁ : (⟨1, by omega⟩ : Fin hyp.w1) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  have hj₁ : (⟨1, by omega⟩ : Fin hyp.w2) ≠ 0 := by
    intro h; exact absurd (congrArg Fin.val h) (by simp)
  set A : ℤ := n ⟨1, by omega⟩ 0 with hAdef
  set B : ℤ := n 0 ⟨1, by omega⟩ with hBdef
  have hA : ∀ i : Fin hyp.w1, i ≠ 0 → n i 0 = A := by
    intro i hi
    have h := hyp.inner_tau_muColumnZero_sub_zeta_columnZero_const hG htype coh hζS hζirr hζ1
      hi₁ hi
    rw [← hψ, hn i 0, hn ⟨1, by omega⟩ 0] at h
    exact_mod_cast h
  have hB : ∀ j : Fin hyp.w2, j ≠ 0 → n 0 j = B := by
    intro j hj
    have h := hyp.inner_tau_muColumnZero_sub_zeta_rowZero_const hG coh hζS hζirr hζ1 hj₁ hj
    rw [← hψ, hn 0 j, hn 0 ⟨1, by omega⟩] at h
    exact_mod_cast h
  -- the (3.7) separability, integer form: `n i j + n 0 0 = n i 0 + n 0 j`
  have hsep : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), n i j + n 0 0 = n i 0 + n 0 j := by
    intro i j
    have hcoeff : ∀ (i' : Fin hyp.w1) (j' : Fin hyp.w2),
        tic.sigmaCoeff hVeq app ψ (ρ i', κ j')
          = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i' j') := by
      intro i' j'
      change ClassFunction.inner ψ (tic.chiFam hVeq app (ρ i', κ j')) = _
      rw [← hprod i' j']
    have h := tic.sigmaCoeff_add_eq hVeq app hpsiV (ρ i) (ρ 0) (κ j) (κ 0)
    rw [hcoeff i j, hcoeff 0 0, hcoeff i 0, hcoeff 0 j, hn i j, hn 0 0, hn i 0, hn 0 j] at h
    exact_mod_cast h
  have hC : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), i ≠ 0 → j ≠ 0 → n i j = A + B - 1 := by
    intro i j hi hj
    have := hsep i j
    rw [hn00, hA i hi, hB j hj] at this
    omega
  -- Bessel: `∑ n² ≤ w₁ + 1`
  have hbessel : (∑ p : Fin hyp.w1 × Fin hyp.w2, n p.1 p.2 ^ 2) ≤ ((hyp.w1 + 1 : ℕ) : ℤ) := by
    refine sum_sq_inner_le_of_orthonormal (v := fun p : Fin hyp.w1 × Fin hyp.w2 =>
      hyp.alignedOmegaSigmaGrid hG hodd p.1 p.2) (fun p => hgridZ p.1 p.2) ?_ hψZ hψnorm
      (fun p => hn p.1 p.2)
    intro p q
    rw [hyp.alignedOmegaSigmaGrid_inner hG hodd p.1 q.1 p.2 q.2]
    simp [Prod.ext_iff]
  -- the sum in closed form
  have hcard1 : ((Finset.univ.erase (0 : Fin hyp.w1)).card : ℤ) = (hyp.w1 : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ hyp.w1 := by omega
    push_cast [this]
    omega
  have hcard2 : ((Finset.univ.erase (0 : Fin hyp.w2)).card : ℤ) = (hyp.w2 : ℤ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ hyp.w2 := by omega
    push_cast [this]
    omega
  have hsum : (∑ p : Fin hyp.w1 × Fin hyp.w2, n p.1 p.2 ^ 2)
      = 1 + ((hyp.w1 : ℤ) - 1) * A ^ 2 + ((hyp.w2 : ℤ) - 1) * B ^ 2
        + ((hyp.w1 : ℤ) - 1) * (((hyp.w2 : ℤ) - 1) * (A + B - 1) ^ 2) := by
    rw [Fintype.sum_prod_type]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin hyp.w1))]
    have hrow0 : (∑ j : Fin hyp.w2, n 0 j ^ 2) = 1 + ((hyp.w2 : ℤ) - 1) * B ^ 2 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin hyp.w2)), hn00, one_pow]
      congr 1
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [hB j (Finset.ne_of_mem_erase hj)]), Finset.sum_const, nsmul_eq_mul, hcard2]
    have hrowi : ∀ i ∈ Finset.univ.erase (0 : Fin hyp.w1),
        (∑ j : Fin hyp.w2, n i j ^ 2)
          = A ^ 2 + ((hyp.w2 : ℤ) - 1) * (A + B - 1) ^ 2 := by
      intro i hi
      have hine := Finset.ne_of_mem_erase hi
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin hyp.w2)), hA i hine]
      congr 1
      rw [Finset.sum_congr rfl (fun j hj => by
        rw [hC i j hine (Finset.ne_of_mem_erase hj)]), Finset.sum_const, nsmul_eq_mul, hcard2]
    rw [hrow0, Finset.sum_congr rfl hrowi, Finset.sum_const, nsmul_eq_mul, hcard1]
    ring
  have hbound : 1 + ((hyp.w1 : ℤ) - 1) * A ^ 2 + ((hyp.w2 : ℤ) - 1) * B ^ 2
      + ((hyp.w1 : ℤ) - 1) * (((hyp.w2 : ℤ) - 1) * (A + B - 1) ^ 2)
      ≤ (hyp.w1 : ℤ) + 1 := by
    rw [← hsum]
    calc (∑ p : Fin hyp.w1 × Fin hyp.w2, n p.1 p.2 ^ 2)
        ≤ ((hyp.w1 + 1 : ℕ) : ℤ) := hbessel
      _ = (hyp.w1 : ℤ) + 1 := by push_cast; ring
  have h3w1' : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast h3w1
  have h3w2' : (3 : ℤ) ≤ (hyp.w2 : ℤ) := by exact_mod_cast h3w2
  -- the integer case split: `A + B − 1 = 0`, then `A = 0` (else the column-`0` form, refuted
  -- by `h118`), hence `B = 1`
  have h0w1 : (0 : ℤ) ≤ (hyp.w1 : ℤ) - 1 := by linarith
  have h0w2 : (0 : ℤ) ≤ (hyp.w2 : ℤ) - 1 := by linarith
  have hC0 : A + B - 1 = 0 := by
    by_contra hCne
    have h1 : 1 ≤ (A + B - 1) ^ 2 := by
      have := sq_nonneg (A + B - 1)
      rcases lt_or_eq_of_le this with h | h
      · omega
      · exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h.symm) hCne
    have hp2 : ((hyp.w1 : ℤ) - 1) * (((hyp.w2 : ℤ) - 1) * 1)
        ≤ ((hyp.w1 : ℤ) - 1) * (((hyp.w2 : ℤ) - 1) * (A + B - 1) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h0w2) h0w1
    have hp3 : ((hyp.w1 : ℤ) - 1) * 2 ≤ ((hyp.w1 : ℤ) - 1) * ((hyp.w2 : ℤ) - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) h0w1
    have hA2 : 0 ≤ ((hyp.w1 : ℤ) - 1) * A ^ 2 := mul_nonneg h0w1 (sq_nonneg A)
    have hB2 : 0 ≤ ((hyp.w2 : ℤ) - 1) * B ^ 2 := mul_nonneg h0w2 (sq_nonneg B)
    nlinarith [hbound, hp2, hp3, hA2, hB2]
  have hA0 : A = 0 := by
    by_contra hAne
    have hA1 : 1 ≤ A ^ 2 := by
      have := sq_nonneg A
      rcases lt_or_eq_of_le this with h | h
      · omega
      · exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h.symm) hAne
    have hB0 : B = 0 := by
      by_contra hBne
      have hB1 : 1 ≤ B ^ 2 := by
        have := sq_nonneg B
        rcases lt_or_eq_of_le this with h | h
        · omega
        · exact absurd (pow_eq_zero_iff (n := 2) (by omega) |>.mp h.symm) hBne
      have hq1 : ((hyp.w1 : ℤ) - 1) * 1 ≤ ((hyp.w1 : ℤ) - 1) * A ^ 2 :=
        mul_le_mul_of_nonneg_left hA1 h0w1
      have hq2 : ((hyp.w2 : ℤ) - 1) * 1 ≤ ((hyp.w2 : ℤ) - 1) * B ^ 2 :=
        mul_le_mul_of_nonneg_left hB1 h0w2
      have hq3 : 0 ≤ ((hyp.w1 : ℤ) - 1) * (((hyp.w2 : ℤ) - 1) * (A + B - 1) ^ 2) :=
        mul_nonneg h0w1 (mul_nonneg h0w2 (sq_nonneg _))
      nlinarith [hbound, hq1, hq2, hq3]
    have hA1' : A = 1 := by omega
    -- the grid part is the column-`0` sum: refute `h118`
    apply h118
    intro i j
    rw [ClassFunction.inner_sub_left,
      hyp.alignedOmegaSigmaGrid_columnZero_sum_inner hG hodd i j, hn i j]
    rcases eq_or_ne j 0 with rfl | hj
    · rcases eq_or_ne i 0 with rfl | hi
      · rw [hn00, if_pos rfl]; norm_num
      · rw [hA i hi, hA1', if_pos rfl]; norm_num
    · rcases eq_or_ne i 0 with rfl | hi
      · rw [hB j hj, hB0, if_neg hj]; norm_num
      · rw [hC i j hi hj, hA1', hB0, if_neg hj]; norm_num
  have hB1 : B = 1 := by omega
  -- conclusion: the row-`0` indicator
  intro i j
  rw [hn i j]
  rcases eq_or_ne i 0 with rfl | hi
  · rcases eq_or_ne j 0 with rfl | hj
    · rw [hn00, if_pos rfl]; norm_num
    · rw [hB j hj, hB1, if_pos rfl]; norm_num
  · rcases eq_or_ne j 0 with rfl | hj
    · rw [hA i hi, hA0, if_neg hi]; norm_num
    · rw [hC i j hi hj, hA0, hB1, if_neg hi]; norm_num

end OddOrder.Peterfalvi.S12



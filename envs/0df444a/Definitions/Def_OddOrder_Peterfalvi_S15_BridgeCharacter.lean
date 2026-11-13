-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
-- name    : OddOrder_Peterfalvi_S15_BridgeCharacter
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:15:15.242202+00:00
-- url     : https://prove2.me/theorems/a75aad25-08ed-4f7e-a1f3-4ff8f2567ec5
-- title:
--   Peterfalvi (13.18): the bridge characters $\beta_j$ and $\Gamma$
-- statement:
--   Formalizes the (13.18) $S$-side bridge character $\beta_j=\mathrm{Ind}_{PW_1}^S 1-\mu_{0j}$, its Dade image, and the prime-TI Dade cross-relations on the $S$- and $T$-sides.
--
--   Main declarations: `tauS_mu_cross` ((4.8)/(5.3) prime-`TI` Dade cross-relation, full-grid form); `tauT_nu_cross` ((4.8)/(5.3) prime-`TI` Dade cross-relation, `T`-side full-grid form); `tauT_nuRow_diff_eq` (The honest Dade image of a reducible `𝒯`-member row difference).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_BridgeCharacter.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_BridgeCharacter.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacterBasic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, full-grid form**:
`τ_S(μ_{i,j₁} − μ_{i,j₂}) = η_{i,j₁} − η_{i,j₂}` for any row `i` and distinct nontrivial columns
`j₁ ≠ j₂` (both `≠ 0`).  The all-rows/all-cols generalization of `tauS_mu_row0_cross` (Coq
`prDade_sub_TIirr` with the FT sign `δ = 1`): `X := τ_S(μ-diff)` is a norm-`2` `ZIrr` character
(Dade isometry on the `A₀(S)`-supported difference `tauS_mu_diff_support`) agreeing with
`η_{i,j₁} − η_{i,j₂}` on the regular set `V^S` (`tauS_mu_vanish_on_V`), so `S16.eta_diff_rigidity`
(Pf (3.8), general in the row `i`) pins it.  This is the per-row engine the reducible caseB
`R`-family sums over a μ-column: `τ_S(μ_j − μ̄_j) = ∑ᵢ τ_S(μ_{ij} − μ_{ik}) = ∑ᵢ(η_{ij} − η_{ik})`
(for the two column indices `j ≠ k` of `μ_j`, `μ̄_j`). -/
theorem tauS_mu_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) (hj12 : j1 ≠ j2) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData)
        (hyp.mu i j1 - hyp.mu i j2)
      = hyp.eta i j1 - hyp.eta i j2 := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) with hD
  have hμaIrr : IsIrreducibleCharacter (hyp.mu i j1) := hyp.mu_irreducible _ _
  have hμbIrr : IsIrreducibleCharacter (hyp.mu i j2) := hyp.mu_irreducible _ _
  have h_ab : ClassFunction.inner (hyp.mu i j1) (hyp.mu i j2) = 0 := by
    rw [hyp.mu_orthonormal]; exact if_neg (fun hc => hj12 hc.2)
  have h_ba : ClassFunction.inner (hyp.mu i j2) (hyp.mu i j1) = 0 := by
    rw [hyp.mu_orthonormal]; exact if_neg (fun hc => (Ne.symm hj12) hc.2)
  have hsupp := hyp.tauS_mu_diff_support hG i hj1 hj2
  have hZIrrS : (hyp.mu i j1 - hyp.mu i j2) ∈ ZIrr (↥hyp.S) :=
    (ZIrr (↥hyp.S)).sub_mem hμaIrr.mem_ZIrr hμbIrr.mem_ZIrr
  -- (a) `X ∈ ZIrr G`.
  have hXZ : D (hyp.mu i j1 - hyp.mu i j2) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS0 hG) hsupp hZIrrS
  -- (b) `‖μ_{i,j₁} − μ_{i,j₂}‖² = 2`, transported through the Dade isometry.
  have hnorm2 : ClassFunction.inner (hyp.mu i j1 - hyp.mu i j2)
      (hyp.mu i j1 - hyp.mu i j2) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, h_ab, h_ba,
      hμaIrr.inner_self_eq_one, hμbIrr.inner_self_eq_one]
    ring
  have hX2 : ClassFunction.inner (D (hyp.mu i j1 - hyp.mu i j2))
      (D (hyp.mu i j1 - hyp.mu i j2)) = 2 := by
    rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS0 hG) hsupp hsupp]
    exact hnorm2
  -- (c) `X − (η_{i,j₁} − η_{i,j₂})` vanishes on the regular set `V^S`.
  have hvanish : ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (D (hyp.mu i j1 - hyp.mu i j2)
        - ((1 : ℤ) : ℂ) • (hyp.eta i j1 - hyp.eta i j2)) x = 0 := by
    intro x hx
    have hv := hyp.tauS_mu_vanish_on_V hG hnoV i hj1 hj2 x hx
    simpa [hD] using hv
  -- (3.8) rigidity: a norm-`2` `ZIrr` character agreeing with `η_{i,j₁} − η_{i,j₂}` on `V` is it.
  have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity hyp hXZ hX2 i hj12
    (s := (1 : ℤ)) (Or.inl rfl) hvanish
  rw [Int.cast_one, one_smul] at hrig
  exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(4.8)/(5.3) prime-`TI` Dade cross-relation, `T`-side full-grid form** (mirror of
`tauS_mu_cross`): `τ_T(ν_{r,j} − ν_{s,j}) = η_{r,j} − η_{s,j}` for any column `j` and
distinct nontrivial rows `r ≠ s` (both `≠ 0`).  `X := τ_T(ν-diff)` is a norm-`2` `ZIrr`
character (Dade isometry on the `A₀(T)`-supported difference `tauT_nu_diff_support`)
agreeing with `η_{r,j} − η_{s,j}` on the regular set (`tauT_nu_vanish_on_V`); the (3.8)
rigidity is the **swap-transposed** `S16.eta_diff_rigidity` at `hyp.swap` (whose `η`-grid is
the transpose, so its row-fixed/column-difference form *is* the `T`-side
column-fixed/row-difference form), with the swap's structural input `hV` supplied by the
unconditional `isMulCommutative_V_unconditional`.  This is the per-column engine the
reducible caseB-`T` `R`-family sums over a ν-row:
`τ_T(ν_r − ν̄_r) = ∑_j τ_T(ν_{rj} − ν_{sj}) = ∑_j(η_{rj} − η_{sj})`. -/
theorem tauT_nu_cross [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
        (hyp.nu r j - hyp.nu s j)
      = hyp.eta r j - hyp.eta s j := by
  classical
  set D := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
      ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
    with hD
  have hνaIrr : IsIrreducibleCharacter (hyp.nu r j) := pins.nu_irreducible _ _
  have hνbIrr : IsIrreducibleCharacter (hyp.nu s j) := pins.nu_irreducible _ _
  have h_ab : ClassFunction.inner (hyp.nu r j) (hyp.nu s j) = 0 := by
    rw [pins.nu_orthonormal]; exact if_neg (fun hc => hrs hc.1)
  have h_ba : ClassFunction.inner (hyp.nu s j) (hyp.nu r j) = 0 := by
    rw [pins.nu_orthonormal]; exact if_neg (fun hc => (Ne.symm hrs) hc.1)
  have hsupp := hyp.tauT_nu_diff_support hG pins Tdata hU hW1 hW2 j hr hs
  have hZIrrT : (hyp.nu r j - hyp.nu s j) ∈ ZIrr (↥hyp.T) :=
    (ZIrr (↥hyp.T)).sub_mem hνaIrr.mem_ZIrr hνbIrr.mem_ZIrr
  -- (a) `X ∈ ZIrr G`.
  have hXZ : D (hyp.nu r j - hyp.nu s j) ∈ ZIrr G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypT0 hG hTP Tdata) hsupp hZIrrT
  -- (b) norm `2`, transported through the Dade isometry.
  have hnorm2 : ClassFunction.inner (hyp.nu r j - hyp.nu s j)
      (hyp.nu r j - hyp.nu s j) = 2 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, h_ab, h_ba,
      hνaIrr.inner_self_eq_one, hνbIrr.inner_self_eq_one]
    ring
  have hX2 : ClassFunction.inner (D (hyp.nu r j - hyp.nu s j))
      (D (hyp.nu r j - hyp.nu s j)) = 2 := by
    rw [hD, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypT0 hG hTP Tdata) hsupp hsupp]
    exact hnorm2
  -- (c) `X − (η_{r,j} − η_{s,j})` vanishes on the regular set.
  have hvanish : ∀ x ∈ conjClassSet
      ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (D (hyp.nu r j - hyp.nu s j)
        - ((1 : ℤ) : ℂ) • (hyp.eta r j - hyp.eta s j)) x = 0 := by
    intro x hx
    have hv := hyp.tauT_nu_vanish_on_V hG hnoV pins hTP Tdata hU hW1 hW2 j hr hs x hx
    simpa [hD] using hv
  -- (3.8) rigidity, column form — directly at `hyp` (issue 2035 #86 de-swap)
  have hrig := OddOrder.Peterfalvi.S16.eta_diff_rigidity_col
    hyp hXZ hX2 hrs j (s := (1 : ℤ)) (Or.inl rfl) hvanish
  rw [Int.cast_one, one_smul] at hrig
  exact hrig

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The honest Dade image of a reducible `𝒯`-member row difference** (mirror of
`tauS_muColumn_diff_eq`; route B, the core of the reducible caseB-`T` `R`-family): for a
reducible `η = ∑_j ν_{rj} ∈ 𝒯` with conjugate `η̄ = ∑_j ν_{sj}` (`r ≠ s`, both `≠ 0`), the
honest `A(T)`-Dade image is `τ_T(η − η̄) = ∑_j(η_{rj} − η_{sj})` — the `A`/`A₀` Dade maps agree
with `Ind_T^G` on the `A(T)`-supported difference (`tInstance_dade_eq_induce` /
`tInstance_dade0_eq_induce`), and the per-column cross-relation `tauT_nu_cross` evaluates each
summand. -/
theorem tauT_nuRow_diff_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {r s : Fin hyp.q}
    (hr0 : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs0 : s ≠ ⟨0, hyp.q_prime.pos⟩) (hrs : r ≠ s)
    {η : ClassFunction ↥hyp.T ℂ}
    (hη : η ∈ OddOrder.Peterfalvi.S11.sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hreq : η = ∑ j : Fin hyp.p, hyp.nu r j)
    (hseq : (η : ClassFunction ↥hyp.T ℂ).conj = ∑ j : Fin hyp.p, hyp.nu s j) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = ∑ j : Fin hyp.p, (hyp.eta r j - hyp.eta s j) := by
  classical
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  -- `η − η̄ = ∑_j(ν_{rj} − ν_{sj})`.
  have hsub : (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = ∑ j : Fin hyp.p, (hyp.nu r j - hyp.nu s j) := by
    rw [hseq, hreq, ← Finset.sum_sub_distrib]
  -- `A(T)`-support of the row difference.
  have hAsupp : (η - (η : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    rw [show (η - (η : ClassFunction ↥hyp.T ℂ).conj)
        = -((η : ClassFunction ↥hyp.T ℂ).conj - η) from by abel,
      ClassFunction.support_neg]
    exact hyp.sSet_member_conjDiff_supported_T hG hvd hη
  have hA0supp : (η - (η : ClassFunction ↥hyp.T ℂ).conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T :=
    hAsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono
      (S10.typePACore_subset_A0Set Tdata))
  -- the honest `A`-Dade agrees with the `A₀`-Dade on the `A(T)`-supported row difference.
  have hτeq : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData)
        (η - (η : ClassFunction ↥hyp.T ℂ).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
          ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
          (η - (η : ClassFunction ↥hyp.T ℂ).conj) := by
    rw [hyp.tInstance_dade_eq_induce hG hnoV hTP hAsupp,
      hyp.tInstance_dade0_eq_induce hG hnoV hTP Tdata hA0supp]
  rw [hτeq, hsub, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    tauT_nu_cross hG hnoV hyp pins hTP Tdata hU hW1 hW2 j hr0 hs0 hrs

end OddOrder.Peterfalvi.S15



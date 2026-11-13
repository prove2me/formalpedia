-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_Prop109
-- name    : OddOrder_Peterfalvi_S12_Prop109
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:15:51.175671+00:00
-- url     : https://prove2.me/theorems/f4e12b0e-b493-4d66-b162-50e7165ea225
-- title:
--   Peterfalvi (10.9): the column-0 $\mu$-sum and the trivial character
-- statement:
--   Formalizes facts for Peterfalvi (10.9): the row-0, column-0 entry of the $\mu$-grid is the trivial character, and the column-0 $\mu$-sum satisfies the corresponding inner-product and Galois-fixedness properties.
--
--   Main declarations: `Hypothesis.muGrid_zero_zero_eq_trivial` (§10 column-`0` row-`0` is the trivial character); `Hypothesis.muColumnZero_inner_trivial` (§10 `⟨μ_0, 1_M⟩ = 1`); `Hypothesis.mapRingEquiv_muColumnZero_sum` (The column-`0` `μ`-sum is Galois-fixed); `inner_muColumnZero_sub_zeta_self` (Peterfalvi (10.9)/(11.8.4) norm).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_Prop109.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_Prop109.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalBasic

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **§10 column-`0` row-`0` is the trivial character** (the `μ_{00} = 1_M` anchor, Peterfalvi
(4.3.a)/(4.5)): the `(0,0)` entry of the materialized `μ`-grid is the trivial class function of `M`.
This is the §6 certain-type anchor `certainType_zero_column_anchor.2` read through the `muGrid`
definition (same reconstruction as `muGrid_zero_column_apply_one`). -/
theorem Hypothesis.muGrid_zero_zero_eq_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.muGrid hG hodd 0 0 = trivialClassFunction (↥M) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have hrow0 : (finCongr hcardW1.symm (0 : Fin hyp.w1)) = 0 := by apply Fin.ext; simp
  have e00 : hyp.muGrid hG hodd 0 0
      = ((h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm (0 : Fin
          hyp.w2)))).mu
          (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid; rfl
  rw [e00, hdual0, hrow0, h.certainType_zero_column_anchor.2]

open scoped FiniteInduce in
/-- **§10 `⟨μ_0, 1_M⟩ = 1`** (Peterfalvi (10.9), the `a_{00}` constant term, M-side): the column-`0`
sum `μ_0 = ∑_i μ_{i0}` has principal multiplicity `1`, since `μ_{00} = 1_M` (anchor,
`muGrid_zero_zero_eq_trivial`) contributes `1` and the remaining `μ_{i0}` (`i ≠ 0`) are orthogonal
to
`μ_{00}` (column-`0` orthonormality, `muGrid_inner_within_column`). -/
theorem Hypothesis.muColumnZero_inner_trivial [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
        (trivialClassFunction (↥M)) = 1 := by
  have := hyp.finiteG
  classical
  have : NeZero hyp.w1 := ⟨by
    have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
    omega⟩
  rw [← hyp.muGrid_zero_zero_eq_trivial hG hodd, inner_sum_left]
  rw [Finset.sum_eq_single (0 : Fin hyp.w1)]
  · exact hyp.muGrid_inner_self hG hodd 0 0
  · intro i _ hi
    exact hyp.muGrid_inner_within_column hG hodd 0 hi
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped FiniteInduce in
/-- **The column-`0` `μ`-sum is Galois-fixed**: `σ(μ_0) = μ_0` for every coefficient automorphism
`σ : ℂ ≃+* ℂ`.  The column-`0` sum is the induction of the trivial character of `K = HC`
(`μ_0 = ∑_i μ_{i0} = Ind_K^M (Res_K μ_{00}) = Ind_K^M 1_K` — Peterfalvi (4.5.a)
`induce_restrict_certainType_eq` at `χ₂ = 1` with the trivial restriction
`chiRestrict_one_eq_trivial`), and induction commutes with `mapRingEquiv`
(`ClassFunction.mapRingEquiv_induce`) while the trivial character is `σ`-fixed.  This is the
`M`-side `ν(μ_0) = μ_0` input (Coq `prTIred_aut` + `aut_Iirr0`) of the Galois row/column-constancy
step of the (11.9.a) grid analysis (issue 1024 G1; cf. the `T`-side
`primeTIred_zero_mapRingEquiv`). -/
theorem Hypothesis.mapRingEquiv_muColumnZero_sum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (σ : ℂ ≃+* ℂ) :
    ClassFunction.mapRingEquiv σ (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 := by
  have := hyp.finiteG
  classical
  -- Reconstruct the §6 host, as in `muGrid_zero_zero_eq_trivial`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  -- the column-`0` sum in the §6 host: reindex `Fin w₁ ≃ Fin |W₁|`, rewrite the dual `0 ↦ 1`.
  have hsum : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0)
      = ∑ i', ((h.columnFamily 1).mu i' : ClassFunction ↥M ℂ) := by
    have hterm : ∀ i : Fin hyp.w1, hyp.muGrid hG hodd i 0
        = ((h.columnFamily 1).mu (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
      intro i
      have e : hyp.muGrid hG hodd i 0
          = ((h.columnFamily (finCardEquivCharacterGroup _
              (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu
              (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ) := by
        unfold Hypothesis.muGrid; rfl
      rw [e, hdual0]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact Fintype.sum_equiv (finCongr hcardW1.symm) _ _ (fun i => rfl)
  -- `μ_0 = Ind_K^M 1_K`: (4.5.a) at `χ₂ = 1` with the trivial restriction.
  have hres : ClassFunction.restrict h.K ((h.columnFamily 1).mu 0 : ClassFunction ↥M ℂ)
      = trivialClassFunction ↥h.K := by
    rw [← h.coe_chiRestrict 1, h.chiRestrict_one_eq_trivial,
      IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  rw [hsum, ← h.induce_restrict_certainType_eq 1, hres, ClassFunction.mapRingEquiv_induce]
  congr 1
  ext x
  rw [ClassFunction.mapRingEquiv_apply, trivialClassFunction_apply, map_one]

open scoped FiniteInduce in
/-- **Peterfalvi (10.9)/(11.8.4) norm**: `‖μ_0 − ζ‖² = w₁ + 1` for an irreducible `ζ ∈ S` of degree
`w₁`, where `μ_0 = ∑_i μ_{i0}` is the column-`0` sum.  Expand: `‖μ_0‖² = w₁` (orthonormality of the
`μ_{i0}`, `muGrid_column_sum_inner_self`), `⟨μ_0, ζ⟩ = 0` (the degree mismatch `μ_{i0}(1) = 1 ≠ w₁`,
`muGrid_inner_eq_zero_of_apply_one_ne`), and `‖ζ‖² = 1`.  This is the `M`-side norm used by the
coherence-free (10.9) (`‖(μ_0 − ζ)^τ‖² = w₁ + 1` via the Dade isometry, hence `NC ≤ w₁ + 1`) and by
Peterfalvi (11.8.4) (`‖χ‖² = ‖μ_0 − ζ‖² − q = 1`). -/
theorem inner_muColumnZero_sub_zeta_self [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) {ζ : ClassFunction ↥M ℂ}
    (hzirr : IsIrreducibleCharacter ζ) (hz1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.inner ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - ζ)
        ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i 0) - ζ) = ((hyp.w1 + 1 : ℕ) : ℂ) := by
  have := hyp.finiteG
  have hodd : Odd (Nat.card G) := hG.odd
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hodd).three_le_card_W1
  have hμ0perp : ClassFunction.inner (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ζ = 0 := by
    rw [inner_sum_left]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hzirr ?_
    rw [hyp.muGrid_zero_column_apply_one hG hodd i, hz1]
    intro he
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast he.symm
    omega
  have hζμ0 : ClassFunction.inner ζ (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hμ0perp, star_zero]
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hzirr
    rw [irr_cf_inner hzmem hzmem, if_pos rfl]
  rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_sub_right,
    hyp.muGrid_column_sum_inner_self hG hodd 0, hμ0perp, hζμ0, hζζ]
  push_cast; ring

open scoped FiniteInduce in
/-- **Peterfalvi (10.9), coherence-free σ-coefficient form**.  Under Hypothesis (10.1), for any
irreducible `ζ ∈ S = inducedFamily M` of degree `ζ(1) = w₁`, if `w₁ < w₂` then the `σ`-coefficient
grid of `ψ = (μ_0 − ζ)^τ` is the single constant column `j = 0` with value `1`:
`⟨ψ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)` for all `i, j`.

Unlike `orthogonality_of_w1_lt_w2`, this needs **no coherence** of `S` (it does not identify the
residual as `ζ^{τ₁}`).  The argument is the (3.8) trichotomy (`sigmaCoeff_trichotomy`) applied to
`ψ`, which vanishes on `V` and is anchored by `a_{00} = ⟨μ_0 − ζ, 1_M⟩ = 1`.  The **coherence-free**
norm bound `‖ψ‖² = ‖μ_0 − ζ‖² = w₁ + 1` (Dade isometry `tau_inner_eq_of_supported`, orthonormality
of the `μ_{i0}` `muGrid_column_sum_inner_self`, the degree-mismatch `⟨μ_{i0}, ζ⟩ = 0`, and
`‖ζ‖² = 1`) gives `NC(ψ) ≤ w₁ + 1 < 2w₁` by Bessel
(`ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast`).  The all-zero branch is excluded by
`a_{00} = 1`; the single-row branch by `NC ≥ w₂ > w₁ + 1` (a full row carries `w₂` nonzero
coefficients, but the odd-order gap forces `w₁ + 2 ≤ w₂`).  This is the form consumed by Peterfalvi
(11.9.b) (`q > p`), where `S` is *not* coherent (10.8). -/
theorem inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ)) (hw : hyp.w1 < hyp.w2) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = (if j = 0 then (1 : ℂ) else 0) := by
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
  obtain ⟨ρ, κ, hρinj, hκinj, hprod⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_product hG hodd
  set ψ : ClassFunction G ℂ :=
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) with hψ
  -- the σ-coefficient at the product index `(ρ i, κ j)` equals `⟨ψ, ω_{ij}^σ⟩`.
  have hcoeff_prod : ∀ i j, tic.sigmaCoeff hVeq app ψ (ρ i, κ j)
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j) := by
    intro i j
    change ClassFunction.inner ψ (tic.chiFam hVeq app (ρ i, κ j))
      = ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd i j)
    rw [hprod i j]
  -- `μ_0 − ζ` is `A_0`-supported.
  have hsupp : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 :=
    hyp.muColumnZero_sub_zeta_support hG hodd hzS hz1
  -- `⟨ζ, 1_M⟩ = 0` (degree `w₁ > 1`).
  have hzeta_triv : ClassFunction.inner ζ (trivialClassFunction (↥M)) = 0 := by
    have hzmem : ζ ∈ irreducibleCharacters (↥M) := mem_irreducibleCharacters.mpr hzirr
    have htmem : trivialClassFunction (↥M) ∈ irreducibleCharacters (↥M) :=
      mem_irreducibleCharacters.mpr trivialClassFunction_isIrreducible
    rw [irr_cf_inner hzmem htmem, if_neg ?_]
    intro hcontra
    have h1 : ζ 1 = trivialClassFunction (↥M) 1 :=
      congrArg (fun f : ClassFunction (↥M) ℂ => (f : (↥M) → ℂ) 1) hcontra
    rw [hz1, trivialClassFunction_apply] at h1
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    have : (hyp.w1 : ℕ) = 1 := by exact_mod_cast h1
    omega
  -- `a_{00} = ⟨ψ, ω_{00}^σ⟩ = ⟨μ_0 − ζ, 1_M⟩ = 1`.
  have ha00 : ClassFunction.inner ψ (hyp.alignedOmegaSigmaGrid hG hodd 0 0) = 1 := by
    rw [hyp.alignedOmegaSigmaGrid_zero_zero hG hodd, hψ, hyp.tau_inner_trivial hsupp,
      ClassFunction.inner_sub_left, hyp.muColumnZero_inner_trivial hG hodd, hzeta_triv, sub_zero]
  have ha00coeff : tic.sigmaCoeff hVeq app ψ (ρ 0, κ 0) = 1 := by
    rw [hcoeff_prod 0 0, ha00]
  -- `ψ` vanishes on `V`.
  have hpsiV : ∀ v ∈ tic.V, ψ v = 0 := by
    intro v hv
    have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
    rw [hψ, hyp.tau_apply_of_mem_typePV hsupp hv hvM]
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]; exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived
          hyp.typeP hv
    obtain ⟨θ, _hθne, hζeq⟩ := hzS
    have hζv : ζ ⟨v, hvM⟩ = 0 := by
      rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
    have hμv : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ⟨v, hvM⟩ = 0 :=
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hnotmem
    rw [ClassFunction.sub_apply, hμv, hζv, sub_zero]
  -- `ψ ∈ ZIrr G` and the coherence-free norm `‖ψ‖² = w₁ + 1`.
  have hμ0Z : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) ∈ ZIrr ↥M :=
    Submodule.sum_mem _ (fun i _ => (hyp.muGrid_isIrreducible hG hodd i 0).mem_ZIrr)
  have hdiffZ : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hμ0Z hzirr.mem_ZIrr
  have hψZ : ψ ∈ ZIrr G := by
    rw [hψ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp hdiffZ
  have hψnorm : ClassFunction.inner ψ ψ = ((hyp.w1 + 1 : ℕ) : ℂ) := by
    rw [hψ, hyp.tau_inner_eq_of_supported hsupp hsupp,
      inner_muColumnZero_sub_zeta_self hG hyp hzirr hz1]
  -- NC bound (Bessel) and the `< 2w₁` form.
  have hNC : tic.sigmaNC hVeq app ψ ≤ hyp.w1 + 1 :=
    tic.ncard_sigmaCoeff_ne_zero_le_of_inner_self_natCast hVeq app hψZ hψnorm
  have hNC2 : tic.sigmaNC hVeq app ψ < 2 * Nat.card ↥tic.W1 := by
    have h3 : (3 : ℕ) ≤ hyp.w1 := hcardW1 ▸ tic.three_le_card_W1
    rw [hcardW1]; omega
  -- the odd-order gap `w₁ + 2 ≤ w₂`.
  have hgap : Nat.card ↥tic.W1 + 2 ≤ Nat.card ↥tic.W2 := by
    have hodd1 : Odd (Nat.card ↥tic.W1) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W1_le_W)
    have hodd2 : Odd (Nat.card ↥tic.W2) :=
      tic.W_card_odd.of_dvd_nat (Subgroup.card_dvd_of_le tic.W2_le_W)
    have hlt : Nat.card ↥tic.W1 < Nat.card ↥tic.W2 := by rw [hcardW1, hcardW2]; exact hw
    obtain ⟨a, ha⟩ := hodd1
    obtain ⟨b, hb⟩ := hodd2
    omega
  -- apply the (3.8) trichotomy.
  rcases tic.sigmaCoeff_trichotomy hVeq app hpsiV hgap hNC2 with
    hall | ⟨j₀, c, hc, hcol, hrest⟩ | ⟨i₀, c, hc, hrow, hrest⟩
  · -- all-zero branch: contradicts `a_{00} = 1`.
    exact absurd (ha00coeff.symm.trans (hall (ρ 0, κ 0))) one_ne_zero
  · -- single-column branch: the desired conclusion.
    have hκ0 : κ 0 = j₀ := by
      by_contra hne
      exact absurd (ha00coeff.symm.trans (hrest (ρ 0) (κ 0) hne)) one_ne_zero
    have hc1 : c = 1 := by
      rw [hκ0] at ha00coeff; rw [hcol (ρ 0)] at ha00coeff; exact ha00coeff
    intro i j
    have hval : tic.sigmaCoeff hVeq app ψ (ρ i, κ j) = (if j = 0 then (1 : ℂ) else 0) := by
      by_cases hj : j = 0
      · subst hj; rw [hκ0, hcol (ρ i), hc1, if_pos rfl]
      · rw [hrest (ρ i) (κ j) (fun he => hj (hκinj (he.trans hκ0.symm))), if_neg hj]
    rw [← hcoeff_prod i j, hval]
  · -- single-row branch: a full `i₀`-row has `w₂` nonzero coefficients, so `NC ≥ w₂ > w₁ + 1`.
    exfalso
    have hinj : Function.Injective (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q)) :=
      fun a b h => (Prod.ext_iff.mp h).2
    have hrowsub : Set.range (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q))
        ⊆ {pq | tic.sigmaCoeff hVeq app ψ pq ≠ 0} := by
      rintro _ ⟨q, rfl⟩
      simp only [Set.mem_ofPred_eq]
      rw [hrow q]; exact hc
    have hrowcard : (Set.range (fun q : (tic.W2.subgroupOf tic.W) →* ℂˣ => (i₀, q))).ncard
        = hyp.w2 := by
      rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj,
        tic.card_charGroup_subgroupOf tic.W2_le_W, hcardW2]
    have hge : hyp.w2 ≤ tic.sigmaNC hVeq app ψ := by
      rw [← hrowcard]
      exact Set.ncard_le_ncard hrowsub (Set.toFinite _)
    rw [hcardW1, hcardW2] at hgap
    omega

open scoped FiniteInduce in
/-- **Peterfalvi (10.9), residual-orthogonal form** (coherence-free).  When `w₁ < w₂`, the residual
`(μ_0 − ζ)^τ − ∑_{i} ω_{i0}^σ` is orthogonal to every `ω_{ij}^σ`, i.e. to `(Irr W)^σ`.  Immediate
from the σ-coefficient form `inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2`
(`⟨ψ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)`) together with the σ-grid orthonormality
(`∑_{i'} ⟨ω_{i'0}^σ, ω_{ij}^σ⟩ = (if j = 0 then 1 else 0)`).  This is the orthogonality that
Peterfalvi (11.9.b) contradicts against (11.8) to force `q > p`. -/
theorem residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ)) (hw : hyp.w1 < hyp.w2) :
    ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  have := hyp.finiteG
  classical
  intro i j
  rw [ClassFunction.inner_sub_left, inner_sum_left,
    inner_tau_muColumnZero_sub_zeta_alignedOmegaSigma_of_w1_lt_w2 hG hyp hzS hzirr hz1 hw i j,
    Finset.sum_eq_single i]
  · rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i i 0 j]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg hj, if_neg (fun hh => hj hh.2.symm), sub_zero]
  · intro i' _ hi'
    rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i' i 0 j, if_neg (fun hh => hi' hh.1)]
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped FiniteInduce in
/-- **Peterfalvi (11.9.b), the `q > p` reduction** (modulo (11.8)).  For an irreducible
`ζ ∈ S = inducedFamily M` of degree `w₁`, given the genuine (11.8) non-orthogonality `h118`
(`(μ_0 − ζ)^τ − ∑ ω_{i0}^σ` is **not** orthogonal to `(Irr W)^σ`), it follows that `w₂ < w₁`
(i.e. `q > p`).

This is the textbook (11.9.b) argument "follows from (10.9) and (11.8)": were `w₁ < w₂`, the
coherence-free (10.9) (`residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2`) would make the
residual orthogonal to `(Irr W)^σ`, contradicting `h118`; and `w₁ ≠ w₂` because `|W₁|, |W₂|` are
coprime with `w₁ ≥ 3`.  The hypothesis `h118` is the genuine (11.8) statement, here an explicit
obligation; its honest proof (Peterfalvi (11.8.1)–(11.8.6)) is the remaining §11 character content
(lane-b W3, issue 2020), and the consumer is `card_kappaHall_lt_of_isTypeIIIorIV`
(`|K*| < |K|`, `q = |W₁| = |K|`, `p = |W₂| = |K*|`). -/
theorem w2_lt_w1_of_residual_not_orthogonal [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {ζ : ClassFunction ↥M ℂ} (hzS : ζ ∈ inducedFamily M) (hzirr : IsIrreducibleCharacter ζ)
    (hz1 : ζ 1 = (hyp.w1 : ℂ))
    (h118 : ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
      ClassFunction.inner
        ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
          - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
        (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0) :
    hyp.w2 < hyp.w1 := by
  have := hyp.finiteG
  have h3 : (3 : ℕ) ≤ hyp.w1 := (typePData_toTICyclicHypothesis hyp.typeP hG.odd).three_le_card_W1
  have hne : hyp.w1 ≠ hyp.w2 := by
    intro he
    have hcop : Nat.Coprime hyp.w1 hyp.w2 := typePData_coprime_card_W1_W2 hyp.typeP
    rw [← he] at hcop
    have hgcd : Nat.gcd hyp.w1 hyp.w1 = 1 := hcop
    rw [Nat.gcd_self] at hgcd
    omega
  rcases lt_trichotomy hyp.w1 hyp.w2 with hlt | heq | hgt
  · exact absurd
      (residual_alignedOmegaSigma_inner_eq_zero_of_w1_lt_w2 hG hyp hzS hzirr hz1 hlt) h118
  · exact absurd heq hne
  · exact hgt

open scoped FiniteInduce in
/-- **Coherence of an equal-degree subfamily of `S`** (Peterfalvi (5.7)/(1.4) for §11): an injective
family `χ : Fin n → Irr(M)` (`n ≥ 2`) of irreducible characters, each a member of
`S = inducedFamily M` and all of the *same degree*, is coherent for the §10 Dade isometry `τ`.

This is the (11.8) materialization bridge.  Every input of the equal-degree coherence producer
`coherentEqualDegree_fromDade` is discharged from the §10 `Hypothesis` data with no opaque field:
* the `(5.1)` base map is `τ = dadeIntegralCharacterMap hyp.dadeData.dade …` (definitionally
`hyp.tau`);
* the support is `A₀(M) = supportInSubgroup (typePA0 M) M` (definitionally `hyp.A0`);
* the signed-difference supports `(χⱼ − χ₀).support ⊆ A₀(M)` are `inducedFamily_sub_support` (the
  members share a degree, so each difference vanishes off `M'^#`);
* `1 ∉ A₀(M)` is `S04.Hypothesis.ne_one` (`A₀ ⊆ G^#`).

Applied to the degree-`w₁` subfamily `S(HC)` (the `(u−1)/q ≥ 2` degree-`q = w₁` constituents of the
`(U/C) ⋊ W₁` Frobenius), it gives the `S₁ = S(HC)` coherence `τ₁` the (11.8) contradiction consumes;
the remaining content is enumerating `S(HC)` as such a family. -/
noncomputable def Hypothesis.inducedFamily_isCoherent_of_equalDegreeFamily [Finite G]
    {M : Subgroup G}
    (hyp : Hypothesis M) {n : ℕ} [NeZero n] (hn : 2 ≤ n) (χ : Fin n → IrreducibleCharacter (↥M))
    (hχinj : Function.Injective χ)
    (hmem : ∀ j, (χ j : ClassFunction ↥M ℂ) ∈ inducedFamily M)
    (hdeg : ∀ j, ((χ j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = ((χ 0 : ClassFunction ↥M ℂ) : ↥M → ℂ) 1) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      (Set.range (fun j => (χ j : ClassFunction ↥M ℂ))) hyp.A0 := by
  haveI := hyp.finiteG
  have h1notA : (1 : G) ∉ typePA0 M hyp.typeP := fun h => hyp.dadeData.dade.ne_one h rfl
  have hsuppdiff : ∀ j, (irreducibleCharacterDifference χ j).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := fun j =>
    hyp.inducedFamily_sub_support (hmem j) (hmem 0) (hdeg j)
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dadeData.dade hn χ
    hχinj hdeg hsuppdiff h1notA

/-- **The degree-`w₁` irreducible subfamily `S(HC) = S₁`** of `S = inducedFamily M`: the
uniform-degree family whose (5.7) coherence `τ₁` the (11.8) contradiction consumes.  Abbreviates the
recurring `{φ ∈ S | φ irreducible, φ(1) = w₁}` set comprehension so the (11.8.5)
extension-generalization lemmas can quantify over an arbitrary coherent extension
`coh : IsCoherent hyp.tau hyp.SHCSet hyp.A0` (both `SHC_isCoherent` and the branch-2 swap
`SHC_swap` are such). -/
abbrev Hypothesis.SHCSet [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    Set (ClassFunction ↥M ℂ) :=
  {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
    ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))}

open scoped FiniteInduce in
/-- **Peterfalvi (11.8)/(5.7): coherence of `S₁ = S(HC)`**, the uniform degree-`w₁` irreducible
subfamily of `S = inducedFamily M`.

This materializes the coq `cohS1 : coherent S1 M^# tau := uniform_degree_coherence scohS1`
(`PFsection11.v`): the degree-`w₁` irreducible members of `S` all share the degree `w₁`, so the
equal-degree coherence producer applies.  The family is enumerated as a `Finset` of *bundled*
irreducible characters (`IrreducibleCharacter ↥M = {φ // IsIrreducibleCharacter φ}`);
`Finset.equivFin`
gives an injective `Fin n` indexing for free, and `inducedFamily_isCoherent_of_equalDegreeFamily`
discharges the rest.  Nonemptiness with `n ≥ 2` is the conjugate pair `{ζ, ζ̄}` of the degree-`w₁`
witness `exists_zeta_in_inducedFamily_degree_w1` (distinct since `S` has no real characters,
`inducedFamily_hasNoRealCharacters`).

This is the `S₁`-coherence the (11.8) contradiction consumes (with `S₂ = S(C) − S(HC)` and a glue to
build full `S(C)` coherence, contradicting (11.3)/(10.8)). -/
noncomputable def Hypothesis.SHC_isCoherent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 := by
  haveI := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- `s` = the bundled degree-`w₁` irreducible members of `S`.
  set p : IrreducibleCharacter ↥M → Prop := fun χ =>
    (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
      ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) with hp
  set s : Finset (IrreducibleCharacter ↥M) := Finset.univ.filter p with hs_def
  have hmem_s : ∀ χ, χ ∈ s ↔ p χ := fun χ => by
    rw [hs_def, Finset.mem_filter]; exact and_iff_right (Finset.mem_univ _)
  -- the enumerating family, injective for free via `Finset.equivFin`.
  set χfam : Fin s.card → IrreducibleCharacter ↥M :=
    fun j => (s.equivFin.symm j : IrreducibleCharacter ↥M) with hχfam
  have hχfam_mem : ∀ j, χfam j ∈ s := fun j => (s.equivFin.symm j).2
  have hinj : Function.Injective χfam := fun a b h =>
    s.equivFin.symm.injective (Subtype.ext h)
  have hmem : ∀ j, (χfam j : ClassFunction ↥M ℂ) ∈ inducedFamily M := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).1
  have hdegfam : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := fun j =>
    ((hmem_s _).mp (hχfam_mem j)).2
  -- `n ≥ 2`: the conjugate pair `{ζ, ζ̄}` of the degree-`w₁` witness (a `Prop`, so the `∃`-witness
  -- elimination is confined to this proof — the enclosing goal `IsCoherent …` is `Type`-valued).
  have hcard : 2 ≤ s.card := by
    obtain ⟨ζ, hζS, hζirr, hζ1⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
    have hζ1' : ((ζ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := hζ1
    have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
    have hζc1 : ((ζ.conj : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ) := by
      rw [ClassFunction.conj_apply, hζ1', star_natCast]
    have hζi_s : (⟨ζ, hζirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hζS, hζ1'⟩
    have hζci_s : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ∈ s :=
      (hmem_s _).mpr ⟨hζcS, hζc1⟩
    have hne : (⟨ζ.conj, hζirr.conj⟩ : IrreducibleCharacter ↥M) ≠ ⟨ζ, hζirr⟩ := by
      intro h
      exact inducedFamily_hasNoRealCharacters hModd hζS (congrArg Subtype.val h)
    have hsub : ({⟨ζ.conj, hζirr.conj⟩, ⟨ζ, hζirr⟩} : Finset (IrreducibleCharacter ↥M)) ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact hζci_s
      · rw [Finset.mem_singleton] at hx'; exact hx' ▸ hζi_s
    exact (Finset.card_pair hne).symm.trans_le (Finset.card_le_card hsub)
  haveI : NeZero s.card := ⟨by omega⟩
  have hdeg : ∀ j, ((χfam j : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = ((χfam 0 : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 := fun j => by rw [hdegfam j, hdegfam 0]
  -- coherence on the range, then identify the range with `S₁ = S(HC)`.
  have hcoh := hyp.inducedFamily_isCoherent_of_equalDegreeFamily hcard χfam hinj hmem hdeg
  have hrange : (Set.range fun j => (χfam j : ClassFunction ↥M ℂ)) =
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} := by
    ext φ
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨hmem j, (χfam j).2, hdegfam j⟩
    · rintro ⟨hφS, hφirr, hφ1⟩
      have hsφ : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥M) ∈ s := (hmem_s _).mpr ⟨hφS, hφ1⟩
      exact ⟨s.equivFin ⟨⟨φ, hφirr⟩, hsφ⟩, by simp [hχfam]⟩
  rw [hrange] at hcoh
  exact hcoh

/-- **`ℤ[S(HC)]`-vanishing-at-`1` combinations are `A_0`-supported** (the Peterfalvi (5.x)
`ℤ[S, M^#] = ℤ[S, A_0]` condition for the uniform degree-`w₁` family `S(HC)`).  Since every member
`χ ∈ S(HC)` has the same degree `χ(1) = w₁`, any `φ = ∑ c_χ χ ∈ ℤ[S(HC)]` with `φ(1) = 0` has
`w₁·∑ c_χ = 0`, hence `∑ c_χ = 0`, so `φ = ∑ c_χ (χ − χ₀)` collapses to a combination of the
`A_0`-supported differences `χ − χ₀` (`inducedFamily_sub_support`). Proved by `span_induction` on
the
strengthened invariant `(ψ − (ψ(1)·w₁⁻¹)·χ₀).support ⊆ A_0` (closed under `+`/`•`, `= χ − χ₀` on
generators), specialized at `φ(1) = 0`.  This is the `hspan` hypothesis of the Galois-equivariance
`IsCoherent.extension_mapRingEquiv_comm` for the `S(HC)`-coherent `τ₁`. -/
theorem Hypothesis.SHC_zSpan_vanish_support [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥M ℂ | ψ ∈ inducedFamily M ∧ IsIrreducibleCharacter ψ ∧
        ((ψ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))})
    (hφ1 : φ 1 = 0) :
    φ.support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := by
    have h1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : hyp.w1 ≠ 0)
  obtain ⟨χ₀, hχ₀S, hχ₀irr, hχ₀1⟩ := exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
    (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  suffices hstrong : ∀ ψ ∈ OddOrder.Peterfalvi.S07.zSpan
      {ψ : ClassFunction ↥M ℂ | ψ ∈ inducedFamily M ∧ IsIrreducibleCharacter ψ ∧
        ((ψ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))},
      (ψ - (ψ 1 * (hyp.w1 : ℂ)⁻¹) • χ₀).support ⊆ hyp.A0 by
    have h := hstrong φ hφ
    rwa [hφ1, zero_mul, zero_smul, sub_zero] at h
  intro ψ hψ
  induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨hxS, _hxirr, hx1⟩ := hx
        rw [hx1, mul_inv_cancel₀ hw1ne, one_smul]
        exact hyp.inducedFamily_sub_support hxS hχ₀S (hx1.trans hχ₀1.symm)
    | zero => simp
    | add x y _ _ hx hy =>
        have hrw : (x + y - ((x + y) 1 * (hyp.w1 : ℂ)⁻¹) • χ₀)
            = (x - (x 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) + (y - (y 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) := by
          rw [ClassFunction.add_apply]; module
        rw [hrw]
        exact (ClassFunction.support_add_subset _ _).trans (Set.union_subset hx hy)
    | smul c x _ hx =>
        have hrw : (c • x - ((c • x) 1 * (hyp.w1 : ℂ)⁻¹) • χ₀)
            = (c : ℂ) • (x - (x 1 * (hyp.w1 : ℂ)⁻¹) • χ₀) := by
          rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply]; module
        rw [hrw]
        exact (ClassFunction.support_smul_subset _ _).trans hx

open scoped FiniteInduce in
/-- **The `S(HC)`-coherent extension `τ₁` commutes with complex conjugation** (Peterfalvi (5.9)(a) /
`cfConjC_Dade_coherent`): for a degree-`w₁` irreducible `ζ ∈ S = inducedFamily M`,
`(ζ^{τ₁})‾ = (ζ‾)^{τ₁}`.  This instantiates the general Galois-equivariance
`IsCoherent.extension_mapRingEquiv_comm` at `σc = conjAe` for the landed `SHC_isCoherent`
coherence: the `A_0`-support condition `hspan` is `SHC_zSpan_vanish_support`, `S` is closed under
conjugation (`inducedFamily_closedUnderConjugate` + `IsIrreducibleCharacter.conj` + degree), the
images lie in `ℤ[Irr G]` (`extension_mem_ZIrr`), and `|S| ≥ 2` via the conjugate pair `{ζ, ζ‾}`
(`inducedFamily_hasNoRealCharacters` in odd order).  This is the `τ₁`-side Galois-equivariance
feeding the (11.8.3) reality `β‾ = β`. -/
theorem Hypothesis.SHC_extension_conj [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {χ : ClassFunction ↥M ℂ} (hχS : χ ∈ inducedFamily M) (hχirr : IsIrreducibleCharacter χ)
    (hχ1 : χ 1 = (hyp.w1 : ℂ)) :
    ((hyp.SHC_isCoherent hG).extension χ).conj = (hyp.SHC_isCoherent hG).extension χ.conj := by
  have := hyp.finiteG
  classical
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hbridge : ∀ X : ClassFunction ↥M ℂ,
      X.conj = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv X := fun X => by
    ext g; rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]; rfl
  simp only [hbridge]
  refine (hyp.SHC_isCoherent hG).extension_mapRingEquiv_comm subset_rfl
    (fun ψ hψ => mem_irreducibleCharacters.mpr hψ.2.1)
    (fun ψ hψ hψ1 => hyp.SHC_zSpan_vanish_support hG hψ hψ1)
    Complex.conjAe.toRingEquiv ?_
    (fun ψ hψ => (hyp.SHC_isCoherent hG).extension_mem_ZIrr ψ (Submodule.subset_span hψ))
    ⟨hχS, hχirr, hχ1⟩ ?_
  · rintro ψ ⟨hψS, hψirr, hψ1⟩
    exact ⟨by rw [← hbridge]; exact inducedFamily_closedUnderConjugate M hψS,
      by rw [← hbridge]; exact hψirr.conj,
      by rw [← hbridge, ClassFunction.conj_apply, hψ1, star_natCast]⟩
  · exact ⟨χ.conj, ⟨inducedFamily_closedUnderConjugate M hχS, hχirr.conj, by
      rw [ClassFunction.conj_apply, hχ1, star_natCast]⟩,
      fun h => inducedFamily_hasNoRealCharacters hModd hχS h⟩

/-- **Generic isometry-normalization of a coherent extension**: for any coherent extension `coh`
of `τ` over a set `S` of irreducible characters, an irreducible `ζ ∈ S` has `‖coh ζ‖² = ‖ζ‖² = 1`.
The extension-agnostic core of `SHC_extension_inner_self`, reusable for both `SHC_isCoherent`
and the (11.8.4) branch-2 swap `SHC_swap` (the (11.8.5) extension-generalization). -/
theorem _root_.OddOrder.Peterfalvi.S07.IsCoherent.inner_extension_self_eq_one
    {L H : Type*} [Group L] [Group H] [Fintype L] [Fintype H]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card H : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L H}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    {ζ : ClassFunction L ℂ} (hζS : ζ ∈ S) (hζirr : IsIrreducibleCharacter ζ) :
    ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 := by
  rw [coh.extension_inner_eq _ _ (Submodule.subset_span hζS) (Submodule.subset_span hζS),
    OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]

/-- **Generic orthogonality of coherent images of distinct irreducibles**: for a coherent extension
`coh` over `S`, distinct irreducibles `φ, ψ ∈ S` have `⟨coh φ, coh ψ⟩ = ⟨φ, ψ⟩ = 0`.  The
extension-agnostic core of `SHC_extension_inner_of_ne`. -/
theorem _root_.OddOrder.Peterfalvi.S07.IsCoherent.inner_extension_eq_zero_of_ne
    {L H : Type*} [Group L] [Group H] [Fintype L] [Fintype H]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card H : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L H}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent τ S A)
    {φ ψ : ClassFunction L ℂ} (hφS : φ ∈ S) (hφirr : IsIrreducibleCharacter φ)
    (hψS : ψ ∈ S) (hψirr : IsIrreducibleCharacter ψ) (hne : φ ≠ ψ) :
    ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 := by
  rw [coh.extension_inner_eq _ _ (Submodule.subset_span hφS) (Submodule.subset_span hψS),
    OddOrder.RepresentationTheory.irr_cf_inner hφirr hψirr, if_neg hne]

open scoped FiniteInduce in
/-- **`‖ζ^{τ₁}‖² = 1` for the `S(HC)`-coherent extension** (α-grid `S₁`-`τ₁` input to (11.8.2)).
The `S(HC)`-coherence `τ₁ = SHC_isCoherent.extension` is an isometry on `ℤ[S(HC)]`
(`extension_inner_eq`) and the degree-`w₁` irreducible `ζ ∈ S(HC)`, so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`.
Specializes the generic `IsCoherent.inner_extension_self_eq_one` to `coh = SHC_isCoherent`. -/
theorem Hypothesis.SHC_extension_inner_self [Finite G] {M : Subgroup G}
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ClassFunction.inner (coh.extension ζ) (coh.extension ζ) = 1 :=
  coh.inner_extension_self_eq_one ⟨hζS, hζirr, hζ1⟩ hζirr

open scoped FiniteInduce in
/-- **`⟨φ^{τ₁}, ψ^{τ₁}⟩ = 0` for distinct `S(HC)` members** (α-grid `S₁`-`τ₁` input to (11.8.2)).
Together with `SHC_extension_inner_self` (`‖φ^{τ₁}‖² = 1`) this says the coherent images
`{φ^{τ₁} : φ ∈ S(HC)}` form an **orthonormal family** — the `S₁^{τ₁}` basis against which the
(11.8.2) decomposition `α_{ij}^τ = X − nζ^{τ₁} + a·∑_{λ∈S₁} λ^{τ₁}` projects.  Proof: `τ₁` is an
isometry on `ℤ[S(HC)]` (`extension_inner_eq`), so `(φ^{τ₁}, ψ^{τ₁}) = (φ, ψ) = 0` for distinct
irreducibles.  Available from `SHC_isCoherent` alone (no full-`S` `coh`). -/
theorem Hypothesis.SHC_extension_inner_of_ne [Finite G] {M : Subgroup G}
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0)
    {φ ψ : ClassFunction ↥M ℂ}
    (hφS : φ ∈ inducedFamily M) (hφirr : IsIrreducibleCharacter φ) (hφ1 : φ 1 = (hyp.w1 : ℂ))
    (hψS : ψ ∈ inducedFamily M) (hψirr : IsIrreducibleCharacter ψ) (hψ1 : ψ 1 = (hyp.w1 : ℂ))
    (hne : φ ≠ ψ) :
    ClassFunction.inner (coh.extension φ) (coh.extension ψ) = 0 :=
  coh.inner_extension_eq_zero_of_ne
    ⟨hφS, hφirr, hφ1⟩ hφirr ⟨hψS, hψirr, hψ1⟩ hψirr hne

open scoped FiniteInduce in
/-- **SHC-coherence analog of `tau_zeta_sub_conj_eq_tau1`** (α-grid `S₁`-`τ₁` bridge for (11.8.5)).
For a degree-`w₁` irreducible `ζ ∈ S(HC)`, the Dade image of the supported difference `ζ − ζ̄`
equals the `S(HC)`-coherent split `ζ^{τ₁} − ζ̄^{τ₁}`. Since `ζ, ζ̄ ∈ S(HC)` and `ζ − ζ̄` is
supported
on `A₀`, it lies in the supported lattice `ℤ[S(HC), A₀]` where `SHC_isCoherent.extension` agrees
with
`hyp.tau` (`extends_on_supported`); `extension`-linearity (`map_sub`) then splits it.

This is the essential SHC ingredient of the (5.3.b) `⟨ω^σ, ζ^{τ₁}⟩ = 0` argument (via
`inner_left_eq_zero_of_inner_sub_eq_zero` and the coherence-free `(ζ − ζ̄)^τ ⊥ ω^σ`), which the
(11.8.5) `a = 0` step needs — the by-contradiction has `SHC_isCoherent` but not the full-`S`
`coh`. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_SHC_extension [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.SHCSet hyp.A0) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    hyp.tau (ζ - ζ.conj)
      = coh.extension ζ - coh.extension ζ.conj := by
  have hζcS : ζ.conj ∈ inducedFamily M := inducedFamily_closedUnderConjugate M hζS
  have hζcirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hζc1 : ζ.conj 1 = (hyp.w1 : ℂ) := by
    rw [ClassFunction.conj_apply, hζ1, star_natCast]
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζS, hζirr, hζ1⟩
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} :=
    Submodule.subset_span ⟨hζcS, hζcirr, hζc1⟩
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      {φ : ClassFunction ↥M ℂ | φ ∈ inducedFamily M ∧ IsIrreducibleCharacter φ ∧
        ((φ : ↥M → ℂ) 1 = (hyp.w1 : ℂ))} hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.extends_on_supported _ hmem, map_sub]

end OddOrder.Peterfalvi.S12



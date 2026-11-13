-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:49:48.409561+00:00
-- url     : https://prove2.me/theorems/78985193-23ea-421d-97df-2bc875152d4a
-- title:
--   Peterfalvi (9.8)–(9.10): character counts in the two Clifford cases
-- statement:
--   Formalizes character-counting and normality facts for the two Clifford cases of the analysis of maximal subgroups of types II, III and IV, covering Peterfalvi (9.8)–(9.10), including the chief-factor constituent of (9.9.a).
--
--   Main declarations: `chiefFactor_H0supC_subgroupOf_normal` (`H₀C ◁ M`); `cprimeSub_normalized_by_uW1` (`U W₁ ≤ N(C')`); `uprimeSub_normalized_by_uW1` (`U W₁ ≤ N_G(U')`); `caseB_exists_chiefFactorConstituent` (Peterfalvi (9.9.a), the chief-factor constituent of `χ ∈ 𝒳(H₀)`).
--
--   The bundle also proves 25 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/CharacterCounts.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/CharacterCounts.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **Generic §9↔§6 reducible count over a carrier `K`** (Coq `PFsection9` `nb_redM`): for a
normal `K.subgroupOf M ◁ ↥M` with `K ≤ M'`, `W₁ ⊓ K = ⊥`, `W₂ ⊄ K`, and the chief-factor image
order `|W̄₂| = p`, the §9 family `𝒮(K)` contains exactly `p − 1` reducible characters.  Both
`K = H₀` and `K = H₀C` instantiate this (the unifying condition `K ∩ H = H₀` enters through the
`|W̄₂| = p` input).  The bijection `Irr(K̄) ⊇ B' ↔ {reducible 𝒮(K)}` is the inflation–induction
composite `χ̄ ↦ induceHU (compHom g χ̄) = compHom (mk' K) (induce K̄ χ̄)`. -/
theorem reducible_count_sOf_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (K : Subgroup G) [hKnorm : (K.subgroupOf M).Normal]
    (hN'le : K.subgroupOf M ≤ (derivedInG M).subgroupOf M)
    (hW1inf : data.W1.subgroupOf M ⊓ K.subgroupOf M = ⊥)
    (hW2notle : ¬ data.W2.subgroupOf M ≤ K.subgroupOf M)
    (hW2card : Nat.card ↥((data.W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)))
      = chief.p) :
    {φ ∈ sOf data K | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  classical
  have hN : (K.subgroupOf M).Normal := hKnorm
  let : Fintype ↥M := Fintype.ofFinite _
  have hKhu : K.subgroupOf M ≤ huSub data := by
    rw [huSub_eq_derivedInG_subgroupOf]; exact hN'le
  have hodd : Odd (Nat.card G) := hG.odd
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
    rw [show Nat.card ↥(derivedInG M) = Nat.card ↥data.typeP.H * Nat.card ↥data.typeP.U by
      rw [← data.typeP.derived_complement.card_mul_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.H_le).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.U_le).toEquiv]]
    exact (Nat.Coprime.mul_right (typeP_coprime_H_W1 data.typeP).symm
      (typeP_coprime_U_W1 data.typeP hU).symm).symm
  set h := chiefFactorQuotientHypothesisGen chief (K.subgroupOf M) hN'le hW1inf hW2notle hodd hHall
    with hh_def
  have hKeq : h.K = (huSub data).map (QuotientGroup.mk' (K.subgroupOf M)) :=
    chiefFactorQuotientHypothesisGen_K_eq chief (K.subgroupOf M) hN'le hW1inf hW2notle hodd hHall
  -- the inflation hom `g : ↥(huSub) →* ↥(h.K)`, surjective with kernel `H₀`
  set sm := (QuotientGroup.mk' (K.subgroupOf M)).subgroupMap (huSub data) with hsm_def
  set g : ↥(huSub data) →* ↥h.K :=
    (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom.comp sm with hg_def
  have hg_surj : Function.Surjective g :=
    (MulEquiv.subgroupCongr hKeq.symm).surjective.comp
      ((QuotientGroup.mk' (K.subgroupOf M)).subgroupMap_surjective (huSub data))
  have hg_ker : g.ker = (K.subgroupOf M).subgroupOf (huSub data) := by
    have hsmker : sm.ker = (K.subgroupOf M).subgroupOf (huSub data) := by
      rw [hsm_def, Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
    rw [hg_def]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ (MulEquiv.subgroupCongr hKeq.symm).injective]
    rw [← MonoidHom.mem_ker, hsmker]
  -- instances for the §6 count, the commute, and `induceHU` (one shared scope, no diamonds)
  have : Invertible (Nat.card (↥M ⧸ (K.subgroupOf M)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : NeZero (Nat.card ↥h.W1) := ⟨Nat.card_pos.ne'⟩
  have : Fintype ↥h.K := Fintype.ofFinite _
  have : Invertible (Nat.card ↥h.K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible
      (Nat.card ↥((huSub data).map (QuotientGroup.mk' (K.subgroupOf M))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the commute / Φ-identity: `induceHU (compHom g χ̄) = compHom (mk' N) (induce h.K χ̄)`
  have hPhi : ∀ χbar : IrreducibleCharacter ↥h.K,
      induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))
        = ClassFunction.compHom (QuotientGroup.mk' (K.subgroupOf M))
            (ClassFunction.induce h.K (χbar : ClassFunction ↥h.K ℂ)) := by
    intro χbar
    have hunfold : ∀ Y : ClassFunction ↥(huSub data) ℂ,
        induceHU data Y = ClassFunction.induce (huSub data) Y := fun _ => rfl
    rw [hg_def, ← ClassFunction.compHom_comp, hunfold, hsm_def,
      induce_compHom_subgroupMap_mk' (K.subgroupOf M)
        (hKhu)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χbar : ClassFunction ↥h.K ℂ))]
    congr 1
    exact induce_compHom_subgroupCongr hKeq.symm (χbar : ClassFunction ↥h.K ℂ)
  -- the §6 reducible-with-`H̄⊄ker` subset `B'` of `Irr(K̄)` (counted as `p − 1`)
  set B' : Set (IrreducibleCharacter ↥h.K) :=
    {χbar | ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χbar : ClassFunction ↥h.K ℂ))
      ∧ ¬ (((hInHu data).map g : Set ↥h.K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χbar : ClassFunction ↥h.K ℂ))} with hB'_def
  have hW2H : h.W2.subgroupOf h.K ≤ (hInHu data).map g := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    have hW2eq : h.W2
        = (data.W2.subgroupOf M).map (QuotientGroup.mk' (K.subgroupOf M)) := rfl
    rw [hW2eq, Subgroup.mem_map] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    rw [Subgroup.mem_subgroupOf] at hw
    have hwH : (w : G) ∈ data.H := (data.typeP.W2_le hw).1
    have hwHU : w ∈ huSub data := by
      rw [huSub, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hwH
    refine ⟨⟨w, hwHU⟩, ?_, ?_⟩
    · change (⟨w, hwHU⟩ : ↥(huSub data)) ∈ (data.H.subgroupOf M).subgroupOf (huSub data)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hwH
    · apply Subtype.ext
      have hco : ((g ⟨w, hwHU⟩ : ↥h.K) : ↥M ⧸ (K.subgroupOf M))
          = QuotientGroup.mk' (K.subgroupOf M) w := rfl
      rw [hco]; exact hwy
  -- image equality: `{φ ∈ 𝒮(H₀) | ¬ irr φ} = Φ '' B'`, `Φ χ̄ = induceHU (compHom g χ̄)`
  have himage : {φ ∈ sOf data K | ¬ IsIrreducibleCharacter φ}
      = (fun χbar : IrreducibleCharacter ↥h.K =>
          induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))) '' B' := by
    ext φ
    simp only [Set.mem_image, hB'_def, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hφS, hred⟩
      rw [mem_sOf] at hφS
      obtain ⟨χ, hχxi, rfl⟩ := hφS
      rw [mem_xiOf] at hχxi
      obtain ⟨hχX, hχH0⟩ := hχxi
      have hgker_sub : (g.ker : Set ↥(huSub data)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) := by
        rw [hg_ker]; exact hχH0
      obtain ⟨χbar, hχbar⟩ :=
        OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hg_surj χ
          hgker_sub
      refine ⟨χbar, ⟨?_, ?_⟩, ?_⟩
      · rw [← isIrreducibleCharacter_compHom_mk'_iff (K.subgroupOf M), ← hPhi χbar, hχbar]
        exact hred
      · rw [← subset_characterKernel_compHom_iff g (χbar : ClassFunction ↥h.K ℂ) (hInHu data),
          hχbar]
        exact hχX
      · rw [hχbar]
    · rintro ⟨χbar, ⟨hred, hker⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_sOf]
        refine ⟨⟨ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ),
          IsIrreducibleCharacter.compHom_of_surjective hg_surj χbar.isIrreducible⟩, ?_, rfl⟩
        rw [mem_xiOf]
        refine ⟨?_, ?_⟩
        · change ¬ ((hInHu data : Set ↥(huSub data)) ⊆ _)
          rw [subset_characterKernel_compHom_iff g (χbar : ClassFunction ↥h.K ℂ) (hInHu data)]
          exact hker
        · rw [← hg_ker]
          intro x hx
          rw [SetLike.mem_coe, MonoidHom.mem_ker] at hx
          rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
            OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.compHom_apply,
            ClassFunction.compHom_apply, hx, map_one]
      · rw [hPhi χbar, isIrreducibleCharacter_compHom_mk'_iff]
        exact hred
  -- injectivity of `Φ` on `B'`
  have hInj : Set.InjOn
      (fun χbar : IrreducibleCharacter ↥h.K =>
          induceHU data (ClassFunction.compHom g (χbar : ClassFunction ↥h.K ℂ))) B' := by
    intro χbar hχbar χbar' _ heq
    simp only at heq
    rw [hPhi χbar, hPhi χbar'] at heq
    rw [hB'_def, Set.mem_ofPred_eq] at hχbar
    exact h.induce_injective_on_reducible hχbar.1
      (ClassFunction.compHom_injective_of_surjective
        (QuotientGroup.mk'_surjective (K.subgroupOf M)) heq)
  -- conclude: `|{φ ∈ 𝒮(H₀) | ¬ irr}| = |B'| = w̄₂ − 1 = p − 1`
  rw [himage, hInj.ncard_image]
  have hcardW2 : Nat.card ↥h.W2 = chief.p := hW2card
  rw [hB'_def, ← Nat.card_coe_set_eq, ← hcardW2]
  exact h.card_reducible_Hnontrivial_induce_eq_W2_sub_one hW2H

theorem reducible_count_sOf_H0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  have := chiefFactor_H0_subgroupOf_normal chief
  refine reducible_count_sOf_K hG chief chief.H0
    (Subgroup.comap_mono (chief.H0_lt_H.le.trans data.typeP.H_le))
    (chiefFactor_W1_inf_H0_subgroupOf_eq_bot chief) ?_ (chiefFactor_card_W2bar chief)
  intro hle
  refine chiefFactor_W2_not_le_H0 chief (fun y hy => ?_)
  have hW2leM : data.W2 ≤ M := (data.typeP.W2_le.trans inf_le_left).trans (H_le_M data)
  have hyM : (⟨y, hW2leM hy⟩ : ↥M) ∈ data.W2.subgroupOf M := Subgroup.mem_subgroupOf.mpr hy
  exact Subgroup.mem_subgroupOf.mp (hle hyM)

/-- **Parity dichotomy of Peterfalvi (9.8.c)** (`oXtheta` / `eqVproper`): the abstract
combinatorial core.  If a finite family `X` has a subfamily `Xmu ⊆ X` of size `p-1`, and the total
count satisfies `u·|X| = (p-1)^q` with `u` odd, `p-1` even and positive, and `q ≥ 2`, then
`Xmu ⊊ X` — there is a member of `X` outside `Xmu`.  The equality case `|X| = p-1` would force
`u·(p-1) = (p-1)^q`, i.e. `u = (p-1)^(q-1)`, which is even (`q-1 ≥ 1`, `p-1` even), contradicting
`u` odd.  In (9.8.c): `X = 𝒳(H₀C)`-regular characters (`u·|X| = (p-1)^q` by `oXtheta`,
numerator `card_regular_chars_Hbar`), `Xmu` the `p-1` reducibles (`reducible_count_sOf_H0`); the
produced member induces the degree-`qu` *irreducible* of `𝒮(H₀C)` (Coq `PFsection9`). -/
theorem exists_regular_not_reducible_of_odd {α : Type*} {X Xmu : Set α}
    (hXfin : X.Finite) (hsub : Xmu ⊆ X) {p q u : ℕ}
    (hXmu : Xmu.ncard = p - 1) (hcount : u * X.ncard = (p - 1) ^ q)
    (hp1_pos : 0 < p - 1) (hp1_even : Even (p - 1)) (hu : Odd u) (hq : 2 ≤ q) :
    ∃ s ∈ X, s ∉ Xmu := by
  have hle : p - 1 ≤ X.ncard := hXmu ▸ Set.ncard_le_ncard hsub hXfin
  have hne : X.ncard ≠ p - 1 := by
    intro heq
    rw [heq] at hcount
    have hsplit : (p - 1) ^ q = (p - 1) * (p - 1) ^ (q - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hsplit] at hcount
    have hu_eq : u = (p - 1) ^ (q - 1) :=
      Nat.eq_of_mul_eq_mul_left hp1_pos (by rw [mul_comm (p - 1) u]; exact hcount)
    have heven : Even ((p - 1) ^ (q - 1)) := by
      have hsplit2 : (p - 1) ^ (q - 1) = (p - 1) * (p - 1) ^ (q - 2) := by
        rw [← pow_succ']; congr 1; omega
      rw [hsplit2]; exact hp1_even.mul_right _
    rw [hu_eq, Nat.odd_iff] at hu
    rw [Nat.even_iff] at heven
    omega
  have hlt : p - 1 < X.ncard := lt_of_le_of_ne hle (Ne.symm hne)
  by_contra hcon
  push Not at hcon
  have hXsub : X ⊆ Xmu := fun s hs => hcon s hs
  have hXeq : X = Xmu := Set.Subset.antisymm hXsub hsub
  rw [hXeq, hXmu] at hlt
  exact (lt_irrefl _) hlt

/-- **`u = |Ū|` is odd**: `u` is the order of the range of the `U`-action `uActionHom` on the chief
factor, so by the first isomorphism theorem `u ∣ |U.subgroupOf (U ⊔ W₁)| ∣ |U ⊔ W₁| ∣ |G|`, and
`|G|`
is odd (odd-order hypothesis).  The parity input `hu` to `exists_regular_not_reducible_of_odd` in
the
(9.8.c) counting argument (`u` odd + `p-1` even forces `|𝒳(H₀C)| > p-1`). -/
theorem u_odd [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) : Odd chars.u := by
  have hdvd : chars.u ∣ Nat.card G := by
    rw [chars.u_eq_card_quotient]
    set g := (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype
    have hA : Nat.card ↥g.range ∣ Nat.card ↥(data.typeP.U.subgroupOf
        (data.typeP.U ⊔ data.typeP.W1)) := by
      rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
      exact Subgroup.card_quotient_dvd_card g.ker
    exact hA.trans
      (((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).card_subgroup_dvd_card).trans
        (data.typeP.U ⊔ data.typeP.W1).card_subgroup_dvd_card)
  rcases hdvd with ⟨k, hk⟩
  exact (Nat.odd_mul.mp (hk ▸ hG.odd)).1

section

open scoped IsMulCommutative

/-- **`⁅H, H⁆ ≤ H₀`** (the chief factor `H̄ = H/H₀` is abelian): `derivedInG H ≤ H₀`.  Since
`↥H ⧸ N` is elementary abelian, `commutator ↥H ≤ N`, and mapping into `G` gives `derivedInG H ≤ H₀`.
A structural input of the (9.9.a) `⁅HC,HC⁆ ⊆ 𝒮(H₀C')`-kernel linearity. -/
theorem derivedInG_H_le_H0 {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    derivedInG data.H ≤ chief.H0 := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  rw [derivedInG, chief.H0_eq]
  apply Subgroup.map_mono
  rw [← QuotientGroup.ker_mk' chief.N]
  exact Abelianization.commutator_subset_ker (QuotientGroup.mk' chief.N)

/-- **`⁅C, H⁆ ≤ H₀`** (`C = C_U(H̄)` centralizes the chief factor): for `c ∈ C` and `h ∈ H`,
`c` acts trivially on `H̄ = H/H₀`, so `c h c⁻¹ ≡ h (mod H₀)` and `⁅c,h⁆ ∈ H₀`.  A structural
input of the (9.9.a) `⁅HC,HC⁆ ⊆ 𝒮(H₀C')`-kernel linearity. -/
theorem commutator_cSub_H_le_H0 [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅cSub data chief, data.H⁆ ≤ chief.H0 := by
  have := chief.N_normal
  rw [Subgroup.commutator_le]
  intro c hc h hh
  -- `c` is the `G`-image of a kernel element `z ∈ U W₁` (`uActionHom z = 1`).
  simp only [cSub, Subgroup.mem_map] at hc
  obtain ⟨z, ⟨a, ha_ker, ha_z⟩, hz_c⟩ := hc
  have hz1 : quotientMulAutHom chief.N_aInvariant z = 1 := by
    rw [← ha_z]; exact MonoidHom.mem_ker.mp ha_ker
  set hH : ↥data.H := ⟨h, hh⟩ with hhH
  set W : ↥data.H := typeP_conjAction data.typeP z hH * hH⁻¹ with hW
  -- `W ∈ N`: `mk W = (φ_U z)(mk h) · (mk h)⁻¹ = mk h · (mk h)⁻¹ = 1`.
  have hWN : W ∈ chief.N := by
    have hmk : (QuotientGroup.mk' chief.N) W = 1 := by
      rw [hW, map_mul, map_inv,
        ← OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'
          chief.N_aInvariant z hH, hz1, MulAut.one_apply, mul_inv_cancel]
    have hker := MonoidHom.mem_ker.mpr hmk
    rwa [QuotientGroup.ker_mk'] at hker
  -- `⁅c,h⁆ = (W : G) ∈ H₀`.
  rw [chief.H0_eq]
  refine ⟨W, hWN, ?_⟩
  have hzc : ((z : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) = c := hz_c
  rw [hW, commutatorElement_def, map_mul, map_inv,
    show data.H.subtype (typeP_conjAction data.typeP z hH)
      = ((typeP_conjAction data.typeP z hH : ↥data.H) : G) from rfl,
    typeP_conjAction_apply, hzc]
  simp [hhH]

open scoped commutatorElement in
/-- **`H₀C ◁ M`** (Peterfalvi `Ptype_Fcore_extensions_normal`, the third structural input for the
`H₀C` reducible count, issue 1012): the normal subgroup `H₀ ⊔ C` of `M` realised as
`(H₀ ⊔ C).subgroupOf M ◁ ↥M`.  `M = H ⊔ (U ⊔ W₁)` (`M_complement`, `derivedInG = H ⊔ U`) normalizes
`H₀ ⊔ C` generator-class by generator-class: `M ≤ N(H₀)` (9.4) handles the `H₀` part throughout,
while the `C` part splits — `U W₁ ≤ N(C)` *exactly* (`cSub_normalized_by_uW1`), and `H` normalizes
`H₀C` because `⁅H, C⁆ ≤ H₀` (`commutator_cSub_H_le_H0`) lets `H₀` absorb the `H`-conjugates of
`C`. -/
theorem chiefFactor_H0supC_subgroupOf_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ cSub data chief).subgroupOf M).Normal := by
  have hH0CleM : chief.H0 ⊔ cSub data chief ≤ M :=
    (chiefFactor_H0supC_le_derived chief).trans (derivedInG_le_self M)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hH0CleM]
  -- A subgroup that conjugates `K` into itself normalizes `K` (the reverse inclusion is `g⁻¹`).
  have key : ∀ (K Hs : Subgroup G), (∀ g ∈ Hs, ConjAct.toConjAct g • K ≤ K) →
      Hs ≤ Subgroup.normalizer (K : Set G) := by
    intro K Hs hle g hg
    rw [← Subgroup.conjAct_pointwise_smul_iff]
    refine le_antisymm (hle g hg) ?_
    have h1 : ConjAct.toConjAct g • (ConjAct.toConjAct g⁻¹ • K) ≤ ConjAct.toConjAct g • K :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (hle g⁻¹ (inv_mem hg))
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at h1
  -- `U W₁ ≤ N(H₀ ⊔ C)`: `U W₁ ≤ M ≤ N(H₀)` and `U W₁ ≤ N(C)` (`cSub_normalized_by_uW1`).
  have hUW1 : data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cSub data chief : Subgroup G) : Set G) :=
    le_trans (le_inf (le_trans (sup_le (U_le_M data) data.typeP.W1_le) chief.H0_normalized_by_M)
      (cSub_normalized_by_uW1 data chief))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (cSub data chief))
  -- `H ≤ N(H₀ ⊔ C)`: `H ≤ N(H₀)` and `h C h⁻¹ ⊆ H₀ C` via `⁅H, C⁆ ≤ H₀`.
  have hH :
      data.typeP.H ≤ Subgroup.normalizer ((chief.H0 ⊔ cSub data chief : Subgroup G) : Set G) := by
    refine key _ _ (fun h hh => ?_)
    rw [Subgroup.smul_sup]
    refine sup_le ?_ ?_
    · rw [Subgroup.conjAct_pointwise_smul_eq_self (chief.H0_normalized_by_M (H_le_M data hh))]
      exact le_sup_left
    · intro x hx
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
      have hc₀ : (ConjAct.toConjAct h)⁻¹ • x ∈ cSub data chief := hx
      have hH0mem : ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ ∈ chief.H0 := by
        have hcomm : ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ ∈ ⁅data.typeP.H, cSub data chief⁆ :=
          Subgroup.commutator_mem_commutator hh hc₀
        rw [Subgroup.commutator_comm] at hcomm
        exact commutator_cSub_H_le_H0 data chief hcomm
      have hxeq : x = ⁅h, (ConjAct.toConjAct h)⁻¹ • x⁆ * ((ConjAct.toConjAct h)⁻¹ • x) := by
        rw [commutatorElement_def]
        simp only [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
        group
      rw [hxeq]
      exact mul_mem (Subgroup.mem_sup_left hH0mem) (Subgroup.mem_sup_right hc₀)
  -- `M = H ⊔ (U ⊔ W₁)`.
  have hM'eq : derivedInG M = data.typeP.H ⊔ data.typeP.U := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hMW1 : derivedInG M ⊔ data.typeP.W1 = M := by
    have hmap := congrArg (Subgroup.map M.subtype) data.typeP.M_complement.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (derivedInG_le_self M), inf_of_le_left data.typeP.W1_le,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have hMeq : M = data.typeP.H ⊔ (data.typeP.U ⊔ data.typeP.W1) := by
    rw [← sup_assoc, ← hM'eq, hMW1]
  exact hMeq.le.trans (sup_le hH hUW1)

end

/-- **Peterfalvi (9.9.b) for `𝒮(H₀C)`**: it too contains exactly `p − 1` reducible characters.

The book proves this for `𝒮(H₀)` and `𝒮(H₀C)` in one breath — "By (4.7) and Theorem (4.5), **both**
`𝒮(H₀)` and `𝒮(H₀C)` contain exactly `p − 1` reducible characters `μ_j`" (p. 54) — and the repo's
`reducible_count_sOf_K` is exactly that shared argument, its docstring already noting both
instantiations.  All five inputs are on hand at `K = H₀C`, mirroring `reducible_count_sOf_H0`.

The point of the `H₀C` form is that `H₀C′ ≤ H₀C` makes `𝒮(H₀C) ⊆ 𝒮(H₀C′)` (`sOf_antitone`), so this
is what witnesses `𝒮(H₀C′) ≠ ∅` — the pivot of the (9.11) case (9.7.b) coherence engine — without
going through the §10/§11 packaging (issue 1045). -/
theorem reducible_count_sOf_H0supC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    {φ ∈ sOf data (chief.H0 ⊔ cSub data chief) | ¬ IsIrreducibleCharacter φ}.ncard
      = chief.p - 1 := by
  have := chiefFactor_H0_subgroupOf_normal chief
  have := chiefFactor_H0supC_subgroupOf_normal chief
  exact reducible_count_sOf_K hG chief (chief.H0 ⊔ cSub data chief)
    (Subgroup.comap_mono (chiefFactor_H0supC_le_derived chief))
    (chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot chief)
    (chiefFactor_W2_not_le_H0supC chief) (chiefFactor_card_W2bar_H0supC chief)

/-- `derivedInG H = ⁅H, H⁆` (general): the image of `commutator ↥H` under the inclusion is the
commutator subgroup `⁅H,H⁆`. -/
theorem derivedInG_eq_commutator (H : Subgroup G) : derivedInG H = ⁅H, H⁆ := by
  rw [derivedInG, commutator_def, Subgroup.map_commutator]
  simp only [← H.subtype.range_eq_map, Subgroup.range_subtype]

section

open scoped commutatorElement

/-- **Peterfalvi (9.9.a): `H ⊔ C ≤ normalizer(H₀ ⊔ C')`.**  For a generator `x ∈ H ∪ C` and any
`k ∈ K = H₀C'`, `⁅x,k⁆ ∈ K`: by `closure_induction` on `k`, the base cases (`k ∈ H₀` or `k ∈ C'`)
use
`⁅H,H₀⁆,⁅C,H₀⁆ ≤ H₀` and `⁅H,C'⁆ ≤ H₀`, `⁅C,C'⁆ ≤ C'`, and the inductive conjugations stay in `K`
since `K` is closed under conjugation by its own elements.  Then `x k x⁻¹ = ⁅x,k⁆·k ∈ K`. -/
theorem HsupC_le_normalizer_K [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.H ⊔ cSub data chief
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cprimeSub data chief : Subgroup G) : Set G) := by
  have := chief.N_normal
  set K := chief.H0 ⊔ cprimeSub data chief with hKdef
  have hHH : ⁅data.H, data.H⁆ ≤ K :=
    le_trans ((derivedInG_eq_commutator data.H).symm.trans_le (derivedInG_H_le_H0 data chief))
      le_sup_left
  have hCH : ⁅cSub data chief, data.H⁆ ≤ K :=
    le_trans (commutator_cSub_H_le_H0 data chief) le_sup_left
  have hHC' : ⁅data.H, cSub data chief⁆ ≤ K := by rw [Subgroup.commutator_comm]; exact hCH
  have hCC : ⁅cSub data chief, cSub data chief⁆ ≤ K :=
    le_trans (derivedInG_eq_commutator (cSub data chief)).symm.le le_sup_right
  have hKclosure : K = Subgroup.closure (↑chief.H0 ∪ ↑(cprimeSub data chief) : Set G) := by
    rw [hKdef, Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  -- For a generator `x ∈ H ∪ C` and any `k ∈ K`, `⁅x, k⁆ ∈ K`.
  have hcomm : ∀ x : G, (x ∈ data.H ∨ x ∈ cSub data chief) → ∀ k ∈ K, ⁅x, k⁆ ∈ K := by
    intro x hx k hk
    rw [hKclosure] at hk
    induction hk using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy0 | hyc'
      · rcases hx with hxH | hxC
        · exact hHH (Subgroup.commutator_mem_commutator hxH (chief.H0_lt_H.le hy0))
        · exact hCH (Subgroup.commutator_mem_commutator hxC (chief.H0_lt_H.le hy0))
      · rcases hx with hxH | hxC
        · exact hHC' (Subgroup.commutator_mem_commutator hxH (cprimeSub_le_C data chief hyc'))
        · exact hCC (Subgroup.commutator_mem_commutator hxC (cprimeSub_le_C data chief hyc'))
    | one => simp
    | mul a b ha hb iha ihb =>
      have haK : a ∈ K := by rw [hKclosure]; exact ha
      rw [show ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact mul_mem iha (mul_mem (mul_mem haK ihb) (K.inv_mem haK))
    | inv a ha iha =>
      have haK : a ∈ K := by rw [hKclosure]; exact ha
      rw [show ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a by
        rw [commutatorElement_def, commutatorElement_def]; group]
      exact mul_mem (mul_mem (K.inv_mem haK) (K.inv_mem iha)) haK
  -- conclude normalizer membership for generators, then `sup_le`.
  have hnorm : ∀ x : G, (x ∈ data.H ∨ x ∈ cSub data chief) → x ∈ Subgroup.normalizer K := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [show x * n * x⁻¹ = ⁅x, n⁆ * n by rw [commutatorElement_def]; group]
      exact mul_mem (hcomm x hx n hn) hn
    · have hxinv : x⁻¹ ∈ data.H ∨ x⁻¹ ∈ cSub data chief := by
        rcases hx with h | h
        · exact Or.inl (data.H.inv_mem h)
        · exact Or.inr ((cSub data chief).inv_mem h)
      have hkey := mul_mem (hcomm x⁻¹ hxinv _ hn) hn
      rw [show ⁅x⁻¹, x * n * x⁻¹⁆ * (x * n * x⁻¹) = n by
        rw [commutatorElement_def]; group] at hkey
      exact hkey
  exact sup_le (fun x hx => hnorm x (Or.inl hx)) (fun x hx => hnorm x (Or.inr hx))

/-- **Peterfalvi (9.9.a) commutator step**: `⁅HC, HC⁆ ≤ H₀C'`.  `K = H₀C'` is normal in `HC`
(`HsupC_le_normalizer_K`), and in the quotient `HC/K` the images of `H` and `C` commute and are
abelian (the four sub-commutators `⁅H,H⁆,⁅H,C⁆,⁅C,H⁆,⁅C,C⁆ ≤ K`), so `HC/K` is abelian, i.e.
`⁅HC,HC⁆ ≤ K`.  This is the kernel containment making the (9.9.a) `S(H₀C')`-constituents linear. -/
theorem commutator_HsupC_le_H0Cprime [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅data.H ⊔ cSub data chief, data.H ⊔ cSub data chief⁆
      ≤ chief.H0 ⊔ cprimeSub data chief := by
  have := chief.N_normal
  set HC := data.H ⊔ cSub data chief with hHCdef
  set K := chief.H0 ⊔ cprimeSub data chief with hKdef
  have hHH : ⁅data.H, data.H⁆ ≤ K :=
    le_trans ((derivedInG_eq_commutator data.H).symm.trans_le (derivedInG_H_le_H0 data chief))
      le_sup_left
  have hCH : ⁅cSub data chief, data.H⁆ ≤ K :=
    le_trans (commutator_cSub_H_le_H0 data chief) le_sup_left
  have hHC' : ⁅data.H, cSub data chief⁆ ≤ K := by rw [Subgroup.commutator_comm]; exact hCH
  have hCC : ⁅cSub data chief, cSub data chief⁆ ≤ K :=
    le_trans (derivedInG_eq_commutator (cSub data chief)).symm.le le_sup_right
  have hKle : K ≤ HC :=
    sup_le (le_trans chief.H0_lt_H.le le_sup_left)
      (le_trans (cprimeSub_le_C data chief) le_sup_right)
  have hK'normal : (K.subgroupOf HC).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mpr (HsupC_le_normalizer_K data chief)
  -- `commutator ↥HC ≤ K.subgroupOf HC` via the quotient `HC/K` being abelian.
  have hcomm : commutator ↥HC ≤ K.subgroupOf HC := by
    have hmk_surj := QuotientGroup.mk'_surjective (K.subgroupOf HC)
    set mk := QuotientGroup.mk' (K.subgroupOf HC) with hmk
    have hsub : ∀ P Q : Subgroup G, ⁅P, Q⁆ ≤ K →
        ⁅(P.subgroupOf HC).map mk, (Q.subgroupOf HC).map mk⁆ = ⊥ := by
      intro P Q hPQ
      rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, hmk, QuotientGroup.ker_mk',
        Subgroup.commutator_le]
      intro x hx y hy
      rw [Subgroup.mem_subgroupOf] at hx hy ⊢
      have hxy : ((⁅x, y⁆ : ↥HC) : G) = ⁅((x : ↥HC) : G), ((y : ↥HC) : G)⁆ := by
        simp [commutatorElement_def]
      rw [hxy]
      exact hPQ (Subgroup.commutator_mem_commutator hx hy)
    rw [← QuotientGroup.ker_mk' (K.subgroupOf HC), ← Subgroup.map_eq_bot_iff, commutator_def,
      Subgroup.map_commutator, Subgroup.map_top_of_surjective mk hmk_surj]
    have hAB : (data.H.subgroupOf HC).map mk ⊔ ((cSub data chief).subgroupOf HC).map mk = ⊤ := by
      rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
        show (data.H ⊔ cSub data chief).subgroupOf HC = ⊤ from Subgroup.subgroupOf_self HC,
        Subgroup.map_top_of_surjective mk hmk_surj]
    rw [← hAB, Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.centralizer_sup]
    refine sup_le (le_inf ?_ ?_) (le_inf ?_ ?_)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub data.H data.H hHH)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub data.H (cSub data chief) hHC')
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hsub (cSub data chief) data.H hCH)
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (hsub (cSub data chief) (cSub data chief) hCC)
  -- `⁅HC,HC⁆ = (commutator ↥HC).map subtype ≤ K ⊓ HC ≤ K`.
  calc ⁅data.H ⊔ cSub data chief, data.H ⊔ cSub data chief⁆
      = (commutator ↥HC).map HC.subtype := by rw [← derivedInG_eq_commutator]; rfl
    _ ≤ (K.subgroupOf HC).map HC.subtype := Subgroup.map_mono hcomm
    _ ≤ K := by rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- **(9.9.a) realized commutator bound**: `⁅HC, HC⁆ ⊆ 𝒮(H₀C')`-kernel, i.e. the realized commutator
`⁅hInHu ⊔ cInHu, hInHu ⊔ cInHu⁆` lands in the realized `H₀C'` inside `↥HU`.  Transport of
`commutator_HsupC_le_H0Cprime` along the inclusion `↥HU ↪ ↥M ↪ G` (`map_le_iff_le_comap`). -/
theorem commutator_hcInHu_le_realized [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆
      ≤ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) := by
  have hreal : ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0 ⊔ cprimeSub data chief).comap (M.subtype.comp (huSub data).subtype) := rfl
  have hmaple : (hInHu data ⊔ cInHu data chief).map (M.subtype.comp (huSub data).subtype)
      ≤ data.H ⊔ cSub data chief := by
    rw [Subgroup.map_sup]
    refine sup_le (le_trans ?_ le_sup_left) (le_trans ?_ le_sup_right)
    · have hh : hInHu data = data.H.comap (M.subtype.comp (huSub data).subtype) := by
        rw [hInHu, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_comap]
      rw [hh]; exact Subgroup.map_comap_le _ _
    · have hc : cInHu data chief = (cSub data chief).comap (M.subtype.comp
        (huSub data).subtype) := by
        rw [cInHu, Subgroup.subgroupOf, Subgroup.subgroupOf, Subgroup.comap_comap]
      rw [hc]; exact Subgroup.map_comap_le _ _
  rw [hreal, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
  exact le_trans (Subgroup.commutator_mono hmaple hmaple) (commutator_HsupC_le_H0Cprime data chief)

set_option backward.isDefEq.respectTransparency false in
/-- **`U W₁ ≤ N(C')`**: the normalizer of `C` normalizes its commutator subgroup
`C' = ⁅C,C⁆` — conjugation maps `C` onto itself (`cSub_normalized_by_uW1`), hence maps
`⁅C,C⁆` onto itself (`Subgroup.map_commutator`). -/
theorem cprimeSub_normalized_by_uW1 [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((cprimeSub data chief : Subgroup G) : Set G) := by
  intro g hg
  have hgC : ConjAct.toConjAct g • cSub data chief = cSub data chief :=
    Subgroup.conjAct_pointwise_smul_eq_self (cSub_normalized_by_uW1 data chief hg)
  rw [← Subgroup.conjAct_pointwise_smul_iff,
    show cprimeSub data chief = ⁅cSub data chief, cSub data chief⁆ from
      derivedInG_eq_commutator _,
    Subgroup.pointwise_smul_def, Subgroup.map_commutator, ← Subgroup.pointwise_smul_def, hgC]

set_option backward.isDefEq.respectTransparency false in
/-- **`U W₁ ≤ N_G(U')`** (the `U W₁`-half of `H₀U' ◁ M`, Peterfalvi (9.8.d)): `U W₁` normalizes
`U' = [U,U]`.  `U ⊔ W₁ ≤ N(U)` (`U ≤ N(U)` and `W₁ ≤ N(U)` by `W1_normalizes_U`), and normalizing
`U` normalizes its derived subgroup `[U,U]`.  Mirror of `cprimeSub_normalized_by_uW1`. -/
theorem uprimeSub_normalized_by_uW1 [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((uprimeSub data : Subgroup G) : Set G) := by
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (data.U : Set G) :=
    (sup_le (Subgroup.le_normalizer (H := data.typeP.U)) data.typeP.W1_normalizes_U) hg
  have hgU : ConjAct.toConjAct g • data.U = data.U :=
    Subgroup.conjAct_pointwise_smul_eq_self hgN
  rw [← Subgroup.conjAct_pointwise_smul_iff,
    show uprimeSub data = ⁅data.U, data.U⁆ from derivedInG_eq_commutator _,
    Subgroup.pointwise_smul_def, Subgroup.map_commutator, ← Subgroup.pointwise_smul_def, hgU]

/-- **`H ≤ N_G(U')`** (the `H`-half of `H₀U' ◁ M`, Peterfalvi (9.8.d)): `H` normalizes `U' = [U,U]`
because it *centralizes* it — `U' ≤ C_G(H)` (`typeP_commutator_U_centralizes_H`) means every `h ∈ H`
commutes with every `x ∈ U'`, so `H ≤ C_G(U') ≤ N_G(U')`.  This is the analog of
`HsupC_le_normalizer_K` for the `U'`-side (where `H` centralizes rather than merely normalizes). -/
theorem typeP_H_le_normalizer_uprimeSub [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    data.typeP.H ≤ Subgroup.normalizer ((uprimeSub data : Subgroup G) : Set G) := by
  -- `U' ≤ C(H)`: every `x ∈ U'` commutes with every `h ∈ H`.
  have hUprime_CH : uprimeSub data ≤ Subgroup.centralizer (data.typeP.H : Set G) := by
    rw [show uprimeSub data = ⁅data.U, data.U⁆ from derivedInG_eq_commutator _]
    exact typeP_commutator_U_centralizes_H data.typeP
  -- symmetric form: `H ≤ C(U')`, then `C(U') ≤ N(U')`.
  refine le_trans (fun h hh => ?_) (Subgroup.centralizer_le_normalizer (uprimeSub data : Set G))
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact ((Subgroup.mem_centralizer_iff.mp
    (hUprime_CH (SetLike.mem_coe.mp hx)) h hh)).symm

/-- **`H₀U' ≤ M'`** (Peterfalvi (9.8.d)): the kernel subgroup `H₀ ⊔ U'` lies in the derived subgroup
`M'`.  `H₀ ≤ H ≤ M'` and `U' = [U,U] ≤ U ≤ M'` (both `H` and `U` lie in `M' = F(M) ⋊ U`). -/
theorem chiefFactor_H0supUprime_le_derived {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    chief.H0 ⊔ uprimeSub data ≤ derivedInG M :=
  sup_le (chief.H0_lt_H.le.trans data.typeP.H_le)
    ((uprimeSub_le_U data).trans data.typeP.U_le)

/-- **`H₀U' ◁ M`** (Peterfalvi (9.8.d)): the (9.8.d) kernel subgroup `H₀ ⊔ U'` is normal in `M`.
`M = H ⊔ (U ⊔ W₁)` generator-class by generator-class: `U W₁ ≤ N(H₀) ⊓ N(U')`
(`H0_normalized_by_M`, `uprimeSub_normalized_by_uW1`), and `H ≤ N(H₀) ⊓ N(U')`
(`H0_normalized_by_M`, `typeP_H_le_normalizer_uprimeSub`).  Mirror of
`chiefFactor_H0supCprime_subgroupOf_normal` for the `U'`-side. -/
theorem chiefFactor_H0supUprime_subgroupOf_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ uprimeSub data).subgroupOf M).Normal := by
  have hKleM : chief.H0 ⊔ uprimeSub data ≤ M :=
    (chiefFactor_H0supUprime_le_derived chief).trans (derivedInG_le_self M)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleM]
  have hUW1 : data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((chief.H0 ⊔ uprimeSub data : Subgroup G) : Set G) :=
    le_trans (le_inf (le_trans (sup_le (U_le_M data) data.typeP.W1_le)
        chief.H0_normalized_by_M)
      (uprimeSub_normalized_by_uW1 data))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (uprimeSub data))
  have hH : data.typeP.H
      ≤ Subgroup.normalizer ((chief.H0 ⊔ uprimeSub data : Subgroup G) : Set G) :=
    le_trans (le_inf ((data.typeP.H_le.trans (derivedInG_le_self M)).trans chief.H0_normalized_by_M)
        (typeP_H_le_normalizer_uprimeSub data))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (uprimeSub data))
  have hM'eq : derivedInG M = data.typeP.H ⊔ data.typeP.U := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hMW1 : derivedInG M ⊔ data.typeP.W1 = M := by
    have hmap := congrArg (Subgroup.map M.subtype) data.typeP.M_complement.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (derivedInG_le_self M), inf_of_le_left data.typeP.W1_le,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have hMeq : M = data.typeP.H ⊔ (data.typeP.U ⊔ data.typeP.W1) := by
    rw [← sup_assoc, ← hM'eq, hMW1]
  exact hMeq.le.trans (sup_le hH hUW1)

/-- **realized `H₀U' ◁ HU`**: restriction of `H₀U' ◁ M` along `huSub ≤ ↥M`.  The `[A.Normal]`
input of the induce-kernel step for the (9.8.d) source character's `𝒮(H₀U')`-membership. -/
theorem realizedH0supUprime_normal_huSub [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)).Normal :=
  (chiefFactor_H0supUprime_subgroupOf_normal chief).subgroupOf (huSub data)

/-- **`H₀C' ◁ M`** (mirror of `chiefFactor_H0supC_subgroupOf_normal` for `C'`): the (9.9)
exceptional-case kernel subgroup `H₀ ⊔ C'` is normal in `M`.  `M = H ⊔ (U ⊔ W₁)`
generator-class by generator-class: `U W₁ ≤ N(H₀) ⊓ N(C') ≤ N(H₀C')`
(`cprimeSub_normalized_by_uW1`), and `H ≤ HC ≤ N(H₀C')` (`HsupC_le_normalizer_K`). -/
theorem chiefFactor_H0supCprime_subgroupOf_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).Normal := by
  have hKleM : chief.H0 ⊔ cprimeSub data chief ≤ M :=
    le_trans (sup_le_sup_left (cprimeSub_le_C data chief) chief.H0)
      ((chiefFactor_H0supC_le_derived chief).trans (derivedInG_le_self M))
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKleM]
  have hUW1 : data.typeP.U ⊔ data.typeP.W1
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cprimeSub data chief : Subgroup G) : Set G) :=
    le_trans (le_inf (le_trans (sup_le (U_le_M data) data.typeP.W1_le)
        chief.H0_normalized_by_M)
      (cprimeSub_normalized_by_uW1 data chief))
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup chief.H0 (cprimeSub data chief))
  have hH : data.typeP.H
      ≤ Subgroup.normalizer ((chief.H0 ⊔ cprimeSub data chief : Subgroup G) : Set G) :=
    le_trans (le_sup_left : data.typeP.H ≤ data.H ⊔ cSub data chief)
      (HsupC_le_normalizer_K data chief)
  have hM'eq : derivedInG M = data.typeP.H ⊔ data.typeP.U := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hMW1 : derivedInG M ⊔ data.typeP.W1 = M := by
    have hmap := congrArg (Subgroup.map M.subtype) data.typeP.M_complement.sup_eq_top
    rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left (derivedInG_le_self M), inf_of_le_left data.typeP.W1_le,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  have hMeq : M = data.typeP.H ⊔ (data.typeP.U ⊔ data.typeP.W1) := by
    rw [← sup_assoc, ← hM'eq, hMW1]
  exact hMeq.le.trans (sup_le hH hUW1)

/-- **realized `H₀C' ◁ HU`**: restriction of `H₀C' ◁ M` along `huSub ≤ ↥M`.  The `[A.Normal]`
input of the induce-kernel step for the (9.9.c) pair character. -/
theorem realizedH0supCprime_normal_huSub [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
  (chiefFactor_H0supCprime_subgroupOf_normal chief).subgroupOf (huSub data)

/-- **realized `H₀C' = H₀ ⊔ C'` distributes** (mirror of
`realizedH0supC_eq_realizedH0_sup_cInHu`): the realized `H₀C'` inside `HU` equals
`(realized H₀) ⊔ (realized C')`.  Feeds the `h₀·c'` decomposition of the pair-character kernel
computation. -/
theorem realizedH0supCprime_eq_realizedH0_sup_cprimeInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0.subgroupOf M).subgroupOf (huSub data)
          ⊔ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) := by
  have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
  have hCM : cprimeSub data chief ≤ M :=
    ((cprimeSub_le_C data chief).trans (cSub_le_U data chief)).trans (U_le_M data)
  rw [Subgroup.subgroupOf_sup hH0M hCM]
  have hH0sub : (chief.H0.subgroupOf M) ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans chief.H0_lt_H.le le_sup_left)
  have hCsub : (cprimeSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans ((cprimeSub_le_C data chief).trans
      (cSub_le_U data chief)) le_sup_right)
  rw [Subgroup.subgroupOf_sup hH0sub hCsub]

end

/-- **(9.9.a) index step (C): `[U:C] = u`** realized form `(cInHu.subgroupOf uInHu).index = u`.
First isomorphism `U/C ≃ Ū` (the `U`-action image on the chief factor), with `u = |Ū|`. -/
theorem index_cInHu_subgroupOf_uInHu_eq_u [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    (chars : Section11CharacterData data chief) :
    ((cInHu data chief).subgroupOf (uInHu data)).index = chars.u := by
  -- (I): `|C| · [U:C] = |U|`.
  have hI : Nat.card ↥(cSub data chief) * ((cInHu data chief).subgroupOf (uInHu data)).index
      = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cInHu data chief).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cInHu_le_uInHu data chief)).toEquiv,
      card_cInHu_eq data chief, card_uInHu_eq data] at h
    exact h
  -- (II): `|U| = u · |C|` (first iso for the `U`-action hom).
  have hu : chars.u = Nat.card ↥(uActionHom data chief).range := chars.u_eq_card_quotient
  have hII : Nat.card ↥data.U = chars.u * Nat.card ↥(cSub data chief) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (uActionHom data chief).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (uActionHom data chief)).toEquiv,
      ← card_cSub_eq_card_ker data chief, ← hu,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
    exact h
  have hcancel : Nat.card ↥(cSub data chief)
      * ((cInHu data chief).subgroupOf (uInHu data)).index
      = Nat.card ↥(cSub data chief) * chars.u := by rw [hI, hII, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel

/-- **Constituent kernel inheritance (lies-over form).**  If `χ ∈ Irr Γ` lies over `θ ∈ Irr K`
for a subgroup `K ≤ Γ`, then every element of `K` lying in the character kernel of `χ` also lies in
the character kernel of `θ`: each constituent of `Res^Γ_K χ` inherits `χ`'s kernel containments.

This is the input that makes the (9.9.a) constituent `θ` of `Res^{HU}_H χ` trivial on the
chief-factor kernel `N` (since `H₀ ⊆ ker χ`), so `θ` is an inflation of an `H̄`-character. -/
theorem liesOver_mem_characterKernel {Γ : Type*} [Group Γ] [Finite Γ]
    [Invertible (Nat.card Γ : ℂ)] {K : Subgroup Γ} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    {χ : IrreducibleCharacter Γ} {θ : IrreducibleCharacter ↥K}
    (hlo : IrreducibleCharacter.LiesOver K χ θ) {g : ↥K}
    (hg : ((g : Γ)) ∈ OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction Γ ℂ)) :
    g ∈ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ) := by
  have : Fintype Γ := Fintype.ofFinite Γ
  refine OddOrder.Peterfalvi.S08.characterKernel_subset_of_isCharacter_of_inner_ne_zero
    (ψ := ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
    (OddOrder.Peterfalvi.S08.isCharacter_restrict χ.isIrreducible.isCharacter K)
    θ.isIrreducible ?_ ?_
  · rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  · rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      ClassFunction.restrict_apply]
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hg
    have h1 : ClassFunction.restrict K (χ : ClassFunction Γ ℂ) 1
        = (χ : ClassFunction Γ ℂ) 1 := by
      rw [ClassFunction.restrict_apply]; rfl
    rw [h1]; exact hg

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.9.a), the chief-factor constituent of `χ ∈ 𝒳(H₀)`.**

In Clifford case (b) (`U` acts irreducibly on `H̄ = H/H_0`), any `χ ∈ Irr(HU)` with `H ⊄ Ker χ`
(`χ ∈ 𝒳`) and `H_0 ⊆ Ker χ` lies over a chief-factor constituent `θ₀ ∈ Irr(H)`, realised in
inflation form `θ₀ = compHom (H̄ ≃ ·) (compHom (mk' N) θ̄)` for a nontrivial `θ̄ ∈ Irr(H̄)`.  Its
inertia group in `HU` is `HC` (`inertia_eq_hcInHu`, the case-(b) crux) and it is linear
(`θ₀(1) = 1`, `H̄` elementary abelian).  This is the shared extraction behind the (9.9.a) degree
statements `caseB_degree_qu` (`χ(1) = u` on `𝒳(H₀C')`) and `caseB_xi_H0_degree_dvd_u`
(`u ∣ χ(1)` on the larger `𝒳(H₀)`). -/
theorem caseB_exists_chiefFactorConstituent [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχX : χ ∈ xiSet data)
    (hχH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ θ₀ : IrreducibleCharacter ↥(hInHu data),
      IrreducibleCharacter.LiesOver (hInHu data) χ θ₀ ∧
      IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀
        = hInHu data ⊔ cInHu data chief ∧
      (θ₀ : ClassFunction ↥(hInHu data) ℂ) (1 : ↥(hInHu data)) = 1 := by
  classical
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  -- A nontrivial constituent `θ` of `Res^{HU}_H χ` (`H ⊄ Ker χ`).
  obtain ⟨θ, hθlo, hθnt⟩ :=
    OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
      (A := hInHu data) (B := hInHu data) le_rfl χ hχX
  -- The descent hom `f = (mk' N) ∘ hInHuEquivH : ↥(hInHu) → H̄ = ↥H ⧸ N`.
  set f : ↥(hInHu data) →* (↥data.H ⧸ chief.N) :=
    (QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom with hf
  have hfsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  -- `f.ker ⊆ ker θ`: `f x = 1` puts the `G`-coordinate of `x` in `H₀ ⊆ ker χ`.
  have hfker : (f.ker : Set ↥(hInHu data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥(hInHu data) ℂ) := by
    intro x hx
    have hxN : (hInHuEquivH data) x ∈ chief.N := by
      have hx1 : f x = 1 := hx
      rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx1
      exact hx1
    have hxH0 : (((x : ↥(huSub data)) : ↥M) : G) ∈ chief.H0 := by
      rw [chief.H0_eq, ← hInHuEquivH_coe data x]
      exact Subgroup.mem_map_of_mem data.H.subtype hxN
    have hxχ : (x : ↥(huSub data)) ∈
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) := by
      apply hχH0
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hxH0
    exact liesOver_mem_characterKernel hθlo hxχ
  -- `θ` is an inflation: `θ = compHom f θbar` for some `θbar ∈ Irr(H̄)`.
  obtain ⟨θbar, hθbar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hfsurj θ hfker
  have hθeq : (θ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) := by
    rw [← hθbar, hf, ClassFunction.compHom_comp]
  have hθbarnt : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθnt
    rw [Subgroup.subgroupOf_self]
    intro y _
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
      hθeq, h0]
    simp [ClassFunction.compHom_apply, trivialClassFunction]
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  refine ⟨θ, hθlo, ?_, ?_⟩
  · change ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
      (θ : ClassFunction ↥(hInHu data) ℂ) = hInHu data ⊔ cInHu data chief
    rw [hθeq]
    exact inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  · rw [hθeq]
    simp only [ClassFunction.compHom_apply, map_one]
    exact θbar.isIrreducible.apply_one_eq_one_of_isMulCommutative

/-- **caseA constituent extraction (hom form)** (Peterfalvi (9.8.c) surjectivity route): any
`χ ∈ 𝒳` with `H₀ ⊆ Ker χ` lies over a nontrivial *linear* chief-factor constituent
`linearIrreducibleCharacter (θbar ∘ mk'N ∘ hInHuEquivH)` for some nontrivial `θbar : H̄ →* ℂˣ`.

Case-agnostic (no `U`-irreducibility): mirrors `caseB_exists_chiefFactorConstituent`'s constituent
extraction but returns the *hom-form* seed `θbar : H̄ →* ℂˣ` — needed for the per-`Hpart` regularity
argument of the (9.8.c) surjectivity route, which multiplies `θbar` by the `Hpart i` inclusions
(`θbar.comp (caseA.Hpart i).subtype`).  Extract a constituent `θ` of `Res_H χ` not killing `H`
(`exists_constituent_not_subset_characterKernel`), inflate it through `f = mk'N ∘ hInHuEquivH`
(`H₀ ⊆ Ker χ ⟹ f.ker ⊆ Ker θ`, `exists_compHom_eq_of_subset_characterKernel`), and convert the
resulting irreducible `H̄`-character to hom form (`H̄` abelian,
`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`).  The caseA regularity of
`θbar` (from `M`-fixedness of `χ`) is established separately. -/
theorem exists_hom_constituent_of_mem_xiSet_H0 [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχX : χ ∈ xiSet data)
    (hχH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ,
      θbar ≠ 1 ∧
      IrreducibleCharacter.LiesOver (hInHu data) χ
        (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom))) := by
  classical
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  -- A nontrivial constituent `θ` of `Res^{HU}_H χ` (`H ⊄ Ker χ`).
  obtain ⟨θ, hθlo, hθnt⟩ :=
    OddOrder.RepresentationTheory.exists_constituent_not_subset_characterKernel
      (A := hInHu data) (B := hInHu data) le_rfl χ hχX
  -- The descent hom `f = (mk' N) ∘ hInHuEquivH : ↥(hInHu) → H̄ = ↥H ⧸ N`.
  set f : ↥(hInHu data) →* (↥data.H ⧸ chief.N) :=
    (QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom with hf
  have hfsurj : Function.Surjective f :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  -- `f.ker ⊆ ker θ`: `f x = 1` puts the `G`-coordinate of `x` in `H₀ ⊆ ker χ`.
  have hfker : (f.ker : Set ↥(hInHu data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥(hInHu data) ℂ) := by
    intro x hx
    have hxN : (hInHuEquivH data) x ∈ chief.N := by
      have hx1 : f x = 1 := hx
      rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx1
      exact hx1
    have hxH0 : (((x : ↥(huSub data)) : ↥M) : G) ∈ chief.H0 := by
      rw [chief.H0_eq, ← hInHuEquivH_coe data x]
      exact Subgroup.mem_map_of_mem data.H.subtype hxN
    have hxχ : (x : ↥(huSub data)) ∈
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) := by
      apply hχH0
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact hxH0
    exact liesOver_mem_characterKernel hθlo hxχ
  -- `θ` is an inflation `θ = compHom f θbar_irr` for some `θbar_irr ∈ Irr(H̄)`.
  obtain ⟨θbar_irr, hθbar⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel hfsurj θ hfker
  -- `H̄` abelian, so `θbar_irr` is a linear character `θbar : H̄ →* ℂˣ`.
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbarval⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θbar_irr.isIrreducible
  have hθbar_eq : (θbar_irr : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
    ext g
    rw [linearIrreducibleCharacter_apply, hθbarval]
  have hθ_eq : (θ : ClassFunction ↥(hInHu data) ℂ)
      = (linearIrreducibleCharacter (θbar.comp f) : ClassFunction ↥(hInHu data) ℂ) := by
    rw [← hθbar, hθbar_eq, ClassFunction.compHom_linearIrreducibleCharacter]
  have hθθ : θ = linearIrreducibleCharacter (θbar.comp f) := IrreducibleCharacter.ext hθ_eq
  refine ⟨θbar, ?_, ?_⟩
  · -- `θbar ≠ 1`: else `θ = linear(1) = trivial`, contradicting `H ⊄ Ker θ`.
    intro h0
    apply hθnt
    rw [Subgroup.subgroupOf_self]
    intro y _
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_eq, h0]
    simp
  · show IrreducibleCharacter.LiesOver (hInHu data) χ
      (linearIrreducibleCharacter (θbar.comp f))
    rw [← hθθ]; exact hθlo

/-- **Peterfalvi (9.9.a)**: every member of `𝒮(H₀C')` has degree `qu`.

For `φ = Ind_{HU}^M χ ∈ 𝒮(H₀C')` (so `χ ∈ 𝒳(H₀C')`, i.e. `χ ∈ Irr(HU)` with `H ⊄ Ker χ` and
`H₀C' ⊆ Ker χ`), `φ(1) = [M:HU]·χ(1) = q·χ(1)` (`induceHU_apply_one_eq_q_mul`), so it suffices to
show `χ(1) = u`.  That is the Clifford degree `χ(1) = [HU:HC]` via
`apply_one_eq_index_of_liesOver_linear_inertia`: `χ` lies over a nontrivial chief-factor character
`θ₀` (inflation of `θbar ∈ Irr(H̄)`, linear since `H̄` is abelian) whose inertia in `HU` is `HC`
(`inertia_eq_hcInHu`, case (b)), and over a linear `ψ ∈ Irr(HC)` (`[HC,HC] ⊆ Ker χ ⟹ ψ(1)=1`); the
degree sandwich forces `χ(1) = [HU:HC] = u`. -/
theorem caseB_degree_qu [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    ∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), φ 1 = ((data.q * chars.u : ℕ) : ℂ) := by
  classical
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ cInHu data chief) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥(hInHu data ⊔ cInHu data chief) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro φ hφ
  rw [Section11CharacterData.SOf_eq, mem_sOf] at hφ
  obtain ⟨χ, hχ, rfl⟩ := hφ
  rw [induceHU_apply_one_eq_q_mul]
  -- Reduce `q·χ(1) = qu` to `χ(1) = u`.
  suffices hχu : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (chars.u : ℂ) by
    rw [hχu]; push_cast; ring
  -- Obligation 1: the chief-factor constituent `θ₀` (case-(b) crux, shared helper).  `χ ∈ 𝒳(H₀C')`
  -- supplies `χ ∈ 𝒳` (`hχ.1`) and, via `H₀ ≤ H₀C'`, the `H₀ ⊆ Ker χ` the helper needs.
  obtain ⟨θ₀, hθ₀over, hθ₀inertia, hθ₀deg⟩ :=
    caseB_exists_chiefFactorConstituent chars caseB hχ.1
      (subset_trans (SetLike.coe_subset_coe.mpr
        (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M le_sup_left))) hχ.2)
  -- Obligation 3: a constituent `ψ ∈ Irr(HC)` that `χ` lies over, linear.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    -- `ψ` is linear: `⁅HC,HC⁆ ⊆ ker χ`, so the constituent `ψ` factors through the abelian
    -- `HC/⁅HC,HC⁆`.
    have : IsMulCommutative (↥(hInHu data ⊔ cInHu data chief) ⧸
        commutator ↥(hInHu data ⊔ cInHu data chief)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥(hInHu data ⊔ cInHu data chief)))
    refine apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ cInHu data chief)) ψ ?_
    intro g hg
    refine liesOver_mem_characterKernel hψover ?_
    refine hχ.2 ?_
    have hgmem : (g : ↥(huSub data))
        ∈ ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆ := by
      rw [← derivedInG_eq_commutator]
      exact Subgroup.mem_map_of_mem _ hg
    exact commutator_hcInHu_le_realized data chief hgmem
  -- Clifford degree: `χ(1) = [HU:HC]`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_index_of_liesOver_linear_inertia
    (H := hInHu data) (I := hInHu data ⊔ cInHu data chief)
    χ θ₀ ψ hθ₀over hθ₀inertia hθ₀deg hψover hψdeg
  -- Obligation 4: `[HU:HC] = u` = `[U:C]` (second iso (A) + first iso (C)).
  have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
    (index_hcInHu_eq_relindex_cInHu data chief).trans
      (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
  rw [key, hidx]

/-- **Peterfalvi (9.9.b), degree part**: every member of `𝒮(H₀C)` has degree `qu`.

Immediate from `caseB_degree_qu` (degree `qu` on `𝒮(H₀C')`): since `C' = ⁅C,C⁆ ≤ C`
(`Cprime_le_C`), we have `H₀C' ≤ H₀C`, so `𝒮(H₀C) ⊆ 𝒮(H₀C')` (`sOf_antitone` — a larger kernel
demand selects fewer characters).  Thus the (9.9.b) degree claim (each reducible member of `𝒮(H₀)`
has degree `qu`) reduces to its membership claim (the reducibles lie in `𝒮(H₀C)`): once a reducible
`φ ∈ 𝒮(H₀)` is shown to lie in `𝒮(H₀C)`, this lemma gives its degree.  The membership itself is the
deep Clifford crux — reducible `Ind_{HU}^M χ` ⟺ `χ` is `W₁`/`M`-invariant, and via the direct
product `HC/H₀ = H̄ × (C/H₀)` the underlying `HC`-linear character is `C`-trivial (Peterfalvi
(9.9.b)/(9.8.b) shared subproof, Coq `PFsection9` `Part_a`). -/
theorem forall_mem_sOf_H0C_apply_one_eq_qu [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    ∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.C), φ 1 = ((data.q * chars.u : ℕ) : ℂ) := by
  intro φ hφ
  refine caseB_degree_qu hG chars caseB φ ?_
  rw [Section11CharacterData.SOf_eq] at hφ ⊢
  exact sOf_antitone data (sup_le_sup_left chars.Cprime_le_C chief.H0) hφ

/-- **Peterfalvi (9.9.b), the `H₀C` reducible count** — parallel to `reducible_count_sOf_H0`.

`𝒮(H₀C)` contains exactly `p − 1` reducible characters.  The same §9↔§6 bijection as
`reducible_count_sOf_H0`, but with the `M/(H₀C)`-certain-type hypothesis: Peterfalvi (8.4.d) holds
for `L = M/(H₀C)` as well as `L = M/H₀`, and `W̄₂' = W₂`-image in `M/(H₀C)` still has order `p`
(`W₂ ∩ H₀C = W₂ ∩ H₀`, since `W₂ ≤ H` and `C ≤ U` meet `H` trivially).  Closing this is the
remaining work — a parallel of the `chiefFactorQuotientHypothesis` + bijection construction with the
normal subgroup `H₀ ⊔ C` in place of `H₀` (issue 1012). -/
theorem reducible_count_sOf_H0C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    {φ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 := by
  have := chiefFactor_H0_subgroupOf_normal chief
  have := chiefFactor_H0supC_subgroupOf_normal chief
  rw [show chars.C = cSub data chief from rfl]
  exact reducible_count_sOf_K hG chief (chief.H0 ⊔ cSub data chief)
    (Subgroup.comap_mono (chiefFactor_H0supC_le_derived chief))
    (chiefFactor_W1_inf_H0supC_subgroupOf_eq_bot chief)
    (chiefFactor_W2_not_le_H0supC chief)
    (chiefFactor_card_W2bar_H0supC chief)

/-- **Peterfalvi (9.9.b), membership**: every reducible member of `𝒮(H₀)` lies in `𝒮(H₀C)`.

A clean **cardinality** argument that avoids the full §9 character construction: `𝒮(H₀C) ⊆ 𝒮(H₀)`
(`sOf_antitone`, `H₀ ≤ H₀C`), so the reducibles of `𝒮(H₀C)` are a subset of those of `𝒮(H₀)`; both
number `p − 1` (`reducible_count_sOf_H0C` / `reducible_count_sOf_H0`).  A subset of equal finite
cardinality is the whole set (`Set.eq_of_subset_of_ncard_le`, finiteness from `p − 1 ≠ 0` as `p` is
prime).  Hence every reducible `𝒮(H₀)`-member already lies in `𝒮(H₀C)`.  Together with
`forall_mem_sOf_H0C_apply_one_eq_qu` (degree), this is the full (9.9.b) degree+membership
conjunct. -/
theorem reducible_mem_sOf_H0C [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    ∀ φ ∈ sOf data chief.H0, ¬ IsIrreducibleCharacter φ →
      φ ∈ sOf data (chief.H0 ⊔ chars.C) := by
  intro φ hφ hred
  have hBA : {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ}
      ⊆ {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ} := by
    rintro ψ ⟨hψS, hψr⟩
    exact ⟨sOf_antitone data le_sup_left hψS, hψr⟩
  have hAfin : {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ}.Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [reducible_count_sOf_H0 hG chief]
      exact Nat.sub_ne_zero_of_lt chief.p_prime.one_lt)
  have hAB : {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ}
      = {ψ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter ψ} :=
    Set.eq_of_subset_of_ncard_le hBA
      (le_of_eq (by rw [reducible_count_sOf_H0 hG chief, reducible_count_sOf_H0C hG chars]))
      hAfin
  have hφmem : φ ∈ {ψ ∈ sOf data (chief.H0 ⊔ chars.C) | ¬ IsIrreducibleCharacter ψ} := by
    rw [hAB]; exact ⟨hφ, hred⟩
  exact hφmem.1

end OddOrder.Peterfalvi.S11



-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry105
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Isometry105
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:31:05.152217+00:00
-- url     : https://prove2.me/theorems/e88ad4ca-f762-4164-9ad2-ad512b420027
-- title:
--   Peterfalvi (10.5): Dade isometry calculations, part 1 (Isometry105)
-- statement:
--   A continuation of the Dade-isometry calculations in §10, covering the four-corner and zero-row identities on the aligned grid, the Dade value on $V$, and the inner-product part of (10.5).
--
--   Main declarations: `Hypothesis.tau_muGrid_zeroRow_diff` (Peterfalvi (4.8) on the §10 aligned grid, row `0`); `Hypothesis.tau_muGrid_fourCorner` (Peterfalvi (4.10) on the §10 aligned grid); `Hypothesis.tau_apply_of_mem_typePV` (§10 Dade value on `V`); `Hypothesis.tau_muGridAlpha_apply_eq_on_typePV` (Peterfalvi (10.5), the Dade-image value on `V`).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Isometry105.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Isometry105.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (4.8) on the §10 aligned grid, row `0`** (coherence-free): for two nonzero
columns `j, k`, `(μ_{0j} − μ_{0k})^τ = δ_j·(ω_{0j}^σ − ω_{0k}^σ)`, where `τ = hyp.tau`,
`ω^σ = alignedOmegaSigmaGrid`, and `δ_j = muColumnSign j`.

This is the §6 isometry identity `certainType_diff_dade_eq` cited through the (8.15)
instantiation `toHypothesis46`: the §10 Dade map is *definitionally* the certain-type
`dadeIntegralCharacterMap h46.dade0 h46.tau`, `muGrid`/`muColumnSign` unfold to the §6
`columnFamily` data (`unfold … rfl`), the equal-degree input is the (10.3) cross-column
constancy `muGrid_apply_one_eq` (whence `hw2`), and the §6 σ-image `certainTypeOmegaSigma`
is the aligned grid (the ω-arguments agree pointwise along `ticWEquivSdiffW = e`).  This
discharges the `h48` thread of the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_zeroRow_diff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime)
    {j k : Fin hyp.w2} (hj : j ≠ 0) (hk : k ≠ 0) :
    hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k) := by
  have := hyp.finiteG
  classical
  by_cases hjk : j = k
  · subst hjk
    simp
  -- §6 host context (the standard `muGrid`/`alignedOmegaSigmaGrid` let-context)
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set χ₂' := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm k) with hχ₂'def
  set i0 : Fin (Nat.card h.W1) := finCongr hcardW1.symm (0 : Fin hyp.w1) with hi0def
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  have : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- column-character facts
  have hcol_ne : ∀ (l : Fin hyp.w2), l ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm l) ≠ 1 := by
    intro l hl heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hl0 : finCongr hcardW2sub.symm l = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hl
    have hval : (l : ℕ) = 0 := by simpa using congrArg Fin.val hl0
    exact Fin.ext hval
  have hχ₂ne1 : χ₂ ≠ 1 := hcol_ne j hj
  have hχ₂'ne1 : χ₂' ≠ 1 := hcol_ne k hk
  have hχne : χ₂ ≠ χ₂' := by
    intro heq
    apply hjk
    rw [hχ₂def, hχ₂'def] at heq
    have := (finCardEquivCharacterGroup _).injective heq
    have hval : (j : ℕ) = (k : ℕ) := by simpa using congrArg Fin.val this
    exact Fin.ext hval
  -- `muGrid` unfolds (definitional, the `unfold … rfl` idiom)
  have emj : hyp.muGrid hG hodd 0 j = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  have emk : hyp.muGrid hG hodd 0 k = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
    unfold Hypothesis.muGrid
    rfl
  -- equal degree: the (10.3) cross-column constancy
  have hdeg : ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ) 1
      = ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) 1 := by
    rw [← emj, ← emk]
    exact hyp.muGrid_apply_one_eq hG hodd hw2 0 0 hj hk
  -- σ-bridge: `certainTypeOmegaSigma (toHypothesis46) = alignedOmegaSigmaGrid`
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    change (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    change (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- `hyp.tau` on the (4.8) supported difference is the certain-type Dade map
  have hsupp : (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46.toCore hχ₂ne1 hχ₂'ne1 i0 hdeg).2
  have happly : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
      = h46.tau.toDadeMap
          (OddOrder.Peterfalvi.S06.certainTypeDiffSupported h46.toCore hχ₂ne1 hχ₂'ne1 i0
            hdeg) := by
    have h1 : hyp.tau (hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k)
        = h46.dade0.dadeMap (k := ℂ)
            ⟨hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k,
              ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    have hval : hyp.muGrid hG hodd 0 j - hyp.muGrid hG hodd 0 k
        = ((h.columnFamily χ₂).mu i0 : ClassFunction ↥M ℂ)
          - ((h.columnFamily χ₂').mu i0 : ClassFunction ↥M ℂ) := by
      rw [emj, emk]
    exact congrArg _ (Subtype.ext hval)
  -- assemble: (4.8) + σ-bridge + sign reconciliation
  have esign : hyp.muColumnSign hG hodd j = (h46.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  rw [happly]
  refine (OddOrder.Peterfalvi.S06.certainType_diff_dade_eq h46 hχne hχ₂ne1 hχ₂'ne1 i0 hdeg).trans ?_
  rw [hbridge χ₂ i0 0 j hχ₂def hi0def, hbridge χ₂' i0 0 k hχ₂'def hi0def,
    ← Int.cast_smul_eq_zsmul ℂ]
  exact congrArg (fun s : ℤ => (s : ℂ) •
    (hyp.alignedOmegaSigmaGrid hG hodd 0 j - hyp.alignedOmegaSigmaGrid hG hodd 0 k)) esign.symm

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (4.10) on the §10 aligned grid** (coherence-free, `δ_j`-scaled): the four-corner
Dade identity `(μ_{ij} − μ_{0j} − δ_j μ_{i0} + δ_j μ_{00})^τ = δ_j·(ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ
+ ω_{00}^σ)`.

This is the §6 `fourCorner_dade_eq` cited through the (8.15) instantiation `toHypothesis46`
(same bridging as `tau_muGrid_zeroRow_diff`), with the book's `δ_j(μ_{ij} − μ_{0j}) − (μ_{i0} −
μ_{00})` form rescaled by `δ_j` (`δ_j² = 1`, `muColumnSign_eq_one_or_neg_one`) and the trivial
column-`0` sign `δ_0 = 1` (`muColumnSign_zero`) absorbed.  This discharges the `h410` thread of
the (11.8.3)/(11.8.5) β-reality argument (issue 9004). -/
theorem Hypothesis.tau_muGrid_fourCorner [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.tau (hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
        - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
        + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0)
      = (hyp.muColumnSign hG hodd j : ℂ) •
          (hyp.alignedOmegaSigmaGrid hG hodd i j - hyp.alignedOmegaSigmaGrid hG hodd 0 j
            - hyp.alignedOmegaSigmaGrid hG hodd i 0 + hyp.alignedOmegaSigmaGrid hG hodd 0 0) := by
  have := hyp.finiteG
  classical
  -- §6 host context
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ := finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
    (finCongr hcardW2sub.symm j) with hχ₂def
  set i' : Fin (Nat.card h.W1) := finCongr hcardW1.symm i with hi'def
  have hi00 : (0 : Fin (Nat.card h.W1)) = finCongr hcardW1.symm (0 : Fin hyp.w1) := by
    apply Fin.ext; simp
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  -- §5 tic context
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  set h46 := hyp.toHypothesis46 hG hodd with hh46
  have : NeZero (Nat.card ↥h46.W1) := hNeZ1
  -- signs: `δ_j` matches the §6 column sign, and the trivial column has sign `1`
  have esign : hyp.muColumnSign hG hodd j = (h.columnFamily χ₂).sign := by
    unfold Hypothesis.muColumnSign
    rfl
  have hδ1 : (h.columnFamily
      (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).sign = 1 := by
    have e0 : hyp.muColumnSign hG hodd 0 = (h.columnFamily
        (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
      unfold Hypothesis.muColumnSign
      rfl
    rw [hyp.muColumnSign_zero hG hodd, hdual0] at e0
    exact e0.symm
  -- σ-bridge (as in `tau_muGrid_zeroRow_diff`)
  have hpt : ∀ g : ↥tic.W, OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g = e g := by
    intro g
    apply Subtype.ext
    apply Subtype.ext
    rw [OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW]
    change (g : G) = ((MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm
        ((Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm g) : ↥M) : G)
    rw [MulEquiv.subgroupCongr_apply]
    rfl
  have hbridge : ∀ (χc : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)
      (ic : Fin (Nat.card h.W1)) (ii : Fin hyp.w1) (jj : Fin hyp.w2),
      χc = finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm jj) →
      ic = finCongr hcardW1.symm ii →
      OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χc ic
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj := by
    rintro χc ic ii jj rfl rfl
    have harg : ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46
            (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
              (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii))
            : ClassFunction (OddOrder.Peterfalvi.S06.ticVdiff h46).W ℂ)
        = ClassFunction.compHom e.toMonoidHom
            ((h.chiColumn (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
                (finCongr hcardW2sub.symm jj)) (finCongr hcardW1.symm ii)
              : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)) := by
      ext g
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.omega_apply,
        ClassFunction.compHom_apply,
        show e.toMonoidHom g = OddOrder.Peterfalvi.S06.ticWEquivSdiffW h46 g from (hpt g).symm]
      exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply h46 _ _ g
    change (OddOrder.Peterfalvi.S06.ticVdiff h46).sigma rfl
        (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication h46)
        ((OddOrder.Peterfalvi.S06.ticVdiff h46).omega
          (OddOrder.Peterfalvi.S06.omegaProdCharTic h46 _ (finCongr hcardW1.symm ii)))
      = hyp.alignedOmegaSigmaGrid hG hodd ii jj
    rw [harg]
    unfold Hypothesis.alignedOmegaSigmaGrid
    rfl
  -- the (4.10) four-corner carrier and its `A₀`-support
  set u : ClassFunction ↥M ℂ :=
    (h.columnFamily χ₂).signedDifference i'
      - (h.columnFamily (1 : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).signedDifference i'
    with hudef
  have hsupp : u.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (typePA M hyp.typeP ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M :=
    ClassFunction.mem_supportedSubmodule.mp
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i').2
  have happly : hyp.tau u = h46.tau.toDadeMap
      (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i') := by
    have h1 : hyp.tau u = h46.dade0.dadeMap (k := ℂ)
        ⟨u, ClassFunction.mem_supportedSubmodule.mpr hsupp⟩ :=
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support h46.dade0 h46.tau hsupp
    rw [h1, show h46.tau.toDadeMap = h46.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h46.tau.toDadeIsometryData.isDadeMap
        h46.dade0.isDadeMap_dadeMap]
    exact congrArg _ (Subtype.ext rfl)
  -- the target τ-argument is `δ_j • u` (`δ_j² = 1`, `δ_0 = 1`)
  have hXeq : hyp.muGrid hG hodd i j - hyp.muGrid hG hodd 0 j
      - (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd i 0
      + (hyp.muColumnSign hG hodd j : ℂ) • hyp.muGrid hG hodd 0 0
      = (hyp.muColumnSign hG hodd j : ℂ) • u := by
    rw [hudef,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.signedDifference_apply,
      hδ1, one_zsmul, ← esign]
    have emij : hyp.muGrid hG hodd i j
        = ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em0j : hyp.muGrid hG hodd 0 j
        = ((h.columnFamily χ₂).mu (finCongr hcardW1.symm 0) : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have emi0 : hyp.muGrid hG hodd i 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu i' : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    have em00 : hyp.muGrid hG hodd 0 0
        = ((h.columnFamily (finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
            (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).mu (finCongr hcardW1.symm 0)
          : ClassFunction ↥M ℂ) := by
      unfold Hypothesis.muGrid
      rfl
    rw [emij, em0j, emi0, em00, hdual0, ← hi00]
    simp only [OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.difference,
      OddOrder.RepresentationTheory.SignedIrreducibleDifferenceFamily.classFunction]
    rcases hyp.muColumnSign_eq_one_or_neg_one hG hodd j with hδ | hδ <;> rw [hδ] <;> push_cast <;>
      module
  rw [hXeq, Int.cast_smul_eq_zsmul ℂ, map_smul, happly]
  rw [show h46.tau.toDadeMap (OddOrder.Peterfalvi.S06.fourCornerDiffSupported h46 χ₂ i')
      = OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
        - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
        - (OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
          - OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0) from
    OddOrder.Peterfalvi.S06.fourCorner_dade_eq h46 χ₂ i']
  have hb1 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ i'
      = hyp.alignedOmegaSigmaGrid hG hodd i j := hbridge χ₂ i' i j hχ₂def hi'def
  have hb2 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 χ₂ 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 j := hbridge χ₂ 0 0 j hχ₂def hi00
  have hb3 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 i'
      = hyp.alignedOmegaSigmaGrid hG hodd i 0 := hbridge 1 i' i 0 hdual0.symm hi'def
  have hb4 : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma h46 1 0
      = hyp.alignedOmegaSigmaGrid hG hodd 0 0 := hbridge 1 0 0 0 hdual0.symm hi00
  rw [hb1, hb2, hb3, hb4, ← Int.cast_smul_eq_zsmul ℂ]
  module

open scoped FiniteInduce in
/-- **§10 Dade value on `V`** (Peterfalvi's "by definition of `τ`").  For a class function `φ` on
`M` supported on `A_0(M)`, the Dade image `φ^τ = hyp.tau φ` *restores* `φ`'s value at any
`v ∈ V = typePV M`: `(φ^τ)(v) = φ(v)`.

Since `V = typePV ⊆ V^M ⊆ A_0(M)` (`subset_conjClassSetIn`), this is exactly the
value-on-support property `dadeIntegralCharacterMap_apply_mem` of the genuine §10 Dade isometry
`hyp.tau`.  It is the reusable "agrees/vanishes on `V` by definition of `τ`" step underlying the
Dade-image half of (10.5) (`α_{ij}^τ − δ(ω_{ij}^σ − ω_{i0}^σ)` vanishes on `V`), and the (10.6.b) /
(10.9) value computations. -/
theorem Hypothesis.tau_apply_of_mem_typePV [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0)
    {v : G} (hv : v ∈ typePV M hyp.typeP) (hvM : v ∈ M) :
    hyp.tau φ v = φ ⟨v, hvM⟩ := by
  have := hyp.finiteG
  have hvA0 : v ∈ typePA0 M hyp.typeP := by
    rw [typePA0]
    exact Set.mem_union_right _ (OddOrder.GroupTheory.subset_conjClassSetIn hv)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_mem hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData) hφ hvA0

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), the Dade-image value on `V`** (the "vanishes on `V`" leg of the Dade-image
half): on the exceptional set `V = typePV`, the Dade image `α_{ij}^τ` of the virtual character
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` equals `δ·(ω_{ij}^σ − ω_{i0}^σ)`, where `ω^σ` is the *aligned*
σ-grid `alignedOmegaSigmaGrid` (the σ-image of the same ω that `μ` is built from).

This is Peterfalvi's step *"By (3.2.c), (4.3.c) and the definition of `τ`, `α_{ij}^τ − δ(ω_{ij}^σ −
ω_{i0}^σ)` vanishes on `V`"*, assembled from:
* the cornerstone `tau_apply_of_mem_typePV` — `α` is supported on `A_0(M)` (the support half,
  `muGrid_alpha_support`), so `τ` restores `α`'s value on `V`;
* the reconciliation `muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV` —
  `μ_{ij}(v) = δ_j·ω_{ij}^σ(v)` on `V`, both at `j` and at column `0`;
* `muColumnSign_zero` — `δ_0 = 1`;
* `ζ` vanishing on `V` — `ζ` is induced from the normal `M' = [M,M]` and `v ∉ M'`
  (`typePData_typePV_not_mem_derived`).

It is the reusable on-`V` identity feeding the `(10.5)`/`(10.6.b)`/`(10.9)` value computations; the
*global* Dade-image identity additionally requires the `a = 0` norm/Cauchy–Schwarz argument and the
(3.8) trichotomy. -/
theorem Hypothesis.tau_muGridAlpha_apply_eq_on_typePV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) {i : Fin hyp.w1} {j : Fin hyp.w2} (hj : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    {v : G} (hv : v ∈ typePV M hyp.typeP) :
    hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) v
      = ((δ : ℂ) • (hyp.alignedOmegaSigmaGrid hG hodd i j
          - hyp.alignedOmegaSigmaGrid hG hodd i 0)) v := by
  have := hyp.finiteG
  classical
  -- `v ∈ M` (`V ⊆ W ⊆ M`).
  have hvM : v ∈ M := typePData_W_le_self hyp.typeP (SetLike.mem_coe.mp hv.1)
  -- The (10.5) support half, so `τ` restores `α` on `V`.
  have hsupp := hyp.muGrid_alpha_support hG hodd hj hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_apply_of_mem_typePV hsupp hv hvM]
  -- `ζ` vanishes on `V`: induced from the normal `M'`, and `v ∉ M'`.
  have hζv : ζ ⟨v, hvM⟩ = 0 := by
    obtain ⟨θ, _hθne, hζeq⟩ := hζS
    have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
    have hnotmem : (⟨v, hvM⟩ : ↥M) ∉ (derivedInG M).subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      exact OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.typeP hv
    rw [hζeq]
    exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hnotmem
  -- Evaluate `α ⟨v⟩` via the reconciliation (`μ = δ_j·ω^σ`), `δ_0 = 1`, and `ζ(v) = 0`.
  rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.smul_apply,
    ClassFunction.smul_apply,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i j hv hvM,
    hyp.muGrid_apply_eq_columnSign_smul_alignedOmegaSigma_of_mem_typePV hG hodd i 0 hv hvM,
    hδj, hyp.muColumnSign_zero hG hodd, hζv,
    ClassFunction.smul_apply, ClassFunction.sub_apply]
  push_cast
  ring

open scoped FiniteInduce in
/-- **§10 Dade isometry on the support lattice** (the inner-product half of (10.5)/(10.6)): the
genuine Dade map `τ = hyp.tau` preserves the class-function inner product on functions supported in
`A_0(M)`.  This is the §7 `dadeIntegralCharacterMap_inner_eq_on_supported_span` for the (8.15) Dade
data `hyp.dadeData`, instantiated on the two-element set `{φ, ψ}` whose members are `A_0`-supported.

It is the isometry input to the (10.5) `a = 0` argument: every `(α_{ij}^τ, …)` inner product is
computed on the `M`-side via this transfer, since `α_{ij}` is `A_0`-supported by
`muGrid_alpha_support`. -/
theorem Hypothesis.tau_inner_eq_of_supported [Finite G] {M : Subgroup G}
    [Invertible (Nat.card ↥M : ℂ)] (hyp : Hypothesis M)
    {φ ψ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) (hψ : ψ.support ⊆ hyp.A0) :
    ClassFunction.inner (hyp.tau φ) (hyp.tau ψ) = ClassFunction.inner φ ψ := by
  have := hyp.finiteG
  classical
  have hS : ∀ s ∈ ({φ, ψ} : Set (ClassFunction ↥M ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hφ
    · exact hψ
  have hφ' : φ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hψ' : ψ ∈ OddOrder.Peterfalvi.S07.zSpan ({φ, ψ} : Set (ClassFunction ↥M ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dadeData.dade hS hφ' hψ'

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `‖α_{ij}^τ‖² = 2 + n²`**: the Dade image `α_{ij}^τ` has the same norm as
`α_{ij}`.  The genuine Dade map `τ` is an isometry on `A_0`-supported functions
(`tau_inner_eq_of_supported`), and `α_{ij}` is `A_0`-supported (`muGrid_alpha_support`), so
`‖α_{ij}^τ‖² = ‖α_{ij}‖² = 2 + n²` (`muGridAlpha_inner_self`).  This is the `‖α_{ij}^τ‖²` factor of
the (10.5) Cauchy–Schwarz bound `d²a² ≤ ‖α_{ij}^τ‖²‖μ_k^{τ₁}‖² = (2 + n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau_inner_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hδpm : δ = 1 ∨ δ = -1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
      = 2 + (n : ℂ) ^ 2 := by
  have := hyp.finiteG
  classical
  have hsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  rw [hyp.tau_inner_eq_of_supported hsupp hsupp]
  exact hyp.muGridAlpha_inner_self hG hodd i hj0 hζirr hdζ h0ζ hδpm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, ζ − ζ̄) = −n`** (M-side): the inner product of
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `ζ − ζ̄`.  The certain-type characters `μ_{ij}`, `μ_{i0}`
are degree-distinct from `ζ` and its conjugate `ζ̄` (both of degree `w₁ = ζ(1)`), so they are
orthogonal to both (`muGrid_inner_eq_zero_of_apply_one_ne`); `ζ ≠ ζ̄` (no real characters) gives
`(ζ, ζ̄) = 0`, while `(ζ, ζ) = 1`.  The only surviving term is `−n·(ζ, ζ) = −n`.

This is the `M`-side of the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step of the (10.5)
`a = 0` argument (`ζ − ζ̄` is `A_0`-supported, so the Dade isometry transfers it). -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - ζ.conj) = -(n : ℂ) := by
  have := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number, fixed by `star`.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijζc : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact hdζ)
  have hμi0ζc : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ.conj = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζζc : ClassFunction.inner ζ ζ.conj = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijζc, hμi0ζc, hζζ, hζζc,
    mul_zero, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.2), `(α_{ij}, ζ − η) = −n`** for any degree-`w₁` irreducible `η ∈ S(HC)`
distinct from `ζ`.  General-`η` companion of `muGridAlpha_inner_zeta_sub_conj` (the `η = ζ̄` case):
since `η` has the same degree as `ζ` (`hη1 : η(1) = ζ(1)`), both `μ_{ij}, μ_{i0}` are
degree-distinct
from — hence orthogonal to — `η` (`muGrid_inner_eq_zero_of_apply_one_ne`), and `(ζ, η) = 0`
(`η ≠ ζ`, both irreducible), so only the `−nζ` term survives:
`(α_{ij}, ζ − η) = −n(ζ, ζ) = −n` (independent of `δ`).

This is the source value that (11.8.2) lifts (via the `τ`-isometry) to `(α_{ij}^τ, (ζ − η)^τ) = −n`
for every `η ∈ S₁ = S(HC)`, `η ≠ ζ` — pinning the `ζ^{τ₁}`-coefficient of the `α_{ij}^τ` projection
onto the orthonormal `S₁^{τ₁}` (`SHC_extension_inner_*`) to `−n`. -/
theorem Hypothesis.muGridAlpha_inner_zeta_sub_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2)
    {ζ η : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hηirr : IsIrreducibleCharacter η)
    {δ : ℤ} {n : ℕ}
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hη1 : η 1 = ζ 1) (hηne : η ≠ ζ) :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (ζ - η) = -(n : ℂ) := by
  have := hyp.finiteG
  classical
  have hμijζ : ClassFunction.inner (hyp.muGrid hG hodd i j) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
  have hμi0ζ : ClassFunction.inner (hyp.muGrid hG hodd i 0) ζ = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
  have hμijη : ClassFunction.inner (hyp.muGrid hG hodd i j) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hηirr (by rw [hη1]; exact hdζ)
  have hμi0η : ClassFunction.inner (hyp.muGrid hG hodd i 0) η = 0 :=
    hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hηirr (by rw [hη1]; exact h0ζ)
  have hζζ : ClassFunction.inner ζ ζ = 1 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
  have hζη : ClassFunction.inner ζ η = 0 := by
    rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hηirr, if_neg (Ne.symm hηne)]
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, hμijζ, hμi0ζ, hμijη, hμi0η, hζζ, hζη,
    mul_zero, sub_zero, zero_sub, mul_one]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}, μ_k − dζ̄) = 0`** (M-side, `0 < k < w₂`, `k ≠ j`): the inner
product of `α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` against `μ_k − dζ̄`, where `μ_k = ∑_{0≤i'<w₁} μ_{i'k}`
is the `W₂`-column-`k` sum.  Since `k ≠ j` and `k ≠ 0`, every `μ_{i'k}` is cross-column-orthogonal
to `μ_{ij}` and `μ_{i0}` (`muGrid_inner_cross_column`), and degree-distinct from `ζ`
(`hkζ`), so `(α_{ij}, μ_k) = 0`; and `(α_{ij}, ζ̄) = 0` (degree distinctness + `(ζ, ζ̄) = 0`), so
`(α_{ij}, dζ̄) = 0`.  Hence `(α_{ij}, μ_k − dζ̄) = 0`.

This is the `M`-side of the `(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = (α_{ij}, μ_k − dζ̄) = 0` step of
the (10.5) `a = 0` argument (whence `(α_{ij}^τ, μ_k^{τ₁}) = da`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j k : Fin hyp.w2)
    (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj) = 0 := by
  have := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr (by rw [hconj1]; exact
        hdζ)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr (by rw [hconj1]; exact
        h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'k}) = 0` for each `i'`: cross-column (`k ≠ j`, `k ≠ 0`) + degree (`k`-column ≠
  -- ζ).
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' k) = 0 := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hjk
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hk0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' k) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' k) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' k hζirr (hkζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_eq_zero (fun i' _ => hrow i'),
    OddOrder.RepresentationTheory.inner_smul_right, hαζc, mul_zero, sub_zero]

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}, μ_j − dζ̄) = 1`** (M-side, `0 < j < w₂`): the diagonal
companion of `muGridAlpha_inner_muColumn_sub_conj`, where `μ_j = ∑_{0≤i'<w₁} μ_{i'j}` is the
`W₂`-column-`j` sum (the column of `μ_{ij}` itself).  Within column `j` the `μ_{i'j}` are
orthonormal (`muGrid_inner_self`/`muGrid_inner_within_column`), so `(μ_{ij}, μ_j) = 1`; `μ_{i0}` and
`ζ` are cross-column resp. degree-distinct from column `j` (`muGrid_inner_cross_column`, `hjζ`), so
`(δμ_{i0}, μ_j) = (nζ, μ_j) = 0`, giving `(α_{ij}, μ_j) = 1`; and `(α_{ij}, ζ̄) = 0` (degree
distinctness + `(ζ, ζ̄) = 0`).  Hence `(α_{ij}, μ_j − dζ̄) = 1`.

This is the `M`-side opening `1 = (α_{ij}, μ_j − dζ̄)` of Peterfalvi (10.6)(a), feeding the
`(δ(ω_{ij}^σ − ω_{i0}^σ), μ_j^{τ₁}) = 1` step (then Peterfalvi (5.8) gives the summed isometry
`μ_j^{τ₁} = δ∑_i ω_{ij}^σ`). -/
theorem Hypothesis.muGridAlpha_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζne : ζ.conj ≠ ζ)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n d : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj) = 1 := by
  have := hyp.finiteG
  classical
  have hconjirr : IsIrreducibleCharacter ζ.conj := hζirr.conj
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- `(α_{ij}, ζ̄) = 0`: `μ_{ij}, μ_{i0}` degree-distinct from `ζ̄`, and `(ζ, ζ̄) = 0`.
  have hαζc : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ.conj = 0 := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hconjirr
      (by rw [hconj1]; exact hjζ i)
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hconjirr
      (by rw [hconj1]; exact h0ζ)
    have a3 : ClassFunction.inner ζ ζ.conj = 0 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hconjirr, if_neg (Ne.symm hζne)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero]
  -- `(α_{ij}, μ_{i'j}) = δ_{i,i'}`: within-column orthonormal; `μ_{i0}, ζ` off column `j`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' j) = (if i = i' then (1 : ℂ) else 0) := by
    intro i'
    have h1 : ClassFunction.inner (hyp.muGrid hG hodd i j) (hyp.muGrid hG hodd i' j)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i j
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd j hii'
    have h2 := hyp.muGrid_inner_cross_column hG hodd i i' (Ne.symm hj0)
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' j) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' j) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' j hζirr (hjζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, sub_zero]
  rw [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right, hαζc,
    mul_zero, sub_zero, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i')]
  simp

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5) M-side inner product** `(α_{ij}, μ₀ − ζ) = n − δ`, where
`μ₀ = ∑_{i'} μ_{i'0}`
is the column-`0` sum (`0 < j`).  Within column `0` the `μ_{i'0}` are orthonormal, so only `i' = i`
survives in `(δ·μ_{i0}, μ₀)`, giving `−δ`; `μ_{ij}` (column `j ≠ 0`) is cross-column to column `0`;
`ζ` (degree `w₁ > 1`) is degree-distinct from every `μ_{i'0}` (degree `1`) and from
`μ_{ij}`/`μ_{i0}`,
and `(ζ, ζ) = 1` gives `(α_{ij}, ζ) = −n`.  Hence `(α_{ij}, μ₀ − ζ) = −δ − (−n) = n − δ`.  This is
the
`M`-side of the (11.8.5) two-way computation of `((μ₀ − ζ)^τ, α_{ij}^τ) = (μ₀ − ζ, α_{ij})` (Dade
isometry), which together with the `G`-side (via (11.8.4)) forces `a = 0`. -/
theorem Hypothesis.muGridAlpha_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζirr : IsIrreducibleCharacter ζ) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) {δ : ℤ} {n : ℕ} :
    ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ) = (n : ℂ) - (δ : ℂ) := by
  have := hyp.finiteG
  classical
  have hw1 : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hcol0ζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0 1 ≠ ζ 1 := fun i' => by
    rw [hyp.muGrid_zero_column_apply_one hG hodd i', hζ1]
    intro he; have : hyp.w1 = 1 := by exact_mod_cast he.symm
    omega
  -- `(α_{ij}, ζ) = −n`: `μ_{ij}`, `μ_{i0}` degree-distinct from `ζ`, and `(ζ, ζ) = 1`.
  have hαζ : ClassFunction.inner
      (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ) ζ = -(n : ℂ) := by
    have a1 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i j hζirr hdζ
    have a2 := hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i 0 hζirr h0ζ
    have a3 : ClassFunction.inner ζ ζ = 1 := by
      rw [OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr, if_pos rfl]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, a1, a2, a3,
      mul_zero, sub_zero, mul_one, zero_sub]
  -- `(α_{ij}, μ_{i'0}) = −δ·[i = i']`.
  have hrow : ∀ i' : Fin hyp.w1,
      ClassFunction.inner (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ)
        (hyp.muGrid hG hodd i' 0) = (if i = i' then -(δ : ℂ) else 0) := by
    intro i'
    have h1 := hyp.muGrid_inner_cross_column hG hodd i i' hj0
    have h2 : ClassFunction.inner (hyp.muGrid hG hodd i 0) (hyp.muGrid hG hodd i' 0)
        = (if i = i' then (1 : ℂ) else 0) := by
      by_cases hii' : i = i'
      · rw [if_pos hii', ← hii']; exact hyp.muGrid_inner_self hG hodd i 0
      · rw [if_neg hii']; exact hyp.muGrid_inner_within_column hG hodd 0 hii'
    have h3 : ClassFunction.inner ζ (hyp.muGrid hG hodd i' 0) = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm (hyp.muGrid hG hodd i' 0) ζ,
        hyp.muGrid_inner_eq_zero_of_apply_one_ne hG hodd i' 0 hζirr (hcol0ζ i'), star_zero]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left, h1, h2, h3,
      mul_zero, zero_sub, sub_zero]
    by_cases hii' : i = i' <;> simp [hii']
  rw [ClassFunction.inner_sub_right, hαζ, OddOrder.RepresentationTheory.inner_sum_right,
    Finset.sum_congr rfl (fun i' _ => hrow i'), Finset.sum_ite_eq, if_pos (Finset.mem_univ i)]
  ring

open scoped FiniteInduce in
/-- **§10 support of an equal-degree difference in `S`** (Peterfalvi (10.5)/(11.8)): for two members
`ζ₁, ζ₂ ∈ S = inducedFamily M` of *equal degree* (`ζ₁(1) = ζ₂(1)`), the difference `ζ₁ − ζ₂` is
supported in `A_0(M)`.  Both are induced from the normal `M' = [M,M]`, hence vanish off `M'`; and
`(ζ₁ − ζ₂)(1) = 0`, so the support lies in `M'^# = M' − {1}`.  Every element of `M'^#` centralizes
itself, hence lies in `A(M) ⊆ A_0(M)` (the left disjunct of `typePA0`, as in
`muGrid_alpha_support`).

This is the `hsuppdiff` precondition feeding the (5.7)/(1.4) equal-degree coherence producer
`coherentEqualDegree_fromDade` on the degree-`w₁` subfamily `S(HC)` (Peterfalvi (11.8)); the
conjugate-pair special case `ζ₂ = ζ̄` is `zeta_sub_conj_support`, used in the `(α_{ij}^τ, (ζ−ζ̄)^τ)`
step of the (10.5) `a = 0` argument. -/
theorem Hypothesis.inducedFamily_sub_support [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {ζ₁ ζ₂ : ClassFunction ↥M ℂ} (hζ₁ : ζ₁ ∈ inducedFamily M) (hζ₂ : ζ₂ ∈ inducedFamily M)
    (hdeg : ζ₁ 1 = ζ₂ 1) :
    (ζ₁ - ζ₂).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  obtain ⟨θ₁, _hθ₁ne, hζ₁eq⟩ := hζ₁
  obtain ⟨θ₂, _hθ₂ne, hζ₂eq⟩ := hζ₂
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζ₁vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₁ w = 0 := fun {w} hw => by
    rw [hζ₁eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hζ₂vanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ₂ w = 0 := fun {w} hw => by
    rw [hζ₂eq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `ζ₁ z = ζ₂ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, hζ₁vanish hzK, hζ₂vanish hzK, sub_zero]
  -- `z ≠ 1`: `(ζ₁ − ζ₂)(1) = 0` by equal degree.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hdeg, sub_self]
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **§10 support of `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the difference `ζ − ζ̄` of a
degree-`w₁` irreducible `ζ ∈ S` and its conjugate is supported in `A_0(M)`.  The conjugate-pair
special case of `inducedFamily_sub_support`: `ζ̄ = ζ.conj ∈ S`
(`inducedFamily_closedUnderConjugate`)
has the same degree `ζ̄(1) = ζ(1)` (the degree is a real natural number).

This makes `ζ − ζ̄` `A_0`-supported, so the Dade isometry `τ` transfers it
(`tau_inner_eq_of_supported`) in the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄)` step. -/
theorem Hypothesis.zeta_sub_conj_support [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (_hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    (ζ - ζ.conj).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  -- `ζ̄(1) = ζ(1)`: the degree is a real natural number.
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  exact hyp.inducedFamily_sub_support hζS (inducedFamily_closedUnderConjugate M hζS) hconj1.symm

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`**: the Dade-image inner product, transferred to
the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `ζ − ζ̄` (`zeta_sub_conj_support`) are
`A_0`-supported, so the Dade isometry `τ` preserves their inner product
(`tau_inner_eq_of_supported`), and the `M`-side value is `−n`
(`muGridAlpha_inner_zeta_sub_conj`).  This is the `(α_{ij}^τ, (ζ−ζ̄)^τ) = (α_{ij}, ζ−ζ̄) = −n` step
of the (10.5) `a = 0` argument. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeta_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau (ζ - ζ.conj)) = -(n : ℂ) := by
  have := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hζsupp := hyp.zeta_sub_conj_support hG hodd hζS hζirr
  rw [hyp.tau_inner_eq_of_supported hαsupp hζsupp]
  exact hyp.muGridAlpha_inner_zeta_sub_conj hG hodd i j hζirr hζne hdζ h0ζ

open scoped FiniteInduce in
/-- **§10 support of `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the column sum
`μ_k = ∑_{i} μ_{ik}` (an induced character of degree `dw₁`) minus `d` times the conjugate `ζ̄` (also
degree `w₁`) is supported in `A_0(M)`.  Both `μ_k` and `ζ̄` are induced from the normal `M'`, hence
vanish off `M'` (`muGrid_column_sum_vanishes_off_derived`, induced-from-`M'` for `ζ̄`); and the
degrees cancel, `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`, so the support lies in `M'^# ⊆ A(M) ⊆ A_0(M)`.

This is the companion of `zeta_sub_conj_support`: it makes `μ_k − dζ̄` `A_0`-supported, so the Dade
isometry `τ` transfers `(α_{ij}, μ_k − dζ̄) = (α_{ij}^τ, (μ_k − dζ̄)^τ)` with no adjunction. -/
theorem Hypothesis.muColumn_sub_conj_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (k : Fin hyp.w2)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hconj1 : ζ.conj 1 = ζ 1 := by
    obtain ⟨nn, _, hn, _⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  -- evaluation of a finite sum of class functions at a point is the sum of values.
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i k) w = ∑ i ∈ s, hyp.muGrid hG hodd i k w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  -- `z ∈ M'`: else `μ_k z = ζ̄ z = 0`.
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd k hzK, hζvanish hzK, star_zero,
      mul_zero, sub_zero]
  -- `z ≠ 1`: `(μ_k − dζ̄)(1) = dw₁ − dw₁ = 0`.
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, ClassFunction.conj_apply, hζ1,
      hsumapply 1, Finset.sum_congr rfl (fun i _ => hcol1 i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, star_natCast]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **`∑_{i'} μ_{i'0} − ζ` is `A_0`-supported** (Peterfalvi (11.8.5)).  The column-`0` sum `μ₀` and
the
degree-`w₁` irreducible `ζ` are both induced from the normal `M' = [M,M]`, so both vanish off `M'`;
and `(μ₀ − ζ)(1) = w₁·1 − w₁ = 0`, so the support lies in `M'^# ⊆ A_0`.  Companion of
`muColumn_sub_conj_support` with `k = 0`, `d = 1` and `ζ` in place of `ζ̄`, used to transport the
(11.8.5) `M`-side inner product `(α_{ij}, μ₀ − ζ)` to the Dade image via
`tau_inner_eq_of_supported`. -/
theorem Hypothesis.zeroColumnSum_sub_zeta_support [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (_hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) :
    ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) - ζ).support ⊆ hyp.A0 := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, _hθne, hζeq⟩ := hζS
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  have hζvanish : ∀ {w : ↥M}, w ∉ (derivedInG M).subgroupOf M → ζ w = 0 := fun {w} hw => by
    rw [hζeq]; exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
  have hsumapply : ∀ (w : ↥M), (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0) w
      = ∑ i : Fin hyp.w1, hyp.muGrid hG hodd i 0 w := by
    intro w
    refine Finset.univ.induction_on (motive := fun s =>
      (∑ i ∈ s, hyp.muGrid hG hodd i 0) w = ∑ i ∈ s, hyp.muGrid hG hodd i 0 w) ?_ ?_
    · simp
    · intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    apply hz
    rw [ClassFunction.sub_apply,
      hyp.muGrid_column_sum_vanishes_off_derived hG hodd 0 hzK, hζvanish hzK, sub_zero]
  have hz1 : z ≠ 1 := by
    rintro rfl
    apply hz
    rw [ClassFunction.sub_apply, hζ1, hsumapply 1,
      Finset.sum_congr rfl (fun i _ => hyp.muGrid_zero_column_apply_one hG hodd i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    ring
  have hzM' : (z : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp hzK
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', fun h0 => hz1 (Subtype.ext h0), (z : G),
    ⟨z.2, fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (11.8.5), `M`-side transferred to the Dade image**
`(α_{ij}^τ, (μ₀ − ζ)^τ) = n − δ`,
where `μ₀ = ∑_{i'} μ_{i'0}`.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ₀ − ζ`
(`zeroColumnSum_sub_zeta_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their
inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `n − δ`
(`muGridAlpha_inner_zeroColumnSum_sub_zeta`).  Under the (11.8.4) by-contradiction hypothesis
`(μ₀ − ζ)^τ = ∑ ω_{r0}^σ − ζ^{τ₁}`, this becomes `(α_{ij}^τ, ∑ ω_{r0}^σ − ζ^{τ₁}) = n − δ`, whose
`G`-side expansion (via the residual decomposition `α_{ij}^τ = δ(ω^σ diff) − nζ^{τ₁} + a∑β`) equals
`n − δ − a`, forcing `a = 0`. -/
theorem Hypothesis.muGridAlpha_tau_inner_zeroColumnSum_sub_zeta [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ) (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' 0) - ζ)) = (n : ℂ) - (δ : ℂ) := by
  have := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.zeroColumnSum_sub_zeta_support hG hodd hζS hζirr hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_zeroColumnSum_sub_zeta hG hodd i j hj0 hζirr hζ1 hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0`** (`0 < k < w₂`, `k ≠ j`): the Dade-image
inner product, transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and `μ_k − dζ̄`
(`muColumn_sub_conj_support`) are `A_0`-supported, so the Dade isometry `τ` preserves their inner
product (`tau_inner_eq_of_supported`), and the `M`-side value is `0`
(`muGridAlpha_inner_muColumn_sub_conj`).

Since `μ_k`, `ζ̄ ∈ ℤ[S]`, on the coherent side
`(μ_k − dζ̄)^τ = (μ_k − dζ̄)^{τ₁} = μ_k^{τ₁} − dζ̄^{τ₁}`
(the coherent extension agrees with `τ` on this `A_0`-supported lattice element), so this is the
`(α_{ij}^τ, μ_k^{τ₁} − dζ̄^{τ₁}) = 0` step of the (10.5) `a = 0` argument, whence
`(α_{ij}^τ, μ_k^{τ₁}) = da`.  No Dade–coherence adjunction is needed: the combination `μ_k − dζ̄`,
not `μ_k` alone, is supported. -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ))
    (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k) - (d : ℂ) • ζ.conj)) = 0 := by
  have := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_sub_conj hG hodd i j k hjk hk0 hζirr hζne hkζ hdζ h0ζ

open scoped FiniteInduce in
/-- **Peterfalvi (10.6)(a), `(α_{ij}^τ, (μ_j − dζ̄)^τ) = 1`** (diagonal, `0 < j < w₂`): the
Dade-image inner product transferred to the `M`-side.  Both `α_{ij}` (`muGrid_alpha_support`) and
the diagonal column `μ_j − dζ̄` (`muColumn_sub_conj_support`) are `A_0`-supported, so `τ` preserves
the inner product (`tau_inner_eq_of_supported`); the `M`-side value is `1` (the diagonal
`muGridAlpha_inner_muColumn_self_sub_conj`, vs `0` for the off-diagonal companion).

This is the opening `1 = (α_{ij}^τ, μ_j^{τ₁} − dζ̄^{τ₁})` of Peterfalvi (10.6)(a) (on the coherent
side `(μ_j − dζ̄)^τ = μ_j^{τ₁} − dζ̄^{τ₁}`, `tau_muColumn_sub_conj_eq_tau1`), which by Peterfalvi
(5.8) gives the summed isometry `μ_j^{τ₁} = δ∑_i ω_{ij}^σ` (the (10.6)(a) conclusion). -/
theorem Hypothesis.muGridAlpha_tau_inner_muColumn_self_sub_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} [Invertible (Nat.card ↥M : ℂ)]
    (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hjζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j 1 = (d : ℂ)) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' j) - (d : ℂ) • ζ.conj)) = 1 := by
  have := hyp.finiteG
  classical
  have hαsupp := hyp.muGrid_alpha_support hG hodd hj0 hζS hdeg hμ0 hζ1 hnf hδj
  have hμsupp := hyp.muColumn_sub_conj_support hG hodd j hζS hζirr hcol1 hζ1
  rw [hyp.tau_inner_eq_of_supported hαsupp hμsupp]
  exact hyp.muGridAlpha_inner_muColumn_self_sub_conj hG hodd i j hj0 hζirr hζne hjζ h0ζ

/-- **§10 τ/τ₁ compatibility on `ζ − ζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(ζ − ζ̄)^τ` equals `ζ^{τ₁} − ζ̄^{τ₁}` for the coherent extension `τ₁`.  Since `ζ ∈ S` and
`ζ̄ ∈ S` (`inducedFamily_closedUnderConjugate`), the difference `ζ − ζ̄` lies in the supported
lattice `ℤ[S, A_0]` (`zeta_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); linearity of `τ₁` (`map_sub`) then splits the image.

This converts the pure-`τ` identity `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n`
(`muGridAlpha_tau_inner_zeta_sub_conj`) into the `τ₁` form, giving `(α_{ij}^τ, ζ̄^{τ₁}) = a`
(with `a − n := (α_{ij}^τ, ζ^{τ₁})`) in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_zeta_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ) :
    hyp.tau (ζ - ζ.conj) = coh.tau1 ζ - coh.tau1 ζ.conj := by
  have hspanζ : ζ ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hζS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hmem : (ζ - ζ.conj) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanζ hspanζc, hyp.zeta_sub_conj_support hG hodd hζS hζirr⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  rfl

open scoped FiniteInduce in
/-- **§10 τ/τ₁ compatibility on `μ_k − dζ̄`** (Peterfalvi (10.5), `a = 0` argument): the Dade image
`(μ_k − dζ̄)^τ` equals `μ_k^{τ₁} − dζ̄^{τ₁}` for the coherent extension `τ₁`.  Since
`μ_k = ∑_i μ_{ik} ∈ S` (`muGrid_column_sum_mem_inducedFamily`) and `ζ̄ ∈ S`
(`inducedFamily_closedUnderConjugate`), the combination `μ_k − dζ̄` lies in the supported lattice
`ℤ[S, A_0]` (`muColumn_sub_conj_support`), where `τ₁` agrees with `τ`
(`coherent.extends_on_supported`); `τ₁`-linearity (`map_sub`, `map_nsmul`) then splits the image.

This converts `(α_{ij}^τ, (μ_k − dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) into the
`τ₁` form, giving `(α_{ij}^τ, μ_k^{τ₁}) = da` in the (10.5) `a = 0` argument. -/
theorem Hypothesis.tau_muColumn_sub_conj_eq_tau1 [Finite G] [Fintype G] {M : Subgroup G}
    [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (k : Fin hyp.w2) {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    {d : ℕ} (hcol1 : ∀ i, hyp.muGrid hG hodd i k 1 = (d : ℂ)) (hζ1 : ζ 1 = (hyp.w1 : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      = coh.tau1 (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • coh.tau1 ζ.conj := by
  have hμkS := hyp.muGrid_column_sum_mem_inducedFamily hG hodd k hdk1
  have hspanμ : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k)
      ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := Submodule.subset_span hμkS
  have hspanζc : ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span (inducedFamily_closedUnderConjugate M hζS)
  have hsmulmem : (d : ℂ) • ζ.conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hspanζc d
  have hmem : ((∑ i : Fin hyp.w1, hyp.muGrid hG hodd i k) - (d : ℂ) • ζ.conj)
      ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Sset hyp.A0 :=
    ⟨Submodule.sub_mem _ hspanμ hsmulmem,
      hyp.muColumn_sub_conj_support hG hodd k hζS hζirr hcol1 hζ1⟩
  rw [← coh.coherent.extends_on_supported _ hmem, map_sub]
  congr 1
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, Nat.cast_smul_eq_nsmul]
  rfl

/-- **The (10.5) `a = 0` numeric core.**  If `a ∈ ℤ` satisfies the Cauchy–Schwarz bound
`(d·a)² ≤ (2+n²)w₁` with `d = nw₁ + δ`, `δ = ±1`, `w₁ ≥ 3` (odd, since `|G|` is odd) and `n ≥ 2`
(even and positive), then `a = 0`.  Else `a² ≥ 1` gives `d² ≤ (2+n²)w₁`, but `d² = (nw₁+δ)² >
(2+n²)w₁` for `w₁ ≥ 3, n ≥ 2` — a contradiction (Peterfalvi: "`n < 2`, contradicting `n` even,
`n > 0`"). -/
theorem cauchySchwarz_numeric {d n w₁ : ℕ} {δ a : ℤ}
    (hd : (d : ℤ) = (n : ℤ) * (w₁ : ℤ) + δ) (hδ : δ = 1 ∨ δ = -1) (hw1 : 3 ≤ w₁) (hn2 : 2 ≤ n)
    (hbound : ((d : ℝ) * (a : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ)) : a = 0 := by
  by_contra ha
  have ha1 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ a ^ 2 := by
      rcases lt_or_gt_of_ne ha with h | h <;> nlinarith [sq_nonneg a]
    exact_mod_cast this
  have hdpos : (0 : ℝ) ≤ (d : ℝ) ^ 2 := sq_nonneg _
  have hd2 : ((d : ℝ)) ^ 2 ≤ (2 + (n : ℝ) ^ 2) * (w₁ : ℝ) := by nlinarith [hbound, ha1, hdpos]
  have hdR : (d : ℝ) = (n : ℝ) * (w₁ : ℝ) + (δ : ℝ) := by exact_mod_cast hd
  have hw1R : (3 : ℝ) ≤ (w₁ : ℝ) := by exact_mod_cast hw1
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hδR : (δ : ℝ) = 1 ∨ (δ : ℝ) = -1 := by rcases hδ with h | h <;> [left; right] <;>
      exact_mod_cast h
  rw [hdR] at hd2
  rcases hδR with hδ1 | hδ1 <;> rw [hδ1] at hd2 <;>
    nlinarith [hd2, hw1R, hn2R, mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤
        (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ) - 2) (by linarith : (0:ℝ) ≤ (n:ℝ) - 2),
      mul_nonneg (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3) (by linarith : (0:ℝ) ≤ (w₁:ℝ) - 3)]

/-- **Cauchy–Schwarz for the class-function inner product** (real-part form): for class functions
`φ, ψ` of any finite group `H`, `⟨φ, ψ⟩.re² ≤ ⟨φ, φ⟩.re · ⟨ψ, ψ⟩.re`.

Proof by the discriminant: the real quadratic `t ↦ ⟨φ − tψ, φ − tψ⟩.re = ⟨ψ,ψ⟩.re·t² −
2⟨φ,ψ⟩.re·t + ⟨φ,φ⟩.re` is `≥ 0` for every real `t` (positive semidefiniteness,
`inner_self_re_nonneg`), so its discriminant is `≤ 0` (`discrim_le_zero`).  This is the
`(α_{ij}^τ, μ_k^{τ₁})² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖²` of the (10.5) `a = 0` argument. -/
theorem classFunction_inner_re_sq_le {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (φ ψ : ClassFunction H ℂ) :
    (ClassFunction.inner φ ψ).re ^ 2
      ≤ (ClassFunction.inner φ φ).re * (ClassFunction.inner ψ ψ).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (ClassFunction.inner ψ ψ).re * (t * t)
      + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
    intro t
    have key : ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)
        = ClassFunction.inner φ φ - (t : ℂ) * ClassFunction.inner φ ψ
          - (t : ℂ) * ClassFunction.inner ψ φ + (t : ℂ) * (t : ℂ) * ClassFunction.inner ψ ψ := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
        Complex.star_def, Complex.conj_ofReal]
      ring
    have hre : (ClassFunction.inner (φ - (t : ℂ) • ψ) (φ - (t : ℂ) • ψ)).re
        = (ClassFunction.inner ψ ψ).re * (t * t)
          + (-2 * (ClassFunction.inner φ ψ).re) * t + (ClassFunction.inner φ φ).re := by
      rw [key, OddOrder.RepresentationTheory.inner_conj_symm φ ψ]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
        zero_mul, mul_zero, sub_zero, add_zero]
      ring
    rw [← hre]
    exact inner_self_re_nonneg _
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [hd]

open scoped FiniteInduce in
/-- **Peterfalvi (10.5), `(α_{ij}^τ, μ_k^{τ₁}) = da`** (`0 < k < w₂`, `k ≠ j`): the key inner
product of the (10.5) `a = 0` argument, where `a := (α_{ij}^τ, ζ^{τ₁}) + n`.

From the two pure-`τ` Dade-image identities and their `τ₁` forms:
* `(α_{ij}^τ, (ζ−ζ̄)^τ) = −n` (`muGridAlpha_tau_inner_zeta_sub_conj`) with
`(ζ−ζ̄)^τ = ζ^{τ₁}−ζ̄^{τ₁}`
  (`tau_zeta_sub_conj_eq_tau1`) gives `(α_{ij}^τ, ζ̄^{τ₁}) = (α_{ij}^τ, ζ^{τ₁}) + n = a`;
* `(α_{ij}^τ, (μ_k−dζ̄)^τ) = 0` (`muGridAlpha_tau_inner_muColumn_sub_conj`) with
  `(μ_k−dζ̄)^τ = μ_k^{τ₁}−dζ̄^{τ₁}` (`tau_muColumn_sub_conj_eq_tau1`) gives
  `(α_{ij}^τ, μ_k^{τ₁}) = d·(α_{ij}^τ, ζ̄^{τ₁}) = d·a`.

This `d·a` is the `(α_{ij}^τ, μ_k^{τ₁})` term of the Cauchy–Schwarz bound
`d²a² ≤ ‖α_{ij}^τ‖²·‖μ_k^{τ₁}‖² = (2+n²)w₁`. -/
theorem Hypothesis.muGridAlpha_tau1_inner_muColumn [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    (i : Fin hyp.w1) {j : Fin hyp.w2} (hj0 : j ≠ 0) (k : Fin hyp.w2) (hjk : j ≠ k) (hk0 : k ≠ 0)
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ inducedFamily M) (hζirr : IsIrreducibleCharacter ζ)
    (hζne : ζ.conj ≠ ζ) {d : ℕ} {δ : ℤ} {n : ℕ}
    (hdeg : hyp.muGrid hG hodd i j 1 = (d : ℂ)) (hμ0 : hyp.muGrid hG hodd i 0 1 = 1)
    (hζ1 : ζ 1 = (hyp.w1 : ℂ)) (hnf : (n : ℤ) * (hyp.w1 : ℤ) = (d : ℤ) - δ)
    (hδj : hyp.muColumnSign hG hodd j = δ)
    (hdζ : hyp.muGrid hG hodd i j 1 ≠ ζ 1) (h0ζ : hyp.muGrid hG hodd i 0 1 ≠ ζ 1)
    (hkζ : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 ≠ ζ 1)
    (hcol1 : ∀ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k 1 = (d : ℂ))
    (hdk1 : hyp.muGrid hG hodd 0 k 1 ≠ 1) :
    ClassFunction.inner
        (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
        (coh.tau1 (∑ i' : Fin hyp.w1, hyp.muGrid hG hodd i' k))
      = (d : ℂ) * (ClassFunction.inner
          (hyp.tau (hyp.muGrid hG hodd i j - (δ : ℂ) • hyp.muGrid hG hodd i 0 - (n : ℂ) • ζ))
          (coh.tau1 ζ) + (n : ℂ)) := by
  -- `(α^τ, ζ̄^{τ₁}) = (α^τ, ζ^{τ₁}) + n` from the `ζ − ζ̄` identity.
  have h12 := hyp.muGridAlpha_tau_inner_zeta_sub_conj hG hodd i hj0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ
  rw [hyp.tau_zeta_sub_conj_eq_tau1 hG hodd coh hζS hζirr,
    ClassFunction.inner_sub_right] at h12
  -- `(α^τ, μ_k^{τ₁}) = d·(α^τ, ζ̄^{τ₁})` from the `μ_k − dζ̄` identity.
  have h45 := hyp.muGridAlpha_tau_inner_muColumn_sub_conj hG hodd i hj0 k hjk hk0 hζS hζirr hζne
    hdeg hμ0 hζ1 hnf hδj hdζ h0ζ hkζ hcol1
  rw [hyp.tau_muColumn_sub_conj_eq_tau1 hG hodd k coh hζS hζirr hcol1 hζ1 hdk1,
    ClassFunction.inner_sub_right,
    OddOrder.RepresentationTheory.inner_smul_right, star_natCast] at h45
  linear_combination h45 - (d : ℂ) * h12

end OddOrder.Peterfalvi.S12



-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_MuGridConstruction
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_MuGridConstruction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:20:20.353089+00:00
-- url     : https://prove2.me/theorems/0f8b0798-f3e8-44a2-8983-b5623c34a4cf
-- title:
--   Peterfalvi (10.2)–(10.4): the $\mu$-grid and its construction
-- statement:
--   Formalizes the construction side of Peterfalvi (10.2)–(10.4): the $\mu$, $\omega^\sigma$ and aligned $\omega^\sigma$ grids, the degrees and signs of the column family, and the degree identity.
--
--   Main declarations: `finCardEquivCharacterGroup` (Pontryagin reindex); `Hypothesis.muGrid` (§10 μ-grid materialization); `Hypothesis.alignedOmegaSigmaGrid` (§10 aligned ω^σ-grid); `Hypothesis.canonicalFullDadeApp` (The canonical `(3.2)` Dade application of the type-`P` `TICyclicHypothesis`).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/MuGridConstruction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/MuGridConstruction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Pontryagin reindex** (the §5/§6 "`W₂`-dual ↔ `Fin w₂`" bridge): for a finite abelian group
`C`, the index set `Fin |C|` is equivalent to the character group `C →* ℂˣ`.  Since `ℂ` is
algebraically closed it has enough roots of unity, so `C ≃* (C →* ℂˣ)`
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`); composing with `C ≃ Fin |C|` reindexes
the character group by `Fin |C|`.  This is what lets the §6 `columnFamily` (indexed by `W₂`-duals)
populate the `Fin w₂`-indexed `μ`-grid of `CharacterParameters`.

The bijection is normalized to send `0` to the trivial character `1`
(`finCardEquivCharacterGroup_zero`, by composing with the transposition `(0 ↔ e⁻¹ 1)`), matching
Peterfalvi's convention that column `0` is the trivial column (`δ_0 = 1`, `μ_{00} = 1`, by (4.4))
and `0 < j < w₂` are the nontrivial columns of common degree `d` (10.3). -/
noncomputable def finCardEquivCharacterGroup (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
  let e : Fin (Nat.card C) ≃ (C →* ℂˣ) :=
    (Finite.equivFin C).symm.trans
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity C ℂ).some.toEquiv.symm
  (Equiv.swap (0 : Fin (Nat.card C)) (e.symm 1)).trans e

/-- The normalized Pontryagin reindex sends `0` to the trivial character (Peterfalvi's column-`0`
convention). -/
theorem finCardEquivCharacterGroup_zero (C : Type*) [CommGroup C] [Finite C]
    [NeZero (Nat.card C)] : finCardEquivCharacterGroup C 0 = 1 := by
  simp only [finCardEquivCharacterGroup, Equiv.trans_apply, Equiv.swap_apply_left,
    Equiv.apply_symm_apply]

instance instNeZeroW1 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w1 := by
  have := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

instance instNeZeroW2 {M : Subgroup G} (hyp : Hypothesis M) : NeZero hyp.w2 := by
  have := hyp.finiteG
  exact ⟨Nat.card_pos.ne'⟩

open scoped FiniteInduce in
/-- **§10 μ-grid materialization** (Peterfalvi (10.1)/(4.3.b)): the `Fin w₁ × Fin w₂`-indexed family
of induced characters `μ_{ij}` of `M`, read off from the §6 `columnFamily` of the (now
unconditional) §10→§6 bridge `Hypothesis.toCertainTypeHypothesis`, reindexed by
`finCardEquivCharacterGroup` (the `W₂`-dual ↔ `Fin w₂` Pontryagin bijection) on the column index and
by the order identity `|W₁| = w₁` on the row index.  This is the genuine source for
`CharacterParameters.mu`. -/
noncomputable def Hypothesis.muGrid [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    Fin hyp.w1 → Fin hyp.w2 → ClassFunction ↥M ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  exact ((h.columnFamily χ₂).mu (finCongr hcardW1.symm i) : ClassFunction ↥M ℂ)

open scoped FiniteInduce in
/-- **§10 aligned ω^σ-grid** (producer-local alignment fix for (10.5)): the §5 `σ`-image of the
*same* ω that `muGrid` is built from — `h.chiColumn χ₂ i` (`χ₂ = finCardEquivCharacterGroup j`,
`i` via `w1CharEquiv`) — transported from the §6 `↥M`-level `W = W₁ ⊔ W₂` to the §10 `G`-level
`tic.W = data.W` along the `W ≤ M ≤ G` isomorphism `e` (`subgroupOfEquivOfLe` ∘ `subgroupCongr` of
`typePData_sup_subgroupOf_eq`).

Unlike `omegaSigmaGrid` (which reindexes via the *independent* §5 `charEquiv`), this grid shares
`muGrid`'s indexing by construction, so on `V` it satisfies `alignedOmegaSigma_{ij}(v) =
chiColumn(v)` — matching `(μ_{ij} − δ·μ_{i0})(v) = δ·(chiColumn_{ij} − chiColumn_{i0})(v)` ((4.3.c))
needed by the (10.5) Dade-image identity.  This is the genuine `CharacterParameters.omegaSigma`. -/
noncomputable def Hypothesis.alignedOmegaSigmaGrid [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) : Fin hyp.w1 → Fin hyp.w2 → ClassFunction G ℂ := by
  haveI := hyp.finiteG
  classical
  intro i j
  -- §6 host (the source of `muGrid`'s ω `chiColumn`) — mirror `muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  -- §5 `G`-level TI-cyclic hypothesis (for `σ`) — mirror `omegaSigmaGrid`.
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  haveI : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  haveI : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let app : OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication tic :=
    ⟨tic.toDadeHypothesis.fullDadeIsometryData⟩
  -- the `W ≤ M ≤ G` isomorphism `↥tic.W ≃* ↥(h.W₁ ⊔ h.W₂)`.
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- `σ` of the transported `chiColumn` (= `muGrid`'s own ω).
  exact tic.sigmaIntegral rfl app
    (ClassFunction.compHom e.toMonoidHom
      (h.chiColumn χ₂ (finCongr hcardW1.symm i) : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))

open scoped FiniteInduce in
/-- The canonical `(3.2)` Dade application of the type-`P` `TICyclicHypothesis`: the source of the
`σ`-grids (`omegaSigmaGrid`, `alignedOmegaSigmaGrid`).  The TI-cyclic Dade hypothesis has trivial
local subgroups (`HConjInvariant.of_forall_H_eq_bot`), so `Hypothesis.fullDadeIsometryData` applies.
Definitionally equal to the `app` reconstructed inline in the grids, so any `σ`-machinery lemma
(`chiFam`, `sigma`, `sigmaCoeff`) stated with this `app` aligns with the grids by `rfl`. -/
noncomputable def Hypothesis.canonicalFullDadeApp [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.FullDadeApplication
      (typePData_toTICyclicHypothesis hyp.typeP hodd) :=
  ⟨(typePData_toTICyclicHypothesis hyp.typeP hodd).toDadeHypothesis.fullDadeIsometryData⟩

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (10.5), aligned ω^σ-grid is a `χ`-family member** (the §10 analogue of the §6
`certainTypeOmegaSigma_eq_chiFam`): `alignedOmegaSigmaGrid i j` is the `σ`-image of the irreducible
(linear) character `η = compHom e (chiColumn χ₂ i)` of `tic.W` — `chiColumn` is `ω(omegaProdChar …)`
hence a `linearIrreducibleCharacter`, and `compHom` of a linear character is again linear
(`compHom_linearIrreducibleCharacter`).  By `sigma_irreducibleCharacter` it is the orthonormal
family
vector `χ_P` at the index `P = omegaIrrEquiv.symm η`.  This is what lets the (10.5) Dade-image
trichotomy reuse the §6 `(4.8)` endgame (`sigmaCoeff_psi_eq`, `grid_trichotomy`). -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_chiFam_family [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) :
    ∃ P : Fin hyp.w2 →
        (((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ) ×
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ),
      Function.Injective P ∧
        ∀ j, hyp.alignedOmegaSigmaGrid hG hodd i j
          = (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
              (hyp.canonicalFullDadeApp hG hodd) (P j) := by
  have := hyp.finiteG
  classical
  -- reconstruct the lets of `alignedOmegaSigmaGrid`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the transported `chiColumn` is the linear (irreducible) character `η j` of `tic.W`.
  let η : Fin hyp.w2 → IrreducibleCharacter ↥tic.W := fun j =>
    linearIrreducibleCharacter
      ((h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i))
        (χ₂ j)).comp
        e.toMonoidHom)
  refine ⟨fun j => tic.omegaIrrEquiv.symm (η j), ?_, ?_⟩
  · -- injectivity: peel off the injective maps `omegaIrrEquiv.symm`, `linearIrreducibleCharacter`,
    -- precompose-`e`, `omegaProdChar(·, ·)`, `finCardEquivCharacterGroup`, `finCongr`.
    intro j j' hjj'
    have h1 : η j = η j' := tic.omegaIrrEquiv.symm.injective hjj'
    have h2 := linearIrreducibleCharacter_injective h1
    have h3 := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp h2
    have h4 := (h.sdiffTICyclicHypothesis.omegaProdChar_inj h3).2
    exact (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective h4)
  · -- value: `alignedOmegaSigmaGrid i j = σ(η j) = χ_{omegaIrrEquiv.symm (η j)}`.
    intro j
    have step1 : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
          = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η j : ClassFunction ↥tic.W ℂ)
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
    rw [step1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_irreducibleCharacter]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **§10 σ-grid orthonormality** (the (3.2) isometry on the aligned `ω^σ`-grid): the `G`-level
σ-images `alignedOmegaSigmaGrid i j` form an **orthonormal** family indexed by `Fin w₁ × Fin w₂`,
`⟨ω_{ij}^σ, ω_{i'j'}^σ⟩ = [i = i' ∧ j = j']`.

Each `ω_{ij}^σ = σ(η_{ij})` is the σ-image of the irreducible (linear) character
`η_{ij} = (omegaProdChar (w1CharEquiv i) (χ₂ j)).comp e` of `tic.W`; `σ` is an isometry on
irreducibles (`sigma_inner_irreducibleCharacter`), and the index map `(i, j) ↦ η_{ij}` is **jointly
injective** (`linearIrreducibleCharacter`/`e`-precompose/`omegaProdChar_inj`/`w1CharEquiv`/`χ₂` all
injective), so the Gram matrix is the identity.  This is the `orthonormal` field of the column
`OrthonormalCharacterImageFamily` (issue 1009): it makes the `2w₁` signed σ-images
`{δ·ω_{ij}^σ} ∪ {−δ·ω_{ij'}^σ}` orthonormal (same-column rows `i ≠ i'` and cross-column
`j ≠ j'`). -/
theorem Hypothesis.alignedOmegaSigmaGrid_inner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i i' : Fin hyp.w1) (j j' : Fin hyp.w2) :
    ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hodd i j)
        (hyp.alignedOmegaSigmaGrid hG hodd i' j')
      = (if i = i' ∧ j = j' then 1 else 0) := by
  have := hyp.finiteG
  classical
  -- reconstruct the context of `alignedOmegaSigmaGrid` /
  -- `exists_alignedOmegaSigmaGrid_chiFam_family`
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥(h.W1 ⊔ h.W2) :=
    (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self hyp.typeP)).symm.trans
      (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq hyp.typeP).symm)
  -- the linear (irreducible) source character `η_{ij}` of `tic.W`
  let η : Fin hyp.w1 → Fin hyp.w2 → IrreducibleCharacter ↥tic.W := fun i j =>
    linearIrreducibleCharacter
      ((h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv (finCongr hcardW1.symm i))
        (χ₂ j)).comp e.toMonoidHom)
  -- `alignedOmegaSigmaGrid i j = σ(η_{ij})` (mirrors `exists_alignedOmegaSigmaGrid_chiFam_family`).
  have step1 : ∀ a b, hyp.alignedOmegaSigmaGrid hG hodd a b
      = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ) := by
    intro a b
    change tic.sigmaIntegral rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ)
        = tic.sigma rfl (hyp.canonicalFullDadeApp hG hodd) (η a b : ClassFunction ↥tic.W ℂ)
    rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
  -- `(i, j) ↦ η_{ij}` is jointly injective.
  have hηinj : ∀ a b a' b', η a b = η a' b' → a = a' ∧ b = b' := by
    intro a b a' b' he
    have h2 := linearIrreducibleCharacter_injective he
    have h3 := (MonoidHom.cancel_right (MulEquiv.surjective e)).mp h2
    have h4 := h.sdiffTICyclicHypothesis.omegaProdChar_inj h3
    refine ⟨(finCongr hcardW1.symm).injective (h.w1CharEquiv.injective h4.1), ?_⟩
    exact (finCongr hcardW2sub.symm).injective ((finCardEquivCharacterGroup _).injective h4.2)
  -- compute the Gram entry through the σ-isometry.
  rw [step1, step1, OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigma_inner_irreducibleCharacter,
    irreducibleCharacter_inner_eq_ite]
  by_cases hij : i = i' ∧ j = j'
  · rw [if_pos hij, if_pos (by rw [hij.1, hij.2])]
  · rw [if_neg hij, if_neg fun he => hij (hηinj i j i' j' he)]

open scoped FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **§10 σ-grid product structure** (Peterfalvi (10.6) column-structure linchpin): the `G`-level
σ-images factor through a *product* index, `ω_{ij}^σ = χ_{(ρ i, κ j)}`, for an injective `W₁`-row
family `ρ` and an injective `W₂`-column family `κ`.  Crucially the `W₂`-index `κ j` depends only on
the column `j` (not on the row `i`), and the `W₁`-indices `ρ i` exhaust `Ŵ₁` as `i` ranges — this is
what makes `μ_j^{τ₁}`'s σ-coefficient grid *two-column* supported (columns `κ j`, `κ j'`) and lets
the
(5.8) full-column endgame translate `∑_p χ_{(p, κ j)} = ∑_i ω_{ij}^σ`.

`ω_{ij}^σ = σ(ω(ξ_{ij})) = χ_{omegaProdEquiv.symm ξ_{ij}}` (`sigma_omega`) for the transported
product
character `ξ_{ij} = ω^{sdiff}_{χ₁ i, χ₂ j} ∘ e`.  By `omegaProdEquiv_symm_eq` the index pair is
`(ξ_{ij}|_{W₁}, ξ_{ij}|_{W₂})`, and because `e` respects the `W₁/W₂` decomposition
(`typePData_WEquiv_mem_W1/W2`: on the `W₁`-block the `ω_{0j}` factor `χ₂ ∘ wSnd ∘ e` is trivial, and
on the `W₂`-block the `ω_{i0}` factor `χ₁ ∘ wFst ∘ e` is trivial) these restrictions are the
single-factor characters `ρ i = χ₁ i ∘ wFst ∘ e`, `κ j = χ₂ j ∘ wSnd ∘ e`.  Injectivity of `ρ`/`κ`
follows from the joint orthonormality `alignedOmegaSigmaGrid_inner`. -/
theorem Hypothesis.exists_alignedOmegaSigmaGrid_chiFam_product [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    ∃ (ρ : Fin hyp.w1 →
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W1.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ))
      (κ : Fin hyp.w2 →
          (((typePData_toTICyclicHypothesis hyp.typeP hodd).W2.subgroupOf
            (typePData_toTICyclicHypothesis hyp.typeP hodd).W) →* ℂˣ)),
      Function.Injective ρ ∧ Function.Injective κ ∧
        ∀ i j, hyp.alignedOmegaSigmaGrid hG hodd i j
          = (typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam rfl
              (hyp.canonicalFullDadeApp hG hodd) (ρ i, κ j) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have : NeZero hyp.w1 := ⟨by have := h.one_lt_card_W1; rw [hcardW1] at this; omega⟩
  have : NeZero hyp.w2 := ⟨by rw [← hcardW2sub]; exact Nat.card_pos.ne'⟩
  let χ₂ : Fin hyp.w2 → (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun j => finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
  let χ₁ : Fin hyp.w1 → (h.W1.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    fun i => h.w1CharEquiv (finCongr hcardW1.symm i)
  let tic := typePData_toTICyclicHypothesis hyp.typeP hodd
  have : NeZero (Nat.card ↥tic.W1) := ⟨Nat.card_pos.ne'⟩
  have : NeZero (Nat.card ↥tic.W2) := ⟨Nat.card_pos.ne'⟩
  let e : ↥tic.W ≃* ↥h.sdiffTICyclicHypothesis.W := typePData_WEquiv hyp.typeP
  let app := hyp.canonicalFullDadeApp hG hodd
  -- the row/column families.
  let ρ : Fin hyp.w1 → ((tic.W1.subgroupOf tic.W) →* ℂˣ) :=
    fun i => (((χ₁ i).comp h.sdiffTICyclicHypothesis.wFst).comp e.toMonoidHom).comp
      (tic.W1.subgroupOf tic.W).subtype
  let κ : Fin hyp.w2 → ((tic.W2.subgroupOf tic.W) →* ℂˣ) :=
    fun j => (((χ₂ j).comp h.sdiffTICyclicHypothesis.wSnd).comp e.toMonoidHom).comp
      (tic.W2.subgroupOf tic.W).subtype
  -- the value identity `ω_{ij}^σ = χ_{(ρ i, κ j)}`.
  have hval : ∀ i j, hyp.alignedOmegaSigmaGrid hG hodd i j
      = tic.chiFam rfl app (ρ i, κ j) := by
    intro i j
    -- `ω_{ij}^σ = σ(ω(ξ_{ij}))`
    have hAOS : hyp.alignedOmegaSigmaGrid hG hodd i j
        = tic.sigma rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ) := by
      change tic.sigmaIntegral rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ)
        = tic.sigma rfl app (tic.omega
            ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom)
              : ClassFunction ↥tic.W ℂ)
      rw [OddOrder.Peterfalvi.S05.TICyclicHypothesis.sigmaIntegral_apply]
    -- `ξ_{ij}|_{W₁} = ρ i`, `ξ_{ij}|_{W₂} = κ j` (the cross factor is trivial on each block).
    have hc1 : ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom).comp
          (tic.W1.subgroupOf tic.W).subtype = ρ i := by
      apply MonoidHom.ext
      intro x
      have hm : e.toMonoidHom ((tic.W1.subgroupOf tic.W).subtype x) ∈
          h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
        typePData_WEquiv_mem_W1 hyp.typeP x.2
      have hz := h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hm
      simp only [ρ, MonoidHom.comp_apply,
        OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply]
      rw [hz, map_one]; exact mul_one _
    have hc2 : ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom).comp
          (tic.W2.subgroupOf tic.W).subtype = κ j := by
      apply MonoidHom.ext
      intro x
      have hm : e.toMonoidHom ((tic.W2.subgroupOf tic.W).subtype x) ∈
          h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
        typePData_WEquiv_mem_W2 hyp.typeP x.2
      have hz := h.sdiffTICyclicHypothesis.wFst_eq_one_of_mem_W2 hm
      simp only [κ, MonoidHom.comp_apply,
        OddOrder.Peterfalvi.S05.TICyclicHypothesis.omegaProdChar, MonoidHom.mul_apply]
      rw [hz, map_one]; exact one_mul _
    rw [hAOS, tic.sigma_omega rfl app
        ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom),
      tic.omegaProdEquiv_symm_eq
        ((h.sdiffTICyclicHypothesis.omegaProdChar (χ₁ i) (χ₂ j)).comp e.toMonoidHom),
      hc1, hc2]
  refine ⟨ρ, κ, ?_, ?_, hval⟩
  · -- `ρ` injective (joint orthonormality at column `0`)
    intro i i' hii'
    by_contra hne
    have h1 : hyp.alignedOmegaSigmaGrid hG hodd i 0 = hyp.alignedOmegaSigmaGrid hG hodd i' 0 := by
      rw [hval i 0, hval i' 0, hii']
    have h2 := hyp.alignedOmegaSigmaGrid_inner hG hodd i i' 0 0
    rw [if_neg (fun hh => hne hh.1), h1, hyp.alignedOmegaSigmaGrid_inner hG hodd i' i' 0 0,
      if_pos ⟨rfl, rfl⟩] at h2
    exact one_ne_zero h2
  · -- `κ` injective (joint orthonormality at row `0`)
    intro j j' hjj'
    by_contra hne
    have h1 : hyp.alignedOmegaSigmaGrid hG hodd 0 j = hyp.alignedOmegaSigmaGrid hG hodd 0 j' := by
      rw [hval 0 j, hval 0 j', hjj']
    have h2 := hyp.alignedOmegaSigmaGrid_inner hG hodd 0 0 j j'
    rw [if_neg (fun hh => hne hh.2), h1, hyp.alignedOmegaSigmaGrid_inner hG hodd 0 0 j' j',
      if_pos ⟨rfl, rfl⟩] at h2
    exact one_ne_zero h2

open scoped FiniteInduce in
/-- **§10 σ-grid lands in `ℤ[Irr G]`**: each `alignedOmegaSigmaGrid i j = chiFam(P_{ij}) ∈ ZIrr G`
(`exists_alignedOmegaSigmaGrid_chiFam_family` + `chiFam_spec`).  The `mem_ZIrr` field of the column
`OrthonormalCharacterImageFamily`. -/
theorem Hypothesis.alignedOmegaSigmaGrid_mem_ZIrr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.alignedOmegaSigmaGrid hG hodd i j ∈ ZIrr G := by
  obtain ⟨P, _, hP⟩ := hyp.exists_alignedOmegaSigmaGrid_chiFam_family hG hodd i
  rw [hP j]
  exact ((typePData_toTICyclicHypothesis hyp.typeP hodd).chiFam_spec rfl
    (hyp.canonicalFullDadeApp hG hodd)).2.1 _

open scoped FiniteInduce in
/-- **§10 within-column degree constancy** (Peterfalvi (4.5.a), the `i`-independence half of
(10.3)): within a fixed `W₂`-column `j`, the degree `μ_{ij}(1)` of the materialized `μ`-grid does
not depend on the row `i`.  This is the §6 fact `columnFamily_difference_apply_one` (the
within-column difference `μ_{ij} − μ_{0j}` vanishes at `1`) read through the `muGrid` definition. -/
theorem Hypothesis.muGrid_apply_one_within_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (i : Fin hyp.w1) (j : Fin hyp.w2) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd 0 j 1 := by
  have := hyp.finiteG
  classical
  have key : ∀ (h : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h.W1)]
      (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((h.columnFamily χ₂).mu k : ClassFunction (↥M) ℂ) 1
        = ((h.columnFamily χ₂).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h _ χ₂ k
    have hd := h.columnFamily_difference_apply_one χ₂ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]

open OddOrder.Peterfalvi.S06 in
set_option backward.isDefEq.respectTransparency false in
/-- The `k`-th power of the row-`0` product source `ω(1, χ₂)` is the row-`0` source of the
`k`-th power dual: `(omegaProdChar 1 χ₂)^k = omegaProdChar 1 (χ₂^k)` (on the §6
`toTICyclicHypothesis`).
Row `0` is the trivial `W₁`-dual, fixed by powering, so only the `W₂`-factor `χ₂` is raised. -/
theorem omegaProdChar_one_pow {L : Type*} [Group L] [Fintype L]
    (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : ℕ) :
    (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ^ k
      = h.toTICyclicHypothesis.omegaProdChar 1 (χ₂ ^ k) := by
  rw [h.toTICyclicHypothesis.omegaProdChar_one_left,
    h.toTICyclicHypothesis.omegaProdChar_one_left]
  refine MonoidHom.ext fun w => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (MonoidHom.pow_apply χ₂ k _).symm

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy** (Peterfalvi (10.3) via (3.9.b) + (4.3.b)): the degree
`μ_{0j}(1)` of the column-`0` certain-type character is unchanged when the `W₂`-dual `χ₂` indexing
the column is replaced by a Galois power `χ₂ ^ k` (with `k` coprime to the order of the row-`0`
source character).  This is the cross-column half of (10.3): by (3.9.b) there is a ring
automorphism `u` of `ℂ` with `σ(ω_{0,χ₂^k}) = (σ(ω_{0,χ₂}))^u`, hence by (4.3.b)
`δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`; evaluating at `1` and using that `u` fixes the
integer `δ·μ(1)` (degrees are positive, signs `±1`) forces `μ_{0,χ₂^k}(1) = μ_{0,χ₂}(1)`. -/
theorem columnFamily_mu_zero_apply_one_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    ((h.columnFamily (χ₂ ^ k)).mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  -- (3.9.b): the Galois automorphism `u` relating the row-`0` source to its `k`-th power
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  -- the `k`-th power of the row-`0` source is the row-`0` source of column `χ₂ ^ k`
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  -- (4.3.b) at row `0`, stated in `omega`/source form (`chiColumn ψ 0 = ω(omegaProdChar 1 ψ)`)
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  -- `hu : δ' • μ'_0 = (δ • μ_0)^u`; evaluate at `1`
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  -- `h1 : δ' * d' = u (δ * d)`; `u` fixes the integer `δ * d`
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- magnitudes: signs are `±1`, degrees positive, so `d' = d`
  rw [hd, hd']
  have hdd : d' = d := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simpa using habs
  rw [hdd]

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column *sign* constancy** (Peterfalvi (10.3), the `δ`-part of the (3.9.b) argument):
the sign `δ_{χ₂}` of the column-`0` certain-type difference family is unchanged when the `W₂`-dual
`χ₂` is replaced by a Galois power `χ₂ ^ k` (`k` coprime to the order of the row-`0` source).

This is the sign companion of `columnFamily_mu_zero_apply_one_pow`: the same (3.9.b)+(4.3.b) Galois
identity `δ_{χ₂^k}·μ_{0,χ₂^k} = (δ_{χ₂}·μ_{0,χ₂})^u`, evaluated at `1` and read in `ℤ`, gives
`δ_{χ₂^k}·d' = δ_{χ₂}·d`; since the degrees agree (`d' = d > 0`) the signs agree.  Peterfalvi's
(10.3): "It follows that `δ_j = δ_1` and `μ_{0j}(1) = μ_{01}(1)`." -/
theorem columnFamily_mu_zero_sign_pow {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) {k : ℕ}
    (hk : k.Coprime (orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂))) :
    (h.columnFamily (χ₂ ^ k)).sign = (h.columnFamily χ₂).sign := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  obtain ⟨u, hu, -⟩ := h.toTICyclicHypothesis.exists_mapRingEquiv_sigma_omega_pow rfl
    h.toTICyclicFullDadeApplication (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) hk
  rw [omegaProdChar_one_pow h χ₂ k] at hu
  have e43 : ∀ ψ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (h.toTICyclicHypothesis.omega (h.toTICyclicHypothesis.omegaProdChar 1 ψ) :
            ClassFunction h.toTICyclicHypothesis.W ℂ)
        = (h.columnFamily ψ).sign • ((h.columnFamily ψ).mu 0 : ClassFunction L ℂ) := by
    intro ψ
    have hψ := h.sigma_chiColumn_eq_certainType ψ 0
    rw [h.chiColumn_zero] at hψ
    exact hψ
  rw [e43 (χ₂ ^ k), e43 χ₂] at hu
  have h1 := congrArg (fun f : ClassFunction L ℂ => (f : L → ℂ) (1 : L)) hu
  obtain ⟨d, hd_pos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily χ₂).mu 0)
  obtain ⟨d', hd'_pos, hd'⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily (χ₂ ^ k)).mu 0)
  rw [ClassFunction.zsmul_apply, ClassFunction.mapRingEquiv_apply, ClassFunction.zsmul_apply,
    zsmul_eq_mul, zsmul_eq_mul, hd, hd'] at h1
  rw [← Int.cast_natCast (R := ℂ) d, ← Int.cast_natCast (R := ℂ) d', ← Int.cast_mul,
    ← Int.cast_mul, map_intCast] at h1
  have hZ : (h.columnFamily (χ₂ ^ k)).sign * (d' : ℤ) = (h.columnFamily χ₂).sign * (d : ℤ) :=
    Int.cast_injective h1
  -- the degrees agree (same Galois argument); cancel the positive degree to equate the signs
  have hdd : (d' : ℤ) = (d : ℤ) := by
    have habs := congrArg Int.natAbs hZ
    rw [Int.natAbs_mul, Int.natAbs_mul] at habs
    rcases (h.columnFamily (χ₂ ^ k)).sign_eq with hs | hs <;>
      rcases (h.columnFamily χ₂).sign_eq with hs' | hs' <;>
        simp only [hs, hs'] at habs <;> simp_all
  rw [hdd] at hZ
  have hdne : (d : ℤ) ≠ 0 := by exact_mod_cast hd_pos.ne'
  exact mul_right_cancel₀ hdne hZ

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column sign constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order, every nontrivial column shares the common sign `δ`.  Mirrors
`columnFamily_mu_zero_apply_one_eq_of_ne_one` (any two nontrivial duals are coprime powers of each
other) but for the sign via `columnFamily_mu_zero_sign_pow`. -/
theorem columnFamily_mu_zero_sign_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    (h.columnFamily χ₂').sign = (h.columnFamily χ₂).sign := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  have : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_sign_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open OddOrder.Peterfalvi.S06 in
/-- **§6 cross-column degree constancy, prime-order form** (Peterfalvi (10.3)): when the `W₂`-dual
group has prime order (`w₂` prime), every nontrivial column shares the common degree.  Any two
nontrivial duals `χ₂`, `χ₂'` are powers of each other (the dual group is cyclic of prime order, so
a nontrivial element generates), with the power coprime to `w₂`;
`columnFamily_mu_zero_apply_one_pow` then equates the column-`0` degrees.  This is the full
cross-column (j-independence) half of (10.3):
all the columns `0 < j < w₂` have degree `d = μ_{0j}(1)` independent of `j`. -/
theorem columnFamily_mu_zero_apply_one_eq_of_ne_one {L : Type*} [Group L] [Fintype L]
    [Invertible (Nat.card L : ℂ)] (h : OddOrder.Peterfalvi.S06.Hypothesis L)
    [NeZero (Nat.card h.W1)] [Finite ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime)
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1) :
    ((h.columnFamily χ₂').mu 0 : ClassFunction L ℂ) 1
      = ((h.columnFamily χ₂).mu 0 : ClassFunction L ℂ) 1 := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  classical
  -- a prime cardinality forces the dual group to be finite
  have : Finite ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Nat.card_pos_iff.mp hp.pos).2
  -- `orderOf χ₂ = |D|` (a nontrivial element of a prime-order group generates it)
  have hord : orderOf χ₂ = Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := by
    rcases (hp.eq_one_or_self_of_dvd _ (orderOf_dvd_natCard χ₂)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hχ₂
    · exact h1
  -- `χ₂'` is a power of `χ₂`
  have hgen : χ₂' ∈ Submonoid.powers χ₂ := by
    rw [mem_powers_iff_mem_zpowers]
    have htop : Subgroup.zpowers χ₂ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hord])
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk_eq⟩ := hgen
  -- `k` is coprime to `orderOf χ₂ = |D| = p`
  have hcop : k.Coprime (orderOf χ₂) := by
    rw [hord, Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hdvd
    rw [← hord] at hdvd
    exact hχ₂' (hk_eq ▸ orderOf_dvd_iff_pow_eq_one.mp hdvd)
  -- transfer coprimality to the order of the row-`0` source character
  have hsdvd : orderOf (h.toTICyclicHypothesis.omegaProdChar 1 χ₂) ∣ orderOf χ₂ := by
    apply orderOf_dvd_of_pow_eq_one
    rw [omegaProdChar_one_pow h χ₂ (orderOf χ₂), pow_orderOf_eq_one χ₂]
    exact h.toTICyclicHypothesis.omegaProdChar_one_one
  rw [← hk_eq]
  exact columnFamily_mu_zero_apply_one_pow h χ₂ (hcop.coprime_dvd_right hsdvd)

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column degree constancy** (Peterfalvi (10.3), the `j`-independence half at the
materialized `μ`-grid level): the degree `μ_{0j}(1)` of the row-`0` materialized `μ`-grid is
independent of the *nontrivial* column `0 < j < w₂`.

This wires the §6 prime-order corollary `columnFamily_mu_zero_apply_one_eq_of_ne_one` through the
`muGrid` materialization.  The required prime cardinality of the `W₂`-dual group is supplied by the
Pontryagin count `|Ŵ₂| = |W₂| = w₂` (`card_charGroup_W2`) together with the hypothesis `hw2` that
`w₂` is prime (Theorem (8.8), supplied at producer-construction time to avoid the
`no_typeV_maximal` → parameter-producer dependency cycle); the two columns are nontrivial duals
because the `Fin w₂`-reindex `finCardEquivCharacterGroup` is injective and sends only `0` to the
trivial character.  Together with `muGrid_apply_one_within_column` this gives the full (10.3) degree
independence `μ_{ij}(1) = d` for all `0 ≤ i < w₁`, `0 < j < w₂`. -/
theorem Hypothesis.muGrid_apply_one_cross_column [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd 0 j 1 = hyp.muGrid hG hodd 0 j' 1 := by
  have := hyp.finiteG
  classical
  -- Reconstruct the §6 host and the instances exactly as in `Hypothesis.muGrid`.
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- The `W₂`-dual group has prime cardinality `w₂` (Pontryagin count + (8.8)).
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  -- A nontrivial column index gives a nontrivial `W₂`-dual.
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  -- The within-column degree-constancy key (Peterfalvi (4.5.a)), as in
  -- `muGrid_apply_one_within_column`, used here only to strip the row index to `0`.
  have key : ∀ (h' : OddOrder.Peterfalvi.S06.Hypothesis (↥M)) [NeZero (Nat.card h'.W1)]
      (χ : (h'.W2.subgroupOf (h'.W1 ⊔ h'.W2)) →* ℂˣ) (k : Fin (Nat.card h'.W1)),
      ((h'.columnFamily χ).mu k : ClassFunction (↥M) ℂ) 1
        = ((h'.columnFamily χ).mu 0 : ClassFunction (↥M) ℂ) 1 := by
    intro h' _ χ k
    have hd := h'.columnFamily_difference_apply_one χ k
    simp only [SignedIrreducibleDifferenceFamily.difference_apply,
      SignedIrreducibleDifferenceFamily.classFunction_apply, ClassFunction.sub_apply] at hd
    exact sub_eq_zero.mp hd
  unfold Hypothesis.muGrid
  simp only [key]
  exact (columnFamily_mu_zero_apply_one_eq_of_ne_one h hp (hcol_ne j hj) (hcol_ne j' hj')).symm

/-- **§10 degree independence** (Peterfalvi (10.3), full statement at the materialized `μ`-grid
level): for nontrivial columns (`0 < j, j' < w₂`) the common degree `μ_{ij}(1) = d` is independent
of *both* the row `i` and the (nontrivial) column `j`.  This is the genuine (10.3) degree constancy,
combining the within-column constancy `muGrid_apply_one_within_column` (the `i`-independence
(4.5.a))
with the cross-column constancy `muGrid_apply_one_cross_column` (the `j`-independence via Theorem
(8.8) `w₂` prime + Pontryagin). It is exactly what populates
`CharacterParameters.degree_independent`
once the common value `d` is named (at producer-construction time, where `hw2` is available). -/
theorem Hypothesis.muGrid_apply_one_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) (i i' : Fin hyp.w1) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muGrid hG hodd i j 1 = hyp.muGrid hG hodd i' j' 1 := by
  rw [hyp.muGrid_apply_one_within_column hG hodd i j,
    hyp.muGrid_apply_one_cross_column hG hodd hw2 hj hj',
    ← hyp.muGrid_apply_one_within_column hG hodd i' j']

open scoped FiniteInduce in
/-- **§10 column sign** (Peterfalvi (10.3) `δ_j`): the sign `δ_j ∈ {±1}` of the `j`-th materialized
column, read off from the §6 `columnFamily` of the §10→§6 bridge (the same reconstruction as
`Hypothesis.muGrid`).  This is the genuine source for `CharacterParameters.delta`. -/
noncomputable def Hypothesis.muColumnSign [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) : ℤ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  exact (h.columnFamily (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).sign

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S06 in
/-- **§10 cross-column sign constancy** (Peterfalvi (10.3), the `δ_j`-independence): the column sign
`δ_j` is independent of the nontrivial column `0 < j < w₂`.  Wires the §6 prime-order sign corollary
`columnFamily_mu_zero_sign_eq_of_ne_one` through the `muColumnSign` materialization (same Pontryagin
prime count + nontrivial-dual argument as `muGrid_apply_one_cross_column`). -/
theorem Hypothesis.muColumnSign_eq_of_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) (hw2 : (hyp.w2).Prime) {j j' : Fin hyp.w2}
    (hj : j ≠ 0) (hj' : j' ≠ 0) :
    hyp.muColumnSign hG hodd j = hyp.muColumnSign hG hodd j' := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hp : (Nat.card ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ)).Prime := by
    rw [h.card_charGroup_W2,
      ← (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2)).toEquiv),
      hcardW2sub]
    exact hw2
  have hcol_ne : ∀ (k : Fin hyp.w2), k ≠ 0 →
      finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
        (finCongr hcardW2sub.symm k) ≠ 1 := by
    intro k hk heq
    rw [← finCardEquivCharacterGroup_zero (h.W2.subgroupOf (h.W1 ⊔ h.W2))] at heq
    have hk0 : finCongr hcardW2sub.symm k = 0 := (finCardEquivCharacterGroup _).injective heq
    apply hk
    have hval : (k : ℕ) = 0 := by simpa using congrArg Fin.val hk0
    exact Fin.ext hval
  unfold Hypothesis.muColumnSign
  exact columnFamily_mu_zero_sign_eq_of_ne_one h hp (hcol_ne j' hj') (hcol_ne j hj)

open scoped FiniteInduce in
/-- **§10 column-`0` sign** (Peterfalvi (10.3) / (4.4) `δ_0 = 1`): the sign `δ_0` of the trivial
column is `1`.  The column-`0` dual is the trivial character (`finCardEquivCharacterGroup_zero`),
and
the trivial column has sign `1` (`certainType_zero_column_anchor.1`, the `μ_{00} = 1_L` anchor).
This is the `δ_0 = 1` normalisation used by the (10.5) Dade-image identity (the column-`0` term in
`α_{ij} = μ_{ij} − δ·μ_{i0} − n·ζ` is reconciled against `ω_{i0}^σ` with unit sign). -/
theorem Hypothesis.muColumnSign_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G)) :
    hyp.muColumnSign hG hodd 0 = 1 := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M :=
    (hyp.typeP.W2_le.trans inf_le_left).trans
      (hyp.typeP.H_le.trans (Subgroup.map_subtype_le _))
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hdual0 : finCardEquivCharacterGroup (h.W2.subgroupOf (h.W1 ⊔ h.W2))
      (finCongr hcardW2sub.symm (0 : Fin hyp.w2)) = 1 := by
    rw [show finCongr hcardW2sub.symm (0 : Fin hyp.w2) = 0 from by apply Fin.ext; simp,
      finCardEquivCharacterGroup_zero]
  have esign : hyp.muColumnSign hG hodd 0
      = (h.columnFamily (finCardEquivCharacterGroup _
          (finCongr hcardW2sub.symm (0 : Fin hyp.w2)))).sign := by
    unfold Hypothesis.muColumnSign; rfl
  rw [esign, hdual0]
  exact h.certainType_zero_column_anchor.1

end OddOrder.Peterfalvi.S12



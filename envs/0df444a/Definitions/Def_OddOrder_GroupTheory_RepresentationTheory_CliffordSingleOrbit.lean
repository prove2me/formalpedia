-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordSingleOrbit
-- name    : OddOrder_GroupTheory_RepresentationTheory_CliffordSingleOrbit
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:56.980199+00:00
-- url     : https://prove2.me/theorems/c5adb7db-16bf-4742-abb2-cc5c307aa608
-- title:
--   Clifford's theorem: the constituents of a restriction form a single conjugation orbit
-- statement:
--   The single-orbit half of Clifford's theorem (Isaacs Thm 6.5), the input needed for the Clifford-degree assembly in Peterfalvi (9.9.a). For a $G$-irreducible representation, the irreducible constituents of its restriction to a normal subgroup form a single $G$-conjugation orbit.
--
--   Results include `restrictionConstituentsSingleOrbit_of_isIrreducible` (single orbit at the character level), `exists_induce_constituent_partition` (partition of $\mathrm{Irr}\,G$ into $\mathrm{Ind}_H^G$ blocks), `apply_one_eq_restrictionMultiplicity_mul_index_inertia` (the Clifford degree formula) and `apply_one_eq_index_of_liesOver_linear_inertia` (Clifford correspondence degree, Isaacs Thm 6.11).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/CliffordSingleOrbit.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/CliffordSingleOrbit.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordConjugateChar
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Clifford
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible

namespace OddOrder.RepresentationTheory

open _root_.OddOrder.RepresentationTheory.Representation

open scoped MonoidAlgebra

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {V : Type*} [AddCommGroup V] [Module k V]

variable (ρ : Representation k G V)

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford single-orbit, module level.**  For a `G`-irreducible representation `ρ` and a normal
subgroup `H ⊴ G`, any two simple `k[H]`-submodules `N`, `N'` of the restriction `Res^G_H ρ` have
conjugate characters: there is `g : G` with `χ_{N'}(h) = χ_N(g⁻¹ h g)` for all `h ∈ H`.

Proof: the `G`-conjugates `N.map (conjSemilinearEnd ρ g)` span `⊤`
(`iSup_map_conjSemilinearEnd_eq_top`, irreducibility of `ρ`), so the simple submodule `N'` is
`k[H]`-isomorphic to one of them, `N.map (conjSemilinearEnd ρ g)`
(`Submodule.linearEquiv_of_sSup_eq_top`).  Transporting that isomorphism to the subrepresentations
(`equivOfAsModuleEquiv`) and applying `Representation.char_iso` equates `χ_{N'}` with the character
of the conjugate; `character_subRep_conj` rewrites the latter as `χ_N(g⁻¹ · g)`. -/
theorem character_conj_of_simpleSubmodule [ρ.IsIrreducible] [FiniteDimensional k V]
    {H : Subgroup G} [hH : H.Normal]
    (N N' : Submodule k[↥H] (resRep ρ H).asModule) (hN : N ≠ ⊥)
    [IsSimpleModule k[↥H] ↥N] [IsSimpleModule k[↥H] ↥N'] :
    ∃ g : G, ((Subrepresentation.ofSubmodule' N').toRepresentation).character
      = fun h => ((Subrepresentation.ofSubmodule' N).toRepresentation).character
          (conjNormalMulAut H g⁻¹ h) := by
  classical
  have : ∀ S : (Set.range fun g : G => N.map (conjSemilinearEnd (H := H) ρ g)),
      IsSimpleModule k[↥H] (S : Submodule k[↥H] (resRep ρ H).asModule) := by
    rintro ⟨_, g, rfl⟩
    exact isSimpleModule_map_conjSemilinearEnd ρ g N
  obtain ⟨S, hS, ⟨e⟩⟩ := Submodule.linearEquiv_of_sSup_eq_top N'
    (Set.range fun g : G => N.map (conjSemilinearEnd (H := H) ρ g))
    (by rw [sSup_range]; exact iSup_map_conjSemilinearEnd_eq_top ρ N hN)
  obtain ⟨g, rfl⟩ := hS
  refine ⟨g, ?_⟩
  have hcharEq : ((Subrepresentation.ofSubmodule' N').toRepresentation).character
      = ((Subrepresentation.ofSubmodule'
          (N.map (conjSemilinearEnd (H := H) ρ g))).toRepresentation).character :=
    Representation.char_iso
      (equivOfAsModuleEquiv
        ((subRepAsModuleEquiv (resRep ρ H) N').symm.trans
          (e.trans (subRepAsModuleEquiv (resRep ρ H)
            (N.map (conjSemilinearEnd (H := H) ρ g))))))
  rw [hcharEq]
  funext h
  exact character_subRep_conj ρ N g h

set_option backward.isDefEq.respectTransparency false in
/-- **A nonzero intertwiner yields a simple constituent submodule** (the module side of the
constituent ⟺ submodule bridge).  If `σ` is an irreducible `k[H]`-representation and there is a
nonzero `H`-equivariant map `f : σ → Res^G_H ρ`, then `Res^G_H ρ` has a simple `k[H]`-submodule `N`
whose subrepresentation character equals `χ_σ`.  Proof: pass `f` to its `k[H]`-linear `asModule`
form (`equivLinearMapAsModule`); it is nonzero, so injective by Schur
(`LinearMap.injective_of_ne_zero`, `σ.asModule` simple); its range is a simple submodule
`k[H]`-isomorphic to `σ.asModule` (`LinearEquiv.ofInjective`), and transporting that isomorphism
through `equivOfAsModuleEquiv` + `char_iso` equates the characters. -/
theorem exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner [FiniteDimensional k V]
    {H : Subgroup G} [_hH : H.Normal]
    {W : Type*} [AddCommGroup W] [Module k W]
    (σ : Representation k ↥H W) [σ.IsIrreducible]
    {f : Representation.IntertwiningMap σ (resRep ρ H)} (hf : f ≠ 0) :
    ∃ N : Submodule k[↥H] (resRep ρ H).asModule, IsSimpleModule k[↥H] ↥N ∧
      ((Subrepresentation.ofSubmodule' N).toRepresentation).character = σ.character := by
  have : IsSimpleModule k[↥H] σ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule σ).mp inferInstance
  set fam := Representation.IntertwiningMap.equivLinearMapAsModule σ (resRep ρ H) f with hfam
  have hfam_ne : fam ≠ 0 := by
    rw [hfam, ne_eq, LinearEquiv.map_eq_zero_iff]; exact hf
  have hinj : Function.Injective fam := LinearMap.injective_of_ne_zero hfam_ne
  refine ⟨LinearMap.range fam, ?_, ?_⟩
  · exact (LinearEquiv.ofInjective fam hinj).isSimpleModule_iff.mp inferInstance
  · refine Representation.char_iso
      (equivOfAsModuleEquiv
        ((subRepAsModuleEquiv (resRep ρ H) (LinearMap.range fam)).symm.trans
          (LinearEquiv.ofInjective fam hinj).symm))

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford's theorem, single-orbit (character level)** ([Isaacs] Thm 6.5, first clause): for a
`G`-irreducible character `χ` and a normal subgroup `H ⊴ G`, the irreducible constituents of
`Res^G_H χ` form a single `G`-conjugation orbit.  This discharges the
`RestrictionConstituentsSingleOrbit` hypothesis that `clifford_decomposition` was parametrized on,
and is the input the (9.9.a) Clifford-degree assembly needs (with
`hasCommonRestrictionMultiplicity_of_singleOrbit`).

Proof: realize `χ` by a `G`-irreducible `ρ`.  A constituent `ψ` of `Res χ` has nonzero restriction
multiplicity, hence (`restrictionMultiplicity_eq_finrank_intertwiningMap`) a nonzero `H`-intertwiner
`σ_ψ → Res ρ`, which (`exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner`) yields a simple
`k[H]`-submodule `N_ψ` of `Res ρ` with `χ_{N_ψ} = ψ`.  For two constituents `θ`, `η` the submodules
`N_θ`, `N_η` are `G`-conjugate (`character_conj_of_simpleSubmodule`), giving `g` with
`θ(h) = η(g⁻¹ h g)`, i.e. `conjBy g θ = η`. -/
theorem restrictionConstituentsSingleOrbit_of_isIrreducible
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : IrreducibleCharacter G) :
    IrreducibleCharacter.RestrictionConstituentsSingleOrbit (G := G) (H := H) χ := by
  classical
  obtain ⟨V, _, _, _, ρ, hρirr, hρchar⟩ := χ.isIrreducible
  have := hρirr
  -- Every constituent `ψ` of `Res χ` is the character of a simple `k[H]`-submodule of `Res ρ`.
  have wrapper : ∀ ψ : IrreducibleCharacter ↥H,
      IrreducibleCharacter.LiesOver (G := G) (H := H) χ ψ →
      ∃ N : Submodule ℂ[↥H] (resRep ρ H).asModule, IsSimpleModule ℂ[↥H] ↥N ∧
        ((Subrepresentation.ofSubmodule' N).toRepresentation).character
          = (ψ : ClassFunction ↥H ℂ) := by
    intro ψ hψ
    obtain ⟨W, _, _, _, σ, hσirr, hσchar⟩ := ψ.isIrreducible
    have := hσirr
    have hfr := ClassFunction.restrictionMultiplicity_eq_finrank_intertwiningMap (H := H) ρ σ
      hρchar hσchar
    have hfr_ne : Module.finrank ℂ (Representation.IntertwiningMap σ (ρ.comp H.subtype)) ≠ 0 :=
      fun h0 => hψ (by rw [hfr, h0, Nat.cast_zero])
    have : Nontrivial (Representation.IntertwiningMap σ (ρ.comp H.subtype)) :=
      Module.nontrivial_of_finrank_pos (Nat.pos_of_ne_zero hfr_ne)
    obtain ⟨f, hf⟩ := exists_ne (0 : Representation.IntertwiningMap σ (ρ.comp H.subtype))
    obtain ⟨N, hNsimple, hNchar⟩ :=
      exists_simpleSubmodule_character_eq_of_ne_zero_intertwiner ρ σ hf
    exact ⟨N, hNsimple, hNchar.trans hσchar.symm⟩
  intro θ η hθ hη
  obtain ⟨Nθ, hNθsimple, hNθchar⟩ := wrapper θ hθ
  obtain ⟨Nη, hNηsimple, hNηchar⟩ := wrapper η hη
  have := hNθsimple
  have := hNηsimple
  have hNη_ne : Nη ≠ ⊥ := Nη.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial ℂ[↥H] ↥Nη)
  obtain ⟨g, hg⟩ := character_conj_of_simpleSubmodule ρ Nη Nθ hNη_ne
  -- `hg : χ_{N_θ} = fun h => χ_{N_η} (g⁻¹ h g)`; substitute the constituent characters.
  rw [hNθchar, hNηchar] at hg
  refine ⟨g, ?_⟩
  apply IrreducibleCharacter.ext
  ext h
  rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
  -- `θ(g h g⁻¹) = η(h)`: rewrite `θ` via `hg`, then `g⁻¹ (g h g⁻¹) g = h`.
  rw [hg]
  refine congrArg _ (Subtype.ext ?_)
  simp only [conjNormalMulAut_apply_coe]
  group

/-- **Induced-character constituents sharing a common `G`-constituent are `G`-conjugate.**
For a normal `H ⊴ G` and irreducibles `θ₁, θ₂` of `H`, if some `G`-irreducible `χ` is a constituent
of *both* `Ind_H^G θ₁` and `Ind_H^G θ₂` (`⟨Ind θᵢ, χ⟩ ≠ 0`), then `θ₁` and `θ₂` lie in one
`G`-conjugation orbit (`∃ g, conjBy g θ₁ = θ₂`).

Immediate from Clifford's single-orbit theorem: `⟨Ind θᵢ, χ⟩ ≠ 0 ⟺ θᵢ` lies over `χ`
(`inner_induce_ne_zero_iff_liesOver`), and all constituents of `Res^G_H χ` lie in one `G`-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible`).  Contrapositive: the constituent sets of
`Ind_H^G θ₁` and `Ind_H^G θ₂` are **disjoint** when `θ₁, θ₂` are non-conjugate — the `trivIset` core
of the induced-from-`H'` partition of `Irr H` used in Peterfalvi (12.5). -/
theorem exists_conj_of_common_induce_constituent
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Finite ↥H] [Invertible (Nat.card ↥H : ℂ)]
    {θ₁ θ₂ : IrreducibleCharacter ↥H} {χ : IrreducibleCharacter G}
    (h₁ : ClassFunction.inner (ClassFunction.induce H (θ₁ : ClassFunction ↥H ℂ))
        (χ : ClassFunction G ℂ) ≠ 0)
    (h₂ : ClassFunction.inner (ClassFunction.induce H (θ₂ : ClassFunction ↥H ℂ))
        (χ : ClassFunction G ℂ) ≠ 0) :
    ∃ g : G, IrreducibleCharacter.conjBy g θ₁ = θ₂ := by
  have : Fintype ↥H := Fintype.ofFinite ↥H
  exact (restrictionConstituentsSingleOrbit_of_isIrreducible (H := H) χ).exists_conj
    ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H χ θ₁).mp h₁)
    ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H χ θ₂).mp h₂)

/-- **Dual of `exists_liesOver`**: every irreducible `σ` of a subgroup `H ≤ G` lies *under* some
irreducible `ψ` of `G` (`σ` is a constituent of `Res_H ψ`, i.e. `⟨Ind_H σ, ψ⟩ ≠ 0`).  The induced
character `Ind_H^G σ` has positive degree `[G:H]·σ(1)`, hence is nonzero, hence — by completeness
(`classFunction_eq_zero_of_orthogonal`) — not orthogonal to every irreducible of `G`.  This supplies
the Clifford correspondent `ψ` over `θ'` in the Peterfalvi (1.7.b)/(12.5) inertia setup. -/
theorem exists_liesOver_of_subgroup [Finite G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (σ : IrreducibleCharacter ↥H) :
    ∃ ψ : IrreducibleCharacter G, IrreducibleCharacter.LiesOver H ψ σ := by
  have : Fintype G := Fintype.ofFinite G
  classical
  have hne : ClassFunction.induce H (σ : ClassFunction ↥H ℂ) ≠ 0 := by
    intro hzero
    have h1 : ClassFunction.induce H (σ : ClassFunction ↥H ℂ) 1 = 0 := by rw [hzero]; rfl
    rw [ClassFunction.induce_apply_one] at h1
    obtain ⟨d, hd, hdeq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast σ
    rw [hdeq] at h1
    have hidx : (H.index : ℂ) ≠ 0 := by exact_mod_cast Subgroup.index_ne_zero_of_finite
    exact mul_ne_zero hidx (by exact_mod_cast hd.ne') h1
  by_contra hcon
  push Not at hcon
  apply hne
  apply classFunction_eq_zero_of_orthogonal
  intro ψ
  by_contra hz
  exact hcon ψ ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H ψ σ).mp hz)

open scoped Classical in
/-- **Partition of `Irr G` into `Ind_H^G` blocks.**  For `H ⊴ G`, the irreducible characters of `G`
partition into the constituent-sets of the induced characters `Ind_H^G λ` (`λ ∈ Irr H`): every
`φ ∈ Irr G` lies in exactly one block.  Blocks are indexed by their own `Finset` (conjugate `λ` give
the *same* block), via `cap φ := {θ | ⟨Ind_H λ(φ), θ⟩ ≠ 0}` where `λ(φ)` is a chosen constituent of
`Res_H φ` (`exists_liesOver`).  `PairwiseDisjoint` from `exists_conj_of_common_induce_constituent`
(a shared constituent forces `λ`-conjugacy) + conjugation-closure of `Res_H φ` constituents
(`liesOver_conjBy_iff`); cover from `φ ∈ cap φ`.  The `trivIset`/`cover` packaging for the
Peterfalvi
(12.5) `DpsiH` Fourier regrouping (`Finset.sum_biUnion`). -/
theorem exists_induce_constituent_partition [Finite G]
    [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Fintype (IrreducibleCharacter G)] :
    ∃ parts : Finset (Finset (IrreducibleCharacter G)),
      (Finset.univ : Finset (IrreducibleCharacter G)) = parts.biUnion id ∧
      (↑parts : Set (Finset (IrreducibleCharacter G))).PairwiseDisjoint id ∧
      ∀ A ∈ parts, ∃ ρ : IrreducibleCharacter ↥H, ∀ θ : IrreducibleCharacter G,
        θ ∈ A ↔ IrreducibleCharacter.LiesOver H θ ρ := by
  have : Fintype G := Fintype.ofFinite G
  classical
  let lam : IrreducibleCharacter G → IrreducibleCharacter ↥H :=
    fun φ => (IrreducibleCharacter.exists_liesOver (H := H) φ).choose
  have hlam : ∀ φ, IrreducibleCharacter.LiesOver H φ (lam φ) :=
    fun φ => (IrreducibleCharacter.exists_liesOver (H := H) φ).choose_spec
  let cap : IrreducibleCharacter G → Finset (IrreducibleCharacter G) :=
    fun φ => Finset.univ.filter (fun θ =>
      ClassFunction.inner (ClassFunction.induce H (lam φ : ClassFunction ↥H ℂ))
        (θ : ClassFunction G ℂ) ≠ 0)
  have hmem_cap : ∀ φ θ : IrreducibleCharacter G, θ ∈ cap φ ↔
      IrreducibleCharacter.LiesOver H θ (lam φ) := by
    intro φ θ
    change θ ∈ Finset.univ.filter _ ↔ _
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and]
    exact IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H θ (lam φ)
  have hself : ∀ φ : IrreducibleCharacter G, φ ∈ cap φ := fun φ => (hmem_cap φ φ).mpr (hlam φ)
  refine ⟨Finset.univ.image cap, ?_, ?_, ?_⟩
  · ext φ
    simp only [Finset.mem_univ, true_iff, Finset.mem_biUnion, id_eq]
    exact ⟨cap φ, Finset.mem_image_of_mem cap (Finset.mem_univ φ), hself φ⟩
  · intro B hB B' hB' hBB'
    rw [Finset.mem_coe, Finset.mem_image] at hB hB'
    obtain ⟨φ, -, rfl⟩ := hB
    obtain ⟨φ', -, rfl⟩ := hB'
    simp only [Function.onFun, id_eq]
    rw [Finset.disjoint_left]
    intro θ hθ hθ'
    apply hBB'
    obtain ⟨g, hg⟩ := exists_conj_of_common_induce_constituent
      ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H θ (lam φ)).mpr
        ((hmem_cap φ θ).mp hθ))
      ((IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver H θ (lam φ')).mpr
        ((hmem_cap φ' θ).mp hθ'))
    ext θ''
    rw [hmem_cap, hmem_cap, ← hg, IrreducibleCharacter.liesOver_conjBy_iff]
  · intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨φ, -, rfl⟩ := hA
    exact ⟨lam φ, hmem_cap φ⟩

/-- **Clifford's theorem for an invariant constituent** ([Isaacs] Thm 6.5, invariant case).  For a
normal `H ⊴ G` and `χ ∈ Irr G` lying over `θ ∈ Irr H` with `θ` **`G`-invariant** (`θ^g = θ` for all
`g`), the restriction is a single multiple of `θ`: `Res^G_H χ = e · θ` with `e = ⟨Res χ, θ⟩`.

All constituents of `Res^G_H χ` form one `G`-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible`);
`G`-invariance collapses that orbit to `{θ}`, so the Fourier expansion
(`sum_inner_irreducibleCharacter_smul`) of `Res χ` over `Irr H` has only the `θ`-term.

This is the `Res_H ψ = e·θ` input of the general Peterfalvi (1.7.b) — with the inertia-quotient
decomposition `Ind_H^T(Res ψ) = ψ·∑_β Inf(β)` it gives `e·Ind_H^T θ = ψ·∑_β Inf(β)`, whose
constituents `ψ·Inf(β)` all have the common degree `ψ(1) = e·θ(1)`. -/
theorem restrict_eq_restrictionMultiplicity_smul_of_invariant
    {H : Subgroup G} [hH : H.Normal] [Finite G] [Fintype ↥H]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥H : ℂ)]
    [Finite (IrreducibleCharacter ↥H)]
    (χ : IrreducibleCharacter G) (θ : IrreducibleCharacter ↥H)
    (hover : IrreducibleCharacter.LiesOver H χ θ)
    (hinv : ∀ g : G, IrreducibleCharacter.conjBy g θ = θ) :
    ClassFunction.restrict H (χ : ClassFunction G ℂ)
      = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) (θ : ClassFunction ↥H ℂ)
          • (θ : ClassFunction ↥H ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite (IrreducibleCharacter ↥H)
  classical
  have hsingle := restrictionConstituentsSingleOrbit_of_isIrreducible (H := H) χ
  conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
    (ClassFunction.restrict H (χ : ClassFunction G ℂ))]
  rw [Finset.sum_eq_single θ]
  · rw [ClassFunction.restrictionMultiplicity_def]
  · intro θ' _ hne
    rw [smul_eq_zero]
    left
    by_contra hc
    have hover' : IrreducibleCharacter.LiesOver H χ θ' := hc
    obtain ⟨g, hg⟩ := hsingle θ θ' hover hover'
    rw [hinv g] at hg
    exact hne hg.symm
  · intro h
    exact absurd (Finset.mem_univ θ) h

set_option backward.isDefEq.respectTransparency false in
/-- **Clifford's theorem, degree formula** ([Isaacs] Thm 6.5).  For a `G`-irreducible character `χ`,
a normal subgroup `H ⊴ G`, and a constituent `θ₀` of `Res^G_H χ`, the degree factors as
`χ(1) = ⟨Res χ, θ₀⟩ · [G : I_G(θ₀)] · θ₀(1)`.  Assembles the degree expansion
(`apply_one_eq_sum_restrictionMultiplicity_mul`), single-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible`), common multiplicity
(`hasCommonRestrictionMultiplicity_of_singleOrbit`), and orbit size
(`card_conjByOrbit_eq_index_inertia`): in `∑_θ ⟨Res χ,θ⟩·θ(1)` only the `[G:I]`-element orbit of
`θ₀`
contributes, each term equal to `⟨Res χ,θ₀⟩·θ₀(1)` (common multiplicity, conjugation-invariant
degree). -/
theorem apply_one_eq_restrictionMultiplicity_mul_index_inertia
    [Finite G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Finite (IrreducibleCharacter ↥H)]
    (χ : IrreducibleCharacter G) (θ₀ : IrreducibleCharacter ↥H)
    (hθ₀ : IrreducibleCharacter.LiesOver (G := G) (H := H) χ θ₀) :
    (χ : ClassFunction G ℂ) (1 : G)
      = ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) (θ₀ : ClassFunction ↥H ℂ)
          * ((IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index : ℂ)
          * (θ₀ : ClassFunction ↥H ℂ) 1 := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite (IrreducibleCharacter ↥H)
  classical
  have hsingle := restrictionConstituentsSingleOrbit_of_isIrreducible (G := G) (H := H) χ
  have hcommon :=
    IrreducibleCharacter.hasCommonRestrictionMultiplicity_of_singleOrbit (H := H) hsingle
  rw [apply_one_eq_sum_restrictionMultiplicity_mul (H := H) (χ : ClassFunction G ℂ)]
  have key : ∀ θ : IrreducibleCharacter ↥H,
      ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ) (θ : ClassFunction ↥H ℂ)
          * (θ : ClassFunction ↥H ℂ) 1
        = if θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀ then
            ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
                (θ₀ : ClassFunction ↥H ℂ) * (θ₀ : ClassFunction ↥H ℂ) 1
          else 0 := by
    intro θ
    by_cases hmem : θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀
    · rw [if_pos hmem]
      obtain ⟨g, rfl⟩ := IrreducibleCharacter.mem_conjByOrbit.mp hmem
      rw [IrreducibleCharacter.HasCommonRestrictionMultiplicity.eq_of_liesOver hcommon
        (IrreducibleCharacter.liesOver_conjBy hθ₀ g) hθ₀, conjBy_apply_one]
    · rw [if_neg hmem]
      have hm0 : ClassFunction.restrictionMultiplicity H (χ : ClassFunction G ℂ)
          (θ : ClassFunction ↥H ℂ) = 0 := by
        by_contra hm
        exact hmem (IrreducibleCharacter.mem_conjByOrbit.mpr (hsingle θ₀ θ hθ₀ hm))
      rw [hm0, zero_mul]
  rw [Finset.sum_congr rfl (fun θ _ => key θ), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  have hcard : (Finset.univ.filter
      (fun θ => θ ∈ IrreducibleCharacter.conjByOrbit (G := G) (H := H) θ₀)).card
      = (IrreducibleCharacter.inertia (G := G) (H := H) θ₀).index := by
    rw [← card_conjByOrbit_eq_index_inertia (G := G) (H := H) θ₀,
      Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext θ
    simp [Set.mem_toFinset]
  rw [hcard]
  ring

/-- **Equal-degree constituents over the same character have equal restriction multiplicity.**  For
`H ⊴ G` and `φ₁, φ₂ ∈ Irr G` both lying over `ρ ∈ Irr H` with `φ₁(1) = φ₂(1)`, the multiplicities
`⟨Res_H φᵢ, ρ⟩` agree.  From the Clifford degree formula
`apply_one_eq_restrictionMultiplicity_mul_index_inertia` (`φ(1) = ⟨Res φ, ρ⟩·[G:I(ρ)]·ρ(1)`) and the
common nonzero factor `[G:I(ρ)]·ρ(1)`.  With the general (1.7.b) equal degree of the constituents of
`Ind_H^G ρ`, this gives their **common multiplicity `e`** — the coefficient-matching `a_ρ = c_ρ/e`
of the Peterfalvi (12.5) `DpsiH` decomposition. -/
theorem restrictionMultiplicity_eq_of_liesOver_of_apply_one_eq
    [Finite G] [Invertible (Nat.card G : ℂ)]
    {H : Subgroup G} [hH : H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Finite (IrreducibleCharacter ↥H)]
    {φ₁ φ₂ : IrreducibleCharacter G} {ρ : IrreducibleCharacter ↥H}
    (h₁ : IrreducibleCharacter.LiesOver (G := G) (H := H) φ₁ ρ)
    (h₂ : IrreducibleCharacter.LiesOver (G := G) (H := H) φ₂ ρ)
    (hdeg : (φ₁ : ClassFunction G ℂ) 1 = (φ₂ : ClassFunction G ℂ) 1) :
    ClassFunction.restrictionMultiplicity H (φ₁ : ClassFunction G ℂ) (ρ : ClassFunction ↥H ℂ)
      = ClassFunction.restrictionMultiplicity H (φ₂ : ClassFunction G ℂ)
          (ρ : ClassFunction ↥H ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite (IrreducibleCharacter ↥H)
  have e1 := apply_one_eq_restrictionMultiplicity_mul_index_inertia φ₁ ρ h₁
  have e2 := apply_one_eq_restrictionMultiplicity_mul_index_inertia φ₂ ρ h₂
  rw [hdeg] at e1
  have hkey := e1.symm.trans e2
  have hρ1 : (ρ : ClassFunction ↥H ℂ) 1 ≠ 0 := by
    obtain ⟨d, hd, hdeq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ρ
    rw [hdeq]; exact_mod_cast hd.ne'
  have hIdx : ((IrreducibleCharacter.inertia (G := G) (H := H) ρ).index : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  exact mul_right_cancel₀ hIdx (mul_right_cancel₀ hρ1 hkey)

/-- **Clifford correspondence** ([Isaacs] Thm 6.11, degree form).  If `ψ ∈ Irr I` (for a subgroup
`I ≤ G`) has an *irreducible* induction `Ind_I^G ψ`, and the irreducible `χ ∈ Irr G` lies over `ψ`
(i.e. `ψ` is a constituent of `Res_I χ`), then `χ` **is** that induction: `χ = Ind_I^G ψ` as class
functions.

Proof: `χ` lies over `ψ`, so `⟨Ind_I^G ψ, χ⟩ ≠ 0` by Frobenius reciprocity
(`inner_induce_ne_zero_iff_liesOver`).  Both `Ind_I^G ψ` (by hypothesis) and `χ` are irreducible,
and distinct irreducible characters are orthogonal (`irreducibleCharacter_inner_eq_ite`), so the
nonzero inner product forces them to coincide.

This is the half of the Clifford correspondence that Peterfalvi's (9.8)/(9.9) degree computations
use: an irreducible character that lies over `ψ` and whose induced character is irreducible *equals*
that induced character, so its degree is `[G:I]·ψ(1)`. -/
theorem coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    {I : Subgroup G} [Fintype ↥I] [Invertible (Nat.card ↥I : ℂ)]
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter I)
    (hind : IsIrreducibleCharacter (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ)))
    (hover : IrreducibleCharacter.LiesOver I χ ψ) :
    (χ : ClassFunction G ℂ) = ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) := by
  have hne : ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
      (χ : ClassFunction G ℂ) ≠ 0 :=
    (IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver I χ ψ).mpr hover
  have heq : (⟨ClassFunction.induce I (ψ : ClassFunction ↥I ℂ), hind⟩ : IrreducibleCharacter G)
      = χ := by
    by_contra h
    apply hne
    have hite := irreducibleCharacter_inner_eq_ite
      (⟨ClassFunction.induce I (ψ : ClassFunction ↥I ℂ), hind⟩ : IrreducibleCharacter G) χ
    rw [IrreducibleCharacter.coe_mk] at hite
    rw [hite, if_neg h]
  rw [← heq, IrreducibleCharacter.coe_mk]

open scoped ComplexOrder in
/-- **Constituent degree bound.**  If an irreducible character `χ` of `G` lies over an irreducible
character `ψ` of a subgroup `I ≤ G` (equivalently, `χ` is a constituent of the induced character
`Ind_I^G ψ`), then `χ(1) ≤ (Ind_I^G ψ)(1)`.

The induced character is a genuine character, hence a non-negative integer combination
`Ind_I^G ψ = ∑_η ⟨Ind ψ, η⟩ · η` over `Irr G` (`sum_inner_irreducibleCharacter_smul`).  Frobenius
reciprocity (`inner_induce_eq_inner_restrict`) identifies each coefficient `⟨Ind ψ, η⟩` with the
non-negative integer restriction multiplicity `⟨Res η, ψ⟩` (`restrictionMultiplicity_natCast`), so
evaluating at `1` every summand `⟨Ind ψ, η⟩ · η(1)` is `≥ 0`; the `χ`-summand is
`≥ 1 · χ(1) = χ(1)` because `χ` occurs with multiplicity `≥ 1`.

Unlike `coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce` (which needs `Ind ψ` to be
*irreducible*), this only needs the lies-over relation.  Peterfalvi uses it in (9.8.c)/(9.9.a):
together with the Clifford lower bound `χ(1) = e · [G:I_G(θ₀)] · θ₀(1)` it forces the constituent
multiplicity `e = 1`, so an `H₀C'`-kernel character of `HU` has degree exactly `[HU:HC] = u`. -/
theorem apply_one_le_induce_apply_one_of_liesOver
    [Fintype G] [Invertible (Nat.card G : ℂ)] [Finite (IrreducibleCharacter G)]
    {I : Subgroup G} [Fintype ↥I] [Invertible (Nat.card ↥I : ℂ)]
    (χ : IrreducibleCharacter G) (ψ : IrreducibleCharacter ↥I)
    (hover : IrreducibleCharacter.LiesOver I χ ψ) :
    (χ : ClassFunction G ℂ) (1 : G) ≤
      ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) (1 : G) := by
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite (IrreducibleCharacter G)
  classical
  -- For each irreducible `η` of `G`, the coefficient `⟨Ind ψ, η⟩` equals the restriction
  -- multiplicity `⟨Res η, ψ⟩` (Frobenius + the real-valuedness of the multiplicity).
  have hcoeff : ∀ η : IrreducibleCharacter G,
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ)
        = ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
            (ψ : ClassFunction ↥I ℂ) := by
    intro η
    obtain ⟨k, hk⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := I) η ψ
    rw [ClassFunction.inner_induce_eq_inner_restrict I (ψ : ClassFunction ↥I ℂ)
        (η : ClassFunction G ℂ),
      inner_conj_symm (ClassFunction.restrict I (η : ClassFunction G ℂ))
        (ψ : ClassFunction ↥I ℂ)]
    change star (ClassFunction.restrictionMultiplicity I (η : ClassFunction G ℂ)
        (ψ : ClassFunction ↥I ℂ)) = _
    rw [hk, star_natCast]
  -- Fourier expansion of `Ind ψ` at `1`: degree = `∑_η ⟨Ind ψ, η⟩ · η(1)`.
  have hsumapp : ∀ (s : Finset (IrreducibleCharacter G))
      (F : IrreducibleCharacter G → ClassFunction G ℂ),
      (∑ η ∈ s, F η) (1 : G) = ∑ η ∈ s, (F η) (1 : G) := by
    intro s F
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.add_apply, ih]
  have hexp := sum_inner_irreducibleCharacter_smul (G := G)
    (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
  have key := congrArg (fun f : ClassFunction G ℂ => f (1 : G)) hexp
  simp only [hsumapp, ClassFunction.smul_apply] at key
  -- Every summand `⟨Ind ψ, η⟩ · η(1)` is `≥ 0`.
  have hnn : ∀ η ∈ (Finset.univ : Finset (IrreducibleCharacter G)),
      (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) := by
    intro η _
    have h1 : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (η : ClassFunction G ℂ) := by
      rw [hcoeff η]
      exact ClassFunction.restrictionMultiplicity_nonneg I η.isIrreducible ψ.isIrreducible
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast η
    rw [hd]
    exact mul_nonneg h1 (by positivity)
  -- The `χ`-summand dominates `χ(1)`.
  obtain ⟨dχ, _, hdχ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast χ
  obtain ⟨kχ, hkχ⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := I) χ ψ
  have hχ_coeff_ne : ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
      (χ : ClassFunction G ℂ) ≠ 0 :=
    (IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver I χ ψ).mpr hover
  have hkχ_pos : 1 ≤ kχ := by
    rcases Nat.eq_zero_or_pos kχ with h | h
    · exact absurd (by rw [hcoeff χ, hkχ, h, Nat.cast_zero]) hχ_coeff_ne
    · exact h
  have hχterm : (χ : ClassFunction G ℂ) (1 : G) ≤
      ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
        (χ : ClassFunction G ℂ) * (χ : ClassFunction G ℂ) (1 : G) := by
    rw [hcoeff χ, hkχ, hdχ, ← Nat.cast_mul, Nat.cast_le]
    exact Nat.le_mul_of_pos_left dχ hkχ_pos
  calc (χ : ClassFunction G ℂ) (1 : G)
      ≤ ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
          (χ : ClassFunction G ℂ) * (χ : ClassFunction G ℂ) (1 : G) := hχterm
    _ ≤ ∑ η : IrreducibleCharacter G,
          ClassFunction.inner (ClassFunction.induce I (ψ : ClassFunction ↥I ℂ))
            (η : ClassFunction G ℂ) * (η : ClassFunction G ℂ) (1 : G) :=
        Finset.single_le_sum hnn (Finset.mem_univ χ)
    _ = ClassFunction.induce I (ψ : ClassFunction ↥I ℂ) (1 : G) := key

open scoped ComplexOrder in
/-- **Clifford correspondence degree** ([Is] Thm 6.11, packaged for Peterfalvi (9.8.c)/(9.9.a)).
Let `H ⊴ G`, `I ≤ G`, and `χ ∈ Irr G`.  Suppose `χ` lies over a *linear* (`θ₀(1) = 1`) constituent
`θ₀ ∈ Irr H` whose inertia group in `G` is exactly `I`, and over a *linear* (`ψ(1) = 1`) character
`ψ ∈ Irr I`.  Then `χ(1) = [G : I]`.

The Clifford lower bound `χ(1) = ⟨Res χ, θ₀⟩ · [G : I_G(θ₀)] · θ₀(1) = e · [G : I]` (with
`apply_one_eq_restrictionMultiplicity_mul_index_inertia`, where `e = ⟨Res χ, θ₀⟩ ≥ 1`) and the
constituent upper bound `χ(1) ≤ (Ind_I^G ψ)(1) = [G : I] · ψ(1) = [G : I]`
(`apply_one_le_induce_apply_one_of_liesOver`) sandwich `χ(1)` between `[G : I]` and itself, forcing
`e = 1` and `χ(1) = [G : I]`.  This is the abstract core of Peterfalvi's "every `χ ∈ 𝒮(H₀C')` has
degree `u = [HU : HC]`" (9.9.a): with `H = H`, `I = HC` and `θ₀` a nontrivial chief-factor character
(inertia `HC` by `inertia_eq_hcInHu`). -/
theorem apply_one_eq_index_of_liesOver_linear_inertia
    [Finite G] [Invertible (Nat.card G : ℂ)] [Finite (IrreducibleCharacter G)]
    {H : Subgroup G} [H.Normal] [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    [Finite (IrreducibleCharacter ↥H)]
    {I : Subgroup G} [Fintype ↥I] [Invertible (Nat.card ↥I : ℂ)]
    (χ : IrreducibleCharacter G) (θ₀ : IrreducibleCharacter ↥H) (ψ : IrreducibleCharacter ↥I)
    (hθ₀over : IrreducibleCharacter.LiesOver H χ θ₀)
    (hθ₀inertia : IrreducibleCharacter.inertia (G := G) (H := H) θ₀ = I)
    (hθ₀deg : (θ₀ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψover : IrreducibleCharacter.LiesOver I χ ψ)
    (hψdeg : (ψ : ClassFunction ↥I ℂ) (1 : ↥I) = 1) :
    (χ : ClassFunction G ℂ) (1 : G) = (I.index : ℂ) := by
  have : Fintype G := Fintype.ofFinite G
  have : Fintype (IrreducibleCharacter G) := Fintype.ofFinite (IrreducibleCharacter G)
  have : Fintype (IrreducibleCharacter ↥H) := Fintype.ofFinite (IrreducibleCharacter ↥H)
  classical
  -- The constituent multiplicity `e = ⟨Res χ, θ₀⟩` is a non-negative integer `m`, and `m ≥ 1`
  -- because `χ` lies over `θ₀`.
  obtain ⟨m, hm⟩ := IrreducibleCharacter.restrictionMultiplicity_natCast (H := H) χ θ₀
  have hm_pos : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exact absurd (hm.trans (by rw [h, Nat.cast_zero])) hθ₀over
    · exact h
  -- Lower bound: `χ(1) = m · [G:I]` (Clifford degree formula, inertia `= I`, `θ₀(1) = 1`).
  have hlow : (χ : ClassFunction G ℂ) (1 : G) = (m : ℂ) * (I.index : ℂ) := by
    rw [apply_one_eq_restrictionMultiplicity_mul_index_inertia (H := H) χ θ₀ hθ₀over,
      hm, hθ₀inertia, hθ₀deg, mul_one]
  -- Upper bound: `χ(1) ≤ (Ind_I ψ)(1) = [G:I] · ψ(1) = [G:I]`.
  have hup : (χ : ClassFunction G ℂ) (1 : G) ≤ (I.index : ℂ) := by
    have h := apply_one_le_induce_apply_one_of_liesOver χ ψ hψover
    rwa [ClassFunction.induce_apply_one, hψdeg, mul_one] at h
  -- `[G:I] = 1·[G:I] ≤ m·[G:I] = χ(1)`, sandwiched against `χ(1) ≤ [G:I]`.
  have hge : (I.index : ℂ) ≤ (χ : ClassFunction G ℂ) (1 : G) := by
    rw [hlow]
    calc (I.index : ℂ) = 1 * (I.index : ℂ) := (one_mul _).symm
      _ ≤ (m : ℂ) * (I.index : ℂ) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hm_pos) (Nat.cast_nonneg _)
  exact le_antisymm hup hge

end OddOrder.RepresentationTheory



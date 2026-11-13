-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
-- name    : OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:17:58.804201+00:00
-- url     : https://prove2.me/theorems/7039ed0c-cb42-4871-855a-cfe9fa640cee
-- title:
--   Peterfalvi (10.1): type III/IV/V hypothesis and §5/§6 bridge prerequisites
-- statement:
--   Formalizes Hypothesis (10.1) of Peterfalvi for maximal subgroups of types III, IV and V, together with the bridge prerequisites connecting it to the §5 and §6 machinery.
--
--   Main declarations: `inducedFamily` (Peterfalvi's character family `S` of Hypothesis (10.1)); `inducedFamily_closedUnderConjugate` (The induced family `S` is closed under complex conjugation); `inducedFamily_closedUnderMapRingEquiv` (The induced family `S` is closed under coefficient automorphisms); `inducedFamily_hasNoRealCharacters` (The induced family `S = inducedFamily M` has no real characters).
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Hypothesis.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalIII_IV_V_Core/Hypothesis.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S05_OmegaSigmaGrid
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaTrichotomy
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEndgame
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeFourCorner
import Mathlib.GroupTheory.IsPerfect

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance finiteGFintype [Finite G] : Fintype G :=
  Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

noncomputable scoped instance natCardInvCG [Finite G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

open scoped FiniteInduce in
/-- Peterfalvi's character family `S` of Hypothesis (10.1):
`{Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1_{M'}}`, where `M' = [M,M]` is realised inside
`M` as `(derivedInG M).subgroupOf M`.  The induction is the canonical
`ClassFunction.induce`. -/
noncomputable def inducedFamily (M : Subgroup G) [Finite G] :
    Set (ClassFunction ↥M ℂ) :=
  { χ | ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
      χ = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) }

open scoped FiniteInduce in
/-- **The induced family `S` is closed under complex conjugation** (Peterfalvi §10): for
`χ = Ind_{M'}^M θ ∈ S` with `θ ∈ Irr M'`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_{M'}^M θ̄`
(`ClassFunction.induce_conj`), and `θ̄` is again a non-trivial irreducible of `M'`
(`IsIrreducibleCharacter.conj`, `irreducibleCharacter_conj_ne_trivial`).  This is the
`ζ̄ ∈ S` input to the `(α_{ij}^τ, (ζ−ζ̄)^τ)` step of the (10.5) `a = 0` argument. -/
theorem inducedFamily_closedUnderConjugate [Finite G] (M : Subgroup G) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (inducedFamily M) := by
  classical
  intro φ hφ
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj, θ.isIrreducible.conj⟩,
    ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ).conj
        = trivialClassFunction ↥((derivedInG M).subgroupOf M) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (c : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = trivialClassFunction ↥((derivedInG M).subgroupOf M)
    rw [← ClassFunction.conj_conj (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((derivedInG M).subgroupOf M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)

open scoped FiniteInduce in
/-- **The induced family `S` is closed under coefficient automorphisms** (the Galois analogue of
`inducedFamily_closedUnderConjugate`): for `χ = Ind_{M'}^M θ ∈ S` and a ring automorphism
`σ : ℂ ≃+* ℂ`, the transported `σχ = Ind_{M'}^M (σθ)` (`ClassFunction.mapRingEquiv_induce`), and
`σθ = galoisMap σ θ` is again a non-trivial irreducible of `M'` (the trivial character is
`σ`-fixed).  This is the `ζ^σ ∈ S` input of the Galois row/column-constancy step of the
(11.9.a) grid analysis (Coq `aut_phi`/`cfAut_seqInd`, issue 1024). -/
theorem inducedFamily_closedUnderMapRingEquiv [Finite G] (M : Subgroup G) (σ : ℂ ≃+* ℂ)
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedFamily M) :
    ClassFunction.mapRingEquiv σ φ ∈ inducedFamily M := by
  classical
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨IrreducibleCharacter.galoisMap σ θ, ?_, ?_⟩
  · -- `σθ ≠ 1`: else `θ = σ⁻¹(σθ) = σ⁻¹(1) = 1` (the trivial character is `σ`-fixed).
    intro h
    apply hθ_ne
    have h' := congrArg (IrreducibleCharacter.galoisMap σ.symm) h
    rw [IrreducibleCharacter.galoisMap_symm_galoisMap] at h'
    rw [h']
    apply Subtype.ext
    change (IrreducibleCharacter.galoisMap σ.symm
        (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
        : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = trivialClassFunction ↥((derivedInG M).subgroupOf M)
    ext x
    rw [IrreducibleCharacter.galoisMap_apply_apply]
    change σ.symm ((trivialClassFunction ↥((derivedInG M).subgroupOf M) : _ → ℂ) x) = _
    rw [trivialClassFunction_apply, map_one]
  · rw [hφeq, ClassFunction.mapRingEquiv_induce, IrreducibleCharacter.galoisMap_apply_coe]

/-- **Complex conjugation commutes with `G`-conjugation** of class functions: for a normal
subgroup `H ⊴ G`, `(θ^g)‾ = (θ‾)^g`.  Both sides evaluate to `star (θ ⟨g·h·g⁻¹⟩)`.  This is the
`σ`-commutes-with-the-`M`-action input to the odd-order orbit argument showing that an induced
character `Ind_{M'}^M θ` (`θ ≠ 1`) is non-real. -/
theorem conjBy_conj {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    (g : K) (θ : ClassFunction ↥H ℂ) :
    (ClassFunction.conjBy g θ).conj = ClassFunction.conjBy g θ.conj := by
  ext h
  simp only [ClassFunction.conj_apply, ClassFunction.conjBy_apply]

/-- **The complex-conjugation involution `conjPerm` commutes with `M`-conjugation `conjBy`** on the
irreducible characters of a normal subgroup `H ⊴ K`.  Lifts `conjBy_conj` to `IrreducibleCharacter`
via the coercion lemmas.  This is what makes the conjugation orbit `conjByOrbit θ` invariant under
`conjPerm`, the key to the odd-order non-reality of `Ind_{M'}^M θ`. -/
theorem conjPerm_conjBy_comm {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    (g : K) (θ : IrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H (IrreducibleCharacter.conjBy g θ)
      = IrreducibleCharacter.conjBy g (IrreducibleCharacter.conjPerm ↥H θ) := by
  refine IrreducibleCharacter.ext ?_
  simp only [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.coe_conjBy]
  exact conjBy_conj g (θ : ClassFunction ↥H ℂ)

/-- **The conjugation orbit `conjByOrbit θ` is `conjPerm`-invariant** once it contains `θ̄`.  If the
complex conjugate `θ̄ = conjPerm θ` lies in the `M`-conjugation orbit of `θ`, then so does the
conjugate of every orbit member.  Combines `conjPerm_conjBy_comm` (`σ` commutes with the action)
with the group-action laws (`conjBy_mul`). -/
theorem conjPerm_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal] [Finite ↥H]
    {θ : IrreducibleCharacter ↥H}
    (hmem : IrreducibleCharacter.conjPerm ↥H θ ∈ IrreducibleCharacter.conjByOrbit (G := K) θ)
    {η : IrreducibleCharacter ↥H} (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  obtain ⟨g, rfl⟩ := hη
  rw [conjPerm_conjBy_comm]
  obtain ⟨g₀, hg₀⟩ := hmem
  rw [← hg₀, ← IrreducibleCharacter.conjBy_mul]
  exact IrreducibleCharacter.conjBy_mem_conjByOrbit θ (g₀ * g)

/-- **`G`-conjugation fixes the trivial character.** -/
theorem conjBy_trivial {K : Type*} [Group K] {H : Subgroup K} [H.Normal] (g : K) :
    IrreducibleCharacter.conjBy g (trivialIrreducibleCharacter ↥H)
      = trivialIrreducibleCharacter ↥H := by
  apply IrreducibleCharacter.ext
  ext h
  simp [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]

/-- **The trivial character is not in the conjugation orbit of a nontrivial character.**  If
`conjBy g θ = 1` then `θ = conjBy g⁻¹ 1 = 1` (`conjBy_trivial`). -/
theorem trivial_not_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    {θ : IrreducibleCharacter ↥H} (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    trivialIrreducibleCharacter ↥H ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  rintro ⟨g, hg⟩
  apply hθ
  have : θ = IrreducibleCharacter.conjBy g⁻¹ (trivialIrreducibleCharacter ↥H) := by
    rw [← hg]; exact (IrreducibleCharacter.conjBy_inv_conjBy g θ).symm
  rw [this, conjBy_trivial]

/-- **No `conjPerm`-fixed point in the conjugation orbit of a nontrivial character** (odd order).
A fixed point `η` of `conjPerm` is real (`conjPerm_eq_self_iff`), hence trivial in odd order
(`not_isReal_of_ne_trivial_of_odd_card'`); but the trivial character is not in `conjByOrbit θ` for
`θ ≠ 1` (`trivial_not_mem_conjByOrbit`). -/
theorem conjPerm_ne_self_of_mem_conjByOrbit {K : Type*} [Group K] {H : Subgroup K} [H.Normal]
    [Finite ↥H] (hodd : Odd (Nat.card ↥H)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) {η : IrreducibleCharacter ↥H}
    (hη : η ∈ IrreducibleCharacter.conjByOrbit (G := K) θ) :
    IrreducibleCharacter.conjPerm ↥H η ≠ η := by
  intro hfix
  have hreal : ClassFunction.IsReal (η : ClassFunction ↥H ℂ) :=
    (IrreducibleCharacter.conjPerm_eq_self_iff η).mp hfix
  have htriv : η = trivialIrreducibleCharacter ↥H := by
    by_contra hne
    exact OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hodd hne hreal
  exact trivial_not_mem_conjByOrbit hθ (htriv ▸ hη)

/-- **`conjPerm` is an involution**: `(χ̄)‾ = χ`. -/
theorem conjPerm_conjPerm {L : Type*} [Group L] [Finite L] (χ : IrreducibleCharacter L) :
    IrreducibleCharacter.conjPerm L (IrreducibleCharacter.conjPerm L χ) = χ := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.conjPerm_apply_coe, IrreducibleCharacter.conjPerm_apply_coe,
    ClassFunction.conj_conj]

/-- **A nontrivial character is not conjugate to its complex conjugate, in odd order** (the orbit
form of Peterfalvi (1.1)).  The conjugation orbit `conjByOrbit θ` has odd cardinality `[K : I_θ]`
(`card_conjByOrbit_eq_index_inertia`, a divisor of the odd `|K|`); were `θ̄ ∈ conjByOrbit θ`, the
involution `σ = conjPerm` would restrict to it, and by `card_fixedPoints_modEq` (`p = 2`) an
involution on an odd-cardinality set has a fixed point — a real, hence trivial, character in the
orbit, impossible by `conjPerm_ne_self_of_mem_conjByOrbit`. -/
theorem conjPerm_not_mem_conjByOrbit {K : Type*} [Group K] [Finite K] {H : Subgroup K} [H.Normal]
    (hodd : Odd (Nat.card K)) {θ : IrreducibleCharacter ↥H}
    (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    IrreducibleCharacter.conjPerm ↥H θ ∉ IrreducibleCharacter.conjByOrbit (G := K) θ := by
  intro hmem
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype ↥H := Fintype.ofFinite ↥H
  have : Invertible (Nat.card K : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have : Invertible (Nat.card ↥H : ℂ) := invertibleOfNonzero (by exact_mod_cast Nat.card_pos.ne')
  have : Fintype ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) := Fintype.ofFinite _
  have hoddH : Odd (Nat.card ↥H) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card H)
  set f : Function.End ↥(IrreducibleCharacter.conjByOrbit (G := K) θ) :=
    fun η => ⟨IrreducibleCharacter.conjPerm ↥H η.1, conjPerm_mem_conjByOrbit hmem η.2⟩ with hf
  have hf2 : f ^ 2 = 1 := by
    funext η
    change f (f η) = η
    exact Subtype.ext (conjPerm_conjPerm η.1)
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := 2) (n := 1) (by simpa using hf2)
  have hodd_orbit : Odd (Fintype.card ↥(IrreducibleCharacter.conjByOrbit (G := K) θ)) := by
    rw [← Nat.card_eq_fintype_card, card_conjByOrbit_eq_index_inertia]
    exact hodd.of_dvd_nat (Subgroup.index_dvd_card _)
  have hfp_pos : 0 < Fintype.card f.fixedPoints := by
    have h1 := Nat.odd_iff.mp hodd_orbit
    rw [Nat.ModEq] at hmod
    omega
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hfp_pos
  have hxf : f x.1 = x.1 := x.2
  have hfix : IrreducibleCharacter.conjPerm ↥H x.1.1 = x.1.1 := Subtype.ext_iff.mp hxf
  exact conjPerm_ne_self_of_mem_conjByOrbit hoddH hθ x.1.2 hfix

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` has no real characters** (Peterfalvi §10, the
`no_real_characters` clause of the §7 coherence hypothesis for `S`).  Every `Ind_{M'}^M θ`
(`θ ∈ Irr M'`, `θ ≠ 1`) of the odd-order group `M` is non-real: its conjugate
`(Ind θ)‾ = Ind θ̄` (`induce_conj`) is orthogonal to `Ind θ`, because `θ̄ = conjPerm θ` is not
`M`-conjugate to `θ` (`conjPerm_not_mem_conjByOrbit`) so `inner_induce_eq_zero_of_not_conj` gives
`⟨Ind θ, Ind θ̄⟩ = 0`; but `⟨Ind θ, Ind θ⟩ ≠ 0` (`card_mul_inner_self_induce_eq_card_inertia`,
`|I_θ| ≠ 0`), and the two coincide when `Ind θ` is real. -/
theorem inducedFamily_hasNoRealCharacters {M : Subgroup G} [Finite G]
    (hodd : Odd (Nat.card ↥M)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (inducedFamily M) := by
  classical
  intro χ hχ hreal
  obtain ⟨θ, hθne, rfl⟩ := hχ
  have : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  have hnotconj : ∀ g : ↥M, IrreducibleCharacter.conjBy g θ
      ≠ IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ :=
    fun g hg => conjPerm_not_mem_conjByOrbit hodd hθne ⟨g, hg⟩
  have hzero := inner_induce_eq_zero_of_not_conj θ
    (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ) hnotconj
  have hconjeq : (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction).conj
      = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ).toClassFunction := by
    rw [ClassFunction.induce_conj, IrreducibleCharacter.conjPerm_apply_coe]
  unfold ClassFunction.IsReal at hreal
  have heq : ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction
      = ClassFunction.induce ((derivedInG M).subgroupOf M)
        (IrreducibleCharacter.conjPerm ↥((derivedInG M).subgroupOf M) θ).toClassFunction :=
    hreal.symm.trans hconjeq
  have hself0 : ClassFunction.inner
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction)
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction) = 0 :=
    (congrArg (ClassFunction.inner
      (ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction)) heq).trans hzero
  have hc := card_mul_inner_self_induce_eq_card_inertia θ
  rw [hself0, mul_zero] at hc
  exact (show (Nat.card ↥(ClassFunction.inertia θ.toClassFunction) : ℂ) ≠ 0 by
    exact_mod_cast Nat.card_pos.ne') hc.symm

open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` is pairwise orthogonal** (the `pairwise_orthogonal`
clause of the §7 coherence hypothesis for `S`).  Distinct members `Ind_{M'}^M θ ≠ Ind_{M'}^M θ'`
have non-`M`-conjugate sources (`induce_eq_induce_iff_conj`), so `inner_induce_eq_zero_of_not_conj`
gives `⟨Ind θ, Ind θ'⟩ = 0`. -/
theorem inducedFamily_pairwiseOrthogonal {M : Subgroup G} [Finite G] :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (inducedFamily M) := by
  intro χ ψ hχ hψ hne
  obtain ⟨θ, hθne, rfl⟩ := hχ
  obtain ⟨θ', hθ'ne, rfl⟩ := hψ
  have : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  exact inner_induce_eq_zero_of_not_conj θ θ'
    (fun g hg => hne ((induce_eq_induce_iff_conj θ θ').mpr ⟨g, hg⟩))

open scoped FiniteInduce in
/-- **The induced family `S = inducedFamily M` is finite**: it is contained in the image of the
finite type `IrreducibleCharacter M'` (`finite_irreducibleCharacter`, `M' = [M,M]`) under
`Ind_{M'}^M`, hence a finite set.  This is the `hXfin`/`hYfin` input when the (11.8.6) union
instantiates the S07 orthogonal glue `exists_integralCharacterMap_glue_of_orthogonal`. -/
theorem inducedFamily_finite {M : Subgroup G} [Finite G] : (inducedFamily M).Finite := by
  classical
  have : Finite (IrreducibleCharacter ↥((derivedInG M).subgroupOf M)) :=
    finite_irreducibleCharacter
  refine Set.Finite.subset (Set.finite_range
    (fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
      ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ))) ?_
  rintro χ ⟨θ, -, rfl⟩
  exact ⟨θ, rfl⟩

open scoped FiniteInduce in
/-- **Peterfalvi (10.1)**: the common setup for a maximal subgroup of type III,
IV, or V.

Finiteness of `G` is carried as the instance field `finiteG` (the `S15`
`FiniteInduce` pattern), so that the *genuine* Dade isometry `tau`, the induced
family `Sset`, and the support `A0 = A_0(M)` can be defined as honest projections
(see `Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A0`) rather than carried as
unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis for
`A_0(M)` (supplied by `S10.dadeSupportHypotheses_typeP`), and `hconj` is its
`L`-conjugation invariance, which together build the Dade isometry. -/
structure Hypothesis (M : Subgroup G) where
  [finiteG : Finite G]
  maximal : M ∈ maximalSubgroups G
  typeP : TypePData M
  type_alt : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M (typePA0 M typeP)

namespace Hypothesis

/-- Peterfalvi's `W_1` from Definition (8.4). -/
def W1 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W1

/-- Peterfalvi's `W_2` from Definition (8.4). -/
def W2 {M : Subgroup G} (hyp : Hypothesis M) : Subgroup G :=
  hyp.typeP.W2

/-- Peterfalvi's `w_1 = |W_1|`. -/
noncomputable def w1 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W1

/-- Peterfalvi's `w_2 = |W_2|`. -/
noncomputable def w2 {M : Subgroup G} (hyp : Hypothesis M) : ℕ :=
  Nat.card ↥hyp.W2

/-- Peterfalvi's support `A_0(M)` from (8.10), as a subset of `M` (the
`supportInSubgroup` restriction of the ambient set `typePA0 M`).  This is the
genuine support for the Dade isometry, no longer an unconstrained field. -/
def A0 {M : Subgroup G} (hyp : Hypothesis M) : Set ↥M :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M

open scoped FiniteInduce in
/-- Peterfalvi's family `S` of (10.1), pinned to the genuine `inducedFamily M`
`= {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}`, no longer an unconstrained field. -/
noncomputable def Sset {M : Subgroup G} (hyp : Hypothesis M) :
    Set (ClassFunction ↥M ℂ) :=
  haveI := hyp.finiteG
  inducedFamily M

open scoped FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A_0(M), M, G)` from (10.1),
pinned to the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data
`dadeData` (no longer an unconstrained field). -/
noncomputable def tau {M : Subgroup G} (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData)

open scoped FiniteInduce in
/-- **The §10 Dade isometry `τ` commutes with coefficientwise ring automorphisms** (Peterfalvi
`Dade_aut`): for `A_0`-supported `φ`, `(φ^{σc})^τ = (φ^τ)^{σc}`.  The Dade integral character map is
pointwise (its value is `φ(a)` at a base point, `0` elsewhere), so applying `σc` to coefficients
commutes with it (`dadeIntegralCharacterMap_mapRingEquiv_comm`).  Taking `σc = conjAe` this is the
`τ`-side Galois-equivariance feeding the (11.8.3) reality `β̄ = β`. -/
theorem tau_mapRingEquiv_comm [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (σc : ℂ ≃+* ℂ) {φ : ClassFunction ↥M ℂ} (hφ : φ.support ⊆ hyp.A0) :
    hyp.tau (ClassFunction.mapRingEquiv σc φ) = ClassFunction.mapRingEquiv σc (hyp.tau φ) := by
  have := hyp.finiteG
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mapRingEquiv_comm
    hyp.dadeData.dade (hyp.dadeData.dade.fullDadeIsometryData) σc hφ

open scoped FiniteInduce in
/-- **`A(M)` is `M`-invariant**: `M ≤ N_G(A(M))` — the easy half of Peterfalvi (8.16) for the
type-`P` support, self-contained group theory (no Dade data, no simplicity).
`A(M) = centralizerSupport (M#) M'` is `M`-invariant: `M` normalizes `M' = derivedInG M`
(`derivedInG_pointwise_smul` + `conj_smul_eq_self_of_mem`), permutes `M# = M \ {1}`
(`image_sharpSubgroup`), and conjugates the centralizer condition elementwise.

This is the `M`-stability input to `toHypothesis71` / `toFamilyHypothesis71` (the §7 inputs to
Peterfalvi (10.8)), so those §7 constructions are self-contained from the genuine `Hypothesis`. -/
theorem le_normalizer_typePA {M : Subgroup G} (hyp : Hypothesis M) :
    M ≤ Subgroup.normalizer (typePA M hyp.typeP) := by
  have := hyp.finiteG
  intro m hm
  rw [Subgroup.mem_set_normalizer_iff]
  -- forward `M`-invariance, applied to both `m` and `m⁻¹`.
  suffices hfwd : ∀ a ∈ M, ∀ y, y ∈ typePA M hyp.typeP → a * y * a⁻¹ ∈ typePA M hyp.typeP by
    intro h
    refine ⟨hfwd m hm h, fun hh => ?_⟩
    have hb := hfwd m⁻¹ (inv_mem hm) _ hh
    simpa [mul_assoc] using hb
  intro a ha y hy
  simp only [typePA, centralizerSupport, Set.mem_ofPred_eq] at hy ⊢
  obtain ⟨hyM', hy1, x, hxM, hyx⟩ := hy
  -- (i) `a y a⁻¹ ∈ M' = derivedInG M` (`M` normalizes its derived subgroup).
  have hM'inv : MulAut.conj a • derivedInG M = derivedInG M := by
    rw [derivedInG_pointwise_smul, Subgroup.conj_smul_eq_self_of_mem ha]
  have hyM'2 : a * y * a⁻¹ ∈ derivedInG M := by
    rw [← hM'inv, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hsm : (MulAut.conj a)⁻¹ • (a * y * a⁻¹) = y := by
      rw [← map_inv, MulAut.smul_def, MulAut.conj_apply]; group
    rw [hsm]; exact hyM'
  -- (ii) `a y a⁻¹ ≠ 1`.
  have hne : a * y * a⁻¹ ≠ 1 := by
    intro h1; apply hy1
    have hyrw : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    rw [hyrw, h1]; group
  -- (iii) `a x a⁻¹ ∈ M# = sharpSubgroup M`.
  have hxM2 : a * x * a⁻¹ ∈ sharpSubgroup M := by
    have himg : (MulAut.conj a) '' sharpSubgroup M = sharpSubgroup M := by
      rw [image_sharpSubgroup, Subgroup.conj_smul_eq_self_of_mem ha]
    rw [← himg]
    exact ⟨x, hxM, by rw [MulAut.conj_apply]⟩
  -- (iv) `a y a⁻¹` centralizes `a x a⁻¹` (conjugate of `y ∈ C_G({x})`).
  have hcent : a * y * a⁻¹ ∈ Subgroup.centralizer ({a * x * a⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hyx ⊢
    have hxy : x * y = y * x := hyx x rfl
    rintro z hz
    rw [Set.mem_singleton_iff] at hz; subst hz
    calc a * x * a⁻¹ * (a * y * a⁻¹)
        = a * (x * y) * a⁻¹ := by group
      _ = a * (y * x) * a⁻¹ := by rw [hxy]
      _ = a * y * a⁻¹ * (a * x * a⁻¹) := by group
  exact ⟨hyM'2, hne, a * x * a⁻¹, hxM2, hcent⟩

open scoped FiniteInduce in
/-- **Peterfalvi (8.16) for the type-`P` support `A(M)`**: `N_G(A(M)) = M`.

`M ≤ N_G(A(M))` is the `M`-invariance `le_normalizer_typePA`.  Conversely, since
`A(M) = (M')#` (`typePA_eq_sharpSubgroup_derivedInG`), a normalizer of the *set* `A(M)`
normalizes the subgroup `M' = derivedInG M` (conjugation fixes `1`), so
`N_G(A(M)) ≤ N_G(M')`.  The latter contains the maximal `M`, so it is `M` or `G`; were it
`G`, then `M' ⊴ G` with `⊥ ≠ W₂ ≤ M' ≤ M < G` would contradict the simplicity of `G`.
Hence `N_G(M') = M`. -/
theorem normalizer_typePA_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    Subgroup.normalizer (typePA M hyp.typeP) = M := by
  apply le_antisymm
  · -- Step 1: `N_G(A(M)) ≤ N_G(M')` (a set-normalizer of `(M')#` normalizes `M'`).
    have hstep : Subgroup.normalizer (typePA M hyp.typeP) ≤
        Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) := by
      intro g hg
      rw [Subgroup.mem_set_normalizer_iff] at hg ⊢
      intro h
      by_cases h1 : h = 1
      · subst h1
        simp
      · have hg' := hg h
        rw [typePA_eq_sharpSubgroup_derivedInG] at hg'
        simp only [sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe] at hg' ⊢
        constructor
        · intro hh
          exact (hg'.mp ⟨hh, h1⟩).1
        · intro hh
          have hc1 : g * h * g⁻¹ ≠ 1 := by
            intro he
            apply h1
            have hrw : h = g⁻¹ * (g * h * g⁻¹) * g := by group
            rw [hrw, he]
            group
          exact (hg'.mpr ⟨hh, hc1⟩).1
    -- Step 2: `N_G(M') = M` by maximality + simplicity.
    have hMle : M ≤ Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) := by
      intro m hm
      have hM'inv : MulAut.conj m • derivedInG M = derivedInG M := by
        rw [derivedInG_pointwise_smul, Subgroup.conj_smul_eq_self_of_mem hm]
      rw [Subgroup.mem_set_normalizer_iff]
      intro h
      have hiff : h ∈ derivedInG M ↔
          (MulAut.conj m) • h ∈ (MulAut.conj m) • derivedInG M :=
        (Subgroup.smul_mem_pointwise_smul_iff).symm
      rw [hM'inv] at hiff
      simpa [MulAut.smul_def, MulAut.conj_apply] using hiff
    by_cases hN : Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) = M
    · exact hstep.trans hN.le
    · exfalso
      have htop : Subgroup.normalizer ((derivedInG M : Subgroup G) : Set G) = ⊤ :=
        hyp.maximal.2 _ (hMle.lt_of_ne (Ne.symm hN))
      have hnormal : (derivedInG M).Normal := Subgroup.normalizer_eq_top_iff.mp htop
      rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnormal with hbot | htop'
      · -- `M' = ⊥` contradicts `⊥ ≠ W₂ ≤ H ≤ M'`.
        have hW2le : hyp.typeP.W2 ≤ derivedInG M :=
          hyp.typeP.W2_le.trans (inf_le_left.trans hyp.typeP.H_le)
        exact hyp.typeP.W2_nontrivial (le_bot_iff.mp (hbot ▸ hW2le))
      · -- `M' = ⊤` gives `M = ⊤`, contradicting the maximality (coatom) of `M`.
        exact hyp.maximal.1
          (top_le_iff.mp (htop' ▸ (Subgroup.map_subtype_le _ : derivedInG M ≤ M)))
  · exact hyp.le_normalizer_typePA

open scoped FiniteInduce in
/-- **The Peterfalvi (7.1) `ρ`-machinery data for `(L, A) = (M, A(M))`** — the §7 input to the
(10.8) non-coherence estimate.

Built genuinely from the §10 Dade isometry on `A_0(M)` (carried by `hyp.dadeData`/`hyp.hconj`) by
restricting to the `M`-stable subset `A(M) = typePA ⊆ A_0(M) = typePA0` (`Set.subset_union_left`):
`FullDadeIsometryData.restrict` restricts the Dade map and its `IsDadeMap` certificate, and the
`L`-equivariance of the restricted datum is `S04.Hypothesis.hConjInvariant`.  The `M`-stability
the `M`-stability of `A(M)` is supplied by `le_normalizer_typePA`, so this
construction is self-contained from the genuine `Hypothesis` (**sorry-free**, no external `hN`).

This is the foundational `S09.Hypothesis71` instance that lets the §10 estimate apply the family
inequality (7.5) `S09.family_inequality` and the coherence norm estimate (7.8.b)
`S09.Hypothesis78.NormEstimates` to `M` (Peterfalvi (10.8), 04.12 line 79). -/
noncomputable def toHypothesis71 {M : Subgroup G} [Finite G] (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (typePA M hyp.typeP) M :=
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  { hyp := hyp.dadeData.dade.restrict Set.subset_union_left hnorm
    τ := ((hyp.dadeData.dade.fullDadeIsometryData).restrict
      Set.subset_union_left hnorm).toDadeMap
    isDadeMap := ((hyp.dadeData.dade.fullDadeIsometryData).restrict
      Set.subset_union_left hnorm).toDadeIsometryData.isDadeMap
    }

open scoped FiniteInduce in
/-- **The Peterfalvi (7.4) one-member family `{(M, A(M))}`** — the direct input to the family
inequality (7.5) `S09.family_inequality` for the (10.8) estimate.  The single member's (7.1) data is
`toHypothesis71`; the `IsDadeIsometry` certificate is the restricted Dade isometry's
(`FullDadeIsometryData.toDadeIsometryData.isDadeIsometry`), and `pairwise_disjoint` is vacuous over
`Fin 1`.  Sorry-free and self-contained (the `M`-stability is `le_normalizer_typePA`). -/
noncomputable def toFamilyHypothesis71 {M : Subgroup G} [Finite G] (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S09.FamilyHypothesis71 G 1 where
  L := fun _ => M
  A := fun _ => typePA M hyp.typeP
  fintypeL := fun _ => inferInstance
  invertibleL := fun _ => inferInstance
  hyp71 := fun _ => hyp.toHypothesis71
  isDadeIsometry := fun _ => by
    have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
        (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
      ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
    exact ((hyp.dadeData.dade.fullDadeIsometryData).restrict
      Set.subset_union_left hnorm).toDadeIsometryData.isDadeIsometry
  pairwise_disjoint := fun i j hij => absurd (Subsingleton.elim i j) hij

end Hypothesis

open scoped FiniteInduce in
/-- **Peterfalvi (10.1), existence**: every maximal subgroup `M` of type III, IV,
or V carries the (10.1) Hypothesis.  The character family, support, and Dade
isometry are now the genuine `inducedFamily`, `A_0(M)`, and
`S07.dadeIntegralCharacterMap`; the only inputs are the (8.15) Dade support data
(`S10.dadeSupportHypotheses_typeP`) and the conjugation invariance `hconj` of the
support kernels (a (8.14)/(8.15) fact). -/
theorem exists_hypothesis_of_typeIIIorIVorV [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hType : IsTypeIII M ∨ IsTypeIV M ∨ IsTypeV M) :
    Nonempty (Hypothesis M) := by
  obtain ⟨data⟩ := typePData_of_isTypeNonI (Or.inr hType)
  -- Types III/IV/V are `P₁` (classification): III/IV via `(III∨IV) ↔ (P₁ ∧ M_F≠M_σ)`, V via
  -- `V ↔ (P₁ ∧ M_F=M_σ)`.  This routes the `A_0(M)` datum through the type-`P₁` construction
  -- `dadeSupportHypothesisData_typePA0_of_isTypeP1` rather than the general
  -- `dadeSupportHypotheses_typeP`, whose type-`P₂` branches were the later-landing side.
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification hG hM
    rcases hType with h | h | h
    · exact (hcls.2.2.1.mp (Or.inl h)).1
    · exact (hcls.2.2.1.mp (Or.inr h)).1
    · exact (hcls.2.2.2.1.mp h).1
  obtain ⟨dadeData⟩ :=
    OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1 hG hM data hP1
  -- (8.14)/(8.15): the kernel conjugation invariance is carried by the faithful datum.
  refine ⟨?_⟩
  exact
    { maximal := hM
      typeP := data
      type_alt := hType
      dadeData := dadeData }

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup are disjoint:
`W₁` complements `M' = [M,M]` in `M` (`TypePData.M_complement`), and `W₂ ≤ M'`
(`W₂ ≤ H ⊓ M'' ≤ H ≤ M'`), so `W₁ ⊓ W₂ ≤ W₁ ⊓ M' = ⊥`. -/
theorem typePData_disjoint_W1_W2 {M : Subgroup G} (data : TypePData M) :
    Disjoint data.W1 data.W2 := by
  have hW2D : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (inf_le_left.trans data.H_le)
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  have hxM : x ∈ M := data.W1_le hx1
  have hdisj := data.M_complement.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hmem1 : (⟨x, hxM⟩ : ↥M) ∈ (derivedInG M).subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr (hW2D hx2)
  have hmem2 : (⟨x, hxM⟩ : ↥M) ∈ data.W1.subgroupOf M :=
    Subgroup.mem_subgroupOf.mpr hx1
  exact Subtype.ext_iff.mp (hdisj hmem1 hmem2)

/-- The cyclic factors `W₁`, `W₂` of a type-`P` maximal subgroup have coprime orders.
`W = W₁ × W₂` is cyclic (`TypePData.W_cyclic`) and `W₁`, `W₂` are disjoint
(`typePData_disjoint_W1_W2`), so the multiplication map `↥W₁ × ↥W₂ →* ↥W` is injective;
a group embedding into the cyclic `↥W` is cyclic, and a finite cyclic product forces
coprime factor orders (`coprime_card_of_isCyclic_prod`). -/
theorem typePData_coprime_card_W1_W2 [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.Coprime (Nat.card ↥data.W1) (Nat.card ↥data.W2) := by
  have hcyc : IsCyclic ↥data.W := data.W_cyclic
  let : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := typePData_disjoint_W1_W2 data
  have hinj : Function.Injective
      ((Subgroup.inclusion hW1le).coprod (Subgroup.inclusion hW2le)) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, b⟩ hab
    rw [MonoidHom.coprod_apply] at hab
    have hG : (a : G) * (b : G) = 1 := by
      have h2 := congrArg (Subtype.val (p := fun x => x ∈ data.W)) hab
      simpa [Subgroup.coe_inclusion] using h2
    have ha1 : (a : G) = 1 := by
      have haW2 : (a : G) ∈ data.W2 := by
        rw [mul_eq_one_iff_eq_inv.mp hG]; exact data.W2.inv_mem b.2
      have hmem : (a : G) ∈ data.W1 ⊓ data.W2 := ⟨a.2, haW2⟩
      rw [disjoint_iff.mp hdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hb1 : (b : G) = 1 := by rw [ha1, one_mul] at hG; exact hG
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
  have : IsCyclic (↥data.W1 × ↥data.W2) := isCyclic_of_injective _ hinj
  exact coprime_card_of_isCyclic_prod (↥data.W1) (↥data.W2)

/-- The cyclic factor product `W = W₁ × W₂` of a type-`P` maximal subgroup has odd order.
`W ≤ G`, so `|W| ∣ |G|`, and `G` has odd order; a divisor of an odd number is odd. -/
theorem typePData_W_card_odd [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G)) : Odd (Nat.card ↥data.W) :=
  hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.W)

/-- For a type-`P` maximal subgroup the exceptional set `V = W − (W₁ ∪ W₂)` is nonempty:
the product `x·y` of a nontrivial `x ∈ W₁` and a nontrivial `y ∈ W₂` lies in `W` but in neither
factor, since `W₁` and `W₂` are disjoint (`typePData_disjoint_W1_W2`). -/
theorem typePData_typePV_nonempty {M : Subgroup G} (data : TypePData M) :
    (typePV M data).Nonempty := by
  obtain ⟨x, hxW1, hxne⟩ := (data.W1.bot_or_exists_ne_one).resolve_left data.W1_nontrivial
  obtain ⟨y, hyW2, hyne⟩ := (data.W2.bot_or_exists_ne_one).resolve_left data.W2_nontrivial
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := disjoint_iff.mp (typePData_disjoint_W1_W2 data)
  refine ⟨x * y, ?_⟩
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
  refine ⟨mul_mem (hW1le hxW1) (hW2le hyW2), ?_, ?_⟩
  · intro hxy
    have hy1 : y ∈ data.W1 := by
      have he : y = x⁻¹ * (x * y) := by group
      rw [he]; exact mul_mem (inv_mem hxW1) hxy
    exact hyne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hy1, hyW2⟩))
  · intro hxy
    have hx1 : x ∈ data.W2 := by
      have he : x = (x * y) * y⁻¹ := by group
      rw [he]; exact mul_mem hxy (inv_mem hyW2)
    exact hxne (Subgroup.mem_bot.mp (hdisj ▸ Subgroup.mem_inf.mpr ⟨hxW1, hx1⟩))

/-- **The type-`P` torus has order `|W| = w₁·w₂`** (`W = W₁ × W₂`).  The factors `W₁`, `W₂` are
disjoint (`typePData_disjoint_W1_W2`) subgroups of the cyclic — hence abelian — `W`
(`W = W₁ ⊔ W₂`), so realised inside `↥W` they are a normal complement pair and the order is the
product (`card_sup_eq_card_mul_card_of_disjoint_normal`).  Fundamental structural fact of the
type-`P` torus, used throughout §10--§11 (the `(4.5)` reducible characters, the `V^G` counting). -/
theorem typePData_card_W [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥data.W = Nat.card ↥data.W1 * Nat.card ↥data.W2 := by
  have hcyc : IsCyclic ↥data.W := data.W_cyclic
  let : CommGroup ↥data.W := hcyc.commGroup
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hBnorm : (data.W2.subgroupOf data.W).Normal := ⟨fun n hn g => by
    have h : g * n * g⁻¹ = n := by rw [mul_comm g n]; group
    rw [h]; exact hn⟩
  have hdisjAB : data.W1.subgroupOf data.W ⊓ data.W2.subgroupOf data.W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have h1 : ((x : ↥data.W) : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx.1
    have h2 : ((x : ↥data.W) : G) ∈ data.W2 := Subgroup.mem_subgroupOf.mp hx.2
    have hmem : ((x : ↥data.W) : G) ∈ data.W1 ⊓ data.W2 := ⟨h1, h2⟩
    rw [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have hsupAB : data.W1.subgroupOf data.W ⊔ data.W2.subgroupOf data.W = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hW1le hW2le, ← data.W_eq, Subgroup.subgroupOf_self]
  have hcard := OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
    (T := data.W1.subgroupOf data.W) (M := data.W2.subgroupOf data.W) hdisjAB
  rw [hsupAB, Nat.card_congr (Subgroup.topEquiv (G := ↥data.W)).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv] at hcard
  exact hcard

/-- **The exceptional set `V = W − (W₁ ∪ W₂)` has `|V| = w₁w₂ − w₁ − w₂ + 1`.**  Since `W₁, W₂ ⊆ W`
their union lies in `W`, so `|V| = |W| − |W₁ ∪ W₂|`; the factors meet only in `1`
(`typePData_disjoint_W1_W2`), so `|W₁ ∪ W₂| = w₁ + w₂ − 1`, and `|W| = w₁w₂`
(`typePData_card_W`).  This is the `|V^G| = |G:W|·(w₁w₂−w₁−w₂+1)` numerator of Peterfalvi (10.8). -/
theorem typePData_typePV_ncard [Finite G] {M : Subgroup G} (data : TypePData M) :
    (typePV M data).ncard
      = Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1 - Nat.card ↥data.W2 + 1 := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  -- set cardinalities of the subgroups
  have hcW1 : ((data.W1 : Set G)).ncard = Nat.card ↥data.W1 := (Nat.card_coe_set_eq _).symm
  have hcW2 : ((data.W2 : Set G)).ncard = Nat.card ↥data.W2 := (Nat.card_coe_set_eq _).symm
  have hcW : ((data.W : Set G)).ncard = Nat.card ↥data.W := (Nat.card_coe_set_eq _).symm
  -- `W₁ ∪ W₂ ⊆ W`
  have hsub : ((data.W1 : Set G) ∪ (data.W2 : Set G)) ⊆ (data.W : Set G) :=
    Set.union_subset hW1le hW2le
  -- `W₂ \ W₁ = W₂ \ {1}`: for `x ∈ W₂`, `x ∈ W₁ ↔ x = 1` (disjointness).
  have hW2diff : (data.W2 : Set G) \ (data.W1 : Set G) = (data.W2 : Set G) \ {1} := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    refine ⟨fun ⟨hx2, hx1⟩ => ⟨hx2, fun h => hx1 (h ▸ data.W1.one_mem)⟩,
      fun ⟨hx2, hxne⟩ => ⟨hx2, fun hx1 => hxne ?_⟩⟩
    have hmem : x ∈ data.W1 ⊓ data.W2 := ⟨hx1, hx2⟩
    rw [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
    exact hmem
  -- `|W₁ ∪ W₂| = w₁ + w₂ − 1` (decompose `W₁ ∪ W₂ = W₁ ⊔ (W₂ \ W₁)`, disjoint).
  have hunion : ((data.W1 : Set G) ∪ (data.W2 : Set G)).ncard
      = Nat.card ↥data.W1 + Nat.card ↥data.W2 - 1 := by
    have h2pos : 1 ≤ Nat.card ↥data.W2 := Nat.card_pos
    rw [← Set.union_sdiff_self (s := (data.W1 : Set G)) (t := (data.W2 : Set G)),
      Set.ncard_union_eq disjoint_sdiff_self_right (Set.toFinite _) (Set.toFinite _), hW2diff,
      Set.ncard_sdiff (Set.singleton_subset_iff.mpr data.W2.one_mem), Set.ncard_singleton,
      hcW1, hcW2]
    omega
  -- `V = W \ (W₁ ∪ W₂)` has `|V| = |W| − |W₁ ∪ W₂|`
  have hdiff : (typePV M data).ncard = ((data.W : Set G)).ncard
      - ((data.W1 : Set G) ∪ (data.W2 : Set G)).ncard := by
    rw [typePV, Set.ncard_sdiff hsub]
  rw [hdiff, hunion, hcW, typePData_card_W]
  have hw1ge : 1 < Nat.card ↥data.W1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W1_nontrivial
  have hw2ge : 1 < Nat.card ↥data.W2 := (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W2_nontrivial
  have hprod : Nat.card ↥data.W1 + Nat.card ↥data.W2 ≤ Nat.card ↥data.W1 * Nat.card ↥data.W2 :=
    Nat.add_le_mul hw1ge hw2ge
  omega

/-- For a type-`P` maximal subgroup, every `l ∈ W` stabilises the exceptional set `V` under
conjugation: `l ∈ N_G(V) = W` (`TypePData.normalizer_V` with `X = V`), so `(MulAut.conj l) • V = V`.
This is the `W`-stability input to the `|V^G|` TI-orbit count `ncard_conjClassSet_of_isTISubset`. -/
theorem typePData_W_normalizes_typePV [Finite G] {M : Subgroup G} (data : TypePData M) :
    ∀ l ∈ data.W, MulAut.conj l • (typePV M data) = typePV M data := by
  intro l hl
  have hlN : l ∈ Subgroup.normalizer (typePV M data) := by
    rw [data.normalizer_V (typePV M data) (typePData_typePV_nonempty data) Set.Subset.rfl]
    exact hl
  rw [Subgroup.mem_set_normalizer_iff] at hlN
  ext x
  simp only [Set.mem_smul_set, MulAut.smul_def, MulAut.conj_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact (hlN v).mp hv
  · intro hx
    exact ⟨l⁻¹ * x * l, (hlN _).mpr (by rw [show l * (l⁻¹ * x * l) * l⁻¹ = x by group]; exact hx),
      by group⟩

/-- **The conjugacy-saturation `V^G` of the exceptional set has `|V^G| = |G:W|·(w₁w₂−w₁−w₂+1)`.**
`V` is a TI-subset with normalizer `W` (`typePData_V_ti` + `typePData_W_normalizes_typePV`), so the
orbit count is `|V|·|G:W|` (`ncard_conjClassSet_of_isTISubset`), with `|V| = w₁w₂−w₁−w₂+1`
(`typePData_typePV_ncard`).  This is the `|V^G|` numerator of the Peterfalvi (10.8) TI-counting
(lines 89--91, the `(w₁w₂−w₁−w₂+1)/(w₁w₂)` term once divided by `|G|`). -/
theorem typePData_conjClassSet_typePV_ncard [Finite G] {M : Subgroup G} (data : TypePData M) :
    (conjClassSet (typePV M data)).ncard
      = (Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1 - Nat.card ↥data.W2 + 1)
        * data.W.index := by
  rw [OddOrder.BG.Ch4.S14.ncard_conjClassSet_of_isTISubset (OddOrder.Peterfalvi.S10.typePData_V_ti
      data)
    (typePData_W_normalizes_typePV data), typePData_typePV_ncard]

/-- **The (10.8) `V`-capture step** (Peterfalvi p. 60, the `x ∈ S − HU` branch of the `G₁`
covering, in the (2.1)-style coprime-coset form): an element of a type-`P` maximal `S` outside
the derived subgroup whose order is not coprime to `|W₂|` is conjugate into `V = W ∖ (W₁ ∪ W₂)`.

The commuting `π`-decomposition `x = a·b` (`π = {|W₁|}`, `exists_isPiElement_mul`) has
`b ∈ [S,S]` (its image in the order-`|W₁|` quotient is a `π′`-element), so `a ∉ [S,S]`; Sylow
conjugacy moves the `|W₁|`-element `a` into `W₁` (`|W₁|` prime and coprime to `|[S,S]|`, so `W₁`
is a full Sylow of `S`), carrying `b` into `[S,S] ⊓ C_G(w) = W₂` (`centralizer_W1`).  If the
`W₂`-part is trivial the conjugate lies in `W₁`, forcing the order of `x` to divide `|W₁|`,
coprime to `|W₂|` (`typePData_coprime_card_W1_W2`) — excluded; so both parts are nontrivial and
the conjugate lies in `V`. -/
theorem exists_conj_mem_typePV_of_not_mem_derived [Finite G] {S : Subgroup G}
    (data : TypePData S) (hprime : (Nat.card ↥data.W1).Prime)
    (hcop : Nat.Coprime (Nat.card ↥(derivedInG S)) (Nat.card ↥data.W1))
    {x : G} (hxS : x ∈ S) (hxnot : x ∉ derivedInG S)
    (hxord : ¬ (orderOf x).Coprime (Nat.card ↥data.W2)) :
    ∃ s ∈ S, s * x * s⁻¹ ∈ typePV S data := by
  classical
  set p : ℕ := Nat.card ↥data.W1 with hp
  -- the commuting `{p}`-decomposition of `x`, inside `⟨x⟩ ≤ S`
  obtain ⟨a, b, hab, hcomm, haπ, hbπ', haz, hbz⟩ :=
    OddOrder.GroupTheory.exists_isPiElement_mul ({p} : Set ℕ) x
  have hzle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
  have haS : a ∈ S := hzle haz
  have hbS : b ∈ S := hzle hbz
  -- `p ∤ orderOf b` (a `{p}ᶜ`-element)
  have hpb : ¬ p ∣ orderOf b := fun hdvd =>
    (hbπ' p (Nat.mem_primeFactors.mpr ⟨hprime, hdvd, (orderOf_pos b).ne'⟩)) rfl
  -- `b ∈ [S,S]`: its image in the order-`p` quotient `↥S ⧸ [S,S]` is trivial
  have hNnorm : ((derivedInG S).subgroupOf S).Normal := by
    have heq : (derivedInG S).subgroupOf S = commutator ↥S := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective S.subtype_injective]
    rw [heq]; infer_instance
  have hbS' : b ∈ derivedInG S := by
    have hql : orderOf ((QuotientGroup.mk' ((derivedInG S).subgroupOf S)) ⟨b, hbS⟩)
        ∣ orderOf (⟨b, hbS⟩ : ↥S) := orderOf_map_dvd _ _
    have hqr : orderOf ((QuotientGroup.mk' ((derivedInG S).subgroupOf S)) ⟨b, hbS⟩) ∣ p := by
      have hcard : Nat.card (↥S ⧸ (derivedInG S).subgroupOf S) = p := by
        rw [hp]; exact data.card_W1_eq_derived_index.symm
      exact hcard ▸ orderOf_dvd_natCard _
    have hob : orderOf (⟨b, hbS⟩ : ↥S) = orderOf b :=
      (orderOf_injective S.subtype S.subtype_injective ⟨b, hbS⟩).symm
    have h1 : orderOf ((QuotientGroup.mk' ((derivedInG S).subgroupOf S)) ⟨b, hbS⟩) = 1 := by
      rcases (Nat.dvd_prime hprime).mp hqr with h | h
      · exact h
      · exact absurd (h ▸ (hob ▸ hql)) hpb
    have hker := orderOf_eq_one_iff.mp h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff (⟨b, hbS⟩ : ↥S)] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  -- hence the `{p}`-part `a` is outside `[S,S]`; in particular `a ≠ 1`
  have haS' : a ∉ derivedInG S := fun haIn => hxnot (hab ▸ mul_mem haIn hbS')
  have hane : a ≠ 1 := fun h => haS' (h ▸ one_mem _)
  -- `orderOf a` is a `p`-power
  have hopow : orderOf a = p ^ (orderOf a).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd (orderOf_pos a).ne'
      (fun {d} hd hdvd => Set.mem_singleton_iff.mp
        (haπ d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, (orderOf_pos a).ne'⟩)))
  -- Sylow: conjugate the `p`-element `a` into `W₁`, inside `↥S`
  have : Fact p.Prime := ⟨hprime⟩
  have hcardS : Nat.card ↥S = Nat.card ↥(derivedInG S) * p := by
    have h := Subgroup.card_mul_index ((derivedInG S).subgroupOf S)
    have hle : derivedInG S ≤ S := Subgroup.map_subtype_le _
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
    rw [← h, hp, data.card_W1_eq_derived_index]
  have hfacS : (Nat.card ↥S).factorization p = 1 := by
    rw [hcardS, Nat.factorization_mul (Nat.card_pos).ne' (hprime.pos).ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        ((Nat.Prime.coprime_iff_not_dvd hprime).mp hcop.symm),
      Nat.Prime.factorization_self hprime]
  have hQcard : Nat.card ↥(data.W1.subgroupOf S) = p ^ (Nat.card ↥S).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv, hfacS, pow_one, hp]
  have hoaS : orderOf (⟨a, haS⟩ : ↥S) = orderOf a :=
    (orderOf_injective S.subtype S.subtype_injective ⟨a, haS⟩).symm
  have hpgroup : IsPGroup p ↥(Subgroup.zpowers (⟨a, haS⟩ : ↥S)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hoaS, hopow])
  obtain ⟨P, hPle⟩ := hpgroup.exists_le_sylow
  obtain ⟨g, hgPQ⟩ :=
    MulAction.exists_smul_eq ↥S P (Sylow.ofCard (data.W1.subgroupOf S) hQcard)
  have haP : (⟨a, haS⟩ : ↥S) ∈ (P : Subgroup ↥S) := hPle (Subgroup.mem_zpowers _)
  have haQ : g * (⟨a, haS⟩ : ↥S) * g⁻¹ ∈ data.W1.subgroupOf S := by
    have hsub : ((g • P : Sylow p ↥S) : Subgroup ↥S) = data.W1.subgroupOf S := by
      rw [hgPQ, Sylow.coe_ofCard]
    rw [← hsub, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ haP
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  -- transport to `G`: `w = s·a·s⁻¹ ∈ W₁`, `u = s·b·s⁻¹ ∈ [S,S] ⊓ C_G(w) = W₂`
  set s : G := (g : G) with hs
  set w : G := s * a * s⁻¹ with hw
  set u : G := s * b * s⁻¹ with hu
  have hwW1 : w ∈ data.W1 := by
    have h := Subgroup.mem_subgroupOf.mp haQ
    simpa [hw, hs] using h
  have hwne : w ≠ 1 := by
    intro h
    apply hane
    have := congrArg (fun z => s⁻¹ * z * s) h
    simpa [hw, mul_assoc] using this
  have huS' : u ∈ derivedInG S := by
    have := hNnorm.conj_mem ⟨b, hbS⟩ (Subgroup.mem_subgroupOf.mpr hbS') g
    have hcoe : ((g * (⟨b, hbS⟩ : ↥S) * g⁻¹ : ↥S) : G) ∈ derivedInG S :=
      Subgroup.mem_subgroupOf.mp this
    simpa [hu, hs] using hcoe
  have hcomm' : Commute w u := by
    have := hcomm.map (MulAut.conj s).toMonoidHom
    simpa [hw, hu, MulAut.conj_apply] using this
  have huW2 : u ∈ data.W2 := by
    rw [← data.centralizer_W1 w hwW1 hwne]
    exact Subgroup.mem_inf.mpr ⟨huS',
      Subgroup.mem_centralizer_singleton_iff.mpr hcomm'.symm.eq⟩
  have hconj : s * x * s⁻¹ = w * u := by
    rw [hw, hu, ← hab]; group
  -- the `W₂`-part is nontrivial: otherwise `orderOf x ∣ |W₁|`, coprime to `|W₂|`
  have hune : u ≠ 1 := by
    intro h1
    apply hxord
    have hxw : s * x * s⁻¹ = w := by rw [hconj, h1, mul_one]
    have hoxw : orderOf x = orderOf w := by
      have := orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective x
      rw [← this]
      simp [MulAut.conj_apply, hxw]
    have hdvd : orderOf x ∣ p := by
      rw [hoxw]
      have h1 : orderOf w = orderOf (⟨w, hwW1⟩ : ↥data.W1) :=
        orderOf_injective data.W1.subtype data.W1.subtype_injective ⟨w, hwW1⟩
      rw [h1, hp]
      exact orderOf_dvd_natCard _
    exact Nat.Coprime.coprime_dvd_left hdvd (hp ▸ typePData_coprime_card_W1_W2 data)
  -- assemble: `w·u ∈ V = W ∖ (W₁ ∪ W₂)`
  have hgS : s ∈ S := g.2
  refine ⟨s, hgS, ?_⟩
  rw [hconj]
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  have hdisj := typePData_disjoint_W1_W2 data
  simp only [typePV, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]
  refine ⟨mul_mem (hW1le hwW1) (hW2le huW2), fun hmem => ?_, fun hmem => ?_⟩
  · have huW1 : u ∈ data.W1 := by
      have := mul_mem (inv_mem hwW1) hmem
      rwa [inv_mul_cancel_left] at this
    exact hune (Subgroup.mem_bot.mp (hdisj.le_bot ⟨huW1, huW2⟩))
  · have hwW2 : w ∈ data.W2 := by
      have := mul_mem hmem (inv_mem huW2)
      rwa [mul_inv_cancel_right] at this
    exact hwne (Subgroup.mem_bot.mp (hdisj.le_bot ⟨hwW1, hwW2⟩))

/-- **A `p`-element whose prime divides a Hall subgroup's order is conjugate into it** (the
(8.11)-consumption step of the (10.8) covering).  The Sylow `p`-subgroups of `H` are full Sylow
`p`-subgroups of `G` (the Hall index is prime to `p`), and every `p`-element lies in some Sylow
`p`-subgroup, so Sylow conjugacy lands `a` in a conjugate of `H`.  ⚠ Hoist candidate
(`IsHallSubgroup`-generic, no type-`P` content; natural home = Isaacs Ch03 Hall theory). -/
theorem exists_conj_mem_of_isHallSubgroup_of_orderOf_pow [Finite G] {H : Subgroup G}
    (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥H).primeFactors H)
    {p k : ℕ} (hp : p.Prime) (hpH : p ∣ Nat.card ↥H)
    {a : G} (hoa : orderOf a = p ^ k) :
    ∃ g : G, g * a * g⁻¹ ∈ H := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  -- the Hall index is prime to `p`, so `p` has full multiplicity in `H`
  have hidx : ¬ p ∣ H.index := fun hdvd =>
    hHall.2 p (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨hp, hpH, Nat.card_pos.ne'⟩)
  have hfac : (Nat.card G).factorization p = (Nat.card ↥H).factorization p := by
    rw [← Subgroup.card_mul_index H,
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  -- a Sylow `p`-subgroup of `H`, pushed to `G`, is a full Sylow `p`-subgroup of `G`
  obtain ⟨Q⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hQmap : Nat.card ↥((Q : Subgroup ↥H).map H.subtype)
      = p ^ (Nat.card G).factorization p := by
    rw [Nat.card_congr
        (Subgroup.equivMapOfInjective (Q : Subgroup ↥H) H.subtype
          H.subtype_injective).symm.toEquiv,
      Q.card_eq_multiplicity, hfac]
  -- Sylow conjugacy moves `a` into that copy of `H`
  have hpa : IsPGroup p ↥(Subgroup.zpowers a) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hoa])
  obtain ⟨P, hPle⟩ := hpa.exists_le_sylow
  obtain ⟨g, hgPQ⟩ := MulAction.exists_smul_eq G P
    (Sylow.ofCard ((Q : Subgroup ↥H).map H.subtype) hQmap)
  have haP : a ∈ (P : Subgroup G) := hPle (Subgroup.mem_zpowers a)
  have hmem : g * a * g⁻¹ ∈ (Q : Subgroup ↥H).map H.subtype := by
    have hsub : ((g • P : Sylow p G) : Subgroup G) = (Q : Subgroup ↥H).map H.subtype := by
      rw [hgPQ, Sylow.coe_ofCard]
    rw [← hsub, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ haP
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  exact ⟨g, Subgroup.map_subtype_le _ hmem⟩

/-- **The `G₁`-covering core of Peterfalvi (10.8)** (p. 60 lines 89–91): with the partner data
supplied — `|W₁|` prime and coprime to `|[S,S]|`, `H` a Hall subgroup of `G` ((8.11)),
centralizers of `H#`-elements captured in `S` ((8.6.a)), and the Frobenius-kernel capture
`C_{[S,S]}(H#) ⊆ H` (the (10.7) consequence) — every element whose order is not coprime to
`|W₂|` lies in the conjugates of `H# = H ∖ {1}` or of `V = W ∖ (W₁ ∪ W₂)`.

Peterfalvi's route: an order-`p` power `a` of `x` (`p ∣ gcd(|x|, |W₂|)`) is conjugate into `H`
(`W₂ ≤ H` Hall), the conjugate `y` of `x` centralises `b = a^g ∈ H#`, so `y ∈ S`; inside
`[S,S]` the Frobenius kernel absorbs it (`y ∈ H#`), and outside, the coprime-coset analysis
(`exists_conj_mem_typePV_of_not_mem_derived`) lands it in `V`. -/
theorem mem_conjClassSet_sharpH_or_typePV_of_not_coprime [Finite G] {S : Subgroup G}
    (data : TypePData S) (hprime : (Nat.card ↥data.W1).Prime)
    (hcop : Nat.Coprime (Nat.card ↥(derivedInG S)) (Nat.card ↥data.W1))
    (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥data.H).primeFactors data.H)
    (hcent : ∀ b ∈ data.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ S)
    (hfrobcap : ∀ b ∈ data.H, b ≠ 1 → ∀ y ∈ derivedInG S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ data.H)
    {x : G} (hxord : ¬ (orderOf x).Coprime (Nat.card ↥data.W2)) :
    x ∈ conjClassSet ((data.H : Set G) \ {1}) ∪ conjClassSet (typePV S data) := by
  classical
  -- a prime `p` dividing both `orderOf x` and `|W₂|`, and the order-`p` power `a` of `x`
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hxord
  have hpx : p ∣ orderOf x := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpw : p ∣ Nat.card ↥data.W2 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hxne1 : orderOf x ≠ 1 := fun h =>
    hxord (by rw [h]; exact Nat.coprime_one_left _)
  set a := x ^ (orderOf x / p) with ha
  have hoa : orderOf a = p := orderOf_pow_orderOf_div (orderOf_pos x).ne' hpx
  have hane : a ≠ 1 := fun h => hp.ne_one (by rw [← hoa, h, orderOf_one])
  have hcommxa : Commute x a := (Commute.refl x).pow_right _
  -- conjugate `a` into `H` ((8.11) Hall step; `p ∣ |W₂| ∣ |H|`)
  have hpH : p ∣ Nat.card ↥data.H :=
    hpw.trans (Subgroup.card_dvd_of_le (data.W2_le.trans inf_le_left))
  obtain ⟨g, hga⟩ := exists_conj_mem_of_isHallSubgroup_of_orderOf_pow hHall hp hpH
    (k := 1) (by rw [hoa, pow_one])
  -- the conjugate `y = x^g` centralises `b = a^g ∈ H#`, so `y ∈ S` ((8.6.a))
  set b := g * a * g⁻¹ with hb
  set y := g * x * g⁻¹ with hy
  have hbne : b ≠ 1 := by
    intro h
    apply hane
    have := congrArg (fun z => g⁻¹ * z * g) h
    simpa [hb, mul_assoc] using this
  have hycomm : y ∈ Subgroup.centralizer ({b} : Set G) := by
    have hc := hcommxa.map (MulAut.conj g).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz, hb, hy]
    exact hc.symm.eq
  have hyS : y ∈ S := hcent b hga hbne hycomm
  have hoy : orderOf y = orderOf x := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
    simpa [hy, MulAut.conj_apply] using this
  by_cases hyd : y ∈ derivedInG S
  · -- inside `[S,S]`: the Frobenius kernel absorbs the centralising element
    left
    have hyH : y ∈ data.H := hfrobcap b hga hbne y hyd hycomm
    have hyne : y ≠ 1 := fun h => hxne1 (by rw [← hoy, h, orderOf_one])
    exact ⟨y, ⟨hyH, hyne⟩, g⁻¹, by rw [hy]; group⟩
  · -- outside `[S,S]`: the coprime-coset analysis lands in `V`
    right
    obtain ⟨s, _, hsv⟩ := exists_conj_mem_typePV_of_not_mem_derived data hprime hcop hyS hyd
      (by rw [hoy]; exact hxord)
    exact ⟨s * y * s⁻¹, hsv, (s * g)⁻¹, by rw [hy]; group⟩

/-- `W₂ ≤ M` for type-`P` data (`W₂ ≤ H ⊓ M'' ≤ M' ≤ M`). -/
theorem typePData_W2_le_self {M : Subgroup G} (data : TypePData M) : data.W2 ≤ M :=
  (data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))).trans
    (Subgroup.map_subtype_le _)

/-- `W ≤ M` for type-`P` data (`W = W₁ ⊔ W₂`, both `≤ M`). -/
theorem typePData_W_le_self {M : Subgroup G} (data : TypePData M) : data.W ≤ M :=
  data.W_eq ▸ sup_le data.W1_le (typePData_W2_le_self data)

/-- The §6 `↥M`-level `W = W₁.subgroupOf M ⊔ W₂.subgroupOf M` is `W.subgroupOf M`: the `subgroupOf`
order-iso on subgroups `≤ M` preserves joins. -/
theorem typePData_sup_subgroupOf_eq {M : Subgroup G} (data : TypePData M) :
    data.W1.subgroupOf M ⊔ data.W2.subgroupOf M = data.W.subgroupOf M := by
  rw [← Subgroup.subgroupOf_sup data.W1_le (typePData_W2_le_self data), ← data.W_eq]

/-- The `W ≤ M ≤ G` isomorphism `↥W ≃* ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)` used to transport the
§6 `↥M`-level `ω`-grid (built on `W₁.subgroupOf M ⊔ W₂.subgroupOf M`) to the §5 `G`-level TI-cyclic
hypothesis (built on `W ≤ G`). This is the `e` reconstructed inline in `alignedOmegaSigmaGrid`;
named
here so the (10.6) column-structure argument can reason about how it respects the `W₁/W₂`
decomposition.  Both `subgroupOfEquivOfLe.symm` and `subgroupCongr` preserve the underlying
`G`-element, so does `e` (`typePData_WEquiv_coe`). -/
noncomputable def typePData_WEquiv {M : Subgroup G} (data : TypePData M) :
    ↥data.W ≃* ↥(data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) :=
  (Subgroup.subgroupOfEquivOfLe (typePData_W_le_self data)).symm.trans
    (MulEquiv.subgroupCongr (typePData_sup_subgroupOf_eq data).symm)

/-- `typePData_WEquiv` preserves the underlying `G`-element. -/
@[simp] theorem typePData_WEquiv_coe {M : Subgroup G} (data : TypePData M) (w : ↥data.W) :
    (((typePData_WEquiv data w : ↥(data.W1.subgroupOf M ⊔ data.W2.subgroupOf M)) : ↥M) : G)
      = (w : G) := rfl

/-- `typePData_WEquiv` maps the `W₁`-block into the `W₁`-block: if `w ∈ W₁.subgroupOf W` then
`e w ∈ (W₁.subgroupOf M).subgroupOf (W₁.subgroupOf M ⊔ W₂.subgroupOf M)`.  Underlying-element
preservation reduces both memberships to `(w : G) ∈ W₁`. -/
theorem typePData_WEquiv_mem_W1 {M : Subgroup G} (data : TypePData M) {w : ↥data.W}
    (hw : w ∈ (data.W1.subgroupOf data.W)) :
    typePData_WEquiv data w ∈
      (data.W1.subgroupOf M).subgroupOf (data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, typePData_WEquiv_coe]
  exact Subgroup.mem_subgroupOf.mp hw

/-- `typePData_WEquiv` maps the `W₂`-block into the `W₂`-block (see `typePData_WEquiv_mem_W1`). -/
theorem typePData_WEquiv_mem_W2 {M : Subgroup G} (data : TypePData M) {w : ↥data.W}
    (hw : w ∈ (data.W2.subgroupOf data.W)) :
    typePData_WEquiv data w ∈
      (data.W2.subgroupOf M).subgroupOf (data.W1.subgroupOf M ⊔ data.W2.subgroupOf M) := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, typePData_WEquiv_coe]
  exact Subgroup.mem_subgroupOf.mp hw

open scoped FiniteInduce in
/-- **§10 → §5 ω-grid bridge (gate #3)**: a type-`P` maximal subgroup's cyclic factor
`W = W₁ × W₂`, with the exceptional set `V = W − (W₁ ∪ W₂)`, is a Peterfalvi (3.1) TI-cyclic
normalizer setup in the ambient group `G`.  Every structural field is read off from the
`TypePData`: the `W`-block is disjoint (`typePData_disjoint_W1_W2`) / coprime
(`typePData_coprime_card_W1_W2`) / cyclic (`W_cyclic`), oddness comes from `Odd |G|`, and `V` is
`W`-normalized because the cyclic `W` is abelian.

The ambient TI property `V_ti : IsTISubset V W` — Peterfalvi (4.6.b), the `G`-version of (4.3.a) —
is the one field that does not read off directly from the `TypePData` fields; it is supplied by the
companion `typePData_V_ti`, which derives it from `normalizer_V` together with the cyclic factor
structure (`W₁`, `W₂` are the unique, hence characteristic, subgroups of their orders in the cyclic
`W`).  This makes the bridge **unconditional** (no external TI hypothesis; closes issue 1005).

Through this bridge the entire §5 ω/σ-grid (`TICyclicHypothesis.omegaGrid`, `omegaSigmaGrid`,
`sigmaIntegral`) becomes available for the §10 character analysis ((10.2)–(10.10)). -/
noncomputable def typePData_toTICyclicHypothesis [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis G where
  W := data.W
  W1 := data.W1
  W2 := data.W2
  W1_le_W := by rw [data.W_eq]; exact le_sup_left
  W2_le_W := by rw [data.W_eq]; exact le_sup_right
  W1_nontrivial := data.W1_nontrivial
  W2_nontrivial := data.W2_nontrivial
  W_sup := data.W_eq.symm
  W_disjoint := typePData_disjoint_W1_W2 data
  W_card_coprime := typePData_coprime_card_W1_W2 data
  W_card_odd := typePData_W_card_odd data hodd
  W_cyclic := data.W_cyclic
  V := typePV M data
  V_subset_sharp := by
    intro v hv
    rw [OddOrder.Peterfalvi.S04.mem_sharp]
    refine ⟨Set.mem_univ v, fun heq => hv.2 (Or.inl ?_)⟩
    rw [heq]; exact data.W1.one_mem
  V_subset_W := fun _ hv => hv.1
  W_normalizes_V := by
    intro w v hv
    have hcomm : Commute (w : G) v :=
      S06.commute_of_mem_of_isCyclic data.W_cyclic w.2 hv.1
    have h3 : (w : G) * v * (w : G)⁻¹ = v := by rw [hcomm.eq, mul_inv_cancel_right]
    rw [h3]; exact hv
  V_ti := OddOrder.Peterfalvi.S10.typePData_V_ti data

/-- **Peterfalvi (4.2.a) Hall coprimality** (issue 1006): for a type-`P` maximal subgroup `M`,
`gcd(|M'|, |W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M' = [M,M]` in `M`.

A bare complement need not be Hall, but the κ-Hall structure of a type-`P` maximal supplies it: a
Hall `κ(M)`-subgroup `K ≤ M` (`exists_isHallSubgroup_kappa_ge`) is cyclic (BG Theorem A, the
**sorry-free faithful** `S15.typeP_auxiliary_structure`), so it complements `M'` in `M`
(`typeP_derivedInG_isComplement_kappaHall`); hence `gcd(|K|, |M'|) = 1`
(`IsHallSubgroup.coprime_index`), and `|K| = [M:M'] = |W₁|` (`card_kappaHall_eq_derived_index`,
`TypePData.card_W1_eq_derived_index`).  Discharges the `hHall` obligation of the §10 → §6 bridge. -/
theorem typePData_W1_hall_coprime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K ≤ M`.
  obtain ⟨K, hKM, hK, -⟩ :=
    OddOrder.BG.Ch4.S14.exists_isHallSubgroup_kappa_ge hG hM (X := ⊥) bot_le (by simp)
  -- A `(κ(M) ∪ σ(M))'`-Hall subgroup `U` (needed only to invoke BG Theorem A).
  obtain ⟨U', hU'hall, -⟩ :=
    Ch03.hall_D (G := ↥M)
      (π := (OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U := ⊥) (by simp)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'hall
  -- `K` is cyclic by BG Theorem A (the sorry-free faithful `typeP_auxiliary_structure`).
  have : IsCyclic ↥K :=
    (OddOrder.BG.Ch4.S15.typeP_auxiliary_structure hG hM hKM (Subgroup.map_subtype_le U')
      hK rfl hU).2.1
  -- Coprimality `gcd(|K|, |M'|) = 1` from the κ-Hall complement (mirrors S14_TypePComplement).
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  -- `|K| = [M:M'] = |W₁|`.
  have hKW1 : Nat.card ↥K = Nat.card ↥data.W1 := by
    rw [OddOrder.BG.Ch4.S16.card_kappaHall_eq_derived_index hG hM hP hKM hK,
      data.card_W1_eq_derived_index]
  rw [Nat.coprime_comm, ← hKW1]; exact hCop

/-- **§10 → §6 (4.2) bridge, structural part**: build the Peterfalvi Hypothesis (4.2)
`S06.Hypothesis ↥M` from a type-`P` maximal subgroup's `TypePData`, with `L = M`, `K = M' = [M,M]`
and the (8.4) cyclic factors `W₁, W₂` transported into `↥M` via `subgroupOf`.  Structural fields
come from `TypePData`: `M_complement → isComplement`, `centralizer_W1 → centralizer_W2` (through the
ambient↔`↥M` centralizer transport `S03h.centralizer_subgroupOf`), and cyclicity / oddness through
the order-preserving `subgroupOfEquivOfLe`; `K ⊴ ↥M` because `K = commutator ↥M`.

The Hall coprimality `card_coprime` (`gcd(|M'|,|W₁|) = 1`, i.e. `W₁` is a *Hall* complement to `M'`
in `M`) is **not** derivable from `TypePData` alone — a complement need not be Hall — so it is taken
as the input `hHall`.  This is the Peterfalvi (4.2.a) Hall condition, dischargeable at call sites
from the κ-Hall structure of a type-`P` maximal (`typeP_derivedInG_isComplement_kappaHall` +
`IsHallSubgroup.coprime_index`, since `|W₁| = [M:M'] = |κ-Hall K|`).  See issue 1006. -/
def typePData_toS06Hypothesis [Finite G] {M : Subgroup G} (data : TypePData M)
    (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥M := by
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hW2leM' : data.W2 ≤ derivedInG M :=
    data.W2_le.trans (le_trans inf_le_right (Subgroup.map_subtype_le _))
  have hW2leM : data.W2 ≤ M := hW2leM'.trans hM'le
  haveI := data.W1_cyclic
  haveI := data.W2_cyclic
  exact
    { K := (derivedInG M).subgroupOf M
      W1 := data.W1.subgroupOf M
      W2 := data.W2.subgroupOf M
      K_normal := by
        rw [show (derivedInG M).subgroupOf M = commutator ↥M by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
        infer_instance
      isComplement := data.M_complement
      W1_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W1_nontrivial (disjoint_self.mp (hdisj.mono_right data.W1_le))
      W1_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe data.W1_le).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.W1_le).injective
      card_coprime := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
        exact hHall
      W2_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => data.W2_nontrivial (disjoint_self.mp (hdisj.mono_right hW2leM))
      W2_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hW2leM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hW2leM).injective
      W2_le_K := Subgroup.comap_mono hW2leM'
      centralizer_W2 := by
        intro x hx1 hx2
        have hxW1 : (x : G) ∈ data.W1 := Subgroup.mem_subgroupOf.mp hx1
        have hxne : (x : G) ≠ 1 := fun h => hx2 (Subtype.ext h)
        have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = data.W2 := by
          rw [inf_comm]; exact data.centralizer_W1 (x : G) hxW1 hxne
        rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
        simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]
      W_odd := by
        rw [← Subgroup.subgroupOf_sup data.W1_le hW2leM,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le data.W1_le hW2leM)).toEquiv,
          ← data.W_eq]
        exact typePData_W_card_odd data hodd }

/-- The §10 Hypothesis (10.1) for a type III/IV/V maximal subgroup `M` exhibits `M` as a *BG*
type-`P` maximal (`(κ(M)).Nonempty`).  By BG Proposition 16.1
(`proposition_type_classification`), each Peterfalvi type III/IV/V maps to `S14.IsTypeP1`,
hence to `S14.IsTypeP`.  This is the BG type-`P`
input needed to discharge the Hall coprimality `typePData_W1_hall_coprime`. -/
theorem Hypothesis.bgTypeP [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) : OddOrder.BG.Ch4.S14.IsTypeP M := by
  have hclass := OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.maximal
  rcases hyp.type_alt with h | h | h
  · exact (hclass.2.2.1.mp (Or.inl h)).1.1
  · exact (hclass.2.2.1.mp (Or.inr h)).1.1
  · exact (hclass.2.2.2.1.mp h).1.1

open scoped FiniteInduce in
/-- **§10 → §6 (4.2)+Dade bridge**: from the §10 Hypothesis (10.1) for a type-`P` maximal subgroup
`M`, build the §6 certain-type Hypothesis `S06.CertainTypeHypothesis (A₀(M)) M`.  The structural
(4.2) part is `typePData_toS06Hypothesis`; the Dade datum is the §10 `dadeData.dade` (already a
`S04.Hypothesis G (typePA0 M typeP) M`), so no new Dade construction is needed.  This unlocks the
entire §6 μ/ω/ζ machinery with `L = M`, the common source of (10.2), (10.3) and the `μ`-grid.

The Hall coprimality is discharged internally via `typePData_W1_hall_coprime` (using the BG
type-`P` from `Hypothesis.bgTypeP`), so this bridge is **unconditional** — no external `hHall`
input (closes issue 1006 for the §10 consumer). -/
def Hypothesis.toCertainTypeHypothesis [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.CertainTypeHypothesis (typePA0 M hyp.typeP) M :=
  haveI := hyp.finiteG
  { toHypothesis := typePData_toS06Hypothesis hyp.typeP hodd
      (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
    dade := hyp.dadeData.dade }

open scoped FiniteInduce in
/-- **Peterfalvi (8.15) for type `P` / the (10.1) sentence "Hypothesis (4.6) holds with `L = M`,
`K = M'`, `A = A(M)`, `A₀ = A₀(M)`, `H = M_s`"**: the §10 `Hypothesis` instantiates the §4/§6
Hypothesis (4.6) carrier `S06.Hypothesis46 (A(M)) M`.

Field sources:
* the (4.2) structural part and the `A`-side Dade datum: `toCertainTypeHypothesis`, with the
  Dade hypothesis restricted from `A₀(M)` to the `M`-stable `A(M)` (`S04.Hypothesis.restrict` +
  `le_normalizer_typePA`, as in `toHypothesis71`);
* the ambient (3.1) TI-cyclic data (4.6.b): `typePData_toTICyclicHypothesis`, whose `W`, `W₁`,
  `W₂`, `V = W − (W₁ ∪ W₂)` are the `TypePData` fields — the `subgroupOf`-vs-ambient matching
  `tic_W1`/`tic_W2` is `Subgroup.map_subgroupOf_eq_of_le`, and `tic_V` is definitional;
* (4.6.c): `H := K = M'` (the (10.1) choice `H = M_s`, which equals `M'` for types III/IV and,
  via `U = ⊥`, also for type V), so `W₂ ≤ H ≤ K` are inherited;
* (4.6.d): the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A` is trivial for `H = K`:
  `A(M) = (M')# = K#` (`typePA_eq_sharpSubgroup_derivedInG`) already contains every
  nonidentity element of `K`;
* (4.6.d)/(4.6.e): the `A₀`-side Dade datum and isometry are **definitionally** the (8.15)
  §10 data `hyp.dadeData.dade` / its `fullDadeIsometryData`: `A(M) ∪ conjClassSetIn M tic.V`
  unfolds to `typePA0 M` (`tic.V = typePV M` by construction) — the payoff of stating both
  (8.10) `typePA0` and (4.6.d) with `conjClassSetIn`.

This closes the instantiation gap flagged in issue 9004 and lets the §10 grid consume the §6
(4.8)/(4.10) Dade identities (`certainType_diff_dade_eq`, `fourCorner_dade_eq`) — the `h48`/`h410`
threads of the (11.8.3) `β`-reality argument. -/
noncomputable def Hypothesis.toHypothesis46 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) :
    OddOrder.Peterfalvi.S06.Hypothesis46 (typePA M hyp.typeP) M :=
  haveI := hyp.finiteG
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  { toHypothesis := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
    dade := hyp.dadeData.dade.restrict Set.subset_union_left hnorm
    tic := typePData_toTICyclicHypothesis hyp.typeP hodd
    tic_W1 := (Subgroup.map_subgroupOf_eq_of_le hyp.typeP.W1_le).symm
    tic_W2 := (Subgroup.map_subgroupOf_eq_of_le (typePData_W2_le_self hyp.typeP)).symm
    tic_V := rfl
    subH := (hyp.toCertainTypeHypothesis hG hodd).K
    subH_normal := (hyp.toCertainTypeHypothesis hG hodd).K_normal
    W2_le_subH := (hyp.toCertainTypeHypothesis hG hodd).W2_le_K
    subH_le_K := le_refl _
    A_covers := fun _ _ _ x hx hx1 => by
      rw [typePA_eq_sharpSubgroup_derivedInG]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2,
        fun h1 => hx1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h1))⟩
    dade0 := hyp.dadeData.dade
    tau := hyp.dadeData.dade.fullDadeIsometryData }

/-- **A finite non-perfect group has a non-trivial linear character.**  If `commutator K ≠ ⊤`
(the abelianization `K/[K,K]` is non-trivial), there is a non-trivial degree-one irreducible
character of `K`: a non-trivial element of `K/[K,K]` is separated by some `φ : (K/[K,K]) →* ℂˣ`
(Pontryagin duality over `ℂ`, `exists_apply_ne_one_of_hasEnoughRootsOfUnity`), pulled back along
`K ↠ K/[K,K]`.  This supplies the non-principal degree-`1` character of `M' = [M,M]` whose induction
to `M` is the (10.2) character `ζ`. -/
theorem exists_nontrivial_linearIrreducibleCharacter {K : Type*} [Group K] [Finite K]
    (hK : commutator K ≠ ⊤) :
    ∃ θ : IrreducibleCharacter K, θ ≠ trivialIrreducibleCharacter K ∧
      (θ : ClassFunction K ℂ) 1 = 1 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : K, a ∉ commutator K := by
    by_contra h
    push Not at h
    exact hK (top_le_iff.mp fun x _ => h x)
  have : Finite (Abelianization K) := Quotient.finite _
  have hā : (Abelianization.of a) ≠ 1 := by
    rw [ne_eq, ← MonoidHom.mem_ker, Abelianization.ker_of]; exact ha
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    (G := Abelianization K) (M := ℂ) hā
  set ψ : K →* ℂˣ := φ.comp Abelianization.of with hψdef
  have hψ : ψ ≠ 1 := fun h => hφ (by rw [← MonoidHom.comp_apply, ← hψdef, h, MonoidHom.one_apply])
  refine ⟨linearIrreducibleCharacter ψ, ?_, linearIrreducibleCharacter_apply_one ψ⟩
  rw [ne_eq, linearIrreducibleCharacter_eq_trivial_iff]
  exact hψ

open scoped FiniteInduce in
/-- **Peterfalvi (10.2)**: the family `S = {Ind_{M'}^M θ | θ ∈ Irr M', θ ≠ 1}` contains an
irreducible character `ζ` of degree `w₁ = |W₁|`.

Take a non-principal degree-`1` character `θ` of `M' = [M,M]` (exists since `M'` is not perfect:
`M'' < M'`, via `exists_nontrivial_linearIrreducibleCharacter`).  By the §6 Clifford engine `θ` is
none of the `chiRestrict χ₂` (the `W₁^#`-fixed irreducibles of `M'`): the trivial column gives
`chiRestrict 1 = Res_{M'} μ_{00} = Res_{M'} 1_M = 1_{M'}` (Peterfalvi (4.4) anchor), avoided since
`θ ≠ 1`; a non-trivial column `χ₂` gives `chiRestrict χ₂ = Res_{M'} μ_{0j}` of degree
`μ_{0j}(1) > 1` (else `μ_{0j}` is linear ⇒ `M'`-trivial ⇒ a column-`0` character by (4.4),
contradicting `columnFamily_mu_ne`), avoided by degree.  Hence `Ind_{M'}^M θ` is irreducible
(`induce_isIrreducible_of_forall_chiRestrict_ne`) of degree `[M:M']·1 = |W₁|` (`induce_apply_one`
and `TypePData.card_W1_eq_derived_index`).  The §6 hypothesis is supplied by the §10→§6 bridge
`typePData_toS06Hypothesis` (so `K = M'`), needing the same `hodd`/`hHall` inputs. -/
theorem exists_zeta_in_inducedFamily_degree_w1 [Finite G] {M : Subgroup G}
    (data : TypePData M) (hodd : Odd (Nat.card G))
    (hHall : Nat.Coprime (Nat.card ↥(derivedInG M)) (Nat.card ↥data.W1)) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ inducedFamily M ∧ IsIrreducibleCharacter ζ ∧
      ζ 1 = (Nat.card ↥data.W1 : ℂ) := by
  classical
  let h : OddOrder.Peterfalvi.S06.Hypothesis ↥M := typePData_toS06Hypothesis data hodd hHall
  have hNeZ : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hKeq : h.K = (derivedInG M).subgroupOf M := rfl
  have hKcomm : h.K = commutator ↥M := by
    rw [hKeq, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  -- `M'` is not perfect (issue 7008, replacing the deleted `fitting_lt_derived`): `M' = M_F ⋊ U`
  -- is solvable — `M_F` nilpotent (`maxNilpotentNormalHall_isNilpotent`) is the normal kernel and
  -- the
  -- quotient `M'/M_F ≃ U` is nilpotent (`U_nilpotent`) via `derived_complement` — and nontrivial
  -- (`W₂ ≠ ⊥`, `W₂ ≤ M_F ≤ M'`); a nontrivial solvable group is not perfect.
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hHnorm : (data.H.subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.H_le).mpr ?_
    rw [data.H_eq]
    exact hM'le.trans (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M)
  have : Group.IsSolvable ↥(data.H.subgroupOf (derivedInG M)) := by
    have : Group.IsNilpotent ↥data.H := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    have : Group.IsSolvable ↥data.H := IsNilpotent.to_isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.H_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.H_le).injective
  have : Group.IsSolvable ↥(data.U.subgroupOf (derivedInG M)) := by
    have : Group.IsNilpotent ↥data.U := data.U_nilpotent
    have : Group.IsSolvable ↥data.U := IsNilpotent.to_isSolvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe data.U_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.U_le).injective
  have : Group.IsSolvable (↥(derivedInG M) ⧸ data.H.subgroupOf (derivedInG M)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := data.derived_complement.symm.QuotientMulEquiv.toMonoidHom)
      data.derived_complement.symm.QuotientMulEquiv.injective
  have : Group.IsSolvable ↥(derivedInG M) :=
    Group.isSolvable_of_ker_le_range ((data.H.subgroupOf (derivedInG M)).subtype)
      (QuotientGroup.mk' (data.H.subgroupOf (derivedInG M)))
      (by rw [QuotientGroup.ker_mk']; exact (data.H.subgroupOf (derivedInG M)).range_subtype.ge)
  have : Nontrivial ↥(derivedInG M) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr fun hbot =>
      data.W2_nontrivial (le_bot_iff.mp (hbot ▸ data.W2_le.trans (inf_le_left.trans data.H_le)))
  have hcomm_K : commutator ↥h.K ≠ ⊤ := by
    intro hperf
    have hperfM' : Group.IsPerfect ↥(derivedInG M) := by
      have : Group.IsPerfect ↥((derivedInG M).subgroupOf M) := ⟨hperf⟩
      exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hM'le).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hM'le).surjective
    exact absurd hperfM'.commutator_eq_top
      (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(derivedInG M)).ne
  obtain ⟨θ, hθne, hθ1⟩ := exists_nontrivial_linearIrreducibleCharacter hcomm_K
  -- the crux: `θ` avoids every `chiRestrict χ₂`.
  have havoid : ∀ χ₂, h.chiRestrict χ₂ ≠ θ := by
    intro χ₂ heq
    by_cases hχ₂ : χ₂ = 1
    · subst hχ₂
      refine hθne ?_
      rw [← heq]
      apply IrreducibleCharacter.ext
      rw [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, (h.certainType_zero_column_anchor).2,
        OddOrder.Peterfalvi.S03.restrict_trivialClassFunction]
      rfl
    · have hmu1 : ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) (1 : ↥M) = 1 := by
        have hval := congrArg
          (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) (1 : ↥h.K)) heq
        simp only [OddOrder.Peterfalvi.S06.Hypothesis.coe_chiRestrict, ClassFunction.restrict_apply,
          Subgroup.coe_one] at hval
        rw [hval, hθ1]
      have hker : (h.K : Set ↥M) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          ((h.columnFamily χ₂).mu 0 : ClassFunction ↥M ℂ) := by
        intro x hx
        have hx1 := ((h.columnFamily χ₂).mu 0).isIrreducible
          |>.apply_eq_one_of_mem_commutator_of_apply_one_eq_one hmu1 (hKcomm ▸ hx)
        rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1,
          OddOrder.Peterfalvi.S03.characterDegree_def, hmu1]
      obtain ⟨i, hi⟩ := h.exists_certainType_zero_column_eq_of_subset_characterKernel _ hker
      exact h.columnFamily_mu_ne hχ₂ 0 i hi.symm
  refine ⟨ClassFunction.induce h.K (θ : ClassFunction ↥h.K ℂ), ⟨θ, hθne, rfl⟩,
    h.induce_isIrreducible_of_forall_chiRestrict_ne havoid, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ1, mul_one, hKeq, ← data.card_W1_eq_derived_index]

end OddOrder.Peterfalvi.S12



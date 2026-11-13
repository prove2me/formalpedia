-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:35:57.87365+00:00
-- url     : https://prove2.me/theorems/e3e9dedf-3565-4dc7-9ba3-9a05c84128bf
-- title:
--   Peterfalvi §13: basic facts of the $(S,T)$ hypothesis (continuation)
-- statement:
--   A continuation file for the basic facts of Hypothesis (13.1), including conjugation closure of $\mathcal{X}$ and $\mathcal{S}$ and pairwise orthogonality of $\mathcal{S}$ (Peterfalvi (9.5)).
--
--   Main declarations: `conj_mem_xiSet` (`𝒳` is closed under complex conjugation); `sSet_closedUnderConjugate` (`𝒮` is closed under complex conjugation); `sSet_pairwiseOrthogonal` (`𝒮` is pairwise orthogonal); `sSet_hasNoRealCharacters` (`𝒮` has no real members).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/HypothesisBasics.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_SubcoherenceInputs
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerLineBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearImprimitiveBound
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LineScalarCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_AInvariantSubrep
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenPairAdjoin
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
/-- **`𝒳` is closed under complex conjugation** (Peterfalvi (9.5)): for `χ ∈ 𝒳` (irreducible,
`H ⊄ Ker χ`), the conjugate `χ̄` is again irreducible (`IsIrreducibleCharacter.conj`) with the same
kernel (`characterKernel_conj`), so `H ⊄ Ker χ̄`, i.e. `χ̄ ∈ 𝒳`. -/
theorem conj_mem_xiSet {M : Subgroup G} [Finite G] {data : TypesIIIIIIVSetup M}
    {χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiSet data) :
    (⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩ :
      OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  -- Membership unfolds (rfl) to a `characterKernel`-containment on the conjugate coe, which is
  -- defeq `(↑χ).conj`; `characterKernel_conj` rewrites it back to `characterKernel ↑χ` = `hχ`.
  change ¬ (↑(hInHu data) ⊆ OddOrder.Peterfalvi.S03.characterKernel
    ((χ : ClassFunction ↥(huSub data) ℂ).conj))
  rw [OddOrder.Peterfalvi.S03.characterKernel_conj]
  exact hχ

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮` is closed under complex conjugation** (Peterfalvi (9.5), subcoherence input (5.2.a)).
For `φ = Ind_{HU}^M χ ∈ 𝒮` with `χ ∈ 𝒳`, the conjugate is `φ̄ = Ind_{HU}^M χ̄` (`conj_induce`), and
`χ̄ ∈ 𝒳` (`conj_mem_xiSet`), so `φ̄ ∈ 𝒮`.  This is the `hconj` input the (5.3.a) subcoherence
assembler `S07.irrSubcoherent` consumes for the §9 induced family — a Dade-independent family
property, provable directly from the induced-character conjugation identity `conj_induce`. -/
theorem sSet_closedUnderConjugate {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩
  refine ⟨⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩,
    conj_mem_xiSet hχ, ?_⟩
  -- `(Ind_{HU}^M χ)̄ = Ind_{HU}^M χ̄` (`conj_induce`); `induceHU` bakes in its own `Invertible`
  -- instance, so `convert` absorbs the (subsingleton) instance mismatch.
  change (induceHU data (χ : ClassFunction ↥(huSub data) ℂ)).conj
    = induceHU data ((χ : ClassFunction ↥(huSub data) ℂ).conj)
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  simp only [induceHU]
  convert OddOrder.RepresentationTheory.conj_induce (χ : ClassFunction ↥(huSub data) ℂ) using 2

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` is pairwise orthogonal** (Peterfalvi (9.5), subcoherence input (5.2)).  Distinct members
`Ind_{HU}^M χ ≠ Ind_{HU}^M χ'` arise from non-`M`-conjugate irreducible sources `χ ≁ χ'`
(`induce_eq_induce_iff_conj`), so the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`
gives `⟨Ind χ, Ind χ'⟩ = 0` — a Dade-independent family property (the `𝒮`-instance of the general
`inducedKernelFamily_pairwise_orthogonal`).  The `FiniteInduce`-scoped `Fintype`/`Invertible`
instances are the ones `induceHU` bakes in, so `induceHU = Ind` reduces definitionally.  This is the
`pairwise_orthogonal` input the (5.3.a) assembler `S07.irrSubcoherent` consumes for the honest §9
induced family. -/
theorem sSet_pairwiseOrthogonal {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    OddOrder.Peterfalvi.S03.PairwiseOrthogonal (sSet data) := by
  rintro _ _ ⟨χ, hχ, rfl⟩ ⟨χ', hχ', rfl⟩ hne
  -- non-conjugate sources: else the inductions—hence the members—coincide, contradicting `hne`.
  have hnc : ∀ g : ↥M, IrreducibleCharacter.conjBy g χ ≠ χ' := fun g hg => hne (by
    change ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)
    exact (induce_eq_induce_iff_conj χ χ').mpr ⟨g, hg⟩)
  change ClassFunction.inner (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ))
      (ClassFunction.induce (huSub data) (χ' : ClassFunction ↥(huSub data) ℂ)) = 0
  exact inner_induce_eq_zero_of_not_conj χ χ' hnc

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`𝒮` has no real members** (Peterfalvi (9.5)/(1.1), subcoherence input (5.2)), for `M` of odd
order.  A real `Ind_{HU}^M χ` would force `χ̄ = χ^g` for some `g ∈ M` (`induce_conj` +
`induce_eq_induce_iff_conj`), impossible in odd order (`conjBy_ne_conj_of_odd`: a nontrivial
irreducible of an odd-order group is never `M`-conjugate to its dual).  `𝒳`-membership `H ⊄ Ker χ`
supplies the nontriviality (`Ker 1 = univ ⊇ hInHu`).  The `𝒮`-instance of the general
`inducedKernelFamily_hasNoRealCharacters`; the `no_real_characters` input for
`S07.irrSubcoherent`. -/
theorem sSet_hasNoRealCharacters {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M)
    (hodd : Odd (Nat.card ↥M)) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (sSet data) := by
  rintro _ ⟨χ, hχ, rfl⟩ hreal
  -- `χ` nontrivial: else `Ker χ = univ ⊇ hInHu`, contradicting `χ ∈ 𝒳`.
  have hχne : (χ : ClassFunction ↥(huSub data) ℂ) ≠ trivialClassFunction ↥(huSub data) := by
    intro h
    apply hχ
    rw [h, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  let χc : IrreducibleCharacter ↥(huSub data) :=
    ⟨(χ : ClassFunction ↥(huSub data) ℂ).conj, χ.isIrreducible.conj⟩
  -- realness of `Ind χ` transfers to the sources: `Ind χ = (Ind χ)̄ = Ind χ̄`.
  have hind : ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) := by
    have h1 : (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj
        = ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ) := hreal
    calc ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
        = (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)).conj := h1.symm
      _ = ClassFunction.induce (huSub data) (χc : ClassFunction ↥(huSub data) ℂ) :=
          ClassFunction.induce_conj (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj χ χc).mp hind
  refine conjBy_ne_conj_of_odd hodd χ.isIrreducible hχne g ?_
  have hcoe := congrArg
    (fun η : IrreducibleCharacter ↥(huSub data) => (η : ClassFunction ↥(huSub data) ℂ)) hg
  simpa [IrreducibleCharacter.coe_conjBy, χc] using hcoe

/-- **`Odd |S|`** for the maximal subgroup `S` of the minimal simple group `G` of odd order
(issue 1017, subcoherence input for the §9 induced family).  `|S| ∣ |G|` (subgroup) and `|G|` is odd
(`hG.odd`), so `|S|` is odd — the hypothesis `sSet_hasNoRealCharacters` (the (5.2.a) realness input)
needs. -/
theorem Hypothesis.oddCardS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Odd (Nat.card ↥hyp.S) := by
  rcases hG.odd with ⟨k, hk⟩
  -- From `|S| ∣ |G|` and `|G|` odd, deduce `|S|` odd (a divisor of an odd number is odd).
  have hdvd : Nat.card ↥hyp.S ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.S
  rcases Nat.even_or_odd (Nat.card ↥hyp.S) with heven | hodd
  · exfalso
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    rw [hk] at h2
    omega
  · exact hodd

open OddOrder.Peterfalvi.S11 in
/-- **The per-irreducible-member Dade `CharacterDifferenceImage` for a `𝒮 = sSet`-member**
(Peterfalvi (5.3.a) R-datum, issue 1017 Part B).  Given an irreducible source `ξ ∈ 𝒳` whose induced
`Ind_{HU}^S ξ` is **itself irreducible** (the irreducible sub-family of the mixed §9 family — the
reducible residues `μ_j` are handled separately, as a `CharacterPsiDecomposition.imageFamily` of
variable length, *not* through this 2-element `CharacterDifferenceImage`), this packages the signed
difference image `(Ind ξ − (Ind ξ)̄)^τ = ±(μ − ν)` under the honest (13.2.e) Dade map
`τ = dadeIntegralCharacterMap (dadeHypS hG) …`.

Assembled entirely from landed inputs:
* the Dade hypothesis `dadeHypS hG`;
* the member's non-realness `sSet_hasNoRealCharacters` (needs `oddCardS`);
* the difference support `sSet_member_diffsupp` (`((Ind ξ)̄ − Ind ξ).support ⊆ A(S)`),
  fed through `dadeCharacterDifferenceImageOfDiff`.

This is the exact `S`-instance analogue of the §14 `R1cdi` (`S14_MaximalI.lean:744`), which builds
the same per-member R-datum for the (12.2) family via `dadeCharacterDifferenceImageOfDiff`.  It is
the per-member piece that `S07.irrSubcoherent` consumes on the irreducible sub-family (the (9.11)
base + Galois glue), and the (9.11) pair-adjoining induction consumes (as `Da`/`Dmem` decomposition
data) for the whole family. -/
noncomputable def Hypothesis.sSet_member_differenceImage [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG))
    (hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ))) :
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥hyp.S) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData))
      (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) := by
  -- Bundle the (irreducible) member as an `IrreducibleCharacter ↥S`.
  set φ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S :=
    ⟨induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ), hirr⟩ with hφ_def
  -- Non-realness of the member (the `¬IsReal` input), from the family property + `Odd |S|`.
  have hreal : ¬ ClassFunction.IsReal (φ : ClassFunction ↥hyp.S ℂ) :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG) ⟨ξ, hξ, rfl⟩
  -- The difference support `((φ)̄ − φ).support ⊆ supportInSubgroup A(S) S` (the `hdiffsupp` input).
  have hdiffsupp :
      ((φ : ClassFunction ↥hyp.S ℂ).conj - (φ : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S :=
    hyp.sSet_member_diffsupp hG hξ
  -- Package via the general (5.3.a) Dade R-datum constructor.
  exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    (hyp.dadeHypS hG) φ hreal hdiffsupp

open OddOrder.Peterfalvi.S11 in
/-- **The uniform-degree irreducible sub-family `S₁(d) = {φ ∈ 𝒮 | φ irreducible, φ(1) = d}`**
(issue 1017, the (9.11) base / Galois glue per update #17).  The honest §9 family `𝒮 = sSet` is
*mixed*-degree — both across the `p−1` reducible residues `μ_j` and across the irreducible members
`Ind ξ` of source degree `ξ(1)` (degree `q·ξ(1)`).  Since the (0099) weakening, the
(5.2)-subcoherence `S07.Hypothesis` *is* instantiable on mixed-degree families (its
`tau_isometry_diff` field only demands the isometry on the `A(S)`-supported sublattice `ℤ[S, A]`);
what still needs equal degrees is the **(5.7) equal-degree coherence producer**
(`coherent_of_constant_degree`'s `hconst`/`hsuppdiff` inputs — member differences must vanish at
`1`).  Fixing a single degree value `d` carves out the uniform-degree conjugate-closed irreducible
sub-family on which that producer fires; the (9.11) base case (`d = q·a`) and the whole Galois case
(`d = q·u`) are the two instances the coherence route consumes. -/
noncomputable def Hypothesis.sSetIrrDeg [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) : Set (ClassFunction ↥hyp.S ℂ) :=
  { φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) |
      OddOrder.RepresentationTheory.IsIrreducibleCharacter φ ∧ (φ : ↥hyp.S → ℂ) 1 = d }

open OddOrder.Peterfalvi.S11 in
theorem Hypothesis.sSetIrrDeg_subset_sSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (d : ℂ) :
    hyp.sSetIrrDeg hG d ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := fun _ h => h.1

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` is closed under complex conjugation** (issue 1017, extracted from
`sSetIrrDeg_subcoherent`'s `hconj` input).  For `φ ∈ S₁(d)`: `φ̄ ∈ 𝒮` (`sSet_closedUnderConjugate`),
`φ̄` is irreducible (`IsIrreducibleCharacter.conj`), and `φ̄(1) = star (φ(1)) = star d = d`
(uses `hd : star d = d`).  This is the (A)-engine / (5.3.a) `hconj` input for the uniform
sub-family, and (via `sSetIrrDeg_member_diff_supported`) the `χ̄ ∈ S₁(d)` witness of the
`hconjsupp` / `hsupp` inputs. -/
theorem Hypothesis.sSetIrrDeg_closedUnderConjugate [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (hyp.sSetIrrDeg hG d) := by
  intro φ hφ
  refine ⟨sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupS hG) hφ.1, hφ.2.1.conj, ?_⟩
  rw [ClassFunction.conj_apply, hφ.2.2, hd]

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` has no real members** (issue 1017, extracted from `sSetIrrDeg_subcoherent`'s `hreal`
input): the §9 no-real fact `sSet_hasNoRealCharacters` (via `oddCardS`), restricted to `S₁(d) ⊆ 𝒮`.
The (A)-engine / (5.3.a) `hnoReal` input for the uniform sub-family. -/
theorem Hypothesis.sSetIrrDeg_hasNoRealCharacters [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.sSetIrrDeg hG d) :=
  (sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupS hG) (hyp.oddCardS hG)).mono
    (hyp.sSetIrrDeg_subset_sSet hG d)

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-members are supported in `A(S) ∪ {1}`** (issue 1017, extracted from the `hmem_supp`
local of `sSetIrrDeg_subcoherent`/`sSetIrrDeg_coherent`).  A member `φ = Ind_{HU}^S ξ` has
`φ.support ⊆ A(S) ∪ {1}` by the honest (4.7) support fact `sSet_member_support_subset_A`. -/
theorem Hypothesis.sSetIrrDeg_member_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ)
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ hyp.sSetIrrDeg hG d) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨hφsSet, _⟩ := hφ
  obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
  rw [hφeq]
  exact hyp.sSet_member_support_subset_A hG hξ

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)`-member differences are `A(S)`-supported** (issue 1017, extracted from the
`hdiff_of_mem` local of `sSetIrrDeg_subcoherent` / the `hsuppdiff` local of `sSetIrrDeg_coherent`).
For `x, y ∈ S₁(d)` (hence `x(1) = d = y(1)`), the difference `x − y` vanishes at `1`, so its support
avoids `{1}` and lands in `A(S)` (`sSetIrrDeg_member_support_subset` minus the identity).  This is
the (A)-engine `hsupp` (with `y = x̄`) and the (5.3.a) `hconjsupp` / (5.7) `hsuppdiff` input. -/
theorem Hypothesis.sSetIrrDeg_member_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ)
    {x : ClassFunction ↥hyp.S ℂ} (hx : x ∈ hyp.sSetIrrDeg hG d)
    {y : ClassFunction ↥hyp.S ℂ} (hy : y ∈ hyp.sSetIrrDeg hG d) :
    (x - y).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have : Fintype G := Fintype.ofFinite G
  have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by rw [hx.2.2, hy.2.2]
  rcases (ClassFunction.support_sub_subset x y hz) with h | h
  · rcases hyp.sSetIrrDeg_member_support_subset hG d hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSetIrrDeg_member_support_subset hG d hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Peterfalvi.S11 in
/-- **`S₁(d)` is finite** (issue 1017, extracted from `sSetIrrDeg_coherent`'s `hSfin`): the family
injects into `IrreducibleCharacter ↥S` (a `Finite` type) via its irreducibility field. -/
theorem Hypothesis.sSetIrrDeg_finite [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) (d : ℂ) :
    (hyp.sSetIrrDeg hG d).Finite := by
  apply Set.Finite.subset (Set.finite_range
    (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.S =>
      (χ : ClassFunction ↥hyp.S ℂ)))
  rintro φ ⟨_, hirr, _⟩
  exact ⟨⟨φ, hirr⟩, rfl⟩

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `S07.Hypothesis` (5.2)-subcoherence structure for the uniform-degree irreducible
sub-family `S₁(d)`** (issue 1017, update #17 — the first honest stage of the (9.11) coherence
route).
Assembled from the honest (13.2.e) Dade isometry `τ = Ind_S^G` (`dadeHypS`) and the landed
Dade-independent family inputs:
* `Rdatum` = `sSet_member_differenceImage` per irreducible member;
* `hconj` = `sSet_closedUnderConjugate` (conj of an irreducible degree-`d` member is again one — the
  conjugate `φ̄` is irreducible with `φ̄(1) = conj(φ(1)) = d` as `d = q·s` is a positive real);
* `hreal` = `sSet_hasNoRealCharacters` (via `oddCardS`), restricted to `S₁(d) ⊆ 𝒮`;
* `hortho` = `sSet_pairwiseOrthogonal`, restricted to `S₁(d) ⊆ 𝒮`;
* `hconjsupp` = conjugate differences `χ − χ̄` are `A(S)`-supported: `χ̄ ∈ S₁(d)` (conj-closedness,
  `star d = d`) and equal degrees make the difference vanish at `1`
  (`sSet_member_support_subset_A` minus the identity);
* `hiso` = the (0099) `zSupportedSpan`-form lattice isometry, unconditional from the Dade pair
  brick `dadeIntegralCharacterMap_inner_eq_of_supported` (only the supportedness halves are used).

The `hconj` field requires `d` to be real (`star d = d`); this holds for the genuine degree values
`d = q·s` (positive natural), supplied by the caller.  This is the (5.3.a) subcoherence hypothesis
on
a uniform-degree family, ready for `coherent_subset_of_constant_degree` (the (9.11) base +
Galois). -/
noncomputable def Hypothesis.sSetIrrDeg_subcoherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥hyp.S) (G := G)
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) := by
  classical
  -- The honest (13.2.e) Dade isometry `τ = Ind_S^G`.
  set τ := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
    ((hyp.dadeHypS hG).fullDadeIsometryData) with hτ
  -- Conjugation stability of `S₁(d)` (uses `star d = d`), extracted as
  -- `sSetIrrDeg_closedUnderConjugate`.
  have hconjmem := hyp.sSetIrrDeg_closedUnderConjugate hG d hd
  refine OddOrder.Peterfalvi.S07.irrSubcoherent τ
    (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)
    (fun φ hφ => ?_) ?_ ?_ ?_ ?_ ?_
  · -- `Rdatum`: `φ ∈ S₁(d) ⇒ ∃ ξ ∈ 𝒳, φ = Ind ξ` (irreducible).  The `∃` witness is extracted via
    -- `choose` (not `obtain`) so it may be eliminated into the data goal
    -- `CharacterDifferenceImage`.
    have hφsSet : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) := hφ.1
    have hirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter φ := hφ.2.1
    obtain ⟨hξ, hφeq⟩ := hφsSet.choose_spec
    rw [hφeq] at hirr ⊢
    exact hyp.sSet_member_differenceImage hG hξ hirr
  · -- `hconj`: conjugate of a degree-`d` irreducible member of `𝒮` is again one
    -- (uses `star d = d`).
    exact hconjmem
  · -- `hreal`: no real members, restricted to `S₁(d) ⊆ 𝒮` (`sSetIrrDeg_hasNoRealCharacters`).
    exact hyp.sSetIrrDeg_hasNoRealCharacters hG d
  · -- `hortho`: pairwise orthogonal, restricted to `S₁(d) ⊆ 𝒮`.
    -- The `FiniteInduce`-scoped instances
    -- baked into `sSet_pairwiseOrthogonal`'s `inner` are (subsingleton-)equal to the section ones.
    intro φ ψ hφ hψ hne
    convert sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) hφ.1 hψ.1 hne using 2;
      exact Subsingleton.elim _ _
  · -- `hconjsupp`: the conjugate difference `χ − χ̄` is `A(S)`-supported
    -- (`χ̄ ∈ S₁(d)` + equal degree),
    -- extracted as `sSetIrrDeg_member_diff_supported` (with `y = χ̄`).
    intro χ hχ
    exact hyp.sSetIrrDeg_member_diff_supported hG d hχ (hconjmem hχ)
  · -- `hiso`: the (0099) `zSupportedSpan`-form lattice isometry — unconditional from the Dade
    -- pair brick (only the supportedness halves of the `ℤ[S₁(d), A(S)]` memberships are used).
    intro φ ψ hφ hψ
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
      (hyp.dadeHypS hG) hφ.2 hψ.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) base / Galois coherence of the uniform-degree irreducible sub-family `S₁(d)`**
(issue 1017, update #18 — the honest (9.11) base coherence).  Feeds the landed subcoherence
`sSetIrrDeg_subcoherent` into `coherent_subset_of_constant_degree` (Peterfalvi (5.7)∘(5.3.a),
`S07_Subcoherent.lean:246`) with `S' = S = sSetIrrDeg d` (the uniform subset of itself), producing
`Nonempty (IsCoherent τ (S₁ d) A)` for the honest Dade map `τ = Ind_S^G` (`dadeHypS`) and support
`A(S)`.  This is the whole **Galois case** (`d = q·u`) and the **base case `S₁`** (`d = q·a`) of the
(9.11) `Ptype_core_coherence` derived-series induction (Coq `PFsection9.v:1484`).

The `coherent_subset_of_constant_degree` hypotheses discharge as follows, all *internally* from the
landed §9 family lemmas — **except `hcard` (≥ 2 membership)**, which is *exposed as a parameter*
`h2`: no `2 ≤ (S₁ d).ncard` fact exists yet in the repo (the degree-`d` count is the §9 (9.8.d)
counting content — `caseA_exists_irreducible_source_degree_qa`, `S11:6437`, and its `M`-induction
strengthening at `S11:12250`, give an *existence* `∃ ζ`, not two distinct members).  Exposing it
keeps this def sorry-free and defers the genuine upstream count to the caller — the honest pattern.

Internal discharges:
* `hconj'` = `sSetIrrDeg_subcoherent`'s own `.conjugate_closed` field (conj of a degree-`d`
  irreducible member is again one, uses `star d = d`);
* `hSfin` = `S₁ d ⊆ range (IrreducibleCharacter.toClassFunction)` (finite range of a `Finite` type);
* `hirr` = `IsIrreducibleCharacter.inner_self_eq_one` (each member is irreducible by definition);
* `hZIrr` = `dadeIntegralCharacterMap_mem_ZIrr_of_supported` — the member difference `a − b` is
  `A(S)`-supported (equal degree, vanishes at `1`) and a virtual character (difference of two
  irreducibles), so the honest Dade map sends it into `ℤ[Irr G]`;
* `hconst` = definitional uniform degree `φ(1) = d`;
* `hdeg0` = exposed `d ≠ 0`;
* `h1A` = `S10.typePACore_one_not_mem` (`1 ∉ A(S)`);
* `hsuppdiff` = the equal-degree two-member support fact (member differences `A(S)`-supported),
  the same argument `sSetIrrDeg_subcoherent`'s `hiso` uses internally. -/
theorem Hypothesis.sSetIrrDeg_coherent [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    [Fintype ↥hyp.S] [Invertible (Nat.card ↥hyp.S : ℂ)] [Invertible (Nat.card G : ℂ)]
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData))
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)) := by
  classical
  set A := OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S with hA
  -- The landed (5.3.a) subcoherence structure on `S₁(d)`; its `.tau` is the honest Dade map.
  set hyp' := hyp.sSetIrrDeg_subcoherent hG d hd with hhyp'
  -- `hSfin`: `S₁(d)` injects into `IrreducibleCharacter ↥S` (a `Finite` type) —
  -- `sSetIrrDeg_finite`.
  have hSfin : (hyp.sSetIrrDeg hG d).Finite := hyp.sSetIrrDeg_finite hG d
  -- `hirr`: each member is an irreducible character, so has self-inner `1`.
  have hirr : ∀ ζ ∈ hyp.sSetIrrDeg hG d, ClassFunction.inner ζ ζ = 1 :=
    fun ζ hζ => hζ.2.1.inner_self_eq_one
  -- `hconst`: uniform degree `φ(1) = d` (definitional membership).
  have hconst : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 =
        ((b : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 :=
    fun a ha b hb => by rw [ha.2.2, hb.2.2]
  -- `hdeg0`: nonzero degree (exposed `d ≠ 0`).
  have hdeg0 : ∀ a ∈ hyp.sSetIrrDeg hG d, ((a : ClassFunction ↥hyp.S ℂ) : ↥hyp.S → ℂ) 1 ≠ 0 :=
    fun a ha => by rw [ha.2.2]; exact hd0
  -- `h1A`: `1 ∉ A(S)`.
  have h1A : (1 : ↥hyp.S) ∉ A := by
    rw [hA, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    simp
  -- `hsuppdiff`: for `x, y ∈ S₁(d)`, `(x − y).support ⊆ A(S)` (equal degree ⇒ vanish at `1`);
  -- extracted as `sSetIrrDeg_member_diff_supported` (also the (5.3.a) `hconjsupp` input).
  have hsuppdiff : ∀ x ∈ hyp.sSetIrrDeg hG d, ∀ y ∈ hyp.sSetIrrDeg hG d,
      ((x - y : ClassFunction ↥hyp.S ℂ)).support ⊆ A := by
    intro x hx y hy
    exact hyp.sSetIrrDeg_member_diff_supported hG d hx hy
  -- `hZIrr`: the honest Dade map sends `A(S)`-supported virtual-character differences into
  -- `ℤ[Irr G]`.
  have hZIrr : ∀ a ∈ hyp.sSetIrrDeg hG d, ∀ b ∈ hyp.sSetIrrDeg hG d,
      hyp'.tau (a - b) ∈ OddOrder.RepresentationTheory.ZIrr G := by
    intro a ha b hb
    have hab_supp : (a - b : ClassFunction ↥hyp.S ℂ).support ⊆ A := hsuppdiff a ha b hb
    have hab_Z : (a - b : ClassFunction ↥hyp.S ℂ) ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
      Submodule.sub_mem _ ha.2.1.mem_ZIrr hb.2.1.mem_ZIrr
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      (hyp.dadeHypS hG) hab_supp hab_Z
  -- Fire the (5.7)∘(5.3.a) uniform-degree coherence producer on `S' = S = S₁(d)`.
  exact OddOrder.Peterfalvi.S07.coherent_subset_of_constant_degree hyp'
    (subset_refl _) hyp'.conjugate_closed hSfin h2 hirr hZIrr hconst hdeg0 h1A hsuppdiff

open scoped FiniteInduce in
/-- **(9.11) base / Galois coherence of `S₁(d)`, re-grounded onto the induction map `τ = Ind_S^G`**
(issue 1017, update #19 — the honest-`indS` re-grounding of `sSetIrrDeg_coherent`).  The landed
uniform-degree coherence `sSetIrrDeg_coherent` produces `IsCoherent τ (S₁ d) A(S)` for the honest
Dade map `τ = dadeIntegralCharacterMap (dadeHypS hG) …`; but the (13.3) consumers — the (A) engine
`S15.coherentIndS_image_inner_eta_eq_zero` and (ultimately) `coherent_H0Cprime_S` — want the
coherence phrased with the plain induction map `hyp.indS = Ind_S^G` (Peterfalvi (13.2.e)).

The two maps **agree on every `A(S)`-supported class function**
(`sInstance_dade_eq_induce`, the honest (13.2.e) `normedTI` isometry half, Rungs B+C), and
`S07.IsCoherent` depends on its map *only* through `extends_on_supported` (whose domain is
`zSupportedSpan (S₁ d) A(S)`, every member of which is `A(S)`-supported by definition), so the
general `S07.IsCoherent.congrMap` re-targets the coherence onto `indS` with no further analytic
input.  This is the `indS`-form the honest (9.11) route delivers to the (A) engine; once the
(9.11.1)–(9.11.8) pair-adjoining induction lifts it from the uniform sub-family to the full `sSet`,
the same `congrMap` step re-grounds `coherent_H0Cprime_S` off the unsound `sibleyTarget_H0C`.

All finiteness instances are taken from the `FiniteInduce` scope (from `[Finite G]`), so the
`Ind_S^G` produced here (via `indS`) and the one `sInstance_dade_eq_induce` names share the *same*
`Fintype ↥S` instance — no subsingleton-instance juggling is needed. -/
theorem Hypothesis.sSetIrrDeg_coherent_indS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (d : ℂ) (hd : star d = d) (hd0 : d ≠ 0)
    (h2 : 2 ≤ (hyp.sSetIrrDeg hG d).ncard) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (hyp.sSetIrrDeg hG d)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)) :=
  (hyp.sSetIrrDeg_coherent hG d hd hd0 h2).map fun c =>
    c.congrMap fun φ hφ => by
      rw [hyp.indS_apply]
      exact hyp.sInstance_dade_eq_induce hG hnoV hφ.2

open OddOrder.Peterfalvi.S11 in
/-- **(9.11) base cardinality `2 ≤ (S₁(q·a)).ncard`** in the non-Galois case (issue 1017, Step 2 —
the honest discharge of `sSetIrrDeg_coherent`/`sSetIrrDeg_coherent_indS`'s exposed `h2` at the base
degree `d = q·a`).

Coq `PFsection9.v:1537-1551` needs only `0 < size S1` for the uniform base `S1 = {ζ ∈ 𝒮 | ζ(1) =
q·a}`: since `𝒮` is conjugate-closed and has no real members, a single member `χ` and its distinct
conjugate `χ̄` give `size S1 ≥ 2`.  The single member comes from the **positive** (9.8.d) count
`caseA_exists_irreducible_qa` — `(p−1)/a ≥ 1` since `a ∣ p−1` (`CliffordCaseAData.a_dvd_p_sub_one`)
and `[C_U(S₀):U′] ≥ 1` — whose witness lies in `𝒮(H₀U′) ⊆ 𝒮` (`sOf_subset_sSet`); conjugate-closure
(`sSetIrrDeg_closedUnderConjugate`, `q·a` a positive real so `star d = d`) and non-realness
(`sSetIrrDeg_hasNoRealCharacters`) then double it.

Given a `CliffordCaseAData` for the `S`-instance §9 data (the non-Galois case assumption), this
discharges the `h2` parameter of `sSetIrrDeg_coherent_indS` at the base degree `d = q·a`, un-gating
the uniform base coherence (whose downstream is the (A)-engine orthogonality
`S15.sSetIrrDeg_coherentIndS_image_inner_eta_eq_zero`).  In the Galois case (caseB) the whole
family is uniform of degree `q·u`, so no such base-count is needed. -/
theorem Hypothesis.sSetIrrDeg_qa_two_le_ncard [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    2 ≤ (hyp.sSetIrrDeg hG
        (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)).ncard := by
  classical
  -- (9.8.d) existence of one degree-`q·a` irreducible member of `𝒮(H₀U′) ⊆ 𝒮`.
  obtain ⟨χ, hχSOf, hχirr, hχdeg⟩ := caseA_exists_irreducible_qa hG chars caseA
  set d : ℂ := (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) with hd_def
  have hd : star d = d := by rw [hd_def]; exact star_natCast _
  rw [chars.SOf_eq] at hχSOf
  have hχ : χ ∈ hyp.sSetIrrDeg hG d :=
    ⟨sOf_subset_sSet _ _ hχSOf, hχirr, hχdeg⟩
  -- `χ̄ ∈ S₁(d)` (conj-closed) and `χ ≠ χ̄` (no real members).
  have hχc : χ.conj ∈ hyp.sSetIrrDeg hG d := hyp.sSetIrrDeg_closedUnderConjugate hG d hd hχ
  have hne : χ ≠ χ.conj := fun heq =>
    hyp.sSetIrrDeg_hasNoRealCharacters hG d hχ heq.symm
  -- `{χ, χ̄} ⊆ S₁(d)` has two distinct members.
  calc 2 = ({χ, χ.conj} : Set (ClassFunction ↥hyp.S ℂ)).ncard := (Set.ncard_pair hne).symm
    _ ≤ (hyp.sSetIrrDeg hG d).ncard :=
        Set.ncard_le_ncard (Set.insert_subset hχ (Set.singleton_subset_iff.mpr hχc))
          (hyp.sSetIrrDeg_finite hG d)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(9.11) non-Galois base coherence of `S₁(q·a)` on `Ind_S^G`, fully un-gated** (issue 1017,
Step 2 — the `h0` entry point of the pair-adjoining lift).  Combines the uniform base coherence
`sSetIrrDeg_coherent_indS` with the base-count discharge `sSetIrrDeg_qa_two_le_ncard`, so the
exposed `hd`/`hd0`/`h2` parameters are all discharged from the `S`-instance §9 caseA data:
`star (q·a) = q·a` (positive real, `star_natCast`), `q·a ≠ 0` (`data.q > 0` = `Nat.card_pos`,
`caseA.a_pos`), and `2 ≤ ncard` (the (9.8.d) count + conjugacy doubling).

This is the base coherence `h0` that Peterfalvi's (9.11) pair-adjoining induction (Coq
`Ptype_core_coherence`, `coherentPairChain`/`coherentOfPairChainCover`) starts from, for the honest
type-`P₂` `S`.  The remaining lift steps to the full `𝒮 = sSet` are the degree-monotone
decomposition (`hpairs`/`hcover`, the reducible `μ_j` via `CharacterPsiDecomposition` and the
irreducible conjugate pairs via `CharacterDifferenceImage`) and the per-pair (5.6)/(9.11.5) retarget
(`Snorm`/`sumnS` squeeze + `xAdjoinStepW`), all keeping `S₀ = S₁(q·a)` as the anchor prefix.  In the
Galois case (caseB) the whole family is uniform of degree `q·u`, coherent directly by
`sSetIrrDeg_coherent_indS` (no lift). -/
theorem Hypothesis.sSetIrrDeg_qa_coherent_indS_caseA [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.indS
      (hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)) := by
  have hqpos : 0 < (hyp.toTypesIIIIIIVSetupS hG).q := Nat.card_pos
  exact hyp.sSetIrrDeg_coherent_indS hG hnoV _ (star_natCast _)
    (Nat.cast_ne_zero.mpr (Nat.mul_ne_zero hqpos.ne' caseA.a_pos.ne'))
    (hyp.sSetIrrDeg_qa_two_le_ncard hG chars caseA)

/-- **Peterfalvi (13.2.b), order part**: the Fitting kernel `P = S_F` has order `p^q`.

This is the order half of (13.2.b) ("`P` is elementary abelian of order `p^q`").  By (13.2.a),
`S` is of Type II or Type III (`isTypeII_or_isTypeIII_of_isTypeNonI`).  In Type II, §11's
Wielandt fixed-point order relation `typeII_III_IV_order_relations` (Peterfalvi (9.3)) gives
`|S_F| = |W₂|^q`.  In Type III, Peterfalvi (11.7) gives the same order through
`card_H_eq_of_base` and the unconditional (11.3) noncoherence theorem; the chosen §12 datum's
two type-`P` factors are reconciled with the carried `Sdata` by the derived-index identity and
the generic `|M_σ ∩ C(K)| = |W₂|` bridge.

The one input not derivable from the bare `Hypothesis` fields is the reconciliation `Sdata.W2 = W2`
between the *intrinsic* type-`P` `W₂` of `S` (`Sdata.W2 = C_{S'}(W₁#)`) and the abstract `W₂`
(complement of `W₁` in the cyclic `W = S ∩ T`) — the `W₂`-analogue of the carried
`Sdata_U_eq` / `Sdata_W1_eq`.  It is honest §16-carrier content (`Section16TypePStructure`, which
builds `Sdata`); taken here as an explicit hypothesis so the order computation is unconditional on
its proof.  ⚠ The former "see issue 3001 for threading it through the carrier" note is **stale**
(issue 3001 closed): `Sdata_W2_eq` is now a field of the (13.1) `Hypothesis`, so
`basic_structure_gated`'s `P_order` discharges unconditionally as `hyp.card_P_eq hG
hyp.Sdata_W2_eq`. -/
theorem Hypothesis.card_P_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hSdataW2 : hyp.Sdata.W2 = hyp.W2) :
    Nat.card ↥hyp.P = hyp.p ^ hyp.q := by
  rcases OddOrder.Peterfalvi.S13.isTypeII_or_isTypeIII_of_isTypeNonI
      hG hyp.S_maximal hyp.S_nonI with hSII | hSIII
  · -- Type II: (9.3) on the carried type-`P` datum.
    let setup := hyp.toTypesIIIIIIVSetupS hG
    have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
      setup).1 hSII
    have hord2 := hord.2
    change Nat.card ↥setup.typeP.H =
      Nat.card ↥setup.typeP.W2 ^ Nat.card ↥setup.typeP.W1 at hord2
    change Nat.card ↥hyp.Sdata.H =
      Nat.card ↥hyp.Sdata.W2 ^ Nat.card ↥hyp.Sdata.W1 at hord2
    have hW2card : Nat.card ↥hyp.Sdata.W2 = hyp.p := by
      rw [hSdataW2, ← hyp.p_eq_card_W2]
    rw [hyp.Sdata.H_eq, ← hyp.P_eq_SF, hW2card, hyp.Sdata_W1_eq,
      ← hyp.q_eq_card_W1] at hord2
    exact hord2
  · -- Type III: (11.7), with the chosen §12 datum reconciled to `Sdata` by intrinsic orders.
    obtain ⟨base12⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG
      hyp.S_maximal (Or.inl hSIII)
    have hcard := OddOrder.Peterfalvi.S13.card_H_eq_of_base hG base12 (Or.inl hSIII)
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
    have hHP : base12.typeP.H = hyp.P := by
      rw [base12.typeP.H_eq, ← hyp.P_eq_SF]
    have hw1 : base12.w1 = hyp.q := by
      change Nat.card ↥base12.typeP.W1 = hyp.q
      rw [base12.typeP.card_W1_eq_derived_index,
        ← hyp.Sdata.card_W1_eq_derived_index, hyp.Sdata_W1_eq,
        ← hyp.q_eq_card_W1]
    have hSP : OddOrder.BG.Ch4.S14.IsTypeP hyp.S :=
      OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI
    let : IsCyclic ↥hyp.Sdata.W1 := hyp.Sdata.W1_cyclic
    have hW1hall : OddOrder.Isaacs.Ch03.IsHallSubgroup
        (OddOrder.BG.Ch4.S14.kappa hyp.S) (hyp.Sdata.W1.subgroupOf hyp.S) :=
      OddOrder.Peterfalvi.S12.typePData_W1_isHallSubgroup_kappa
        hG hyp.S_maximal hSP hyp.Sdata
    have hbase := OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG
      hyp.S_maximal hSP hyp.Sdata.W1_le hW1hall base12.typeP
    have hdata := OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG
      hyp.S_maximal hSP hyp.Sdata.W1_le hW1hall hyp.Sdata
    have hw2 : base12.w2 = hyp.p := by
      change Nat.card ↥base12.typeP.W2 = hyp.p
      rw [← hbase, hdata, hSdataW2, ← hyp.p_eq_card_W2]
    rw [hHP, hw1, hw2] at hcard
    exact hcard

/-- **The `S`-instance chief kernel `N` is trivial**: `P = S_F` has order `p^q`
(`card_P_eq`), and the chief factor `H̄ = P/H₀ ≅ ↥P ⧸ N` already has order `(chief.p)^q`
(`chiefFactor_quotient_card`), so `chief.p = p` and `|N| = 1`, i.e. `N = ⊥`.  Thus `↥P ⧸ N ≅ ↥P`
— `P` itself is the chief factor.  The source of both `H₀ = ⊥` (below) and `cSub = C_U(P) = C`
(the `C_U(H̄) = C_U(P)` identification once `H̄ = P`). -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_N_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.N = ⊥ := by
  have := chief.N_normal
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    change hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hq : (hyp.toTypesIIIIIIVSetupS hG).q = hyp.q := by
    change Nat.card ↥hyp.Sdata.W1 = hyp.q
    rw [hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H = hyp.p ^ hyp.q := by
    rw [show ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G) = hyp.P from hHeq]
    exact hyp.card_P_eq hG hyp.Sdata_W2_eq
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  -- `p^q = chief.p^q · |N|` forces `chief.p = p` and `|N| = 1`
  have hdvd : chief.p ∣ hyp.p ^ hyp.q := by
    refine dvd_trans (dvd_pow_self chief.p hyp.q_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.p :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.p_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN1 : Nat.card ↥chief.N = 1 := by
    have := hsplit.symm
    nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.p_prime.pos hyp.q]
  exact Subgroup.card_eq_one.mp hN1

/-- **The `S`-instance chief `H₀` is trivial** (`toTypesIIIIIIVSetupS_chief_N_eq_bot`, mapped):
`H₀ = N.map subtype = ⊥`.  Collapses the §9 families of the `S`-instance (`𝒳(H₀) = 𝒳(⊥)`), making
the (13.3.a) kernel condition `H₀ ⊆ Ker χ_j` automatic. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_chief_H0_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    chief.H0 = ⊥ := by
  rw [chief.H0_eq, hyp.toTypesIIIIIIVSetupS_chief_N_eq_bot hG chief]
  exact Subgroup.map_bot _

open OddOrder.Peterfalvi.S11 in
/-- **The honest `S`-instance family is its own `H₀C′` stratum**: `𝒮 = sSet = 𝒮(H₀C′)` (issue 1017,
the linchpin bridging the `sSet` refuter to the generic (9.11) `sOf`-stratum machinery, which is
uniformly phrased over `sOf data (chief.H₀ ⊔ …)`).  For the type-`P₂` maximal `S` the kernel data
degenerates — `chief.H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`) and `C′ = cprimeSub =
derivedInG (cSub) = ⊥` (`cSub ≤ U` abelian by `S_U_commutative`, same argument as `Cprime_eq_bot`) —
so `chief.H₀ ⊔ chars.Cprime = ⊥` and `𝒮(H₀C′) = 𝒮(⊥) = 𝒮`.  This is the `S`-instance analogue of the
*identity* the M-side gets for free (there `H₀C′` is a genuine proper stratum of `𝒮`); it lets every
generic (9.11) producer over `sOf data (chief.H₀ ⊔ Y)` be instantiated at the `S`-instance full
family `sSet` (mirrors the caseB collapse used in `sSet_caseB_apply_one_eq_qu`). -/
theorem Hypothesis.sSet_eq_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief) :
    sSet (hyp.toTypesIIIIIIVSetupS hG)
      = sOf (hyp.toTypesIIIIIIVSetupS hG) (chief.H0 ⊔ chars.Cprime) := by
  classical
  have hH0 : chief.H0 = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief
  have hCp : chars.Cprime = ⊥ := by
    change OddOrder.Peterfalvi.S11.cprimeSub (hyp.toTypesIIIIIIVSetupS hG) chief = ⊥
    have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief ≤ hyp.U :=
      (OddOrder.Peterfalvi.S11.cSub_le_U _ _).trans (le_of_eq hyp.Sdata_U_eq)
    have hCab : IsMulCommutative
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) :=
      ⟨⟨fun a b => Subtype.ext (by
        have h := hyp.S_U_commutative.is_comm.comm
          (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
        simpa using congrArg Subtype.val h)⟩⟩
    have hcomm : commutator
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hCab.is_comm.comm a b
    change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥
    rw [derivedInG, hcomm, Subgroup.map_bot]
  rw [hH0, hCp, sup_bot_eq]
  apply Set.Subset.antisymm
  · -- `𝒮 ⊆ 𝒮(⊥)`: the `⊥`-kernel demand is vacuous (only the identity lies in `⊥`)
    rintro φ ⟨χ, hχ, rfl⟩
    refine ⟨χ, ?_, rfl⟩
    rw [mem_xiOf]
    refine ⟨hχ, ?_⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx))
      rw [Subgroup.mem_bot] at h2
      exact Subtype.ext (Subtype.ext h2)
    rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
  · exact sOf_subset_sSet _ _

open OddOrder.Peterfalvi.S11 in
/-- **`U′ = [U, U] = ⊥` for the type-`P₂` maximal `S`** (Peterfalvi (13.2.a): abelian `U`).  `U` is
abelian (`S_U_commutative`, BG Lemma 15.1(b)), so its derived subgroup `U′ = uprimeSub =
derivedInG U = ⊥`.  The `uprimeSub`-analogue of `Cprime_eq_bot` (same argument with `U` in place of
`C ≤ U`); it collapses the generic (9.11) anchor stratum `sOf data (H₀ ⊔ U′)` — over which
`nineElevenOne_configuration` and the whole (9.11.1) squeeze are phrased — onto the full family
(`sOf_H0_uprime_eq_sSet`). -/
theorem Hypothesis.uprimeSub_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    uprimeSub (hyp.toTypesIIIIIIVSetupS hG) = ⊥ := by
  change derivedInG (hyp.toTypesIIIIIIVSetupS hG).U = ⊥
  have hUU : (hyp.toTypesIIIIIIVSetupS hG).U ≤ hyp.U := le_of_eq hyp.Sdata_U_eq
  have hUab : IsMulCommutative ↥(hyp.toTypesIIIIIIVSetupS hG).U :=
    ⟨⟨fun a b => Subtype.ext (by
      have h := hyp.S_U_commutative.is_comm.comm
        (⟨(a : G), hUU a.2⟩ : ↥hyp.U) ⟨(b : G), hUU b.2⟩
      simpa using congrArg Subtype.val h)⟩⟩
  have hcomm : commutator ↥(hyp.toTypesIIIIIIVSetupS hG).U = ⊥ := by
    rw [eq_bot_iff]
    refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hUab.is_comm.comm a b
  rw [derivedInG, hcomm, Subgroup.map_bot]

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮(H₀ ⊔ U′) = 𝒮`** for the type-`P₂` `S`-instance (issue 1017 step (a), the strata-collapse
bridge): the generic (9.11) anchor stratum equals the full family.  Both `chief.H₀ = ⊥`
(`toTypesIIIIIIVSetupS_chief_H0_eq_bot`) and `U′ = ⊥` (`uprimeSub_eq_bot`), so `H₀ ⊔ U′ = ⊥` and
`𝒮(⊥) = 𝒮` (`sOf_bot_eq_sSet`).  This makes the generic (9.11.1) squeeze cut — phrased over
`sOf data (chief.H₀ ⊔ uprimeSub data)` in
`nineElevenOne_configuration`/`NineElevenEqualityRefutation`
— equal `sSet`, hence the degree-`qa` anchor cut equal `hyp.sSetIrrDeg hG (q·a)`. -/
theorem Hypothesis.sOf_H0_uprime_eq_sSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    sOf (hyp.toTypesIIIIIIVSetupS hG) (chief.H0 ⊔ uprimeSub (hyp.toTypesIIIIIIVSetupS hG))
      = sSet (hyp.toTypesIIIIIIVSetupS hG) := by
  rw [hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief, hyp.uprimeSub_eq_bot hG, sup_bot_eq,
    sOf_bot_eq_sSet]

/-- **A subgroup of coprime `p`-order lies in a normal subgroup of `p`-coprime index.**  If
`W ≤ S`, `P.subgroupOf S ⊴ S`, `p` is coprime to `[S : P]`, and every `w ∈ W` has order dividing
`p`, then `W ≤ P`: each `w`'s image in `S/P` has order dividing both `p` and `[S : P]`, hence `1`.
This is the substantive core of `pgroup_le_of_normal_coprime_index`, taking the prime-vs-index
coprimality **directly** (so it applies when `p ∣ |P|` is unknown/false but `p ∤ [S : P]`, e.g. to
place `W₁` — of order `q ≠ p` — inside `T'` whose index is `p`). -/
theorem subgroup_le_of_normal_coprime_index_prime [Finite G]
    {S P W : Subgroup G} {p : ℕ}
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime p (P.subgroupOf S).index)
    (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  have := hPnorm
  intro w hw
  have hwS : w ∈ S := hWS hw
  have horder : orderOf w ∣ p := hWp w hw
  have hmk : QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩ = 1 := by
    rw [← orderOf_eq_one_iff]
    have hd1 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣ p := by
      refine (orderOf_map_dvd _ _).trans ?_
      rw [show orderOf (⟨w, hwS⟩ : ↥S) = orderOf w from
        (orderOf_injective S.subtype Subtype.coe_injective ⟨w, hwS⟩).symm]
      exact horder
    have hd2 : orderOf (QuotientGroup.mk' (P.subgroupOf S) ⟨w, hwS⟩) ∣
        (P.subgroupOf S).index := orderOf_dvd_natCard _
    exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hd1 hd2)
  have hmem : (⟨w, hwS⟩ : ↥S) ∈ P.subgroupOf S := by
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
    exact hmk
  rwa [Subgroup.mem_subgroupOf] at hmem

/-- **A `p`-subgroup lies in a normal subgroup of coprime-to-`p` index.**  If `W ≤ S`,
`P.subgroupOf S ⊴ S`, `[S : P]` is coprime to `|P|`, and `p ∣ |P|`, then every element of `W` of
order dividing `p` lies in `P`: its image in `S/P` has order dividing both `p` and `[S : P]`, hence
`1`.  Generic group theory (used to place the prime-order factors `W₁`, `W₂` inside the Fitting
kernels `Q`, `P`).  Reduces to `subgroup_le_of_normal_coprime_index_prime` via `Coprime |P| [S:P]`
and `p ∣ |P|` ⟹ `p ∤ [S:P]` ⟹ `Coprime p [S:P]`. -/
theorem pgroup_le_of_normal_coprime_index [Finite G]
    {S P W : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hWS : W ≤ S) (hPnorm : (P.subgroupOf S).Normal)
    (hcop : Nat.Coprime (Nat.card ↥P) (P.subgroupOf S).index)
    (hpP : p ∣ Nat.card ↥P) (hWp : ∀ w ∈ W, orderOf w ∣ p) : W ≤ P := by
  have hcop2 : Nat.Coprime p (P.subgroupOf S).index :=
    (hp.coprime_iff_not_dvd).mpr fun hdvd =>
      Nat.Prime.not_dvd_one hp (hcop ▸ Nat.dvd_gcd hpP hdvd)
  exact subgroup_le_of_normal_coprime_index_prime hWS hPnorm hcop2 hWp

/-- **Peterfalvi (13.2.b)/(14.2.a): `W₂ ≤ P`.**  `W₂` is a `p`-group (`|W₂| = p`) inside `S`
(`W₂ ≤ W = S ⊓ T ≤ S`), while `P = S_F` is the normal Hall `p`-subgroup of `S` of order `p^q`
(`basic_structure`); hence `W₂ ≤ P` — the `F_p ⊆ F` identification of (14.2.a). -/
theorem W2_le_P [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.W2 ≤ hyp.P := by
  have hP_card : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq _hG hyp.Sdata_W2_eq
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  refine pgroup_le_of_normal_coprime_index (S := hyp.S) hyp.p_prime ?_ ?_ ?_ ?_ ?_
  · have h1 : hyp.W2 ≤ hyp.W := by rw [hyp.W_eq_join]; exact le_sup_right
    have h2 : hyp.W ≤ hyp.S := by rw [hyp.W_eq_inter]; exact inf_le_left
    exact h1.trans h2
  · rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal hyp.S
  · have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have hcard_eq : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
    exact hcard_eq ▸ Ch03.IsHallSubgroup.coprime_index hHall
  · rw [hP_card]; exact dvd_pow_self hyp.p hyp.q_prime.pos.ne'
  · intro w hw
    have heq : orderOf (⟨w, hw⟩ : ↥hyp.W2) = orderOf w :=
      (orderOf_injective hyp.W2.subtype Subtype.coe_injective ⟨w, hw⟩).symm
    have h1 : orderOf (⟨w, hw⟩ : ↥hyp.W2) ∣ Nat.card ↥hyp.W2 := orderOf_dvd_natCard _
    rw [heq, ← hyp.p_eq_card_W2] at h1
    exact h1

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **`μ_j ∈ 𝒮(H₀)` for the `S`-instance** ((13.3.a) membership): the nonzero `μ`-column sum
lies in the §9 family `𝒮(H₀)` of `toTypesIIIIIIVSetupS`.  The (4.5.a) witness `ψ`
(`mu_colSum_eq_induce`) transports along `huSub = S'` (`huSub_eq_derivedInG_subgroupOf`,
`induce_compHom_subgroupCongr`); the `𝒳`-conditions are `H₀ = ⊥ ⊆ Ker`
(`toTypesIIIIIIVSetupS_chief_H0_eq_bot`) and `H = P ⊄ Ker` from the (4.7) `W₂`-nonkernel
conjunct with `W₂ ≤ P` (`W2_le_P`). -/
theorem Hypothesis.mu_colSum_mem_sOf_H0 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j)
      ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG) chief.H0 := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.S := Fintype.ofFinite _
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
    Fintype.ofFinite _
  let : Fintype ↥((derivedInG hyp.S).subgroupOf hyp.S) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((derivedInG hyp.S).subgroupOf hyp.S) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨ψ, hψirr, hψeq, hψker⟩ := hyp.mu_colSum_eq_induce j
  have hKeq : OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)
      = (derivedInG hyp.S).subgroupOf hyp.S :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf _
  set χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom ψ with hχdef
  have hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKeq).surjective hψirr
  rw [OddOrder.Peterfalvi.S11.mem_sOf]
  refine ⟨⟨χ, hχirr⟩, ?_, ?_⟩
  · rw [OddOrder.Peterfalvi.S11.mem_xiOf]
    constructor
    · -- `H ⊄ Ker χ` (`xiSet`): a kernel containment would violate the `W₂`-nonkernel conjunct
      intro hsub
      apply hψker hj
      intro c hc
      have hcW2 : ((c : ↥hyp.S) : G) ∈ hyp.W2 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hc))
      set x : ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) :=
        (MulEquiv.subgroupCongr hKeq).symm c with hxdef
      have hxval : ((x : ↥hyp.S) : G) = ((c : ↥hyp.S) : G) := by
        rw [hxdef]
        exact congrArg Subtype.val (MulEquiv.subgroupCongr_symm_apply hKeq c)
      have hxhInHu : x ∈ OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupS hG) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
        change ((x : ↥hyp.S) : G) ∈ hyp.Sdata.H
        rw [hxval, hyp.Sdata.H_eq, ← hyp.P_eq_SF]
        exact W2_le_P hG hyp hcW2
      have hxker := hsub (SetLike.mem_coe.mpr hxhInHu)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hxker' : χ x = χ 1 := hxker
      rw [hχdef, ClassFunction.compHom_apply, ClassFunction.compHom_apply, hxdef,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at hxker'
      exact hxker'
    · -- `H₀ = ⊥ ⊆ Ker χ`
      rw [hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      intro x hx
      have hx1 : x = 1 := by
        have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
          (SetLike.mem_coe.mp hx))
        rw [Subgroup.mem_bot] at h2
        exact Subtype.ext (Subtype.ext h2)
      rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
  · -- `∑ μ_{ij} = Ind_{HU}^S χ`
    rw [hψeq]
    have h1 : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ
        = ClassFunction.induce
            (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupS hG)) χ := by
      unfold OddOrder.Peterfalvi.S11.induceHU
      congr!
    have h2 : ClassFunction.induce ((derivedInG hyp.S).subgroupOf hyp.S) ψ
        = OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupS hG) χ := by
      rw [h1, hχdef]
      exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq ψ).symm
    exact h2

open OddOrder.Peterfalvi.S11 in
/-- **(9.9.a) uniform degree `q·u` of the full honest §9 family `𝒮 = sSet` in the Galois case**
(issue 1017, the `hdeg` input of the caseB (5.7) uniform-degree coherence engine).  In Clifford
case (b) every member of `𝒮(H₀C′)` has degree `q·u` (`caseB_degree_qu`); for the honest type-`P₂`
`S`-instance the kernel data degenerates — `chief.H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`)
and `C′ = [C,C] = ⊥` (the chief `cprimeSub = derivedInG (cSub)`, `cSub ≤ U` abelian by
`S_U_commutative`, so its derived subgroup is `⊥` — the same argument as `Cprime_eq_bot`), so
`𝒮(H₀C′) = 𝒮(⊥) = 𝒮 = sSet` — whence **every** member of the *full* family has degree `q·u`.  This
is the uniform-degree fact that lets the (5.7) engine `uniform_degree_coherence_of_families` fire on
the whole mixed family (irreducibles + the `p−1` reducible μ_j columns, all degree `q·u`). -/
theorem Hypothesis.sSet_caseB_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) := by
  classical
  -- `chief.H₀ = ⊥` and `C′ = ⊥`, so `chief.H₀ ⊔ chars.Cprime = ⊥` and `sSet = 𝒮(⊥) = 𝒮(H₀C′)`.
  have hH0 : chief.H0 = ⊥ := hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief
  have hCp : chars.Cprime = ⊥ := by
    -- `C′ = cprimeSub = derivedInG (cSub)`, and `cSub ≤ U` abelian, so its derived subgroup is `⊥`.
    change OddOrder.Peterfalvi.S11.cprimeSub (hyp.toTypesIIIIIIVSetupS hG) chief = ⊥
    have hCU : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief ≤ hyp.U :=
      (OddOrder.Peterfalvi.S11.cSub_le_U _ _).trans (le_of_eq hyp.Sdata_U_eq)
    have hCab : IsMulCommutative
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) :=
      ⟨⟨fun a b => Subtype.ext (by
        have h := hyp.S_U_commutative.is_comm.comm
          (⟨(a : G), hCU a.2⟩ : ↥hyp.U) ⟨(b : G), hCU b.2⟩
        simpa using congrArg Subtype.val h)⟩⟩
    have hcomm : commutator
        ↥(OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hCab.is_comm.comm a b
    change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief) = ⊥
    rw [derivedInG, hcomm, Subgroup.map_bot]
  -- membership in the smaller `𝒮(H₀C′)` (equal to `sSet` once the kernel demand degenerates)
  have hmem : φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime) := by
    rw [Section11CharacterData.SOf_eq, hH0, hCp, sup_bot_eq]
    obtain ⟨χ, hχ, rfl⟩ := hφ
    refine ⟨χ, ?_, rfl⟩
    rw [mem_xiOf]
    refine ⟨hχ, ?_⟩
    -- the realized `⊥` kernel demand is vacuous
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx))
      rw [Subgroup.mem_bot] at h2
      exact Subtype.ext (Subtype.ext h2)
    rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
  exact caseB_degree_qu hG chars caseB φ hmem

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮`-members are supported in `A(S) ∪ {1}`** (issue 1017, the full-family analogue of
`sSetIrrDeg_member_support_subset`).  Every `φ = Ind_{HU}^S ξ ∈ 𝒮` has `φ.support ⊆ A(S) ∪ {1}` by
the honest (4.7) support fact `sSet_member_support_subset_A`. -/
theorem Hypothesis.sSet_member_support_subset [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {φ : ClassFunction ↥hyp.S ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨ξ, hξ, rfl⟩ := hφ
  exact hyp.sSet_member_support_subset_A hG hξ

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮`-member differences are `A(S)`-supported in the Galois case** (issue 1017, the `hsuppdiff`
input of the caseB (5.7) coherence engine).  For `x, y ∈ 𝒮` both of the uniform degree `q·u`
(`sSet_caseB_apply_one_eq_qu`), the difference `x − y` vanishes at `1`, so its support avoids `{1}`
and lands in `A(S)` (`sSet_member_support_subset` minus the identity). -/
theorem Hypothesis.sSet_caseB_member_diff_supported [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseB : CliffordCaseBData chars)
    {x : ClassFunction ↥hyp.S ℂ} (hx : x ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    {y : ClassFunction ↥hyp.S ℂ} (hy : y ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (x - y).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have : Fintype G := Fintype.ofFinite G
  have hdeg : (x : ↥hyp.S → ℂ) 1 = (y : ↥hyp.S → ℂ) 1 := by
    rw [hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hx,
      hyp.sSet_caseB_apply_one_eq_qu hG chars caseB hy]
  rcases ClassFunction.support_sub_subset x y hz with h | h
  · rcases hyp.sSet_member_support_subset hG hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset hG hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **`C_U(H̄) = C`** for the `S`-instance: the §9 kernel `cSub` (`= C_U(H̄)`) equals Peterfalvi's
`C = C_U(P) = U ⊓ C_G(P)`.  The reverse `C ≤ cSub` is general (an element of `U` centralizing
`H = P` acts trivially on any quotient of `H`, so lies in the action kernel); the forward
`cSub ≤ C` uses `H₀ = ⊥` (`toTypesIIIIIIVSetupS_chief_H0_eq_bot`): with `H̄ = P/H₀ = P` the kernel
`cSub` centralizes `H = P` (`⁅cSub, H⁆ ≤ H₀ = ⊥`, `commutator_cSub_H_le_H0`).  This is the
last spelling piece of the (13.3.a) `μ_j = Ind_{PC}(linear)`: `HC = P·C = P·cSub`. -/
theorem Hypothesis.toTypesIIIIIIVSetupS_cSub_eq_C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief = hyp.C := by
  have := hyp.finiteG
  have := chief.N_normal
  have hUeq : (hyp.toTypesIIIIIIVSetupS hG).U = hyp.U := hyp.Sdata_U_eq
  have hHeq : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  apply le_antisymm
  · -- forward: `cSub ≤ U ⊓ C_G(P)`
    rw [hyp.C_eq]
    intro g hg
    refine Subgroup.mem_inf.mpr ⟨hUeq ▸ OddOrder.Peterfalvi.S11.cSub_le_U _ chief hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    -- `⁅cSub, H⁆ ≤ H₀ = ⊥`, so `g` centralizes `H = P`
    have hcomm : ⁅OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief,
        (hyp.toTypesIIIIIIVSetupS hG).H⁆ ≤ ⊥ := by
      rw [← hyp.toTypesIIIIIIVSetupS_chief_H0_eq_bot hG chief]
      exact OddOrder.Peterfalvi.S11.commutator_cSub_H_le_H0 _ chief
    have hpH : p ∈ (hyp.toTypesIIIIIIVSetupS hG).H := hHeq ▸ hp
    have hcm := hcomm (Subgroup.commutator_mem_commutator hg hpH)
    rw [Subgroup.mem_bot, commutatorElement_def] at hcm
    -- `g p g⁻¹ p⁻¹ = 1 ⟹ p g = g p`
    have hpg : g * p * g⁻¹ = p := by
      have h1 : g * p * g⁻¹ * p⁻¹ * p = p := by rw [hcm, one_mul]
      rwa [inv_mul_cancel_right] at h1
    have hgp : g * p = p * g := by
      have h2 : g * p * g⁻¹ * g = p * g := by rw [hpg]
      rwa [inv_mul_cancel_right] at h2
    exact hgp.symm
  · -- reverse: `U ⊓ C_G(P) ≤ cSub`
    rw [hyp.C_eq]
    intro g hg
    obtain ⟨hgU, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgUdata : g ∈ (hyp.toTypesIIIIIIVSetupS hG).U := hUeq ▸ hgU
    have hgUW1 : g ∈ (hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1 :=
      (le_sup_left : (hyp.toTypesIIIIIIVSetupS hG).typeP.U ≤ _) hgUdata
    set bUW1 : ↥((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) := ⟨g, hgUW1⟩ with hbUW1def
    have hbUW1mem : bUW1 ∈ ((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hgUdata
    -- `bUW1` acts trivially on `H̄`: `g` centralizes `H = P`
    have haut : quotientMulAutHom chief.N_aInvariant bUW1 = 1 := by
      ext q
      refine QuotientGroup.induction_on q ?_
      intro x
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
        chief.N_aInvariant bUW1 x, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply]
      have hxP : ((x : G)) ∈ hyp.P := hHeq ▸ x.2
      have hcx : g * (x : G) = (x : G) * g :=
        (Subgroup.mem_centralizer_iff.mp hgC (x : G) hxP).symm
      change (bUW1 : G) * (x : G) * (bUW1 : G)⁻¹ = (x : G)
      rw [hbUW1def]
      change g * (x : G) * g⁻¹ = (x : G)
      rw [hcx]; group
    have hbker : (⟨bUW1, hbUW1mem⟩ : ↥(((hyp.toTypesIIIIIIVSetupS hG).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)))
        ∈ (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupS hG) chief).ker := by
      rw [MonoidHom.mem_ker, OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply]
      exact haut
    -- assemble `g ∈ cSub`
    simp only [OddOrder.Peterfalvi.S11.cSub, Subgroup.mem_map]
    exact ⟨bUW1, ⟨⟨bUW1, hbUW1mem⟩, hbker, rfl⟩, rfl⟩

end OddOrder.Peterfalvi.S15



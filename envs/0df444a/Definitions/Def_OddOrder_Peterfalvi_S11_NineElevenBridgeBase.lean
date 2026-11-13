-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenBridgeBase
-- name    : OddOrder_Peterfalvi_S11_NineElevenBridgeBase
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:31:19.911796+00:00
-- url     : https://prove2.me/theorems/ec40adbe-34c6-4173-b9f0-c652d15276ef
-- title:
--   Peterfalvi (8.15.3)/(9.5): the §9 family inside the (8.15.3) family, base layer
-- statement:
--   Formalizes the base layer of the subcoherence bridge showing that the §9 family sits inside the (8.15.3) family (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8 (8.15.3), §9 (9.5), pp. 47-51), yielding the base coherence used by (9.11).
--
--   Main declarations: `sOf_subset_inducedNonKernelFamily` (The §9 family is contained in the (8.15.3) family); `sOf_degreeSubfamily_coherent` ((9.11) base coherence at §9 level); `caseA_coherent_sOf_cprime_of_refuter` (Peterfalvi (9.11), case (9.7.a), at §9 level); `sOf_subset_inducedKernelFamily_bot` (The §9 family sits inside the `⊥`-kernel induced family).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenBridgeBase.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenBridgeBase.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence
import Definitions.Def_OddOrder_Peterfalvi_S10_SubcoherentTypeP
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **`M' ⊴ M`, realised inside `↥M`**: `(derivedInG M).subgroupOf M` is the comap of a `map` along
the injective `M.subtype`, i.e. `commutator ↥M`.

The §11/§13 chain gets this instance transitively from its packaging's import closure; the §9 leaves
here need it explicitly to borrow the `S08.inducedKernelFamily_*` suite. -/
theorem derivedInG_subgroupOf_normal (M : Subgroup G) : ((derivedInG M).subgroupOf M).Normal := by
  rw [derivedInG, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

/-- **`H` sits inside `M_σ`, realised in `HU`**: `hInHu data ≤ (M_σ.subgroupOf M).subgroupOf (HU)`.

Two applications of `Subgroup.subgroupOf` monotonicity to `M_F ≤ M_σ`
(`BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma`, rewritten through `data.typeP.H_eq`). -/
theorem hInHu_le_Msigma_subgroupOf [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) :
    hInHu data ≤ ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).subgroupOf (huSub data) := by
  have hMF : data.H ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [show data.H = data.typeP.H from rfl, data.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM
  exact Subgroup.comap_mono (Subgroup.comap_mono hMF)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §9 family is contained in the (8.15.3) family** (issue 1045): `𝒮(Y) ⊆ 𝒮_{(8.15.3)}`.

This is what lets Peterfalvi's own route to the (9.11) base coherence — (8.15.3) followed by (5.7)
— replace the repo's §10 μ-grid engine, and with it the type-III/IV restriction: the (8.15.3)
producer `S10.typePACore_subcoherent` carries no type hypothesis beyond `IsTypeP`.

The proof establishes membership over `huSub data` and then transports along
`huSub_eq_derivedInG_subgroupOf`; the two subgroups are only *propositionally* equal, so
`↥(huSub data)` and `↥((derivedInG M).subgroupOf M)` are distinct types and the characters do not
transfer definitionally.  This is the same `▸`-transport idiom the repo already uses for
`S08.inducedKernelFamily` (`S15_SSetMemberRFamily`). -/
theorem sOf_subset_inducedNonKernelFamily [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ OddOrder.Peterfalvi.S10.inducedNonKernelFamily
      ((derivedInG M).subgroupOf M) ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
  have hKeq : huSub data = (derivedInG M).subgroupOf M :=
    huSub_eq_derivedInG_subgroupOf data
  have hle := hInHu_le_Msigma_subgroupOf hG hM data
  -- first over `huSub data`, then transport
  have hbase : sOf data Y ⊆ OddOrder.Peterfalvi.S10.inducedNonKernelFamily
      (huSub data) ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
    rintro φ ⟨χ, hχ, rfl⟩
    refine ⟨χ, ?_, induceHU_eq_induce data _⟩
    -- `M_σ ⊄ Ker χ`: else `H ⊆ Ker χ` too, contradicting `χ ∈ 𝒳`
    intro hsub
    exact hχ.1 fun x hx => hsub (SetLike.mem_coe.mpr (hle (SetLike.mem_coe.mp hx)))
  exact hKeq ▸ hbase

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(9.11) base coherence at §9 level**: the degree-`d` irreducible cut of `𝒮(Y)` is coherent.

This is the step that takes the (9.11) base case off the §10 μ-grid engine.  The repo obtained it
from `S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`, which needs a `S13.Hypothesis` and
hence types III/IV; Peterfalvi instead routes it through **(8.15.3) then (5.7)**, neither of which
carries a type hypothesis.  Here that route is assembled:

* the cut sits inside the (8.15.3) family — `sOf_subset_inducedNonKernelFamily`;
* it is conjugation-closed — `irrCut_conjClosed` (§9-level since issue 1045);
* it is finite — `sOf_finite` (§9-level since issue 1045);
* (5.3.b) + (5.7) — `S10.inducedNonKernelFamily_degreeSubfamily_coherent`.

⚠ `h2 : 2 ≤ ncard` stays exposed, as in the §8 companion and in
`S15.Hypothesis.sSetIrrDeg_coherent`: the (9.8.d) count gives `∃ ζ`, not two members.

`hKeq` pins Hypothesis (4.6)'s `K` to `M'`, and `hHle` asks only that its `H` *contain* `M_σ` —
the book's choice `H = M_s = M_σ` (`S10.typePACore_toHypothesis46_core`) is the equality case, and
the §10/§13 packaging, which instantiates (4.6.c) at the larger `H = K = M'`, also qualifies
(`inducedNonKernelFamily_mono`; issue 1045 着手順 3).  They are hypotheses rather than definitional
assumptions so that no `Hypothesis46Core` has to be rebuilt here (rebuilding it is what makes the
two copies fail to be definitionally equal). -/
theorem sOf_degreeSubfamily_coherent [Finite G] {M : Subgroup G} {A : Set G}
    (hodd : Odd (Nat.card ↥M))
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46Core A M)
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) (d : ℕ)
    (hKeq : h46.K = (derivedInG M).subgroupOf M)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46.subH)
    (hd0 : ((d : ℂ)) ≠ 0)
    (h2 : 2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.ncard)
    (h1A : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S10.inducedNonKernelFamily_subcoherent hodd h46 dd
        (fun _ hx => OddOrder.Peterfalvi.S10.inducedNonKernelFamily_mono hHle
          (hKeq ▸ sOf_subset_inducedNonKernelFamily hG hM data Y hx.1))
        (fun _ hx => hx.2.1)
        (fun _ hx => irrCut_conjClosed data Y d hx)).tau
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M)) :=
  OddOrder.Peterfalvi.S10.inducedNonKernelFamily_degreeSubfamily_coherent hodd h46 dd _ _ _
    ((sOf_finite data Y).subset fun _ hx => hx.1) h2 (d : ℂ) (fun _ hx => hx.2.2) hd0 h1A

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), case (9.7.a), at §9 level**: reduction to the maximality refuter.

The §9-level form of `S13.caseA_coherent_sOf_H0Cprime_of_refuter`.  Everything is stated over
Hypotheses (9.2)/(9.4)/(9.5) — `data`, `chief`, `chars` — with the Dade map `tau` and support `A0`
as explicit parameters, so **no type hypothesis appears anywhere**.

The §11 version reaches the same conclusion through `S13.Hypothesis`, whose `type_alt` pins types
III/IV.  Tracing its proof shows that packaging is inessential: `hyp.C` is `cSub data chief`,
`hyp.H0Cprime` is `chief.H0 ⊔ cprimeSub data chief`, `hyp.base.tau`/`.A0` are parameters, the
finiteness bridge is `sOf_finite`, and the degree-`qa` base coherence — the one genuinely §10-bound
input, via `S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent` — becomes the parameter
`hbase`, which `sOf_degreeSubfamily_coherent` supplies along the book's (8.15.3) → (5.7) route.

Book argument (unchanged): the (9.8.d) count `caseA_character_count_exact` has positive lower
bound `(p−1)·[U:U′]`, so a degree-`qa` irreducible exists in `𝒮(H₀U′)`; it transports to
`𝒮(H₀C′)` along `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′`), and the maximality skeleton
`S07.coherent_of_maximal_coherent_pair_refuted` closes it against `hrefute`. -/
theorem caseA_coherent_sOf_cprime_of_refuter [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G) (A0 : Set ↥M)
    (caseA : CliffordCaseAData chars)
    (hbase : OddOrder.Peterfalvi.S07.IsCoherent tau
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} A0)
    (hrefute : ∀ S₂ : Set (ClassFunction ↥M ℂ),
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
          IsIrreducibleCharacter φ ∧
          ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))} ⊆ S₂ →
        S₂ ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) →
        OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂ →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau S₂ A0) →
        (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty →
        (∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
          ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {χ, χ.conj}) A0)) → False) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent tau
      (sOf data (chief.H0 ⊔ cprimeSub data chief)) A0) := by
  classical
  -- positivity of the (9.8.d) count lower bound `(p−1)·[U:U′]`
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  have hrel : 0 < (uprimeSub data).relIndex data.U :=
    lt_of_lt_of_le (u_odd hG chars).pos (u_le_relIndex_uprimeSub_U chars)
  have hNpos := lt_of_lt_of_le (mul_pos hp1 hrel) (caseA_character_count_exact hG caseA)
  -- the (9.8.d) count set is nonempty: a degree-`qa` irreducible in `𝒮(H₀U′)`
  have hne : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
      IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    intro h0
    rw [h0, Nat.zero_mul] at hNpos
    exact absurd hNpos (lt_irrefl 0)
  -- `H₀C′ ≤ H₀U′` (`C′ = [C,C] ≤ [U,U] = U′` by derived-subgroup monotonicity)
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  -- assemble the reduction via the maximality skeleton
  exact OddOrder.Peterfalvi.S07.coherent_of_maximal_coherent_pair_refuted
    (S₁ := {φ : ClassFunction ↥M ℂ | φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ))})
    (sOf_finite data _)
    (sOf_closedUnderConjugate data _)
    (fun _ hφ => hφ.1)
    (fun _ hχ => irrCut_conjClosed data _ (data.q * caseA.a) hχ)
    ⟨hbase⟩
    hrefute

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The §9 family sits inside the `⊥`-kernel induced family**: `𝒮(Y) ⊆ S(⊥)`.

Composite of `sOf_subset_inducedNonKernelFamily` with
`S10.inducedNonKernelFamily_subset_inducedKernelFamily_bot`.

This is the §9-level replacement for the "world-bridge" step that the §11 chain performs with
`hyp.SOf_eq`/`hyp.sOf_subset_SOf` — the route through the `S13.Hypothesis` packaging.  The §11
pivot lemmas (`caseB_sOf_memberRFamily`, `sOf_anchor_diff_support`, …) use that bridge only to
borrow the `S08.inducedKernelFamily_*` suite (support, no-real-characters, pairwise orthogonality,
`ZIrr` membership); with this lemma they can borrow the same suite without a `S13.Hypothesis`. -/
theorem sOf_subset_inducedKernelFamily_bot [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun _ hx =>
  OddOrder.Peterfalvi.S10.inducedNonKernelFamily_subset_inducedKernelFamily_bot
    (sOf_subset_inducedNonKernelFamily hG hM data Y hx)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **A nonempty degree cut of `𝒮(Y)` has at least two members** — the `h2` input of
`sOf_degreeSubfamily_coherent`, from mere nonemptiness.

`G` has odd order, so no member of the `⊥`-kernel induced family is real
(`S08.inducedKernelFamily_hasNoRealCharacters`); the cut is conjugation-closed
(`irrCut_conjClosed`, degrees being natural numbers).  So `φ` and `φ̄` are two *distinct* members.

⚠ This is what lets the §9 route match §13's: §13 obtains its base coherence from the §10 μ-grid
engine with only an existence witness, while the (8.15.3) + (5.7) route of issue 1045 asks for
`2 ≤ ncard`.  The gap was apparent — for a conjugation-closed family in odd order the two are the
same condition. -/
theorem irrCut_two_le_ncard [Finite G] {M : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G) (d : ℕ)
    (hne : {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.Nonempty) :
    2 ≤ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.ncard := by
  classical
  have := derivedInG_subgroupOf_normal M
  obtain ⟨φ, hφ⟩ := hne
  have hφc := irrCut_conjClosed data Y d hφ
  have hne' : φ ≠ φ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)) (⊥ : Subgroup ↥M)
      (sOf_subset_inducedKernelFamily_bot hG hM data Y hφ.1) h.symm
  have hfin : {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}.Finite :=
    (sOf_finite data Y).subset fun _ hx => hx.1
  have hsub : ({φ, φ.conj} : Set (ClassFunction ↥M ℂ)) ⊆
      {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
        IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} := by
    rintro x (rfl | rfl)
    · exact hφ
    · exact hφc
  have hpair : ({φ, φ.conj} : Set (ClassFunction ↥M ℂ)).ncard = 2 := by
    rw [Set.ncard_pair hne']
  exact hpair ▸ Set.ncard_le_ncard hsub hfin

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Uniform-degree member differences are `A₀`-supported, at §9 level** (the `hsuppdiff` input of
the (9.11) caseB engine).

The §9 form of `S13.sOf_anchor_diff_support`.  That version reaches the `⊥`-kernel induced family
through `hyp.SOf_eq`/`hyp.sOf_subset_SOf`, i.e. through `S13.Hypothesis`; here the same step is
`sOf_subset_inducedKernelFamily_bot`, and the (8.10) containment `(M')^# ⊆ A₀` — which the §13
version reads off `hyp.base.mderivSharp_subset_A0` — becomes the explicit parameter `hKsupp`.

Neither version needs a type hypothesis; the §13 binding was purely the packaging. -/
theorem sOf_anchor_diff_support [Finite G] {M : Subgroup G} {A0 : Set ↥M}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    (data : TypesIIIIIIVSetup M) (Y : Subgroup G)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 → x ∈ A0)
    (d : ℕ) (hunif : ∀ φ ∈ sOf data Y, ((φ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (d : ℂ))
    {χ₁ x : ClassFunction ↥M ℂ}
    (hχ₁mem : χ₁ ∈ sOf data Y) (hx : x ∈ sOf data Y) :
    ((x - χ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 := by
  have := derivedInG_subgroupOf_normal M
  have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hx)
    (sOf_subset_inducedKernelFamily_bot hG hM data Y hχ₁mem) (d := 1)
    (by rw [Nat.cast_one, one_mul, hunif x hx, hunif χ₁ hχ₁mem])
  rwa [one_smul] at h

end OddOrder.Peterfalvi.S11



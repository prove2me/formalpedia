-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_Hypothesis
-- name    : OddOrder_Peterfalvi_S14_MaximalI_Hypothesis
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:46:40.054208+00:00
-- url     : https://prove2.me/theorems/80af632c-930b-41f8-8960-abacde171aa4
-- title:
--   Peterfalvi (12.1)–(12.2.b): type I hypothesis, Dade domain and $R(\chi)$ families
-- statement:
--   Formalizes Hypothesis (12.1), the setup for a maximal subgroup $L$ of type I, together with its Dade domain and the $R(\chi)$ families of (12.2.b).
--
--   Main declarations: `Hypothesis` (Peterfalvi (12.1)); `H` (Peterfalvi's `H = L_F`); `ambientA` (Peterfalvi's ambient `A(L)` set from Definition (8.3)); `A` (Peterfalvi's support `A(L)` restricted to `L` (the `supportInSubgroup` of the ambient `A(L)`)…).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/Hypothesis.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/Hypothesis.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IV
import Definitions.Def_OddOrder_Peterfalvi_S10_CoherenceWiring
import Definitions.Def_OddOrder_Peterfalvi_S09_CertificateDischarge
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceConstantDegree
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CliffordDecomposition
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CyclotomicCharacterCongruence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedInvariantConstituent
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Mathlib.RepresentationTheory.Irreducible

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1)**: setup for a maximal subgroup `L` of type I.

`G` is finite (carried as the instance field `finiteG`, the `S12`/`S15`
`FiniteInduce` pattern), so the *genuine* Dade isometry `tau`, the induced family
`Sset = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` (`H = L_F`), and the support `A = A(L)`
are honest projections (`Hypothesis.tau`, `Hypothesis.Sset`, `Hypothesis.A`)
rather than unconstrained data.  `dadeData` is the (8.15) Dade support hypothesis
for `A(L)` (supplied by `S10.dadeSupportHypotheses_typeI`), and `hconj` is its
`L`-conjugation invariance; together they build the Dade isometry relative to
`(A(L), L, G)` (Peterfalvi (12.1)). -/
structure Hypothesis (L : Subgroup G) where
  [finiteG : Finite G]
  maximal : L ∈ maximalSubgroups G
  typeI : TypeIData L
  dadeData : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData L (typeIA L typeI)

namespace Hypothesis

/-- Peterfalvi's `H = L_F`. -/
def H {L : Subgroup G} (hyp : Hypothesis L) : Subgroup G :=
  hyp.typeI.typeF.H

/-- Peterfalvi's ambient `A(L)` set from Definition (8.3). -/
def ambientA {L : Subgroup G} (hyp : Hypothesis L) : Set G :=
  typeIA L hyp.typeI

/-- Peterfalvi's support `A(L)` restricted to `L` (the `supportInSubgroup` of the
ambient `A(L)`), the genuine support of the Dade isometry, no longer an
unconstrained field. -/
def A {L : Subgroup G} (hyp : Hypothesis L) : Set ↥L :=
  OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's family `S = {Ind_H^L θ | θ ∈ Irr H, θ ≠ 1_H}` of (12.1),
`H = L_F`, induced via the canonical `ClassFunction.induce`.  No longer an
unconstrained field. -/
noncomputable def Sset {L : Subgroup G} (hyp : Hypothesis L) :
    Set (ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  { χ | ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      χ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) }

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The **filtration** `S(A) = {Ind_H^L θ | θ ≠ 1, A ⊆ Ker θ}` of the witness family `Sset`
(Peterfalvi (6.1)), indexed by subgroups `A ≤ L`.  `S(⊥) = Sset`, and the abstract Peterfalvi (6.3)
descent `six_three_of_six_two_oracle` runs on this filtration (with `SOf = SsubFiltration`,
`τ = tau`, `A0 = A`, kernel `H = L_F`).  Mirrors the Sibley `SibleyDadeHypothesis.SsubFiltration`
but over the witness's canonical `(L_F).subgroupOf L` kernel and Dade map. -/
noncomputable def SsubFiltration {L : Subgroup G} (hyp : Hypothesis L) (A : Subgroup ↥L) :
    Set (ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  { φ | ∃ θ : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L),
      θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) ∧
      ((A.subgroupOf ((hyp.typeI.typeF.H).subgroupOf L)) :
          Set ↥((hyp.typeI.typeF.H).subgroupOf L)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ∧
      φ = ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) }

/-- `S(⊥) = Sset`: the kernel condition `⊥ ⊆ Ker θ` is vacuous (Peterfalvi's `S(1) = S`). -/
theorem SsubFiltration_bot {L : Subgroup G} (hyp : Hypothesis L) :
    hyp.SsubFiltration ⊥ = hyp.Sset := by
  ext φ
  simp only [SsubFiltration, Sset, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨θ, hθ, -, hφ⟩; exact ⟨θ, hθ, hφ⟩
  · rintro ⟨θ, hθ, hφ⟩
    refine ⟨θ, hθ, ?_, hφ⟩
    rw [Subgroup.bot_subgroupOf, Subgroup.coe_bot]
    intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _

/-- Every member of a filtration level `S(A)` lies in the ambient family `Sset`. -/
theorem SsubFiltration_subset_Sset {L : Subgroup G} (hyp : Hypothesis L) {A : Subgroup ↥L} :
    hyp.SsubFiltration A ⊆ hyp.Sset := by
  intro φ hφ
  simp only [SsubFiltration, Set.mem_ofPred_eq] at hφ
  obtain ⟨θ, hθ, -, hφeq⟩ := hφ
  simp only [Sset, Set.mem_ofPred_eq]
  exact ⟨θ, hθ, hφeq⟩

/-- The filtration is **antitone**: a larger kernel-constraint subgroup gives fewer members,
`A ≤ B → S(B) ⊆ S(A)` (Peterfalvi (6.1)). -/
theorem SsubFiltration_antitone {L : Subgroup G} (hyp : Hypothesis L) {A B : Subgroup ↥L}
    (hAB : A ≤ B) : hyp.SsubFiltration B ⊆ hyp.SsubFiltration A := by
  intro φ hφ
  simp only [SsubFiltration, Set.mem_ofPred_eq] at hφ ⊢
  obtain ⟨θ, hθ, hker, hφeq⟩ := hφ
  refine ⟨θ, hθ, ?_, hφeq⟩
  intro x hxA
  exact hker (Subgroup.mem_subgroupOf.mpr (hAB (Subgroup.mem_subgroupOf.mp hxA)))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- Peterfalvi's Dade isometry `τ` relative to `(A(L), L, G)` of (12.1), pinned to
the genuine `S07.dadeIntegralCharacterMap` of the (8.15) support data `dadeData`.
No longer an unconstrained field. -/
noncomputable def tau {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The Peterfalvi (7.1) `ρ`-machinery data for `(L, A(L))`** — the §7 foundation for the (12.16)
Dade calculation.  Built genuinely from the §10 Dade isometry carried by `hyp.dadeData`/`hyp.hconj`:
unlike the type-`P` `S12.Hypothesis.toHypothesis71`, the type-I support `A(L) = typeIA` is already
the
set on which `dadeData` lives, so no restriction is needed — the Dade map, its `IsDadeMap`
certificate, and the `L`-equivariance transfer directly.  This `S09.Hypothesis71` is what lets the
§9 norm machinery — `chiRho_norm_sq_le` (7.2.b), `chiRho_integral_inequality` (7.3),
`family_inequality` (7.5), and `Hypothesis78.NormEstimates` (7.8.b) — apply to `L`. -/
noncomputable def toHypothesis71 {L : Subgroup G} [Finite G] (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (typeIA L hyp.typeI) L where
  hyp := hyp.dadeData.dade
  τ := (hyp.dadeData.dade.fullDadeIsometryData).toDadeIsometryData.toDadeMap
  isDadeMap := (hyp.dadeData.dade.fullDadeIsometryData).toDadeIsometryData.isDadeMap

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **τ-bridging**: the §9 `Hypothesis71` Dade map `toHypothesis71.τ` (a `DadeMap` on
`SupportedClassFunctions`) agrees with the §7 integral character map `tau` on supported functions.
Both unfold to the underlying §4 Dade map `dadeData.dade.dadeMap` — via
`dadeIntegralCharacterMap_apply_of_support` and `dadeIsometryData_toDadeMap`.  Lets the
`chiRho_adjoint` reciprocity (stated for `toHypothesis71.τ`) meet the coherence
`extends_on_supported` (stated for `tau`) in the (12.5) `o_rpsi_S` Fact-A. -/
theorem toHypothesis71_tau_apply {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ (typeIA L hyp.typeI) L) :
    hyp.toHypothesis71.τ α = hyp.tau (α : ClassFunction ↥L ℂ) := by
  have := hyp.finiteG
  have hsupp : (α : ClassFunction ↥L ℂ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L :=
    (ClassFunction.mem_supportedSubmodule).mp α.2
  have hmap : hyp.toHypothesis71.τ = hyp.dadeData.dade.dadeMap (k := ℂ) :=
    OddOrder.Peterfalvi.S04.IsDadeMap.unique hyp.toHypothesis71.isDadeMap
      hyp.dadeData.dade.isDadeMap_dadeMap
  rw [tau, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      hyp.dadeData.dade _ hsupp, hmap]

end Hypothesis

/-- Conjugation transports the centralizer of a singleton:
`g · C_G(a) · g⁻¹ = C_G(g a g⁻¹)` (S14-local copy of the S12 helper; pure group theory). -/
theorem conj_smul_centralizer_singleton (g a : G) :
    MulAut.conj g • Subgroup.centralizer ({a} : Set G)
      = Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_centralizer_iff,
      Subgroup.mem_centralizer_iff]
  have hinv : (MulAut.conj g)⁻¹ • y = g⁻¹ * y * g := by
    rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
  simp only [Set.mem_singleton_iff, forall_eq, hinv]
  constructor
  · intro h
    calc g * a * g⁻¹ * y
        = g * (a * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * a) * g⁻¹ := by rw [h]
      _ = y * (g * a * g⁻¹) := by group
  · intro h
    calc a * (g⁻¹ * y * g)
        = g⁻¹ * (g * a * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * a * g⁻¹)) * g := by rw [h]
      _ = g⁻¹ * y * g * a := by group

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.1), construction from explicit type-I data**: a type-I maximal subgroup `L`
with a *given* `TypeIData` carries the (12.1) Hypothesis whose `typeI` field is exactly that data.
This refines `exists_typeI_hypothesis` by preserving the identity of the type-I witness, so callers
holding a `TypeIData` (e.g. the Frobenius structure of (12.10)) can recover it — and the associated
Frobenius decomposition of `H = L_F` — from the resulting `Hypothesis`.  The Dade isometry, induced
family, and support are the genuine `S07.dadeIntegralCharacterMap`, `Sset`, and `A(L)`; the only
inputs are the (8.15) Dade support data (`S10.dadeSupportHypotheses_typeI`) and the conjugation
invariance `hconj` of the support kernels (a (8.14)/(8.15) fact). -/
theorem hypothesis_of_typeIData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (data : TypeIData L) :
    ∃ hyp : Hypothesis L, hyp.typeI = data := by
  obtain ⟨dadeData⟩ :=
    (OddOrder.Peterfalvi.S10.dadeSupportHypotheses_typeI hG hL data).1
  -- (8.14)/(8.15): the kernel conjugation invariance is carried by the faithful datum.
  exact ⟨{ maximal := hL, typeI := data, dadeData := dadeData }, rfl⟩

/-- **Peterfalvi (12.1), existence**: every type-I maximal subgroup `L` carries the (12.1)
Hypothesis.  Forgetful form of `hypothesis_of_typeIData`.  Mirrors
`S12.exists_hypothesis_of_typeIIIorIVorV`. -/
theorem exists_typeI_hypothesis [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G}
    (hL : L ∈ maximalSubgroups G) (hType : IsTypeI L) :
    Nonempty (Hypothesis L) := by
  obtain ⟨data⟩ := hType
  obtain ⟨hyp, _⟩ := hypothesis_of_typeIData hG hL data
  exact ⟨hyp⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The type-I family `S = {Ind_H^L θ}` is closed under complex conjugation**
(Peterfalvi §12, the `χ̄ ∈ S` input to (12.2.b)): for `χ = Ind_H^L θ ∈ S` with
`θ ∈ Irr H`, `θ ≠ 1`, the conjugate is `χ̄ = Ind_H^L θ̄` (`ClassFunction.induce_conj`),
and `θ̄` is again a non-trivial irreducible of `H = L_F`. -/
theorem Sset_closedUnderConjugate [Finite G] {L : Subgroup G} (hyp : Hypothesis L) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Sset := by
  classical
  intro φ hφ
  simp only [Hypothesis.Sset, Set.mem_ofPred_eq] at hφ ⊢
  obtain ⟨θ, hθ_ne, hφeq⟩ := hφ
  refine ⟨⟨(θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj,
    θ.isIrreducible.conj⟩, ?_, ?_⟩
  · -- `θ̄ ≠ 1`: else `θ = θ̄̄ = 1̄ = 1` (the trivial character is real).
    intro h
    apply hθ_ne
    have hcoe : (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ).conj
        = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) := by
      simpa using congrArg
        (fun c : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) =>
          (c : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) h
    apply Subtype.ext
    change (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)
      = trivialClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L)
    rw [← ClassFunction.conj_conj
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), hcoe]
    exact trivialClassFunction_isReal
  · rw [hφeq]
    simpa using ClassFunction.induce_conj ((hyp.typeI.typeF.H).subgroupOf L)
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)

/-- **Peterfalvi (12.2)**, genuine carrier: the constituent decomposition of `χ ∈ S`.
`S(χ) = constituents` is the (finite, nonempty) set of irreducible constituents of `χ`, all of
equal degree ((12.2.a)), each non-real (so `φ ≠ φ̄`) and supported in `A(L) ∪ {1}` (so the
differences `φ − φ̄` lie in the Dade domain `A(L)`, feeding (12.2.b) `R1`/`Rset`). -/
structure CharacterDecompositionData {L : Subgroup G} (hyp : Hypothesis L)
    (chi : ClassFunction ↥L ℂ) where
  chi_mem : chi ∈ hyp.Sset
  /-- `S(χ)`: the irreducible constituents of `χ`. -/
  constituents : Finset (IrreducibleCharacter ↥L)
  constituents_nonempty : constituents.Nonempty
  /-- (12.2.a): `χ` is the multiplicity-one sum of its constituents. -/
  decomp : chi = ∑ φ ∈ constituents, (φ : ClassFunction ↥L ℂ)
  /-- (12.2.a): the constituents share a common degree. -/
  equal_degree : ∀ φ ∈ constituents, ∀ φ' ∈ constituents,
    ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
  /-- Each constituent is non-real, so `φ ≠ φ̄` and `φ − φ̄ ≠ 0` ((12.2.b)). -/
  not_real : ∀ φ ∈ constituents, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)
  /-- (12.2.b): no constituent is the conjugate of another — `S(χ) ∩ conj S(χ) = ∅`.  From
  `⟨χ, χ̄⟩ = 0`: `χ̄ ∈ S` (`Sset_closedUnderConjugate`), `χ ≠ χ̄` ((1.5.e)), distinct members
  of `S` are orthogonal ((1.5.c)), and the decomposition is multiplicity-one, so a shared
  irreducible between `S(χ)` and `S(χ̄) = conj S(χ)` would force `⟨χ, χ̄⟩ ≥ 1`.  Feeds the
  cross-`φ` image distinctness of the (12.3) bar-trick descent. -/
  conj_not_mem : ∀ φ ∈ constituents, ∀ φ' ∈ constituents,
    (φ : ClassFunction ↥L ℂ).conj ≠ (φ' : ClassFunction ↥L ℂ)
  /-- (12.2.a): each constituent is supported in `A(L) ∪ {1}` (`H ⊄ Ker φ` (1.5.a), then (1.2)),
  so each difference `φ − φ̄` is supported in the Dade domain `A(L)`. -/
  supported : ∀ φ ∈ constituents, (φ : ClassFunction ↥L ℂ).support ⊆
    OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}

/-- **A commuting element of coprime order is a power of the product** — `g ∈ ⟨zg⟩` when `z`, `g`
commute with coprime orders.  `(zg)^{|z|} = g^{|z|}` (commuting, `z^{|z|}=1`), and `g ∈ ⟨g^{|z|}⟩`
since `gcd(|z|, |g|) = 1` (`mem_zpowers_pow_iff`); hence `g ∈ ⟨(zg)^{|z|}⟩ ≤ ⟨zg⟩`.  This is the
`π`-part step of Peterfalvi (8.2.c): once `(2.1)` conjugates `cg` to a *commuting* product `zg`
(`z ∈ C_H(g)`), `g` is a power of `zg`, so `g` centralizes whatever `zg` does. -/
theorem mem_zpowers_mul_of_commute_coprime {Γ : Type*} [Group Γ] {z g : Γ}
    (hzg : Commute z g) (hcop : Nat.Coprime (orderOf z) (orderOf g)) :
    g ∈ Subgroup.zpowers (z * g) := by
  have hpow : (z * g) ^ orderOf z = g ^ orderOf z := by
    rw [hzg.mul_pow, pow_orderOf_eq_one, one_mul]
  have hg : g ∈ Subgroup.zpowers (g ^ orderOf z) := mem_zpowers_pow_iff.mpr hcop
  rw [← hpow] at hg
  have hle : Subgroup.zpowers ((z * g) ^ orderOf z) ≤ Subgroup.zpowers (z * g) :=
    Subgroup.zpowers_le.mpr ((Subgroup.zpowers (z * g)).pow_mem (Subgroup.mem_zpowers _) _)
  exact hle hg

/-- **Type-`F` class-fixing: an element of `U ∖ U₁` fixes only the identity `H`-class**
(the core of Peterfalvi (8.2.c)).  This is the type-`F` analogue of
`ConjugationBrauer.fixed_eq_one_of_not_mem_of_centralizer_le`, which uses the Frobenius condition
`C_G(h) ≤ H`; here the weaker type-`F` condition `U ⊓ C_G(x) ≤ U₁` (`TypeFData.centralizer_le_U1`)
suffices, at the cost of the coprime `(2.1)` step.  If `g ∈ U ∖ U₁` (`g` coprime to `H`, normalizing
`H`) fixes a class `⟦h⟧` (`h ≠ 1`), then some `c·g` centralizes `h` (`IsConj`); by (2.1)
(`exists_mem_centralizer_conj`) `c·g` is `H`-conjugate to `z·g` with `z ∈ C_H(g)`, so `z·g`
centralizes `w = yhy⁻¹ ≠ 1`; as `z` commutes with `g` coprimely, `g ∈ ⟨z·g⟩` centralizes `w`
(`mem_zpowers_mul_of_commute_coprime`), whence `g ∈ U ⊓ C_G(w) ≤ U₁` — contradiction. -/
theorem fixed_conjClass_eq_one_of_typeF {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [hHN : H.Normal] {g : Γ}
    (hcop : Nat.Coprime (orderOf g) (Nat.card ↥H)) (hgU : g ∈ U) (hgU1 : g ∉ U1)
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1)
    {C : ConjClasses ↥H}
    (hfix : ConjClasses.conjByPerm (G := Γ) (H := H) g C = C) :
    C = 1 := by
  classical
  have hnorm : ∀ x ∈ H, g * x * g⁻¹ ∈ H := fun x hx => hHN.conj_mem x hx g
  rcases ConjClasses.exists_rep C with ⟨h, rfl⟩
  by_cases hh : h = 1
  · rw [hh, ConjClasses.one_eq_mk_one]
  exfalso
  have hmk : ConjClasses.mk (ClassFunction.conjByMulEquiv (G := Γ) (H := H) g h)
      = ConjClasses.mk h := by simpa [ConjClasses.conjByPerm_mk] using hfix
  have hisConj : IsConj (ClassFunction.conjByMulEquiv (G := Γ) (H := H) g h) h :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hmk
  obtain ⟨c, hc⟩ := isConj_iff.mp hisConj
  have hcG : (c : Γ) * (g * (h : Γ) * g⁻¹) * (c : Γ)⁻¹ = (h : Γ) := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, ClassFunction.conjByMulEquiv_apply]
      using congrArg Subtype.val hc
  have hxconj : ((c : Γ) * g) * (h : Γ) * (((c : Γ) * g)⁻¹) = (h : Γ) := by
    simpa [mul_assoc] using hcG
  have hxcent : (c : Γ) * g ∈ Subgroup.centralizer ({(h : Γ)} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul := congrArg (fun y : Γ => y * ((c : Γ) * g)) hxconj
    simpa [mul_assoc] using hmul
  -- (2.1): `c·g ∈ Hg` is `H`-conjugate to `z·g` with `z ∈ C_H(g)`.
  obtain ⟨z, hz, y, hy, hyz⟩ :=
    exists_mem_centralizer_conj (g := g) (H := H) hcop hnorm c.property
  have hzC : z ∈ Subgroup.centralizer ({g} : Set Γ) := (Subgroup.mem_inf.mp hz).2
  have hzH : z ∈ H := (Subgroup.mem_inf.mp hz).1
  -- `w = y·h·y⁻¹ ∈ H`, `w ≠ 1`.
  set w : Γ := y * (h : Γ) * y⁻¹ with hwdef
  have hwH : w ∈ H := H.mul_mem (H.mul_mem hy (h.property)) (H.inv_mem hy)
  have hh1 : (h : Γ) ≠ 1 := fun hc1 => hh (Subtype.ext hc1)
  have hw1 : w ≠ 1 := by
    rw [hwdef]; intro hc1
    exact hh1 (by
      have := congrArg (fun t : Γ => y⁻¹ * t * y) hc1
      simpa [mul_assoc] using this)
  -- `z·g` centralizes `w`.
  have hzgw : z * g ∈ Subgroup.centralizer ({w} : Set Γ) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hyz, hwdef]
    have hce := (Subgroup.mem_centralizer_singleton_iff).mp hxcent
    calc y * ((c : Γ) * g) * y⁻¹ * (y * (h : Γ) * y⁻¹)
        = y * (((c : Γ) * g) * (h : Γ)) * y⁻¹ := by group
      _ = y * ((h : Γ) * ((c : Γ) * g)) * y⁻¹ := by rw [hce]
      _ = y * (h : Γ) * y⁻¹ * (y * ((c : Γ) * g) * y⁻¹) := by group
  -- `z` commutes with `g` coprimely ⟹ `g ∈ ⟨z·g⟩` centralizes `w`.
  have hCommute : Commute z g :=
    Subgroup.mem_centralizer_singleton_iff.mp hzC
  have hcopzg : Nat.Coprime (orderOf z) (orderOf g) := by
    have hzdvd : orderOf z ∣ Nat.card ↥H := by
      have := orderOf_dvd_natCard (⟨z, hzH⟩ : ↥H)
      simpa [orderOf_injective (H.subtype) H.subtype_injective ⟨z, hzH⟩] using this
    exact (Nat.Coprime.coprime_dvd_right hzdvd hcop).symm
  have hgzpow : g ∈ Subgroup.zpowers (z * g) := mem_zpowers_mul_of_commute_coprime hCommute hcopzg
  have hgw : g ∈ Subgroup.centralizer ({w} : Set Γ) :=
    (Subgroup.zpowers_le.mpr hzgw) hgzpow
  exact hgU1 (hcent w hwH hw1 (Subgroup.mem_inf.mpr ⟨hgU, hgw⟩))

/-- **Type-`F` fixed-class count is `1`** for `g ∈ U ∖ U₁`: the identity is the unique fixed
`H`-class (`fixed_conjClass_eq_one_of_typeF`), so `#{fixed classes} = 1`. -/
theorem card_fixedPoints_conjClassPerm_eq_one_of_typeF {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [H.Normal] {g : Γ}
    (hcop : Nat.Coprime (orderOf g) (Nat.card ↥H)) (hgU : g ∈ U) (hgU1 : g ∉ U1)
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1) :
    Nat.card (Function.fixedPoints (ConjClasses.conjByPerm (G := Γ) (H := H) g)) = 1 := by
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun C D => Subtype.ext ?_⟩,
    ⟨⟨1, ConjClasses.conjByPerm_one (G := Γ) (H := H) g⟩⟩⟩
  exact (fixed_conjClass_eq_one_of_typeF hcop hgU hgU1 hcent C.2).trans
    (fixed_conjClass_eq_one_of_typeF hcop hgU hgU1 hcent D.2).symm

/-- **Peterfalvi (8.2.c): `I(θ) ∩ U ⊆ U₁`** for a type-`F` group.  If `θ ∈ Irr H ∖ {1}` and
`g ∈ I(θ) ∩ U` but `g ∉ U₁`, then (`g` coprime to `H`) `g` fixes only the identity `H`-class
(`card_fixedPoints_conjClassPerm_eq_one_of_typeF`), so by Brauer's permutation lemma
(`fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one`) `g` fixes only the trivial character —
contradicting `g ∈ I(θ)`, `θ ≠ 1`.  Hence `g ∈ U₁`.  This is the inertia bound feeding the equal
degree of the constituents of `Ind_H^L θ` in the general type-I (12.2.a). -/
theorem typeF_inertia_inf_le_U1 {Γ : Type*} [Group Γ] [Finite Γ]
    {H U U1 : Subgroup Γ} [H.Normal]
    (hUHcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥H))
    (hcent : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set Γ) ≤ U1)
    (θ : IrreducibleCharacter ↥H) (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) ⊓ U ≤ U1 := by
  intro g hg
  have hgI := (Subgroup.mem_inf.mp hg).1
  have hgU := (Subgroup.mem_inf.mp hg).2
  by_contra hgU1
  have hcop : Nat.Coprime (orderOf g) (Nat.card ↥H) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard U hgU) hUHcop
  have hcard1 := card_fixedPoints_conjClassPerm_eq_one_of_typeF hcop hgU hgU1 hcent
  have hfixθ : IrreducibleCharacter.conjByPerm (G := Γ) (H := H) g θ = θ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.conjByPerm_apply, IrreducibleCharacter.coe_conjBy]
    exact ClassFunction.mem_inertia.mp hgI
  exact hθ (fixed_irreducible_eq_trivial_of_card_fixedClasses_eq_one g hcard1 hfixθ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Type-`F` induced-character constituent structure** (Peterfalvi (8.2.c) + (1.2)/(1.5.a) +
(1.7.c) + Clifford; a faithful §8 obligation — the deep content is type-`F` character theory living
in §8, not §12).  For a type-I maximal `L` and `χ = Ind_H^L θ ∈ S` (`θ ∈ Irr H ∖ {1}`), `χ` is the
multiplicity-one sum of a nonempty finite set of equal-degree, non-real irreducible constituents,
each supported in `A(L) ∪ {1}`.  Body = §8 type-`F` Clifford theory: (8.2.c) `I(θ) ∩ U ⊆ U₁` +
induced-degree (1.7.c) for the equal degree, `(Res_H φ, 1_H) = 0` (1.5.a) + (1.2) for the
support. -/
theorem typeI_induced_char_constituents [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ S : Finset (IrreducibleCharacter ↥L), S.Nonempty ∧
      chi = ∑ φ ∈ S, (φ : ClassFunction ↥L ℂ) ∧
      (∀ φ ∈ S, ∀ φ' ∈ S, ((φ : ClassFunction ↥L ℂ) : ↥L → ℂ) 1
        = ((φ' : ClassFunction ↥L ℂ) : ↥L → ℂ) 1) ∧
      (∀ φ ∈ S, ¬ ClassFunction.IsReal (φ : ClassFunction ↥L ℂ)) ∧
      (∀ φ ∈ S, ∀ φ' ∈ S,
        (φ : ClassFunction ↥L ℂ).conj ≠ (φ' : ClassFunction ↥L ℂ)) ∧
      (∀ φ ∈ S, (φ : ClassFunction ↥L ℂ).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ {1}) := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := hchi
  -- `H = (L_F).subgroupOf L`, kept as a raw term so `θ`'s type matches (no `set`).
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  have hodd : Odd (Nat.card ↥L) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
  obtain ⟨d, _hd_pos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hθirr := θ.isIrreducible
  have hHT : (hyp.typeI.typeF.H).subgroupOf L ≤ ClassFunction.inertia θ.toClassFunction :=
    ClassFunction.subgroup_le_inertia _
  have : (((hyp.typeI.typeF.H).subgroupOf L).subgroupOf
      (ClassFunction.inertia θ.toClassFunction)).Normal := hKnormal.comap _
  have hHU : (hyp.typeI.typeF.H).subgroupOf L ⊔ (hyp.typeI.typeF.U).subgroupOf L = ⊤ :=
    hyp.typeI.typeF.complement.sup_eq_top
  have hHall : Nat.Coprime (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L))
      ((hyp.typeI.typeF.H).subgroupOf L).index := by
    have h := (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall L).coprime_index
    rw [hyp.typeI.typeF.H_eq]; exact h
  have hUHcop : Nat.Coprime (Nat.card ↥((hyp.typeI.typeF.U).subgroupOf L))
      (Nat.card ↥((hyp.typeI.typeF.H).subgroupOf L)) := by
    have hidx : Nat.card ↥((hyp.typeI.typeF.U).subgroupOf L)
        = ((hyp.typeI.typeF.H).subgroupOf L).index :=
      (hyp.typeI.typeF.complement.symm.index_eq_card).symm
    rw [hidx]; exact hHall.symm
  have hcentL : ∀ x ∈ (hyp.typeI.typeF.H).subgroupOf L, x ≠ 1 →
      (hyp.typeI.typeF.U).subgroupOf L ⊓ Subgroup.centralizer ({x} : Set ↥L)
        ≤ (hyp.typeI.typeF.U1).subgroupOf L := by
    intro x hxK hx1 z hz
    obtain ⟨hzU, hzC⟩ := Subgroup.mem_inf.mp hz
    have hzUG : (z : G) ∈ hyp.typeI.typeF.U := Subgroup.mem_subgroupOf.mp hzU
    have hxHG : (x : G) ∈ hyp.typeI.typeF.H := Subgroup.mem_subgroupOf.mp hxK
    have hx1G : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hzCG : (z : G) ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hzC)
    exact Subgroup.mem_subgroupOf.mpr
      (hyp.typeI.typeF.centralizer_le_U1 (x : G) hxHG hx1G (Subgroup.mem_inf.mpr ⟨hzUG, hzCG⟩))
  have hbound : ClassFunction.inertia θ.toClassFunction ⊓ (hyp.typeI.typeF.U).subgroupOf L
      ≤ (hyp.typeI.typeF.U1).subgroupOf L :=
    typeF_inertia_inf_le_U1 hUHcop hcentL θ hθ_ne
  have hU1comm : IsMulCommutative ↥((hyp.typeI.typeF.U1).subgroupOf L) := by
    have hle : hyp.typeI.typeF.U1 ≤ L := le_trans hyp.typeI.typeF.U1_le hyp.typeI.typeF.U_le
    exact OddOrder.GroupTheory.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hle).symm hyp.typeI.typeF.U1_commutative
  have hcop : Nat.Coprime
      (((hyp.typeI.typeF.H).subgroupOf L).subgroupOf
        (ClassFunction.inertia θ.toClassFunction)).index
      (orderOf hθirr.determinant * d) :=
    OddOrder.RepresentationTheory.coprime_index_orderOf_determinant_mul_of_coprime_index
      hHT hHall hθirr hd
  have : Fintype ((ClassFunction.inertia θ.toClassFunction ⧸
      ((hyp.typeI.typeF.H).subgroupOf L).subgroupOf (ClassFunction.inertia θ.toClassFunction))
        →* ℂˣ) := Fintype.ofFinite _
  obtain ⟨_χ, _hχirr, S, hSne, _hScard, hSdecomp, hSdeg, _hSform⟩ :=
    OddOrder.RepresentationTheory.exists_extension_induce_eq_sum_distinct_of_inertia_inf_le
      hHT hθirr rfl hHU hbound hU1comm hd hcop
  have hchisum : chi = ∑ φ ∈ S, (φ : ClassFunction ↥L ℂ) := by rw [hchi_eq]; exact hSdecomp
  refine ⟨S, hSne, hchisum, ?_, ?_, ?_, ?_⟩
  · intro φ hφ φ' hφ'; rw [hSdeg φ hφ, hSdeg φ' hφ']
  · exact OddOrder.RepresentationTheory.forall_mem_not_isReal_of_induce_eq_sum_of_odd
      hodd θ hθ_ne hSdecomp
  · exact OddOrder.RepresentationTheory.forall_mem_conj_ne_of_odd hodd θ hθ_ne hSdecomp
  · -- support `⊆ A(L) ∪ {1}`, via Peterfalvi (1.2)
    intro φ hφ x hx
    by_cases hx1 : x = 1
    · exact Or.inr hx1
    refine Or.inl ?_
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    -- (a) `H ⊄ Ker φ` (φ occurs in `Ind_H θ` with `θ ≠ 1`)
    have hHker : ¬ (((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ)) := by
      intro hsub
      have hrestrict : ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
            (φ : ClassFunction ↥L ℂ)
          = OddOrder.Peterfalvi.S03.characterDegree (φ : ClassFunction ↥L ℂ) •
            (trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) :
              ClassFunction _ ℂ) := by
        ext k
        rw [ClassFunction.restrict_apply, ClassFunction.smul_apply]
        have hmem := hsub k.2
        rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
        simp only [hmem, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
          trivialClassFunction_apply, mul_one]
      have hzero : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 0 := by
        rw [hchi_eq, ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
          OddOrder.RepresentationTheory.inner_smul_right, irreducibleCharacter_inner,
          if_neg hθ_ne, mul_zero]
      have hone : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 1 := by
        rw [hchisum, inner_sum_left,
          Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
            rw [irreducibleCharacter_inner, if_neg hne]),
          irreducibleCharacter_inner, if_pos rfl]
      rw [hone] at hzero; exact one_ne_zero hzero
    -- (b) `C_H(x) = ⊥` would give `φ(x) = 0` (Pf (1.2)); so `C_H(x) ≠ ⊥`, i.e. `(x:G) ∈ A(L)`
    by_contra hxA
    rw [ClassFunction.mem_support] at hx
    refine hx
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
      φ hHker ?_)
    refine (Subgroup.eq_bot_iff_forall _).mpr (fun z hz => ?_)
    by_contra hz1
    obtain ⟨hzK, hzx⟩ := OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup.mp hz
    refine hxA ⟨SetLike.coe_mem x, fun h => hx1 (Subtype.ext h), (z : G),
      ⟨Subgroup.mem_subgroupOf.mp hzK, fun h => hz1 (Subtype.ext h)⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← Subgroup.coe_mul, ← Subgroup.coe_mul]
    exact congrArg Subtype.val hzx.symm

open scoped Classical in
/-- **Odd-order Frobenius: a nontrivial induced character is a single non-real irreducible supported
on the (normal) kernel.**  In a Frobenius group `Γ` of odd order with kernel `H`, for `θ ∈ Irr H`,
`θ ≠ 1`, the induced `Ind_H^Γ θ` is irreducible (`isIrreducibleCharacter_induce_of_frobeniusGroup`),
**non-real** (odd order, `not_isReal_of_ne_trivial_of_odd_card'`, `χ ≠ 1` via `⟨Ind θ, 1⟩ = 0`),
and supported on `H` (it vanishes off the **normal** `H`,
`induceSum_eq_zero_of_not_conjugatesInto`).
Packaged as an **opaque** `ξ : Irr Γ` (with `↑ξ = Ind θ`) — stated with explicit `Fintype`/
`Invertible` binders (not the `FiniteInduce` scope) so the coset-sum coercion stays `whnf`-cheap.
Discharges the type-I (12.2.a) constituent structure trivially for a Frobenius `L`
(`frobenius_typeI_induced_char_constituents`). -/
theorem frobenius_induce_char_singleton {Γ : Type*} [Group Γ] [Fintype Γ]
    [Invertible (Nat.card Γ : ℂ)] {H : Subgroup Γ} [H.Normal] [Finite ↥H]
    [Invertible (Nat.card ↥H : ℂ)] (hodd : Odd (Nat.card Γ)) {W : Subgroup Γ}
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup Γ H W)
    (θ : IrreducibleCharacter ↥H) (hθ : θ ≠ trivialIrreducibleCharacter ↥H) :
    ∃ ξ : IrreducibleCharacter Γ,
      (ξ : ClassFunction Γ ℂ) = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) ∧
      ¬ ClassFunction.IsReal (ξ : ClassFunction Γ ℂ) ∧
      (ξ : ClassFunction Γ ℂ).support ⊆ (H : Set Γ) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hirr := isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ
  have hne_triv : (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ :
      IrreducibleCharacter Γ) ≠ trivialIrreducibleCharacter Γ := by
    intro h
    have hrestrict : ClassFunction.restrict H
          (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ)
        = (trivialIrreducibleCharacter ↥H : ClassFunction ↥H ℂ) := by
      ext x
      simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        trivialClassFunction_apply]
    have hzero : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
        (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) = 0 := by
      rw [ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
        irreducibleCharacter_inner_eq_ite, if_neg hθ]
    have hcf : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
        = (trivialIrreducibleCharacter Γ : ClassFunction Γ ℂ) :=
      congrArg (fun c : IrreducibleCharacter Γ => (c : ClassFunction Γ ℂ)) h
    rw [hcf, irreducibleCharacter_inner_eq_ite, if_pos rfl] at hzero
    exact one_ne_zero hzero
  refine ⟨⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩, rfl,
    not_isReal_of_ne_trivial_of_odd_card' hodd hne_triv, ?_⟩
  -- support: `Ind θ` vanishes off the normal `H`.
  intro x hx
  rw [ClassFunction.mem_support] at hx
  by_contra hxH
  refine hx ?_
  have hconj : (x : Γ) ∉ ClassFunction.conjugatesInto H := by
    rw [ClassFunction.mem_conjugatesInto]
    rintro ⟨y, hy⟩
    have hcm := ‹H.Normal›.conj_mem (y⁻¹ * x * y) hy y
    have he : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    exact hxH (he ▸ hcm)
  rw [ClassFunction.induce_apply, ← ClassFunction.induceSum_apply,
    ClassFunction.induceSum_eq_zero_of_not_conjugatesInto _ hconj, mul_zero]

/-- **Peterfalvi (12.2.a)**: each `χ ∈ S` decomposes (multiplicity one) into irreducible
constituents of equal degree, each non-real and supported in `A(L) ∪ {1}`.  The §12 assembly:
unpack the type-`F` constituent structure (`typeI_induced_char_constituents`) into the genuine
`CharacterDecompositionData` carrier — whose R(χ) blocks of (12.2.b) then come from `R1`/`Rset`. The
deep type-`F` Clifford content ((8.2.c) inertia +
(1.7.c)/(1.5.a)/(1.2)) is isolated in the obligation, keeping this assembly `sorry`-free. -/
theorem character_decomposition_and_dade_domain [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {L : Subgroup G} (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hchi : chi ∈ hyp.Sset) :
    ∃ data : CharacterDecompositionData hyp chi, data.chi_mem = hchi := by
  obtain ⟨S, hne, hdecomp, hdeg, hreal, hconjnm, hsupp⟩ :=
    typeI_induced_char_constituents hG hyp hchi
  exact ⟨⟨hchi, S, hne, hdecomp, hdeg, hreal, hconjnm, hsupp⟩, rfl⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- The constituent difference `φ̄ − φ` (`φ ∈ S(χ)`) is supported in the Dade domain
`A(L) = supportInSubgroup (A(L)) L`: `φ` is supported in `A(L) ∪ {1}` (`data.supported`), `φ̄` has
the same support (conjugation preserves it), and the value at `1` cancels (`φ̄(1) = φ(1)`, the
degree being a real natural number).  Feeds the difference-support constructor
`S07.dadeOrthonormalCharacterImageFamilyOfDiff` for the orthonormal block `R₁(φ)`. -/
theorem R1_diffsupp {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L := by
  have := hyp.finiteG
  have hsupp_eq : (φ : ClassFunction ↥L ℂ).conj.support = (φ : ClassFunction ↥L ℂ).support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : ((φ : ClassFunction ↥L ℂ).conj - (φ : ClassFunction ↥L ℂ)) x ≠ 0 := hx
  have hxsupp : x ∈ (φ : ClassFunction ↥L ℂ).support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases data.supported φ hφ hxsupp with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast φ
    exact hx0 (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hd, star_natCast,
        sub_self])

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the underlying difference image `{μ_φ, ν_φ, ε}` of `R₁(φ)`.**  The Dade
`CharacterDifferenceImage` of the constituent `φ ∈ S(χ)`: `(φ − φ̄)^τ = ε·(μ_φ − ν_φ)`.  `R1` is its
`toOrthonormalImage`; the raw `{μ_φ, ν_φ}` data is what the cross-`L` (4.1) orthogonality of (12.3)
consumes (`S07.CharacterDifferenceImage.toOrthonormalImage_inner_eq_zero_across`). -/
noncomputable def R1cdi {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.CharacterDifferenceImage (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff
    hyp.dadeData.dade φ (data.not_real φ hφ) (R1_diffsupp data hφ)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b), the orthonormal block `R₁(φ)`**: for a constituent `φ ∈ S(χ)`, the
orthonormal Dade-image family of `φ − φ̄`, "an orthonormal subset of `ℤ[Irr G]` of cardinality 2"
with `(φ − φ̄)^τ = ∑_{α ∈ R₁(φ)} α` (the `image_eq` field).  The `toOrthonormalImage` of the
difference image `R1cdi`.  This is the `imageFamily` the `CharacterPsiDecomposition` engine of
(12.4)/(12.5) consumes; its underlying `{μ, ν}` feeds the (12.3) cross-`L` orthogonality. -/
noncomputable def R1 {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) {φ : IrreducibleCharacter ↥L}
    (hφ : φ ∈ data.constituents) :
    haveI := hyp.finiteG
    OddOrder.Peterfalvi.S07.OrthonormalCharacterImageFamily (L := ↥L) (G := G)
      hyp.tau (φ : ClassFunction ↥L ℂ) :=
  haveI := hyp.finiteG
  (R1cdi data hφ).toOrthonormalImage

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.2.b)**: `R(χ) = ⋃_{φ ∈ S(χ)} R₁(φ)`, the union of the two-element orthonormal
Dade-image blocks `R₁(φ) = (R1 data hφ).imageSet` of the constituents.  A class function `ψ` is
"orthogonal to `R(χ)`" iff `⟨ψ, α⟩ = 0` for every `α ∈ R₁(φ)`, `φ ∈ S(χ)` ((12.4)/(12.5)). -/
noncomputable def Rset {L : Subgroup G} {hyp : Hypothesis L} {chi : ClassFunction ↥L ℂ}
    (data : CharacterDecompositionData hyp chi) : Set (ClassFunction G ℂ) :=
  haveI := hyp.finiteG
  {α | ∃ (φ : IrreducibleCharacter ↥L) (_hφ : φ ∈ data.constituents),
    α ∈ (R1 data _hφ).imageSet}

end OddOrder.Peterfalvi.S14



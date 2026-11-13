-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_SubcoherentTypeP
-- name    : OddOrder_Peterfalvi_S10_SubcoherentTypeP
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:20:39.121708+00:00
-- url     : https://prove2.me/theorems/574c401e-9b80-4e95-b578-c40c96872a72
-- title:
--   Peterfalvi (8.15) claim 3: Hypothesis (5.2) for the type $P$ induced family
-- statement:
--   Formalizes claim 3 of Peterfalvi (8.15) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, pp. 47-48): Hypothesis (5.2) for the induced family $\{\mathrm{Ind}_K^L\theta\mid\theta\in\mathrm{Irr}\,K, H\not\subseteq\ker\theta\}$ when $M$ is of type $P$.
--
--   Main declarations: `inducedNonKernelFamily` (Peterfalvi (5.3.b)/(8.15.3)'s family); `inducedNonKernelFamily_apply_eq_zero` (Peterfalvi (4.7) on the (8.15.3) family); `inducedNonKernelFamily_conjDiff_support` (The `hconjsupp` input of (5.2) for the (8.15.3) family); `inducedNonKernelFamily_diff_support` (Member differences of the (8.15.3) family are `A`-supported — the pair version).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_SubcoherentTypeP.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleBasic
import Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoGeneral
import Definitions.Def_OddOrder_Peterfalvi_S10_TypePSupportA0
import Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

section CoreNontrivialFamily

variable {M : Subgroup G} [Fintype ↥M]

variable (K : Subgroup ↥M) [Invertible (Nat.card ↥K : ℂ)]

/-- **Peterfalvi (5.3.b)/(8.15.3)'s family** `{Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}`.

The `H`-nontrivial analogue of `S08.inducedKernelFamily` (which filters by `θ ≠ 1` together with a
*positive* kernel condition `X ⊆ Ker θ`).

At `H = K` the two filters coincide — for irreducible `θ ∈ Irr K`, `K ⊆ Ker θ` iff `θ = 1` — which
is exactly the type-`P₁` coincidence `M_s = M'`.  ⚠ Only the direction used downstream is
formalized: `inducedNonKernelFamily_subset_inducedKernelFamily_bot` proves `H ⊄ Ker θ ⟹ θ ≠ 1`
(hence `⊆`).  The converse `θ ≠ 1 ⟹ K ⊄ Ker θ` — an irreducible character with full kernel is
trivial, via `IsIrreducibleCharacter.inner_self_eq_one` forcing degree 1 — is standard, and is
stated here as motivation, **not** as a formalized lemma. -/
def inducedNonKernelFamily (H : Subgroup ↥M) : Set (ClassFunction ↥M ℂ) :=
  {φ | ∃ θ : IrreducibleCharacter ↥K,
    ¬ ((H.subgroupOf K : Set ↥K) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥K ℂ)) ∧
    φ = ClassFunction.induce K (θ : ClassFunction ↥K ℂ)}

variable {K}

/-- **The (8.15.3) family is monotone in the kernel-test subgroup**: `H₁ ≤ H₂` makes the filter
`H ⊄ Ker θ` easier to pass, so `inducedNonKernelFamily K H₁ ⊆ inducedNonKernelFamily K H₂`.

This is what lets a Hypothesis (4.6) whose `H` is *larger* than `M_σ` — e.g. the §10/§13 packaging,
where (4.6.c) is instantiated at `H = K = M'` — consume the `M_σ`-indexed containment
`S11.sOf_subset_inducedNonKernelFamily`.  Note the covering (4.6.d) is a hypothesis *of* the
ambient `h46`, so the support estimate `inducedNonKernelFamily_conjDiff_support` is unaffected by
which `H` the family was named with (issue 1045). -/
theorem inducedNonKernelFamily_mono {H₁ H₂ : Subgroup ↥M} (h : H₁ ≤ H₂) :
    inducedNonKernelFamily K H₁ ⊆ inducedNonKernelFamily K H₂ := by
  rintro φ ⟨θ, hθ, rfl⟩
  exact ⟨θ, fun hsub => hθ (fun x hx => hsub (Subgroup.subgroupOf_mono K h hx)), rfl⟩

/-- **The book's filter is finer than the repo's**: `{θ | H ⊄ Ker θ} ⊆ {θ | θ ≠ 1}`, so the
(8.15.3) family sits inside `S08.inducedKernelFamily K ⊥`.

The trivial character has every element in its kernel, so `H ⊄ Ker θ` forces `θ ≠ 1`; and the
`⊥`-kernel condition of `inducedKernelFamily` is vacuous.  This inclusion is what lets the whole
`S08.inducedKernelFamily_*` suite (non-reality, pairwise orthogonality, finiteness, conjugation
closure) apply verbatim to the finer family — only the *support* estimate has to be redone, and
that is `inducedNonKernelFamily_conjDiff_support`. -/
theorem inducedNonKernelFamily_subset_inducedKernelFamily_bot {H : Subgroup ↥M} :
    inducedNonKernelFamily K H ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily K ⊥ := by
  rintro φ ⟨θ, hker, rfl⟩
  refine ⟨θ, ?_, ?_, rfl⟩
  · rintro rfl
    exact hker fun x _ => by
      simp [IrreducibleCharacter.coe_trivialIrreducibleCharacter]
  · intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
    rw [show x = 1 from Subtype.ext hx]
    rfl

/-- **Member degrees of the (8.15.3) family are natural numbers** (hence real): `φ(1) = |L:K|·θ(1)`
with `θ(1)` a positive natural.  This is what kills the `{1}` left over by (4.7) when passing from
`Supp φ ⊆ A ∪ {1}` to `Supp (φ − φ̄) ⊆ A`. -/
theorem inducedNonKernelFamily_apply_one_eq_natCast {H : Subgroup ↥M}
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily K H) :
    ∃ n : ℕ, φ 1 = (n : ℂ) := by
  obtain ⟨θ, -, rfl⟩ := hφ
  obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  exact ⟨K.index * d, by rw [ClassFunction.induce_apply_one, hd]; push_cast; ring⟩

end CoreNontrivialFamily

section CoreNontrivialSupport

variable [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {M : Subgroup G} [Fintype ↥M] [Invertible (Nat.card ↥M : ℂ)]

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)] in
/-- **Peterfalvi (4.7) on the (8.15.3) family**: every member vanishes outside `A ∪ {1}`.

Direct application of `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`,
whose ambient set `A` is already a parameter — so it applies verbatim at `A = typePACore M`
(the book-literal `A(M)`), not only at the `P₁`-regime `typePA M`. -/
theorem inducedNonKernelFamily_apply_eq_zero {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h.K : ℂ)]
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily h.K h.subH)
    {z : ↥M} (hz : (z : G) ∉ A ∪ ({1} : Set G)) :
    φ z = 0 := by
  obtain ⟨θ, hker, rfl⟩ := hφ
  exact OddOrder.Peterfalvi.S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
    h θ hker hz

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)] in
/-- **The `hconjsupp` input of (5.2) for the (8.15.3) family**: `Supp (φ − φ̄) ⊆ A`.

This is the type-uniform replacement for `S08.inducedKernelFamily_conjDiff_support`, which needs
`(M')^# ⊆ A` and therefore only reads correctly in the `P₁` regime.  Here (4.7) gives
`Supp φ ⊆ A ∪ {1}` outright, and the identity is removed by the degree being a natural number
(`φ(1) = φ̄(1)`), so no containment `(M')^# ⊆ A` is required. -/
theorem inducedNonKernelFamily_conjDiff_support {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h.K : ℂ)]
    {φ : ClassFunction ↥M ℂ} (hφ : φ ∈ inducedNonKernelFamily h.K h.subH) :
    ((φ - φ.conj : ClassFunction ↥M ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A M := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hzA
  refine hz ?_
  rcases eq_or_ne ((z : G)) 1 with hz1 | hz1
  · -- at the identity the two degrees agree (both the same natural number)
    have hzone : z = 1 := Subtype.ext hz1
    obtain ⟨n, hn⟩ := inducedNonKernelFamily_apply_one_eq_natCast (K := h.K) (H := h.subH) hφ
    rw [ClassFunction.sub_apply, hzone, ClassFunction.conj_apply, hn, star_natCast, sub_self]
  · -- off `A ∪ {1}` the member itself vanishes, hence so does its conjugate
    have hmem : (z : G) ∉ A ∪ ({1} : Set G) := by
      rw [Set.mem_union, Set.mem_singleton_iff, not_or]
      exact ⟨hzA, hz1⟩
    have h0 : φ z = 0 := inducedNonKernelFamily_apply_eq_zero h hφ hmem
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_self]

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥M : ℂ)] in
/-- **Member differences of the (8.15.3) family are `A`-supported — the pair version**:
for `φ, ψ` in the family of the *same degree*, `Supp (φ − ψ) ⊆ A`.

Same (4.7) argument as `inducedNonKernelFamily_conjDiff_support`: off `A ∪ {1}` both members
vanish outright, and at the identity the equal degrees cancel.  The conjugate version is the
special case `ψ = φ̄` (where the degrees agree automatically, being the same natural number).

This is the `hsuppdiff` input of the (5.7) uniform-degree coherence producer
`S07.coherent_subset_of_constant_degree`, and hence of the §9-level route to the (9.11) base
coherence (issue 1045).  Compare the `S`-side analogue
`S15.Hypothesis.sSetIrrDeg_member_diff_supported`. -/
theorem inducedNonKernelFamily_diff_support {A : Set G}
    (h : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h.K : ℂ)]
    {φ ψ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ inducedNonKernelFamily h.K h.subH)
    (hψ : ψ ∈ inducedNonKernelFamily h.K h.subH)
    (hdeg : φ 1 = ψ 1) :
    ((φ - ψ : ClassFunction ↥M ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A M := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  by_contra hzA
  refine hz ?_
  rcases eq_or_ne ((z : G)) 1 with hz1 | hz1
  · -- at the identity the equal degrees cancel
    have hzone : z = 1 := Subtype.ext hz1
    rw [ClassFunction.sub_apply, hzone, hdeg, sub_self]
  · -- off `A ∪ {1}` both members vanish
    have hmem : (z : G) ∉ A ∪ ({1} : Set G) := by
      rw [Set.mem_union, Set.mem_singleton_iff, not_or]
      exact ⟨hzA, hz1⟩
    rw [ClassFunction.sub_apply, inducedNonKernelFamily_apply_eq_zero h hφ hmem,
      inducedNonKernelFamily_apply_eq_zero h hψ hmem, sub_self]

/-- **Peterfalvi (8.15), claim 3 — type-uniform**, on the book's own family
`𝒮 ⊆ {Ind_K^L θ | θ ∈ Irr K, H ⊄ Ker θ}` and an arbitrary ambient Dade support `A`.

This is (5.3.b) verbatim: assume Hypothesis (4.6) (here its Dade-free core `h46` together with the
`A`-Dade datum `d`), (5.2.a) (`hconjS`), and that `𝒮` sits inside the `H`-nontrivial induced
family; then Hypothesis (5.2) holds for `L = M`.

Unlike `inducedKernelFamily_subcoherent` (§8D) this needs **no containment `(M')^# ⊆ A`**, so it is
not confined to the type-`P₁` regime: the book's `H ⊄ Ker θ` filter buys the support estimate
through (4.7) instead (`inducedNonKernelFamily_conjDiff_support`).  Instantiating
`A = typePACore M` with `H = M_s = M_σ` (`typePACore_toHypothesis46_core`) gives the book-literal
(8.15.3) for **every** type `𝒫`, types II and V included.

Everything except the support estimate is inherited from the coarser `S08` family along
`inducedNonKernelFamily_subset_inducedKernelFamily_bot`. -/
noncomputable def inducedNonKernelFamily_subcoherent {A : Set G}
    (hodd : Odd (Nat.card ↥M))
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h46.K : ℂ)]
    (d : DadeSupportHypothesisData M A)
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ inducedNonKernelFamily h46.K h46.subH)
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S) :
    OddOrder.Peterfalvi.S07.Hypothesis (L := ↥M) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M) := by
  classical
  -- the coarser `S08` family, for the non-support inputs
  have hbot : ∀ ⦃χ : ClassFunction ↥M ℂ⦄, χ ∈ S →
      χ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily h46.K ⊥ := fun _ hχ =>
    inducedNonKernelFamily_subset_inducedKernelFamily_bot (hsub hχ)
  refine OddOrder.Peterfalvi.S07.irrSubcoherent
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap d.dade
      (d.dade.fullDadeIsometryData))
    (OddOrder.Peterfalvi.S04.supportInSubgroup A M)
    (fun χ hχ => ?_) hconjS ?_ ?_ ?_ ?_
  · -- `Rdatum`: the (5.2.d) datum, with the **(4.7)** support estimate in place of `(M')^# ⊆ A`
    exact OddOrder.Peterfalvi.S07.dadeCharacterDifferenceImageOfDiff d.dade
      ⟨χ, hirr χ hχ⟩
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hbot hχ))
      (by
        have h := inducedNonKernelFamily_conjDiff_support h46 (hsub hχ)
        intro x hx
        refine h ?_
        rw [ClassFunction.mem_support] at hx ⊢
        intro h0
        refine hx ?_
        rw [ClassFunction.sub_apply] at h0 ⊢
        rw [sub_eq_zero] at h0 ⊢
        exact h0.symm)
  · exact fun χ hχ =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hodd ⊥ (hbot hχ)
  · exact fun χ ψ hχ hψ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal (hbot hχ) (hbot hψ) hne
  · exact fun χ hχ => inducedNonKernelFamily_conjDiff_support h46 (hsub hχ)
  · exact fun φ ψ hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        d.dade hφ.2 hψ.2

/-- **Peterfalvi (5.7) on the (8.15.3) family**: a uniform-degree subfamily is coherent.

The (5.7)∘(5.3.b) companion of `inducedNonKernelFamily_subcoherent`, stated at the same
generality — arbitrary ambient support `A`, with Hypothesis (4.6)'s core `h46` and the `A`-Dade
datum `d` as parameters.  Given a conjugation-closed set `S` of *irreducible* members of the
family, all of the same nonzero degree, `S` is coherent for the Dade map.

This is the book's route to the (9.11) base coherence: (8.15.3) supplies Hypothesis (5.2) and
(5.7) turns a constant-degree subfamily into a coherent one.  The repo previously obtained the
same conclusion from the §10 μ-grid engine
(`S12.Hypothesis.inducedFamily_degreeSubfamily_isCoherent`), which is what tied it to types
III/IV; nothing here carries a type hypothesis.

⚠ `h2 : 2 ≤ S.ncard` is **exposed as a parameter** rather than derived.  This follows the
`S`-side precedent `S15.Hypothesis.sSetIrrDeg_coherent`: the §9 degree count
((9.8.d), `caseA_character_count_exact`) yields an *existence* statement `∃ ζ`, not two distinct
members, so deriving `2 ≤ ncard` here would need genuine upstream counting content.  Exposing it
keeps this producer sorry-free and leaves the count to the caller.

Obligation sources: `hirr` = `IsIrreducibleCharacter.inner_self_eq_one`;
`hZIrr` = `S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported` fed by `hsuppdiff`;
`hsuppdiff` = `inducedNonKernelFamily_diff_support`. -/
theorem inducedNonKernelFamily_degreeSubfamily_coherent {A : Set G}
    (hodd : Odd (Nat.card ↥M))
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46Core A M) [Invertible (Nat.card ↥h46.K : ℂ)]
    (d : DadeSupportHypothesisData M A)
    {S : Set (ClassFunction ↥M ℂ)}
    (hsub : S ⊆ inducedNonKernelFamily h46.K h46.subH)
    (hirrS : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    (hconjS : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hSfin : S.Finite) (h2 : 2 ≤ S.ncard)
    (deg : ℂ) (hconst : ∀ χ ∈ S, ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = deg) (hdeg0 : deg ≠ 0)
    (h1A : (1 : ↥M) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup A M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (inducedNonKernelFamily_subcoherent hodd h46 d hsub hirrS hconjS).tau S
      (OddOrder.Peterfalvi.S04.supportInSubgroup A M)) := by
  classical
  set hyp := inducedNonKernelFamily_subcoherent hodd h46 d hsub hirrS hconjS with hhyp
  -- `hsuppdiff`: equal degrees, so the (4.7) estimate applies to every member difference.
  have hsuppdiff : ∀ a ∈ S, ∀ b ∈ S,
      ((a - b : ClassFunction ↥M ℂ)).support
        ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A M := fun a ha b hb =>
    inducedNonKernelFamily_diff_support h46 (hsub ha) (hsub hb)
      (by rw [hconst a ha, hconst b hb])
  refine OddOrder.Peterfalvi.S07.coherent_subset_of_constant_degree hyp (subset_refl _)
    hconjS hSfin h2 (fun ζ hζ => (hirrS ζ hζ).inner_self_eq_one) ?_
    (fun a ha b hb => by rw [hconst a ha, hconst b hb]) (fun a ha => by rw [hconst a ha]; exact
      hdeg0) h1A hsuppdiff
  -- `hZIrr`: the Dade map carries `A`-supported virtual characters into `ℤ[Irr G]`.
  intro a ha b hb
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported d.dade
    (hsuppdiff a ha b hb)
    (Submodule.sub_mem _ (hirrS a ha).mem_ZIrr (hirrS b hb).mem_ZIrr)

end CoreNontrivialSupport

end OddOrder.Peterfalvi.S10



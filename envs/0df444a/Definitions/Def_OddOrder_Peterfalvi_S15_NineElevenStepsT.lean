-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenStepsT
-- name    : OddOrder_Peterfalvi_S15_NineElevenStepsT
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:35:22.744636+00:00
-- url     : https://prove2.me/theorems/d4a2a774-fd30-4ad3-aa0f-99b922fd8581
-- title:
--   Peterfalvi (9.11.1)–(9.11.4) at $T$: step lemmas
-- statement:
--   The $T$-side mirrors of the (9.11.1)–(9.11.4) step lemmas (Peterfalvi, pp. 87-91), feeding the (9.11.5)–(9.11.8) endgame of the $T$-instance.
--
--   Main declarations: `Hypothesis.sOf_H0Uprime_subset_sSet_T` (The `𝒮(H₀U′)` stratum sits inside `𝒮 = 𝒮(H₀C′)`); `Hypothesis.sSet_mem_Snorm_pos_T` (Every `𝒯 = sSet(setupT)`-member has positive `Snorm` weight); `Hypothesis.nineElevenSTwoExtractionT` (Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction — `T`-instance residual); `Hypothesis.sSet_sThree_coherent_dade_T` (Peterfalvi (9.11.6), `𝒮₃`-coherence on the honest Dade map).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_NineElevenStepsT.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_NineElevenStepsT.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenPairBoundT
import Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSteps

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `𝒮(H₀U′)` stratum sits inside `𝒮 = 𝒮(H₀C′)`** (mirror; issue 2035):
`C′ = [C,C] ≤ [U,U] = U′`
by commutator monotonicity (`cSub_le_U`), so `H₀ ⊔ C′ ≤ H₀ ⊔ U′` and `sOf` is antitone
(`sSet_eq_sOf_H0Cprime` dictionary).  Shared brick of the (9.11.1) extraction and the (9.11.3)
class-equation wiring. -/
theorem Hypothesis.sOf_H0Uprime_subset_sSet_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief) :
    OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd))
      ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) := by
  rw [hyp.sSet_eq_sOf_H0Cprime_T hG hvd chars]
  refine OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupT hG hvd)
    (sup_le_sup_left ?_ chief.H0)
  change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    ≤ derivedInG (hyp.toTypesIIIIIIVSetupT hG hvd).U
  rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator
      (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief),
    OddOrder.Peterfalvi.S11.derivedInG_eq_commutator (hyp.toTypesIIIIIIVSetupT hG hvd).U]
  exact Subgroup.commutator_mono
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupT hG hvd) chief)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Every `𝒯 = sSet(setupT)`-member has positive `Snorm` weight** (mirror; issue 2035; the
`T`-instance mirror
of `S13.sOf_mem_Snorm_pos`): `Snorm χ = (χ(1).re)²/⟨χ,χ⟩.re` with `χ(1) = q·d` a positive
natural degree (`induceHU_apply_one_eq_q_mul`) and `⟨χ,χ⟩.re > 0` (the landed embedding
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`). -/
theorem Hypothesis.sSet_mem_Snorm_pos_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {χ : ClassFunction ↥hyp.T ℂ}
    (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    0 < OddOrder.Peterfalvi.S07.Snorm χ := by
  have := hyp.finiteG
  classical
  have hpos := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
    (hyp.sSet_subset_inducedKernelFamily_T hG hvd hχ)
  obtain ⟨ζ, hζ, rfl⟩ := hχ
  obtain ⟨dζ, hdpos, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hq : 0 < (hyp.toTypesIIIIIIVSetupT hG hvd).q :=
    (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos
  have hdeg : (induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) : ↥hyp.T → ℂ) 1
      = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * dζ : ℕ) : ℂ) := by
    rw [induceHU_apply_one_eq_q_mul, hdζ]
    push_cast
    ring
  unfold OddOrder.Peterfalvi.S07.Snorm
  apply div_pos
  · rw [hdeg, Complex.natCast_re]
    exact pow_pos (Nat.cast_pos.mpr (Nat.mul_pos hq hdpos)) 2
  · exact hpos.2

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction — `T`-instance residual** (mirror; issue 2035;
the
`T`-mirror of the M-side `S13.caseA_sTwo_subset_degreeQaCut`, Coq `PFsection9.v:1626-1680`
`eqS12`).  At the equality configuration the degree-`qa` irreducible cut `𝒮₁′` of `𝒮(H₀U′)`
alone already saturates the (9.11.1) bound `2q²au` exactly (`sumnS_irreducible_constant_degree`
+ the (9.8.d) count equality `hcount` at `C = U′` and `2a = p−1`), so a `𝒮₂`-member outside
`𝒮₁′` would add its positive `Snorm` weight beyond `hFboundU` (positivity via the landed
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`); hence
`𝒮₂ ⊆ 𝒮₁′`.  The M-side proof mirrors modulo the `sSet = 𝒮(H₀C′)` dictionary
(`sSet_eq_sOf_H0Cprime`) — no `htype`/`hncH0C` gate. -/
theorem Hypothesis.nineElevenSTwoExtractionT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.T ℂ))
    (hS₁S₂ : hyp.sSetIrrDegT hG hvd (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.T ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    S₂ ⊆ {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)} := by
  have := hyp.finiteG
  classical
  intro χ hχS₂
  by_contra hnot
  -- make the cut `𝒮₁′` an atom so cast rewrites cannot enter its set-builder
  set S1' : Set (ClassFunction ↥hyp.T ℂ) := {φ ∈ OddOrder.Peterfalvi.S11.sOf
      (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
      IsIrreducibleCharacter φ ∧
      φ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)} with hS1'def
  -- `𝒮₁′ ⊆ 𝒮₂` along `𝒮(H₀U′) ⊆ 𝒮` and the base cut `hS₁S₂`
  have hS1'sub : S1' ⊆ S₂ := fun φ hφ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet_T hG hvd chars hφ.1, hφ.2.1, hφ.2.2⟩
  have hS1'fin : S1'.Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupT hG hvd)).subset fun φ hφ =>
      hyp.sOf_H0Uprime_subset_sSet_T hG hvd chars hφ.1
  -- `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one irreducibles of uniform degree `qa`)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * ((((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℝ)) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  -- the count at `C = U′`: `|𝒮₁′|·a² = 2a·u` in `ℕ`
  have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex
      (hyp.toTypesIIIIIIVSetupT hG hvd).U = chars.u := by
    have hUpC : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief
        = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd) := hCUprime
    rw [← hUpC]
    exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u chars
  have hcount' : S1'.ncard * (caseA.a * caseA.a) = 2 * caseA.a * chars.u := by
    rw [hcount, hrelu, ← h2a]
  -- `𝒮₁′` alone saturates the bound: `sumnS 𝒮₁′ = 2q²au` in `ℝ`
  have hsatur : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = 2 * (((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ)) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    have hcast : ((S1'.ncard : ℝ)) * ((caseA.a : ℝ) * (caseA.a : ℝ))
        = 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount'
    rw [hsum1', ← Set.ncard_eq_toFinset_card _ hS1'fin, Nat.cast_mul]
    linear_combination (((hyp.toTypesIIIIIIVSetupT hG hvd).q : ℝ) ^ 2) * hcast
  -- the offending member: `χ ∈ 𝒮₂ ∖ 𝒮₁′` adds positive `Snorm` beyond the saturated bound
  have hχnot : χ ∉ hS1'fin.toFinset := fun hmem => hnot (hS1'fin.mem_toFinset.mp hmem)
  have hFsub : ↑(insert χ hS1'fin.toFinset) ⊆ S₂ := by
    rw [Finset.coe_insert]
    exact Set.insert_subset hχS₂
      (by rw [Set.Finite.coe_toFinset]; exact hS1'sub)
  have hbound := hFboundU _ hFsub
  have hsplit : OddOrder.Peterfalvi.S07.sumnS (insert χ hS1'fin.toFinset)
      = OddOrder.Peterfalvi.S07.Snorm χ
        + OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset := by
    unfold OddOrder.Peterfalvi.S07.sumnS
    exact Finset.sum_insert hχnot
  rw [hsplit, hsatur] at hbound
  linarith [hyp.sSet_mem_Snorm_pos_T hG hvd (hS₂S hχS₂)]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.6), `𝒮₃`-coherence on the honest Dade map** (mirror; issue 2035; the
`T`-instance
mirror of `S13.caseA_sThree_coherent`).  In the equality configuration every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member
has uniform degree `q·u` (`hS3deg`), so the (5.7) norm-general coherence producer
`S07.uniform_degree_coherence_of_families` fires with an arbitrary pivot `χ₀ ∈ 𝒮₃`: per-member
(5.2.d) `R`-data from the case-agnostic `sSet_memberRFamily`, cross-orthogonality from
`sSet_memberRFamily_orthogonal`, the Dade isometry/`ℤ[Irr]` facts from
`dadeIntegralCharacterMap_*_of_supported`, and the equal-degree `A(T)`-difference supports from
`sSet_scaledDiff_support` at `c = 1`.  This is the `τ₃` of the (9.11.6) dichotomy: the coherent
extension of `𝒮₃` whose unit images the non-orthogonal branch counts against `‖α^τ‖²` (Bessel)
and whose orthogonal branch the (9.11.7)–(9.11.8) residual refutes. -/
theorem Hypothesis.sSet_sThree_coherent_dade_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hvd : hyp.v * hyp.d ≠ 1)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    {S₂ : Set (ClassFunction ↥hyp.T ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      (χ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData))
      (sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T)) := by
  classical
  have := hyp.finiteG
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  -- `𝒮₃` is conjugation-closed
  have hconj : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      a.conj ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂ := by
    intro a ha
    refine ⟨sSet_closedUnderConjugate _ ha.1, fun hc => ?_⟩
    have h := hS₂conj hc
    rw [ClassFunction.conj_conj] at h
    exact ha.2 h
  -- no member is real
  have hnr : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂, a ≠ a.conj :=
    fun a ha h => sSet_hasNoRealCharacters _ (hyp.oddCardT hG) ha.1 h.symm
  -- equal-degree differences are `A(T)`-supported (`sSet_scaledDiff_support` at `c = 1`)
  have hsuppdiff : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ∀ b ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) \ S₂,
      ((a - b : ClassFunction ↥hyp.T ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
    intro a ha b hb
    have h := hyp.sSet_scaledDiff_support_T hG hvd ha.1 hb.1 (c := 1)
      (by rw [hS3deg a ha, hS3deg b hb, Nat.cast_one, one_mul])
    rwa [one_smul] at h
  -- pivot self-norm is a natural (`ℤ[Irr]` sum-of-squares)
  have hN : ∃ n : ℕ, ClassFunction.inner χ₀ χ₀ = (n : ℂ) := by
    obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq
      (sSet_subset_ZIrr _ hχ₀.1)
    have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨(∑ x ∈ c.support, (c x) ^ 2).toNat, ?_⟩
    rw [hcsum]
    exact_mod_cast (congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)).symm
  exact OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    ((sSet_finite _).subset Set.sdiff_subset)
    hχ₀
    (fun η hη => hyp.sSet_memberRFamily_T hG hnoV pins hvd hTP Tdata hU hW1 hW2 hη.1)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupT hG hvd) ha.1 hb.1 hab
      convert h using 2)
    hconj
    hnr
    hN
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypT hG hTP) hφ.2 hψ.2)
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypT hG hTP)
        (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (sSet_subset_ZIrr _ ha.1) (sSet_subset_ZIrr _ hb.1)))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 => hyp.sSet_memberRFamily_orthogonal_T hG hnoV pins hvd hTP Tdata hU hW1
        hW2 hφ.1 hξ.1 h1 h2)
    (fun a ha => (hS3deg a ha).trans (hS3deg χ₀ hχ₀).symm)
    (by
      rw [hS3deg χ₀ hχ₀]
      exact Nat.cast_ne_zero.mpr (Nat.mul_ne_zero Nat.card_pos.ne'
        (OddOrder.Peterfalvi.S11.u_odd hG chars).pos.ne'))
    (by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
      simp)
    (hconj χ₀ hχ₀)
    (fun h => hnr χ₀ hχ₀ h.symm)

open OddOrder.Peterfalvi.S11 in
/-- **`(H·U₁)^# ⊆ A(T)`** (Peterfalvi (9.11.4), issue 1017; the Coq gap-patch
`PFsection9.v:1478-1484`).  Every nonidentity `y ∈ H ⊔ U₁` (`U₁ = cuSubOf caseA i` the explicit
TI-witness) lies in the honest Dade support `A(T)`.  The Coq comment records the gap: `{1} ∪ A(T)`
contains `H` and `U₁` but is *not a subgroup*, so `HU₁ ⊆ {1} ∪ A(T)` needs Philip Hall's theorems
in the solvable `HU₁`.  Proof: split `y` at its `σ(S)`-part `h = piPart σ y` (a power of `y`).
If `h ≠ 1` then `h ∈ T_σ = M_σ(S)` (`mem_Msigma_of_isPiElement_sigma_of_mem`) is a nonidentity
centralized witness (powers of `y` commute with `y`).  If `h = 1` then `y` is a `σ′`-element of
the solvable `K = H ⊔ U₁`; `U₁` is a Hall `σ′`-subgroup of `K` (`|K| = |H|·|U₁|`, `|H|` a
`σ`-number, `|U₁|` a `σ′`-number), so by Hall D/C (`hall_D`/`hall_C`) some `K`-conjugate
`g y g⁻¹` lies in `U₁ ≤ C_G(x₀)` for the fixed-point witness `x₀ ∈ H^#`
(`exists_cuSubOf_centralizer_witness`), whence `y` centralizes `g⁻¹ x₀ g ∈ H^# = T_σ^#`
(`H` is `K`-normal).  In both cases `y ∈ T′` since `K ≤ H ⊔ U = T′`. -/
theorem Hypothesis.mem_typePACore_of_mem_H_sup_cuSubOf_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars) (i : Fin (hyp.toTypesIIIIIIVSetupT hG hvd).q)
    {y : G} (hy : y ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i) (hy1 : y ≠ 1) :
    y ∈ S10.typePACore hyp.T := by
  classical
  -- dictionary: `H = Q ≤ T_σ` (the `≤` suffices at every use — general type `P`) and
  -- `T′ = H ⊔ U = Q ⊔ V`
  have hHMs : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G)
      ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T := by
    rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd, hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.T_maximal
  have hSderiv : derivedInG hyp.T
      = (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ (hyp.toTypesIIIIIIVSetupT hG hvd).U := by
    rw [hyp.T_deriv_eq_QV, hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_U_eq hG hvd]
  have hKderiv : (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i ≤ derivedInG hyp.T := by
    rw [hSderiv]
    exact sup_le le_sup_left ((cuSubOf_le_U caseA i).trans le_sup_right)
  have hKS : (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i ≤ hyp.T :=
    hKderiv.trans (derivedInG_le_self hyp.T)
  have hyS : y ∈ hyp.T := hKS hy
  -- `σ`-prime dictionary: `π(|H|) ⊆ σ(T)` (via `H ≤ M_σ`)
  have hHpi : ∀ p ∈ (Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.sigma hyp.T := by
    intro p hp
    obtain ⟨hpp, hpH, -⟩ := Nat.mem_primeFactors.mp hp
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup hyp.T p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpH.trans (Subgroup.card_dvd_of_le hHMs), Nat.card_pos.ne'⟩)
  by_cases hone : OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.T) y = 1
  · -- `y` is a `σ′`-element: Hall-conjugate into `U₁`, then use the fixed-point witness
    have hyπ' : OddOrder.GroupTheory.IsPiElement ((OddOrder.BG.Ch3.S10.sigma hyp.T)ᶜ) y :=
      OddOrder.BG.Ch4.S14.isPiElement_compl_of_piPart_eq_one hone
    set Kg : Subgroup G := (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i with hKgdef
    have hKsolv : Group.IsSolvable ↥Kg := hG.isSolvable_of_lt_top Kg
      (lt_of_le_of_lt hKS ((show IsCoatom hyp.T from hyp.T_maximal).1.lt_top))
    have hnorm : cuSubOf caseA i ≤ Subgroup.normalizer
        (((hyp.toTypesIIIIIIVSetupT hG hvd).H : Set G)) :=
      (cuSubOf_le_U caseA i).trans (le_sup_left.trans
        (typeP_uW1_le_normalizer_H (hyp.toTypesIIIIIIVSetupT hG hvd).typeP))
    have hdisj : Disjoint (hyp.toTypesIIIIIIVSetupT hG hvd).H (cuSubOf caseA i) := by
      rw [disjoint_iff]
      refine le_bot_iff.mp ?_
      calc (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊓ cuSubOf caseA i
          ≤ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.H ⊓ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U :=
            inf_le_inf_left _ (cuSubOf_le_U caseA i)
        _ = ⊥ := typeP_H_inf_U (hyp.toTypesIIIIIIVSetupT hG hvd).typeP
    have hcardK : Nat.card ↥Kg
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H * Nat.card ↥(cuSubOf caseA i) :=
      OddOrder.BG.Ch1.S03f.card_sup_of_le_normalizer_of_disjoint hnorm hdisj
    -- `U₁` is a Hall `σ′`-subgroup of `K`
    have hU₁K : cuSubOf caseA i ≤ Kg := le_sup_right
    have hcardU₁ : Nat.card ↥((cuSubOf caseA i).subgroupOf Kg)
        = Nat.card ↥(cuSubOf caseA i) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁K).toEquiv
    have hidxU₁ : ((cuSubOf caseA i).subgroupOf Kg).index
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H := by
      have h1 := Subgroup.card_mul_index ((cuSubOf caseA i).subgroupOf Kg)
      rw [hcardU₁, hcardK,
        mul_comm (Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H)] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    -- a Hall-`σ′` subgroup `P₁` of `U₁` is Hall-`σ′` in `K`: `[K : P₁] = |H|·[U₁ : P₁]`,
    -- both `σ`-sided.  (General type `P`: `U₁` itself need not be `σ`-free — for type III/IV
    -- the `σ`-part of `V` is nontrivial — but its `σ`-elements are caught by the `piPart`
    -- branch, and the `σ′`-conjugation only needs *some* Hall-`σ′` inside `U₁`.)
    have hU₁solv : Group.IsSolvable ↥((cuSubOf caseA i).subgroupOf Kg) := inferInstance
    obtain ⟨P₁, hP₁Hall, -⟩ := OddOrder.Isaacs.Ch03.hall_D
      (G := ↥((cuSubOf caseA i).subgroupOf Kg))
      (U := ⊥) (fun p hp => by
        rw [Subgroup.card_bot] at hp
        simp at hp)
    set P₁' : Subgroup ↥Kg := P₁.map ((cuSubOf caseA i).subgroupOf Kg).subtype with hP₁'def
    have hP₁'le : P₁' ≤ (cuSubOf caseA i).subgroupOf Kg := Subgroup.map_subtype_le _
    have hP₁'card : Nat.card ↥P₁' = Nat.card ↥P₁ :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _
        ((cuSubOf caseA i).subgroupOf Kg).subtype_injective).toEquiv.symm
    have hP₁'sub : P₁'.subgroupOf ((cuSubOf caseA i).subgroupOf Kg) = P₁ :=
      Subgroup.comap_map_eq_self_of_injective
        ((cuSubOf caseA i).subgroupOf Kg).subtype_injective P₁
    have hP₁'Hall : OddOrder.Isaacs.Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch3.S10.sigma hyp.T)ᶜ) P₁' := by
      constructor
      · intro p hp
        rw [hP₁'card] at hp
        exact hP₁Hall.1 p hp
      · intro p hp
        have hsplit := Subgroup.relIndex_mul_index hP₁'le
        obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp
        rw [← hsplit] at hpdvd
        simp only [Set.mem_compl_iff, not_not]
        rcases hpp.dvd_mul.mp hpdvd with h | h
        · -- `p ∣ [U₁ : P₁]`: the Hall complement side of `P₁`
          have hrel : P₁'.relIndex ((cuSubOf caseA i).subgroupOf Kg) = P₁.index := by
            rw [Subgroup.relIndex, hP₁'sub]
          rw [hrel] at h
          exact not_not.mp (hP₁Hall.2 p (Nat.mem_primeFactors.mpr
            ⟨hpp, h, Subgroup.index_ne_zero_of_finite⟩))
        · -- `p ∣ [K : U₁] = |H|`
          rw [hidxU₁] at h
          exact hHpi p (Nat.mem_primeFactors.mpr ⟨hpp, h, Nat.card_pos.ne'⟩)
    -- `⟨y⟩` is a `σ′`-subgroup of `K`: Hall D + Hall C conjugate it into `P₁ ≤ U₁`
    have hyK : y ∈ Kg := hy
    have hZpi : ∀ p ∈ (Nat.card ↥(Subgroup.zpowers (⟨y, hyK⟩ : ↥Kg))).primeFactors,
        p ∈ (OddOrder.BG.Ch3.S10.sigma hyp.T)ᶜ := by
      intro p hp
      rw [Nat.card_zpowers] at hp
      have hord : orderOf y = orderOf (⟨y, hyK⟩ : ↥Kg) :=
        orderOf_injective Kg.subtype Kg.subtype_injective ⟨y, hyK⟩
      rw [← hord] at hp
      exact hyπ' p hp
    obtain ⟨Q, hQHall, hZQ⟩ := OddOrder.Isaacs.Ch03.hall_D (G := ↥Kg) hZpi
    obtain ⟨g, hgconj⟩ := OddOrder.Isaacs.Ch03.hall_C hQHall hP₁'Hall
    have hyU₁ : (MulAut.conj g).toMonoidHom (⟨y, hyK⟩ : ↥Kg)
        ∈ (cuSubOf caseA i).subgroupOf Kg := by
      refine hP₁'le ?_
      rw [← hgconj]
      exact Subgroup.mem_map_of_mem _ (hZQ (Subgroup.mem_zpowers _))
    have hgyG : (g : G) * y * (g : G)⁻¹ ∈ cuSubOf caseA i := by
      have h1 := Subgroup.mem_subgroupOf.mp hyU₁
      simpa using h1
    -- the fixed-point witness `x₀ ∈ H^#`, `U₁ ≤ C(x₀)`
    obtain ⟨x₀, hx₀H, hx₀ne, hx₀cent⟩ := exists_cuSubOf_centralizer_witness hG caseA i
    have hKnormH : Kg ≤ Subgroup.normalizer (((hyp.toTypesIIIIIIVSetupT hG hvd).H : Set G)) :=
      sup_le Subgroup.le_normalizer hnorm
    have hx₁H : (g : G)⁻¹ * x₀ * (g : G) ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H := by
      have hgn := hKnormH (Kg.inv_mem g.2)
      have h1 := (Subgroup.mem_normalizer_iff.mp hgn x₀).mp hx₀H
      simpa using h1
    have hx₁ne : (g : G)⁻¹ * x₀ * (g : G) ≠ 1 := by
      intro h
      apply hx₀ne
      have h1 : x₀ = (g : G) * ((g : G)⁻¹ * x₀ * (g : G)) * (g : G)⁻¹ := by group
      rw [h1, h]
      group
    have hcent : y * ((g : G)⁻¹ * x₀ * (g : G)) = ((g : G)⁻¹ * x₀ * (g : G)) * y := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hx₀cent hgyG)
      calc y * ((g : G)⁻¹ * x₀ * (g : G))
          = (g : G)⁻¹ * (((g : G) * y * (g : G)⁻¹) * x₀) * (g : G) := by group
        _ = (g : G)⁻¹ * (x₀ * ((g : G) * y * (g : G)⁻¹)) * (g : G) := by rw [h1]
        _ = ((g : G)⁻¹ * x₀ * (g : G)) * y := by group
    rw [S10.mem_typePACore]
    exact ⟨hKderiv hy, hy1, (g : G)⁻¹ * x₀ * (g : G),
      ⟨SetLike.mem_coe.mpr (hHMs hx₁H), fun h => hx₁ne (Set.mem_singleton_iff.mp h)⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hcent⟩
  · -- the `σ`-part `h ≠ 1` is a nonidentity centralized `T_σ`-witness
    obtain ⟨b, hmul, hcomm, hpiA, hpiB, hhzpow, hbzpow⟩ :=
      OddOrder.BG.Ch4.S14.piPart_spec (OddOrder.BG.Ch3.S10.sigma hyp.T) y
    have hhS : OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.T) y ∈ hyp.T :=
      (Subgroup.zpowers_le.mpr hyS) hhzpow
    have hhMs := OddOrder.BG.Ch4.S14.mem_Msigma_of_isPiElement_sigma_of_mem hG
      hyp.T_maximal hhS (OddOrder.BG.Ch4.S14.isPiElement_piPart _ y)
    rw [S10.mem_typePACore]
    refine ⟨hKderiv hy, hy1, OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.T) y,
      ⟨SetLike.mem_coe.mpr hhMs, fun h => hone (Set.mem_singleton_iff.mp h)⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hhzpow
    rw [← hn]
    exact ((Commute.refl y).zpow_right n).eq

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4), the `A(T)`-support of `α = γ − ψ₁` — `T`-instance residual**
(mirror; issue 2035; the Coq gap-patch site `PFsection9.v:1478-1484`).  For the explicit TI-witness
`U₁ = cuSubOf caseA i = C_U(H̄ᵢ)` and a degree-`qa` member `ψ₁ ∈ 𝒮`, the difference
`α = Ind_{HU₁}^T 1 − ψ₁` is supported in `A(T) = {y ∈ (T′)^# | ∃ x ∈ T_σ^#, y ∈ C(x)}`
(`S10.mem_typePACore`; `H = T_σ = Msigma`).  The M-side dispatches this via
`A(M) = (M′)^#` (`mderivSharp_subset_A0`), **false** here (`A(T) ⊊ (T′)^#` strictly); the honest
route is the book's patched (9.11.4) argument: `supp γ ⊆ ⋃_g (HU₁)^g`
(`support_induce_subset_conjugatesInto`), and `HU₁^# ⊆ A(T)` by the commuting Hall decomposition
in `⟨y⟩` — a nontrivial `H`-part `h ∈ ⟨y⟩ ∩ H^#` gives `y ∈ C(h)` directly, while a σ′-element
`y` lies in a Hall-conjugate of `U₁` (solvable `HU₁`, Hall conjugacy) and `U₁ = C_U(H̄ᵢ)`
centralizes a nontrivial `H`-element by coprime fixed-point lifting; `ψ₁`'s support is
`A(T) ∪ {1}` (`sSet_member_support_subset`) and the value at `1` cancels
(`γ(1) = qa = ψ₁(1)`). -/
theorem Hypothesis.nineElevenAlphaSupportT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars) (i : Fin (hyp.toTypesIIIIIIVSetupT hG hvd).q)
    {ψ₁ : ClassFunction ↥hyp.T ℂ}
    (hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hψ₁deg : (ψ₁ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)) :
    (ClassFunction.induce
        ((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
          ⊔ (cuSubOf caseA i).subgroupOf hyp.T)
        (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
          ⊔ (cuSubOf caseA i).subgroupOf hyp.T))
      - ψ₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  classical
  have := hyp.finiteG
  have : Fintype G := Fintype.ofFinite G
  -- `γ(1) = q·a = ψ₁(1)`: the difference vanishes at the identity
  have hγ1 : ClassFunction.induce
      ((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)) (1 : ↥hyp.T)
      = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupT hG hvd) (cuSubOf_le_U caseA i)
      (relIndex_cuSubOf_U_eq_a caseA i)
  -- the join sits below the `G`-level `K = H ⊔ U₁` (for the `A(T)`-membership core)
  have hjoin : (hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
      ⊔ (cuSubOf caseA i).subgroupOf hyp.T
      ≤ ((hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i).subgroupOf hyp.T :=
    sup_le (Subgroup.subgroupOf_mono hyp.T le_sup_left)
      (Subgroup.subgroupOf_mono hyp.T le_sup_right)
  intro z hz
  have hz0 : (ClassFunction.induce
      ((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)) - ψ₁) z ≠ 0 := hz
  have hzne : z ≠ 1 := by
    rintro rfl
    exact hz0 (by rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self])
  rcases ClassFunction.support_sub_subset _ _ hz with hγ | hψ
  · -- `z ∈ Supp γ`: conjugate into `HU₁`, apply the `A(T)`-core, conjugate back
    have hconj := ClassFunction.support_induce_subset_conjugatesInto
      ((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
        ⊔ (cuSubOf caseA i).subgroupOf hyp.T)) hγ
    rw [ClassFunction.mem_conjugatesInto] at hconj
    obtain ⟨c, hc⟩ := hconj
    have hwG : ((c⁻¹ * z * c : ↥hyp.T) : G)
        ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H ⊔ cuSubOf caseA i :=
      Subgroup.mem_subgroupOf.mp (hjoin hc)
    have hwne : ((c⁻¹ * z * c : ↥hyp.T) : G) ≠ 1 := by
      intro he
      apply hzne
      have h1 : (c⁻¹ * z * c : ↥hyp.T) = 1 := Subtype.ext he
      have h2 : z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      rw [h2, h1]
      group
    have hwA := hyp.mem_typePACore_of_mem_H_sup_cuSubOf_T hG hvd chars caseA i hwG hwne
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hzeq : (z : G) = (c : G) * ((c⁻¹ * z * c : ↥hyp.T) : G) * (c : G)⁻¹ := by
      push_cast
      group
    rw [hzeq]
    exact S10.typePACore_conj_mem c.2 hwA
  · -- `z ∈ Supp ψ₁`: the (4.7) member support minus the identity
    rcases hyp.sSet_member_support_subset_T hG hvd hψ₁mem hψ with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hzne

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4) at the `T`-instance: the cleared Mackey-norm bundle** (mirror; issue 2035;
the
`T`-mirror of `S13.caseA_nineElevenFour_norm_inputs`).  In the equality configuration (`C = U′`,
the (9.8.d) count) there is `N : ℕ` with `N·u = (a+1)·u + (q−1)·a²`, realized as `N = ‖α‖²` for
the `A(T)`-supported virtual character `α = γ − ψ₁ ∈ ℤ[Irr S]` — `γ = Ind_{HU₁}^T 1` at the
explicit TI-witness `U₁ = cuSubOf caseA 0` (`cuSubOf_zero_tiWitness`), `ψ₁` a degree-`qa`
irreducible member from the (9.8.d) count.  Norm: `‖α‖² = ‖γ‖² + 1`
(`cfnorm_sub_irreducible_orthogonal`; orthogonality `nineElevenGamma_inner_induceHU`) and
`‖γ‖²·u = a·u + (q−1)·a²` (`nineElevenGamma_inner_self_mul_u`, the Mackey double-coset count at
the TI-identity); integrality by `mem_ZIrr_inner_self_eq_sum_sq`; support by the
`nineElevenAlphaSupportT` residual. -/
theorem Hypothesis.nineElevenFourNormInputsT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief)
    (caseA : CliffordCaseAData chars)
    (hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief),
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.T → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ))
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 ∧
      ∃ α : ClassFunction ↥hyp.T ℂ,
        α ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T ∧
        α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T ∧
        ClassFunction.inner α α = (N : ℂ) := by
  classical
  have := hyp.finiteG
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupT hG hvd).q :=
    (hyp.toTypesIIIIIIVSetupT hG hvd).nontrivial.2.1.pos
  -- the explicit TI-witness `U₁ = cuSubOf caseA 0` and its (9.11.2) facts
  have hTI := cuSubOf_zero_tiWitness caseA hdich
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupT hG hvd).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)
      ≤ cuSubOf caseA ⟨0, hq0⟩ := by
    have hUpC : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)
        = OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief := hCUprime.symm
    rw [hUpC]; exact hCU₁
  -- `ψ₁ ∈ 𝒮₁`: the degree-`qa` irreducible family is nonempty by the (9.8.d) count
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex
      (hyp.toTypesIIIIIIVSetupT hG hvd).U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have hrpos := Nat.pos_of_ne_zero hrelne
    have : 0 < (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
        (hyp.toTypesIIIIIIVSetupT hG hvd)).relIndex (hyp.toTypesIIIIIIVSetupT hG hvd).U) :=
      Nat.mul_pos (by omega) hrpos
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hζxi : ζ ∈ OddOrder.Peterfalvi.S11.xiSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
    OddOrder.Peterfalvi.S11.xiOf_subset_xiSet (hyp.toTypesIIIIIIVSetupT hG hvd) _ hζmem
  -- `γ = Ind_{HU₁}^T 1` and its landed (9.11.4) facts
  set K : Subgroup ↥hyp.T := (hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T
    ⊔ (cuSubOf caseA ⟨0, hq0⟩).subgroupOf hyp.T with hKdef
  set γ : ClassFunction ↥hyp.T ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T :=
    nineElevenGamma_mem_ZIrr (hyp.toTypesIIIIIIVSetupT hG hvd) (cuSubOf caseA ⟨0, hq0⟩)
  have hγ1 : γ (1 : ↥hyp.T) = (((hyp.toTypesIIIIIIVSetupT hG hvd).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupT hG hvd) hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u
          + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  have hindEq : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) := rfl
  -- orthogonality `⟨γ, ψ₁⟩ = 0` and the norm split `‖α‖² = ‖γ‖² + 1`
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := by
    rw [hψ₁eq, hindEq]
    exact nineElevenGamma_inner_induceHU (hyp.toTypesIIIIIIVSetupT hG hvd) hU₁U hζxi
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  -- `α ∈ ℤ[Irr S]` and the integrality of `‖α‖²`
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.T := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr (hyp.toTypesIIIIIIVSetupT hG hvd) ζ
  obtain ⟨c, -, -, hcsum⟩ :=
    OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]
    push_cast
    rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  refine ⟨N, ?_, γ - ψ₁, hαZIrr, ?_, hNval.symm⟩
  · -- the cleared norm identity `N·u = (a+1)·u + (q−1)·a²`, by `ℕ`-cast injectivity
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u
            + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u
            + ((hyp.toTypesIIIIIIVSetupT hG hvd).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  · -- `Supp(α) ⊆ A(T)`: the (9.11.4) support residual at the explicit witness
    have hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd) :=
      hyp.sOf_H0Uprime_subset_sSet_T hG hvd chars ⟨ζ, hζmem, hψ₁eq⟩
    exact hyp.nineElevenAlphaSupportT hG hvd chars caseA ⟨0, hq0⟩ hψ₁mem hψ₁deg

end OddOrder.Peterfalvi.S15



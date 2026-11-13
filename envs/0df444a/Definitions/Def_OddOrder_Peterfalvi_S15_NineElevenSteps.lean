-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSteps
-- name    : OddOrder_Peterfalvi_S15_NineElevenSteps
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T16:30:52.5052+00:00
-- url     : https://prove2.me/theorems/42c54c97-15ff-43c0-aaf3-af2c91daaed6
-- title:
--   Peterfalvi (9.11.1)–(9.11.4): step lemmas of the $S$-instance case (a) campaign
-- statement:
--   Formalizes the step lemmas feeding the (9.11.5)–(9.11.8) endgame for the honest $S$-instance case (a) refutation.
--
--   Main declarations: `Hypothesis.sOf_H0Uprime_subset_sSet` (The `𝒮(H₀U′)` stratum sits inside `𝒮 = 𝒮(H₀C′)`); `Hypothesis.sSet_mem_Snorm_pos` (Every `𝒮 = sSet`-member has positive `Snorm` weight); `Hypothesis.nineElevenSTwoExtractionS` (Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction — `S`-instance residual); `Hypothesis.sSet_sThree_coherent_dade` (Peterfalvi (9.11.6), `𝒮₃`-coherence on the honest Dade map).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_NineElevenSteps.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_NineElevenSteps.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseBReducibleCoherence

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The `𝒮(H₀U′)` stratum sits inside `𝒮 = 𝒮(H₀C′)`** (issue 1017): `C′ = [C,C] ≤ [U,U] = U′`
by commutator monotonicity (`cSub_le_U`), so `H₀ ⊔ C′ ≤ H₀ ⊔ U′` and `sOf` is antitone
(`sSet_eq_sOf_H0Cprime` dictionary).  Shared brick of the (9.11.1) extraction and the (9.11.3)
class-equation wiring. -/
theorem Hypothesis.sOf_H0Uprime_subset_sSet [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief) :
    OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG))
      ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG) := by
  rw [hyp.sSet_eq_sOf_H0Cprime hG chars]
  refine OddOrder.Peterfalvi.S11.sOf_antitone (hyp.toTypesIIIIIIVSetupS hG)
    (sup_le_sup_left ?_ chief.H0)
  change derivedInG (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief)
    ≤ derivedInG (hyp.toTypesIIIIIIVSetupS hG).U
  rw [OddOrder.Peterfalvi.S11.derivedInG_eq_commutator
      (OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
    OddOrder.Peterfalvi.S11.derivedInG_eq_commutator (hyp.toTypesIIIIIIVSetupS hG).U]
  exact Subgroup.commutator_mono
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)
    (OddOrder.Peterfalvi.S11.cSub_le_U (hyp.toTypesIIIIIIVSetupS hG) chief)

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Every `𝒮 = sSet`-member has positive `Snorm` weight** (issue 1017; the `S`-instance mirror
of `S13.sOf_mem_Snorm_pos`): `Snorm χ = (χ(1).re)²/⟨χ,χ⟩.re` with `χ(1) = q·d` a positive
natural degree (`induceHU_apply_one_eq_q_mul`) and `⟨χ,χ⟩.re > 0` (the landed embedding
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`). -/
theorem Hypothesis.sSet_mem_Snorm_pos [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {χ : ClassFunction ↥hyp.S ℂ}
    (hχ : χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG)) :
    0 < OddOrder.Peterfalvi.S07.Snorm χ := by
  have := hyp.finiteG
  classical
  have hpos := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
    (hyp.sSet_subset_inducedKernelFamily hG hχ)
  obtain ⟨ζ, hζ, rfl⟩ := hχ
  obtain ⟨dζ, hdpos, hdζ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ζ
  have hq : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  have hdeg : (induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) : ↥hyp.S → ℂ) 1
      = (((hyp.toTypesIIIIIIVSetupS hG).q * dζ : ℕ) : ℂ) := by
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
/-- **Peterfalvi (9.11.1), the `𝒮₂ = 𝒮₁` extraction — `S`-instance residual** (issue 1017; the
`S`-mirror of the M-side `S13.caseA_sTwo_subset_degreeQaCut`, Coq `PFsection9.v:1626-1680`
`eqS12`).  At the equality configuration the degree-`qa` irreducible cut `𝒮₁′` of `𝒮(H₀U′)`
alone already saturates the (9.11.1) bound `2q²au` exactly (`sumnS_irreducible_constant_degree`
+ the (9.8.d) count equality `hcount` at `C = U′` and `2a = p−1`), so a `𝒮₂`-member outside
`𝒮₁′` would add its positive `Snorm` weight beyond `hFboundU` (positivity via the landed
`sSet_subset_inducedKernelFamily` + `S08.inducedKernelFamily_inner_self_real_pos`); hence
`𝒮₂ ⊆ 𝒮₁′`.  The M-side proof mirrors modulo the `sSet = 𝒮(H₀C′)` dictionary
(`sSet_eq_sOf_H0Cprime`) — no `htype`/`hncH0C` gate. -/
theorem Hypothesis.nineElevenSTwoExtractionS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (S₂ : Set (ClassFunction ↥hyp.S ℂ))
    (hS₁S₂ : hyp.sSetIrrDeg hG (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) ⊆ S₂)
    (hS₂S : S₂ ⊆ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (h2a : 2 * caseA.a = chief.p - 1)
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U))
    (hFboundU : ∀ F : Finset (ClassFunction ↥hyp.S ℂ), ↑F ⊆ S₂ →
      OddOrder.Peterfalvi.S07.sumnS F ≤ 2 * ((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2
        * (caseA.a : ℝ) * (chars.u : ℝ)) :
    S₂ ⊆ {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
        (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} := by
  have := hyp.finiteG
  classical
  intro χ hχS₂
  by_contra hnot
  -- make the cut `𝒮₁′` an atom so cast rewrites cannot enter its set-builder
  set S1' : Set (ClassFunction ↥hyp.S ℂ) := {φ ∈ OddOrder.Peterfalvi.S11.sOf
      (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter φ ∧
      φ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)} with hS1'def
  -- `𝒮₁′ ⊆ 𝒮₂` along `𝒮(H₀U′) ⊆ 𝒮` and the base cut `hS₁S₂`
  have hS1'sub : S1' ⊆ S₂ := fun φ hφ =>
    hS₁S₂ ⟨hyp.sOf_H0Uprime_subset_sSet hG chars hφ.1, hφ.2.1, hφ.2.2⟩
  have hS1'fin : S1'.Finite :=
    (sSet_finite (hyp.toTypesIIIIIIVSetupS hG)).subset fun φ hφ =>
      hyp.sOf_H0Uprime_subset_sSet hG chars hφ.1
  -- `sumnS 𝒮₁′ = |𝒮₁′|·(qa)²` (norm-one irreducibles of uniform degree `qa`)
  have hsum1' : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = (hS1'fin.toFinset.card : ℝ)
        * ((((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℝ)) ^ 2 :=
    OddOrder.Peterfalvi.S11.sumnS_irreducible_constant_degree hS1'fin.toFinset
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.1)
      (fun ψ hψ => (hS1'fin.mem_toFinset.mp hψ).2.2)
  -- the count at `C = U′`: `|𝒮₁′|·a² = 2a·u` in `ℕ`
  have hrelu : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
      (hyp.toTypesIIIIIIVSetupS hG).U = chars.u := by
    have hUpC : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
        = OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG) := hCUprime
    rw [← hUpC]
    exact OddOrder.Peterfalvi.S11.relIndex_cSub_U_eq_u chars
  have hcount' : S1'.ncard * (caseA.a * caseA.a) = 2 * caseA.a * chars.u := by
    rw [hcount, hrelu, ← h2a]
  -- `𝒮₁′` alone saturates the bound: `sumnS 𝒮₁′ = 2q²au` in `ℝ`
  have hsatur : OddOrder.Peterfalvi.S07.sumnS hS1'fin.toFinset
      = 2 * (((hyp.toTypesIIIIIIVSetupS hG).q : ℝ)) ^ 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
    have hcast : ((S1'.ncard : ℝ)) * ((caseA.a : ℝ) * (caseA.a : ℝ))
        = 2 * (caseA.a : ℝ) * (chars.u : ℝ) := by
      exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hcount'
    rw [hsum1', ← Set.ncard_eq_toFinset_card _ hS1'fin, Nat.cast_mul]
    linear_combination (((hyp.toTypesIIIIIIVSetupS hG).q : ℝ) ^ 2) * hcast
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
  linarith [hyp.sSet_mem_Snorm_pos hG (hS₂S hχS₂)]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.6), `𝒮₃`-coherence on the honest Dade map** (issue 1017; the `S`-instance
mirror of `S13.caseA_sThree_coherent`).  In the equality configuration every `𝒮₃ = 𝒮 ∖ 𝒮₂`-member
has uniform degree `q·u` (`hS3deg`), so the (5.7) norm-general coherence producer
`S07.uniform_degree_coherence_of_families` fires with an arbitrary pivot `χ₀ ∈ 𝒮₃`: per-member
(5.2.d) `R`-data from the case-agnostic `sSet_memberRFamily`, cross-orthogonality from
`sSet_memberRFamily_orthogonal`, the Dade isometry/`ℤ[Irr]` facts from
`dadeIntegralCharacterMap_*_of_supported`, and the equal-degree `A(S)`-difference supports from
`sSet_scaledDiff_support` at `c = 1`.  This is the `τ₃` of the (9.11.6) dichotomy: the coherent
extension of `𝒮₃` whose unit images the non-orthogonal branch counts against `‖α^τ‖²` (Bessel)
and whose orthogonal branch the (9.11.7)–(9.11.8) residual refutes. -/
theorem Hypothesis.sSet_sThree_coherent_dade [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    {S₂ : Set (ClassFunction ↥hyp.S ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      (χ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData))
      (sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S)) := by
  classical
  have := hyp.finiteG
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  -- `𝒮₃` is conjugation-closed
  have hconj : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      a.conj ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂ := by
    intro a ha
    refine ⟨sSet_closedUnderConjugate _ ha.1, fun hc => ?_⟩
    have h := hS₂conj hc
    rw [ClassFunction.conj_conj] at h
    exact ha.2 h
  -- no member is real
  have hnr : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂, a ≠ a.conj :=
    fun a ha h => sSet_hasNoRealCharacters _ (hyp.oddCardS hG) ha.1 h.symm
  -- equal-degree differences are `A(S)`-supported (`sSet_scaledDiff_support` at `c = 1`)
  have hsuppdiff : ∀ a ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ∀ b ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) \ S₂,
      ((a - b : ClassFunction ↥hyp.S ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
    intro a ha b hb
    have h := hyp.sSet_scaledDiff_support hG ha.1 hb.1 (c := 1)
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
    (fun η hη => hyp.sSet_memberRFamily hG hnoV hη.1)
    (fun a ha b hb hab => by
      have h := sSet_pairwiseOrthogonal (hyp.toTypesIIIIIIVSetupS hG) ha.1 hb.1 hab
      convert h using 2)
    hconj
    hnr
    hN
    (fun {φ ψ} hφ hψ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported
        (hyp.dadeHypS hG) hφ.2 hψ.2)
    (fun a ha b hb =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        (hyp.dadeHypS hG)
        (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (sSet_subset_ZIrr _ ha.1) (sSet_subset_ZIrr _ hb.1)))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 => hyp.sSet_memberRFamily_orthogonal hG hnoV hφ.1 hξ.1 h1 h2)
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
open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **The (9.11.2) TI-identity at the explicit witness `U₁ = C_U(H̄₀)`** (issue 1017).  The generic
producer `S11.nineElevenTwoTIWitness_of_degree_dichotomy` proves the (9.11.2) identity but returns
its witness behind an `∃`; the (9.11.4) `S`-instance support argument (`nineElevenAlphaSupportS`)
needs the witness **concretely** — `U₁ = cuSubOf caseA i` centralizes the chief-factor summand
`H̄ᵢ ≠ 1`, which is what puts `U₁^#` inside `A(S)` (coprime fixed-point lifting) — so this restates
the producer with the witness exposed at `i = 0`.  Proof = the producer's, verbatim;
upstream-merge candidate into `S11_NineElevenTIWitness` (issue 1017 update #51). -/
theorem cuSubOf_zero_tiWitness {M : Subgroup G} [Finite G]
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hdeg : ∀ φ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      (φ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    ∀ w ∈ data.typeP.W1, w ≠ 1 →
      cuSubOf caseA ⟨0, data.nontrivial.2.1.pos⟩
          ⊓ MulAut.conj w • cuSubOf caseA ⟨0, data.nontrivial.2.1.pos⟩
        = cSub data chief := by
  classical
  have hq0 : 0 < data.q := data.nontrivial.2.1.pos
  by_cases hall : ∀ k, cuSubOf caseA k = cuSubOf caseA ⟨0, hq0⟩
  · -- all single-factor centralizers coincide: `C = U₁`, the TI-identity is trivial
    have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ := by
      apply le_antisymm (cSub_le_cuSubOf caseA ⟨0, hq0⟩)
      intro g hg
      exact mem_cSub_of_forall_mem_cuSubOf caseA (fun k => (hall k).symm ▸ hg)
    intro w hw _hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    rw [hj, hall j, inf_idem, ← hCeq]
  · -- some centralizer differs: the pair dichotomy resolves to index `u`
    push Not at hall
    obtain ⟨k₀, hk₀⟩ := hall
    intro w hw hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    -- `C_U(H_j) ≠ U₁`: else `⟨w⟩ = W₁` fixes `U₁` and transitivity collapses all
    have hjne : cuSubOf caseA j ≠ cuSubOf caseA ⟨0, hq0⟩ := by
      intro hjeq
      apply hk₀
      have hwfix : MulAut.conj w • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        rw [hj, hjeq]
      have hallfix : ∀ v ∈ data.typeP.W1,
          MulAut.conj v • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        intro v hv
        obtain ⟨n, rfl⟩ := exists_zpow_of_mem_W1 hw hne v hv
        rw [map_zpow]
        have hstab : MulAut.conj w
            ∈ MulAction.stabilizer (MulAut G) (cuSubOf caseA ⟨0, hq0⟩) :=
          MulAction.mem_stabilizer_iff.mpr hwfix
        exact MulAction.mem_stabilizer_iff.mp (zpow_mem hstab n)
      obtain ⟨w0, hw0W, hw0⟩ := exists_w1_rep_Hpart caseA k₀
      obtain ⟨wi, hwiW, hwi⟩ := exists_w1_rep_Hpart caseA ⟨0, hq0⟩
      have hvW : ((w0 * wi⁻¹ : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
        mul_mem hw0W (inv_mem hwiW)
      have hHk₀ : caseA.Hpart k₀ = quotientMulAutHom chief.N_aInvariant (w0 * wi⁻¹)
          • caseA.Hpart ⟨0, hq0⟩ := by
        rw [hw0, hwi, map_mul, mul_smul, map_inv, inv_smul_smul]
      have hdict := conj_smul_cuSubOf_of_Hpart_smul caseA (w0 * wi⁻¹).2 hHk₀
      rw [← hdict]
      exact hallfix _ hvW
    have hij : (⟨0, hq0⟩ : Fin data.q) ≠ j := fun h => hjne (by rw [h])
    rcases nineElevenTwo_relIndex_dichotomy caseA hij hdeg with hu | ha
    · -- index `u`: `C = U₁ ∩ U₁^w` by index equality
      have hCle : cSub data chief ≤ cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j :=
        le_inf (cSub_le_cuSubOf caseA ⟨0, hq0⟩) (cSub_le_cuSubOf caseA j)
      have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne hCle
          (inf_le_left.trans (cuSubOf_le_U caseA ⟨0, hq0⟩)) (fun h => hne' h.symm)
        rw [hu, relIndex_cSub_U_eq_u chars] at hlt
        exact lt_irrefl _ hlt
      rw [hj, ← hCeq]
    · -- index `a`: would force `C_U(H_{i₀}) = C_U(H_j)`, contradicting `hjne`
      exfalso
      apply hjne
      have hi : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA ⟨0, hq0⟩ := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_left : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j
            ≤ cuSubOf caseA ⟨0, hq0⟩)
          (cuSubOf_le_U caseA ⟨0, hq0⟩) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ha] at hlt
        exact lt_irrefl _ hlt
      have hjeq : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_right : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j ≤ cuSubOf caseA j)
          (cuSubOf_le_U caseA j) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA j, ha] at hlt
        exact lt_irrefl _ hlt
      rw [← hjeq, hi]

open OddOrder.Peterfalvi.S11 in
/-- **`C_H(U₁) ≠ 1` for the Clifford-summand centralizer `U₁ = C_U(H̄ᵢ)`** (Peterfalvi (9.11.4),
issue 1017): `U₁ = ker(aInvariantRestrictAut H̄ᵢ)` acts trivially on the nontrivial summand
`H̄ᵢ ≤ H̄ = H/H₀`, so by coprime fixed-point lifting (Isaacs Cor 3.28,
`map_fixedSubgroup_eq_fixedSubgroup_quotient`) the genuine fixed subgroup `C_H(U₁)` surjects onto
a subgroup of `H̄` containing `H̄ᵢ ≠ 1`; any nontrivial fixed point `x₀ ∈ H` is centralized by all
of `U₁`.  Generic (9.11) apparatus (any type-P setup); upstream-merge candidate into
`S11_NineElevenCoherence`. -/
theorem exists_cuSubOf_centralizer_witness {M : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i : Fin data.q) :
    ∃ x₀ : G, x₀ ∈ data.typeP.H ∧ x₀ ≠ 1 ∧
      cuSubOf caseA i ≤ Subgroup.centralizer ({x₀} : Set G) := by
  classical
  set X : Subgroup ↥(data.typeP.U ⊔ data.typeP.W1) :=
    (cuSubOf caseA i).subgroupOf (data.typeP.U ⊔ data.typeP.W1) with hXdef
  -- coprimality `|X| ⟂ |H|` (from `|H| ⟂ |U W₁|`)
  have hcop : Nat.Coprime (Nat.card ↥X) (Nat.card ↥data.typeP.H) :=
    ((typeP_coprime_H_uW1 data.typeP data.nontrivial.1).symm).coprime_dvd_left
      (Subgroup.card_subgroup_dvd_card X)
  -- `H` is solvable (a proper subgroup of the minimal counterexample)
  have hHM : data.typeP.H ≤ M := data.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hHsolv : Group.IsSolvable ↥data.typeP.H :=
    hG.isSolvable_of_lt_top _ (lt_of_le_of_lt hHM
      ((show IsCoatom M from data.maximal).1.lt_top))
  -- the quotient fixed subgroup contains the summand `H̄ᵢ` (kernel elements act trivially)
  have hfix : caseA.Hpart i
      ≤ fixedSubgroup (chief.N_aInvariant.quotientMulAutHom) X := by
    intro z hz
    rw [mem_fixedSubgroup]
    intro l hl
    have hlG : (l : G) ∈ cuSubOf caseA i := hl
    obtain ⟨w, hw, hwl⟩ := Subgroup.mem_map.mp hlG
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.mp hw
    have hwl' : w = l := Subtype.ext hwl
    rw [MonoidHom.mem_ker] at hu
    have hz' := aInvariantRestrictAut_coe (caseA.Hpart_aInvariant i) u ⟨z, hz⟩
    rw [hu] at hz'
    have huz : uActionHom data chief u z = z := by simpa using hz'.symm
    rw [← hwl', ← huw]
    exact huz
  -- lift along `mk' N`: `C_H(U₁) ≠ ⊥`
  have hmap := map_fixedSubgroup_eq_fixedSubgroup_quotient
    (φ := typeP_conjAction data.typeP) (X := X) chief.N_aInvariant hcop (Or.inr hHsolv)
  have hne : fixedSubgroup (typeP_conjAction data.typeP) X ≠ ⊥ := by
    intro hbot
    have h1 : caseA.Hpart i = ⊥ := by
      refine le_bot_iff.mp (hfix.trans ?_)
      rw [← hmap, hbot, Subgroup.map_bot]
    have h2 := caseA.Hpart_order i
    rw [h1, Subgroup.card_bot] at h2
    exact chief.p_prime.one_lt.ne h2
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  refine ⟨((x₀ : ↥data.typeP.H) : G), (x₀ : ↥data.typeP.H).2, ?_, ?_⟩
  · intro h1
    exact hx₀ne (Subtype.ext (Subtype.ext h1))
  · intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvUW : v ∈ data.typeP.U ⊔ data.typeP.W1 :=
      Subgroup.mem_sup_left ((cuSubOf_le_U caseA i) hv)
    have hfixv := x₀.2 (⟨v, hvUW⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
      (Subgroup.mem_subgroupOf.mpr hv)
    have hvx := congrArg (fun t : ↥data.typeP.H => (t : G)) hfixv
    simp only [typeP_conjAction_apply] at hvx
    calc v * ((x₀ : ↥data.typeP.H) : G)
        = (v * ((x₀ : ↥data.typeP.H) : G) * v⁻¹) * v := by group
      _ = ((x₀ : ↥data.typeP.H) : G) * v := by rw [hvx]

open OddOrder.Peterfalvi.S11 in
/-- **`(H·U₁)^# ⊆ A(S)`** (Peterfalvi (9.11.4), issue 1017; the Coq gap-patch
`PFsection9.v:1478-1484`).  Every nonidentity `y ∈ H ⊔ U₁` (`U₁ = cuSubOf caseA i` the explicit
TI-witness) lies in the honest Dade support `A(S)`.  The Coq comment records the gap: `{1} ∪ A(S)`
contains `H` and `U₁` but is *not a subgroup*, so `HU₁ ⊆ {1} ∪ A(S)` needs Philip Hall's theorems
in the solvable `HU₁`.  Proof: split `y` at its `σ(S)`-part `h = piPart σ y` (a power of `y`).
If `h ≠ 1` then `h ∈ S_σ = M_σ(S)` (`mem_Msigma_of_isPiElement_sigma_of_mem`) is a nonidentity
centralized witness (powers of `y` commute with `y`).  If `h = 1` then `y` is a `σ′`-element of
the solvable `K = H ⊔ U₁`; `U₁` is a Hall `σ′`-subgroup of `K` (`|K| = |H|·|U₁|`, `|H|` a
`σ`-number, `|U₁|` a `σ′`-number), so by Hall D/C (`hall_D`/`hall_C`) some `K`-conjugate
`g y g⁻¹` lies in `U₁ ≤ C_G(x₀)` for the fixed-point witness `x₀ ∈ H^#`
(`exists_cuSubOf_centralizer_witness`), whence `y` centralizes `g⁻¹ x₀ g ∈ H^# ⊆ S_σ^#`
(`H` is `K`-normal; `H ≤ M_σ` suffices — general type `P`).  In both cases `y ∈ S′` since
`K ≤ H ⊔ U = S′`. -/
theorem Hypothesis.mem_typePACore_of_mem_H_sup_cuSubOf [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) (i : Fin (hyp.toTypesIIIIIIVSetupS hG).q)
    {y : G} (hy : y ∈ (hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i) (hy1 : y ≠ 1) :
    y ∈ S10.typePACore hyp.S := by
  classical
  -- dictionary: `H = P ≤ S_σ` (the `≤` suffices at every use — general type `P`) and
  -- `S′ = H ⊔ U`
  have hHMs : ((hyp.toTypesIIIIIIVSetupS hG).H : Subgroup G)
      ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    have h1 : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
      change hyp.Sdata.H = hyp.P
      rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
    rw [h1, hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  have hSderiv : derivedInG hyp.S
      = (hyp.toTypesIIIIIIVSetupS hG).H ⊔ (hyp.toTypesIIIIIIVSetupS hG).U := by
    change _ = hyp.Sdata.H ⊔ hyp.Sdata.U
    rw [hyp.Sdata.derivedInG_eq_fitting_sup_U, hyp.Sdata.H_eq]
  have hKderiv : (hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i ≤ derivedInG hyp.S := by
    rw [hSderiv]
    exact sup_le le_sup_left ((cuSubOf_le_U caseA i).trans le_sup_right)
  have hKS : (hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i ≤ hyp.S :=
    hKderiv.trans (derivedInG_le_self hyp.S)
  have hyS : y ∈ hyp.S := hKS hy
  -- `σ`-prime dictionary: `π(|H|) ⊆ σ(S)` (via `H ≤ M_σ`)
  have hHpi : ∀ p ∈ (Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H).primeFactors,
      p ∈ OddOrder.BG.Ch3.S10.sigma hyp.S := by
    intro p hp
    obtain ⟨hpp, hpH, -⟩ := Nat.mem_primeFactors.mp hp
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup hyp.S p (Nat.mem_primeFactors.mpr
      ⟨hpp, hpH.trans (Subgroup.card_dvd_of_le hHMs), Nat.card_pos.ne'⟩)
  by_cases hone : OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.S) y = 1
  · -- `y` is a `σ′`-element: Hall-conjugate into `U₁`, then use the fixed-point witness
    have hyπ' : OddOrder.GroupTheory.IsPiElement ((OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ) y :=
      OddOrder.BG.Ch4.S14.isPiElement_compl_of_piPart_eq_one hone
    set Kg : Subgroup G := (hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i with hKgdef
    have hKsolv : Group.IsSolvable ↥Kg := hG.isSolvable_of_lt_top Kg
      (lt_of_le_of_lt hKS ((show IsCoatom hyp.S from hyp.S_maximal).1.lt_top))
    have hnorm : cuSubOf caseA i ≤ Subgroup.normalizer
        (((hyp.toTypesIIIIIIVSetupS hG).H : Set G)) :=
      (cuSubOf_le_U caseA i).trans (le_sup_left.trans
        (typeP_uW1_le_normalizer_H (hyp.toTypesIIIIIIVSetupS hG).typeP))
    have hdisj : Disjoint (hyp.toTypesIIIIIIVSetupS hG).H (cuSubOf caseA i) := by
      rw [disjoint_iff]
      refine le_bot_iff.mp ?_
      calc (hyp.toTypesIIIIIIVSetupS hG).H ⊓ cuSubOf caseA i
          ≤ (hyp.toTypesIIIIIIVSetupS hG).typeP.H ⊓ (hyp.toTypesIIIIIIVSetupS hG).typeP.U :=
            inf_le_inf_left _ (cuSubOf_le_U caseA i)
        _ = ⊥ := typeP_H_inf_U (hyp.toTypesIIIIIIVSetupS hG).typeP
    have hcardK : Nat.card ↥Kg
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H * Nat.card ↥(cuSubOf caseA i) :=
      OddOrder.BG.Ch1.S03f.card_sup_of_le_normalizer_of_disjoint hnorm hdisj
    -- `U₁` is a Hall `σ′`-subgroup of `K`
    have hU₁K : cuSubOf caseA i ≤ Kg := le_sup_right
    have hcardU₁ : Nat.card ↥((cuSubOf caseA i).subgroupOf Kg)
        = Nat.card ↥(cuSubOf caseA i) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU₁K).toEquiv
    have hidxU₁ : ((cuSubOf caseA i).subgroupOf Kg).index
        = Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H := by
      have h1 := Subgroup.card_mul_index ((cuSubOf caseA i).subgroupOf Kg)
      rw [hcardU₁, hcardK,
        mul_comm (Nat.card ↥(hyp.toTypesIIIIIIVSetupS hG).H)] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
    -- a Hall-`σ′` subgroup `P₁` of `U₁` is Hall-`σ′` in `K`: `[K : P₁] = |H|·[U₁ : P₁]`,
    -- both `σ`-sided.  (General type `P`: `U₁` itself need not be `σ`-free — for type III
    -- the `σ`-part of `U` may be nontrivial — but its `σ`-elements are caught by the
    -- `piPart` branch, and the `σ′`-conjugation only needs *some* Hall-`σ′` inside `U₁`.)
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
        ((OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ) P₁' := by
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
        p ∈ (OddOrder.BG.Ch3.S10.sigma hyp.S)ᶜ := by
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
    have hKnormH : Kg ≤ Subgroup.normalizer (((hyp.toTypesIIIIIIVSetupS hG).H : Set G)) :=
      sup_le Subgroup.le_normalizer hnorm
    have hx₁H : (g : G)⁻¹ * x₀ * (g : G) ∈ (hyp.toTypesIIIIIIVSetupS hG).H := by
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
  · -- the `σ`-part `h ≠ 1` is a nonidentity centralized `S_σ`-witness
    obtain ⟨b, hmul, hcomm, hpiA, hpiB, hhzpow, hbzpow⟩ :=
      OddOrder.BG.Ch4.S14.piPart_spec (OddOrder.BG.Ch3.S10.sigma hyp.S) y
    have hhS : OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.S) y ∈ hyp.S :=
      (Subgroup.zpowers_le.mpr hyS) hhzpow
    have hhMs := OddOrder.BG.Ch4.S14.mem_Msigma_of_isPiElement_sigma_of_mem hG
      hyp.S_maximal hhS (OddOrder.BG.Ch4.S14.isPiElement_piPart _ y)
    rw [S10.mem_typePACore]
    refine ⟨hKderiv hy, hy1, OddOrder.BG.Ch4.S14.piPart (OddOrder.BG.Ch3.S10.sigma hyp.S) y,
      ⟨SetLike.mem_coe.mpr hhMs, fun h => hone (Set.mem_singleton_iff.mp h)⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hhzpow
    rw [← hn]
    exact ((Commute.refl y).zpow_right n).eq

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4), the `A(S)`-support of `α = γ − ψ₁` — `S`-instance residual**
(issue 1017; the Coq gap-patch site `PFsection9.v:1478-1484`).  For the explicit TI-witness
`U₁ = cuSubOf caseA i = C_U(H̄ᵢ)` and a degree-`qa` member `ψ₁ ∈ 𝒮`, the difference
`α = Ind_{HU₁}^S 1 − ψ₁` is supported in `A(S) = {y ∈ (S′)^# | ∃ x ∈ S_σ^#, y ∈ C(x)}`
(`S10.mem_typePACore`; `H = S_σ = Msigma`).  The M-side dispatches this via
`A(M) = (M′)^#` (`mderivSharp_subset_A0`), **false** here (`A(S) ⊊ (S′)^#` strictly); the honest
route is the book's patched (9.11.4) argument: `supp γ ⊆ ⋃_g (HU₁)^g`
(`support_induce_subset_conjugatesInto`), and `HU₁^# ⊆ A(S)` by the commuting Hall decomposition
in `⟨y⟩` — a nontrivial `H`-part `h ∈ ⟨y⟩ ∩ H^#` gives `y ∈ C(h)` directly, while a σ′-element
`y` lies in a Hall-conjugate of `U₁` (solvable `HU₁`, Hall conjugacy) and `U₁ = C_U(H̄ᵢ)`
centralizes a nontrivial `H`-element by coprime fixed-point lifting; `ψ₁`'s support is
`A(S) ∪ {1}` (`sSet_member_support_subset`) and the value at `1` cancels
(`γ(1) = qa = ψ₁(1)`). -/
theorem Hypothesis.nineElevenAlphaSupportS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars) (i : Fin (hyp.toTypesIIIIIIVSetupS hG).q)
    {ψ₁ : ClassFunction ↥hyp.S ℂ}
    (hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG))
    (hψ₁deg : (ψ₁ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)) :
    (ClassFunction.induce
        ((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
          ⊔ (cuSubOf caseA i).subgroupOf hyp.S)
        (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
          ⊔ (cuSubOf caseA i).subgroupOf hyp.S))
      - ψ₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  classical
  have := hyp.finiteG
  have : Fintype G := Fintype.ofFinite G
  -- `γ(1) = q·a = ψ₁(1)`: the difference vanishes at the identity
  have hγ1 : ClassFunction.induce
      ((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)) (1 : ↥hyp.S)
      = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupS hG) (cuSubOf_le_U caseA i)
      (relIndex_cuSubOf_U_eq_a caseA i)
  -- the join sits below the `G`-level `K = H ⊔ U₁` (for the `A(S)`-membership core)
  have hjoin : (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
      ⊔ (cuSubOf caseA i).subgroupOf hyp.S
      ≤ ((hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i).subgroupOf hyp.S :=
    sup_le (Subgroup.subgroupOf_mono hyp.S le_sup_left)
      (Subgroup.subgroupOf_mono hyp.S le_sup_right)
  intro z hz
  have hz0 : (ClassFunction.induce
      ((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)) - ψ₁) z ≠ 0 := hz
  have hzne : z ≠ 1 := by
    rintro rfl
    exact hz0 (by rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self])
  rcases ClassFunction.support_sub_subset _ _ hz with hγ | hψ
  · -- `z ∈ Supp γ`: conjugate into `HU₁`, apply the `A(S)`-core, conjugate back
    have hconj := ClassFunction.support_induce_subset_conjugatesInto
      ((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)
      (trivialClassFunction ↥((hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
        ⊔ (cuSubOf caseA i).subgroupOf hyp.S)) hγ
    rw [ClassFunction.mem_conjugatesInto] at hconj
    obtain ⟨c, hc⟩ := hconj
    have hwG : ((c⁻¹ * z * c : ↥hyp.S) : G)
        ∈ (hyp.toTypesIIIIIIVSetupS hG).H ⊔ cuSubOf caseA i :=
      Subgroup.mem_subgroupOf.mp (hjoin hc)
    have hwne : ((c⁻¹ * z * c : ↥hyp.S) : G) ≠ 1 := by
      intro he
      apply hzne
      have h1 : (c⁻¹ * z * c : ↥hyp.S) = 1 := Subtype.ext he
      have h2 : z = c * (c⁻¹ * z * c) * c⁻¹ := by group
      rw [h2, h1]
      group
    have hwA := hyp.mem_typePACore_of_mem_H_sup_cuSubOf hG chars caseA i hwG hwne
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    have hzeq : (z : G) = (c : G) * ((c⁻¹ * z * c : ↥hyp.S) : G) * (c : G)⁻¹ := by
      push_cast
      group
    rw [hzeq]
    exact S10.typePACore_conj_mem c.2 hwA
  · -- `z ∈ Supp ψ₁`: the (4.7) member support minus the identity
    rcases hyp.sSet_member_support_subset hG hψ₁mem hψ with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hzne

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Peterfalvi (9.11.4) at the `S`-instance: the cleared Mackey-norm bundle** (issue 1017; the
`S`-mirror of `S13.caseA_nineElevenFour_norm_inputs`).  In the equality configuration (`C = U′`,
the (9.8.d) count) there is `N : ℕ` with `N·u = (a+1)·u + (q−1)·a²`, realized as `N = ‖α‖²` for
the `A(S)`-supported virtual character `α = γ − ψ₁ ∈ ℤ[Irr S]` — `γ = Ind_{HU₁}^S 1` at the
explicit TI-witness `U₁ = cuSubOf caseA 0` (`cuSubOf_zero_tiWitness`), `ψ₁` a degree-`qa`
irreducible member from the (9.8.d) count.  Norm: `‖α‖² = ‖γ‖² + 1`
(`cfnorm_sub_irreducible_orthogonal`; orthogonality `nineElevenGamma_inner_induceHU`) and
`‖γ‖²·u = a·u + (q−1)·a²` (`nineElevenGamma_inner_self_mul_u`, the Mackey double-coset count at
the TI-identity); integrality by `mem_ZIrr_inner_self_eq_sum_sq`; support by the
`nineElevenAlphaSupportS` residual. -/
theorem Hypothesis.nineElevenFourNormInputsS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {chief : ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)}
    (chars : Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief)
    (caseA : CliffordCaseAData chars)
    (hdich : ∀ φ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief),
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥hyp.S → ℂ) 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ))
    (hCUprime : chars.C = chars.Uprime)
    (hcount : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
          (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
          IsIrreducibleCharacter χ ∧
            χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a)
        = (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
          (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U)) :
    ∃ N : ℕ,
      N * chars.u = (caseA.a + 1) * chars.u
        + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 ∧
      ∃ α : ClassFunction ↥hyp.S ℂ,
        α ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S ∧
        α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∧
        ClassFunction.inner α α = (N : ℂ) := by
  classical
  have := hyp.finiteG
  have hq0 : 0 < (hyp.toTypesIIIIIIVSetupS hG).q :=
    (hyp.toTypesIIIIIIVSetupS hG).nontrivial.2.1.pos
  -- the explicit TI-witness `U₁ = cuSubOf caseA 0` and its (9.11.2) facts
  have hTI := cuSubOf_zero_tiWitness caseA hdich
  have hCU₁ : OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief
      ≤ cuSubOf caseA ⟨0, hq0⟩ := cSub_le_cuSubOf caseA ⟨0, hq0⟩
  have hU₁U : cuSubOf caseA ⟨0, hq0⟩ ≤ (hyp.toTypesIIIIIIVSetupS hG).U :=
    cuSubOf_le_U caseA ⟨0, hq0⟩
  have hU₁a : (cuSubOf caseA ⟨0, hq0⟩).relIndex (hyp.toTypesIIIIIIVSetupS hG).U = caseA.a :=
    relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩
  have hUpU₁ : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
      ≤ cuSubOf caseA ⟨0, hq0⟩ := by
    have hUpC : OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)
        = OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupS hG) chief := hCUprime.symm
    rw [hUpC]; exact hCU₁
  -- `ψ₁ ∈ 𝒮₁`: the degree-`qa` irreducible family is nonempty by the (9.8.d) count
  have hrelne : (OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)).relIndex
      (hyp.toTypesIIIIIIVSetupS hG).U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupS hG)
      (chief.H0 ⊔ OddOrder.Peterfalvi.S11.uprimeSub (hyp.toTypesIIIIIIVSetupS hG)) |
      IsIrreducibleCharacter χ ∧
        χ 1 = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have hrpos := Nat.pos_of_ne_zero hrelne
    have : 0 < (chief.p - 1) * ((OddOrder.Peterfalvi.S11.uprimeSub
        (hyp.toTypesIIIIIIVSetupS hG)).relIndex (hyp.toTypesIIIIIIVSetupS hG).U) :=
      Nat.mul_pos (by omega) hrpos
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hζxi : ζ ∈ OddOrder.Peterfalvi.S11.xiSet (hyp.toTypesIIIIIIVSetupS hG) :=
    OddOrder.Peterfalvi.S11.xiOf_subset_xiSet (hyp.toTypesIIIIIIVSetupS hG) _ hζmem
  -- `γ = Ind_{HU₁}^S 1` and its landed (9.11.4) facts
  set K : Subgroup ↥hyp.S := (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S
    ⊔ (cuSubOf caseA ⟨0, hq0⟩).subgroupOf hyp.S with hKdef
  set γ : ClassFunction ↥hyp.S ℂ :=
    ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S :=
    nineElevenGamma_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) (cuSubOf caseA ⟨0, hq0⟩)
  have hγ1 : γ (1 : ↥hyp.S) = (((hyp.toTypesIIIIIIVSetupS hG).q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one (hyp.toTypesIIIIIIVSetupS hG) hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u
          + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  have hindEq : induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
      = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupS hG))
        (ζ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) := rfl
  -- orthogonality `⟨γ, ψ₁⟩ = 0` and the norm split `‖α‖² = ‖γ‖² + 1`
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := by
    rw [hψ₁eq, hindEq]
    exact nineElevenGamma_inner_induceHU (hyp.toTypesIIIIIIVSetupS hG) hU₁U hζxi
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  -- `α ∈ ℤ[Irr S]` and the integrality of `‖α‖²`
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥hyp.S := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr (hyp.toTypesIIIIIIVSetupS hG) ζ
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
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ)
          + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u
            + ((hyp.toTypesIIIIIIVSetupS hG).q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  · -- `Supp(α) ⊆ A(S)`: the (9.11.4) support residual at the explicit witness
    have hψ₁mem : ψ₁ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) :=
      hyp.sOf_H0Uprime_subset_sSet hG chars ⟨ζ, hζmem, hψ₁eq⟩
    exact hyp.nineElevenAlphaSupportS hG chars caseA ⟨0, hq0⟩ hψ₁mem hψ₁deg

end OddOrder.Peterfalvi.S15



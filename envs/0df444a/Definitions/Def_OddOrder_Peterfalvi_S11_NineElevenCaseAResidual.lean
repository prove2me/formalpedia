-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCaseAResidual
-- name    : OddOrder_Peterfalvi_S11_NineElevenCaseAResidual
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:45:52.696295+00:00
-- url     : https://prove2.me/theorems/f85ab5ca-3525-4838-b1a6-7eb6815659fa
-- title:
--   Peterfalvi (9.7.a): the residual chain, §9 level
-- statement:
--   Formalizes the case (9.7.a) residual chain at the §9 level (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8 (8.15.3), §9 (9.5), pp. 47-51), including the coherence of $\mathcal{S}_3$ via (5.7) and the (9.11.4)–(9.11.8) norm bound.
--
--   Main declarations: `caseA_sThree_coherent` (Peterfalvi (5.7) at the uniform degree `qu`: `𝒮₃` is coherent, at §9 level); `caseA_normBound_of_sevenEightRefutation` (Peterfalvi (9.11.4)–(9.11.8): the norm bound, at §9 level); `caseA_sevenEightRefutation` (Peterfalvi (9.11.7)–(9.11.8), discharged at §9 level); `caseA_normBound` (Peterfalvi (9.11.4)–(9.11.8), discharged at §9 level).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenCaseAResidual.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenCaseAResidual.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence
import Definitions.Def_OddOrder_Peterfalvi_S07_UnionPairBridge
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenSubcoherentBridge
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenBridgeBase
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenRFamily
import Definitions.Def_OddOrder_Peterfalvi_S10_SubcoherentTypeP
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTIWitness
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.7) at the uniform degree `qu`: `𝒮₃` is coherent, at §9 level** — the §9 form of
`S13.caseA_sThree_coherent`, supplying the `τ₃` of the (9.11.6) dichotomy.

`𝒮₃ = 𝒮(H₀C′) ∖ 𝒮₂` has uniform degree `qu` (`hS3deg`), is conjugation-closed (`𝒮(H₀C′)` is, and
`𝒮₂` is), has no real members (odd order), and its equal-degree differences are `A₀`-supported —
so the norm-general (5.7) engine applies with the §9 `R`-family dispatch in place of the §10 one.

Structurally identical to `sOf_caseB_coherent`; only the family and the degree differ. -/
theorem caseA_sThree_coherent [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    {S₂ : Set (ClassFunction ↥M ℂ)}
    (hS₂conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₂)
    (hS₃ne : (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂).Nonempty)
    (hS3deg : ∀ χ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      (χ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) := by
  classical
  have := derivedInG_subgroupOf_normal M
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  obtain ⟨χ₀, hχ₀⟩ := hS₃ne
  have hconjS : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      a.conj ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := by
    intro a ha
    refine ⟨sOf_closedUnderConjugate data _ ha.1, ?_⟩
    intro hc
    exact ha.2 (by simpa using hS₂conj hc)
  have hnr : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂, a ≠ a.conj := fun a ha h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _ (hIKF ha.1) h.symm
  have hsuppdiff : ∀ a ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ b ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ((a - b : ClassFunction ↥M ℂ)).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M := by
    intro a ha b hb
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF ha.1) (hIKF hb.1) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS3deg a ha, hS3deg b hb])
    rwa [one_smul] at h
  have hN : ∃ n : ℕ, ClassFunction.inner χ₀ χ₀ = (n : ℂ) := by
    obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hχ₀.1))
    have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    refine ⟨(∑ x ∈ c.support, (c x) ^ 2).toNat, ?_⟩
    rw [hcsum]
    exact_mod_cast (congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)).symm
  exact OddOrder.Peterfalvi.S07.uniform_degree_coherence_of_families
    ((sOf_finite data (chief.H0 ⊔ cprimeSub data chief)).subset Set.sdiff_subset)
    hχ₀
    (fun η hη => sOf_memberRFamily hG hM data h46 hKeq htau hKsupp hη.1)
    (fun a ha b hb hab =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF ha.1) (hIKF hb.1) hab)
    hconjS hnr hN
    (fun {φ ψ} hφ hψ => by
      rw [htau]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hφ)
        (OddOrder.Peterfalvi.S07.support_subset_of_mem_zSupportedSpan hψ))
    (fun a ha b hb => by
      rw [htau]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
        h46.dade0 (hsuppdiff a ha b hb)
        (Submodule.sub_mem _ (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF ha.1))
          (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hb.1))))
    hsuppdiff
    (fun {φ ξ} hφ hξ h1 h2 =>
      sOf_memberRFamily_orthogonal hG hM data h46 hKeq htau hKsupp hVsub hφ.1 hξ.1 h1 h2)
    (fun a ha => (hS3deg a ha).trans (hS3deg χ₀ hχ₀).symm)
    (by
      rw [hS3deg χ₀ hχ₀]
      exact Nat.cast_ne_zero.mpr
        (mul_ne_zero data.nontrivial.2.1.pos.ne' (u_odd hG chars).pos.ne'))
    (fun h => (OddOrder.Peterfalvi.S04.mem_sharp.mp
      (h46.dade0.subset_sharp (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h))).2 rfl)
    (hconjS χ₀ hχ₀)
    (fun h => hnr χ₀ hχ₀ h.symm)

set_option maxHeartbeats 1600000 in
-- (9.11) のノルム評価は FiniteInduce スコープ上の重い展開で既定 heartbeat を超えるため引き上げる
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8): the norm bound, at §9 level** — the §9 form of
`S13.nineElevenNormBound_of_sevenEightRefutation`, discharged up to the (9.11.7)–(9.11.8)
residual.

The (9.11.4) context `α = γ − ψ₁` is rebuilt with `γ = Ind_{HU₁}^M 1` from the TI-witness, and
`τ₃` is `caseA_sThree_coherent`.  `⟨α^τ, λ^{τ₃}⟩` is **constant** over `λ ∈ 𝒮₃`: `τ₃` agrees with
`τ` on the `A₀`-supported equal-degree differences, the Dade isometry moves the pairing to the
source, and `⟨α, λ⟩ = 0` there.  Nonzero constant ⇒ each `𝒮₄`-member's `τ₃`-image is a unit
constituent of `α^τ`, so Bessel gives `|𝒮₄| ≤ ‖α‖² = N`.  Zero constant is the book's (9.11.6)
branch, refuted by `h78`.

All the `nineElevenGamma_*` inputs were already §9-level; the only §13 pieces were the TI-witness
and `τ₃`, both descended above.  **No type hypothesis remains** — §13's `hncH0C`/`htype` served
the `H₀C′ ≤ H₀C` step for `𝒮₄ ⊆ 𝒮₃`, definitional here. -/
theorem caseA_normBound_of_sevenEightRefutation [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    (h78 : CaseASevenEightRefutation caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :
    CaseANormBound caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) := by
  classical
  have := derivedInG_subgroupOf_normal M
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
  set A0 : Set ↥M := OddOrder.Peterfalvi.S04.supportInSubgroup
    (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M with hA0def
  obtain ⟨c₃⟩ := caseA_sThree_coherent hG hM chars h46 hKeq htau hKsupp hVsub
    hS₂conj hS₃ne hS3deg
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, hTI⟩ := caseA_nineElevenTwo_tiWitness caseA hS3deg hS2deg
  have hUpU₁ : uprimeSub data ≤ U₁ := by
    have h : cSub data chief = uprimeSub data := hCUprime
    rw [← h]; exact hCU₁
  have hrelne : (uprimeSub data).relIndex data.U ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hcne : {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) | IsIrreducibleCharacter χ ∧
      χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcount
    have hp1 : 1 < chief.p := chief.p_prime.one_lt
    have h1 := Nat.pos_of_ne_zero hrelne
    have h2 : 0 < (chief.p - 1) * ((uprimeSub data).relIndex data.U) := Nat.mul_pos (by omega) h1
    omega
  obtain ⟨ψ₁, hψ₁sOf, hψ₁irr, hψ₁deg⟩ := Set.nonempty_of_ncard_ne_zero hcne
  have hle : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
    refine sup_le_sup_left ?_ chief.H0
    change derivedInG (cSub data chief) ≤ derivedInG data.U
    rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
    exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
  have hψ₁sOfC' : ψ₁ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := sOf_antitone data hle hψ₁sOf
  have hψ₁S₂ : ψ₁ ∈ S₂ := hS₁sub ⟨hψ₁sOfC', hψ₁irr, hψ₁deg⟩
  obtain ⟨ζ, hζmem, hψ₁eq⟩ := hψ₁sOf
  have hindEqζ : induceHU data (ζ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (ζ : ClassFunction ↥(huSub data) ℂ) := rfl
  set K : Subgroup ↥M := data.H.subgroupOf M ⊔ U₁.subgroupOf M with hKdef
  set γ : ClassFunction ↥M ℂ := ClassFunction.induce K (trivialClassFunction ↥K) with hγdef
  have hγsupp : γ.support ⊆ (huSub data : Set ↥M) := nineElevenGamma_support data hU₁U
  have hγZIrr : γ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := nineElevenGamma_mem_ZIrr data U₁
  have hγ1 : γ (1 : ↥M) = ((data.q * caseA.a : ℕ) : ℂ) :=
    nineElevenGamma_apply_one data hU₁U hU₁a
  have hγγu : ClassFunction.inner γ γ * (chars.u : ℂ)
      = ((caseA.a * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) :=
    nineElevenGamma_inner_self_mul_u chars hU₁U hUpU₁ hU₁a hTI
  have hγorth : ∀ φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief),
      ClassFunction.inner γ φ = 0 := by
    intro φ hφ
    obtain ⟨ξ, hξ, rfl⟩ := hφ
    have hξxi : ξ ∈ xiSet data := xiOf_subset_xiSet data _ hξ
    have hindEqξ : induceHU data (ξ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.induce (huSub data) (ξ : ClassFunction ↥(huSub data) ℂ) := rfl
    rw [hindEqξ]
    exact nineElevenGamma_inner_induceHU data hU₁U hξxi
  have hγψ : ClassFunction.inner γ ψ₁ = 0 := hγorth ψ₁ hψ₁sOfC'
  have hαα : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) = ClassFunction.inner γ γ + 1 :=
    cfnorm_sub_irreducible_orthogonal hψ₁irr hγψ
  have hαZIrr : γ - ψ₁ ∈ OddOrder.RepresentationTheory.ZIrr ↥M := by
    refine Submodule.sub_mem _ hγZIrr ?_
    rw [hψ₁eq]
    exact induceHU_mem_ZIrr data ζ
  obtain ⟨c, -, -, hcsum⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_self_eq_sum_sq hαZIrr
  have hm0 : 0 ≤ ∑ x ∈ c.support, (c x) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmval : ClassFunction.inner (γ - ψ₁) (γ - ψ₁)
      = ((∑ x ∈ c.support, (c x) ^ 2 : ℤ) : ℂ) := by
    rw [hcsum]; push_cast; rfl
  set N : ℕ := (∑ x ∈ c.support, (c x) ^ 2).toNat with hNdef
  have hNval : ((N : ℕ) : ℂ) = ClassFunction.inner (γ - ψ₁) (γ - ψ₁) := by
    rw [hmval, hNdef]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) (Int.toNat_of_nonneg hm0)
  have hNu : N * chars.u = (caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 := by
    have h2 : ClassFunction.inner (γ - ψ₁) (γ - ψ₁) * (chars.u : ℂ)
        = ((caseA.a * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) + (chars.u : ℂ) := by
      rw [hαα, add_mul, one_mul, hγγu]
    have h3 : ((N * chars.u : ℕ) : ℂ)
        = (((caseA.a + 1) * chars.u + (data.q - 1) * caseA.a ^ 2 : ℕ) : ℂ) := by
      push_cast at h2 ⊢
      rw [hNval]
      linear_combination h2
    exact Nat.cast_injective h3
  have hαsupp : ((γ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    intro x hx
    have hxmem : x ∈ γ.support ∪ ψ₁.support := ClassFunction.support_sub_subset γ ψ₁ hx
    have hxHU : x ∈ huSub data := by
      rcases hxmem with h | h
      · exact hγsupp h
      · have hψsupp : ψ₁.support ⊆ (huSub data : Set ↥M) := by
          rw [hψ₁eq, hindEqζ]
          exact ClassFunction.support_induce_subset_of_normal _ _
        exact hψsupp h
    have hx1 : x ≠ 1 := by
      intro h1
      rw [ClassFunction.mem_support, h1] at hx
      apply hx
      rw [ClassFunction.sub_apply, hγ1, hψ₁deg, sub_self]
    have hxM' : x ∈ (derivedInG M).subgroupOf M := by
      rwa [← huSub_eq_derivedInG_subgroupOf]
    exact hKsupp x hxM' hx1
  have hταZIrr : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁)
      ∈ OddOrder.RepresentationTheory.ZIrr G := by
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      h46.dade0 hαsupp hαZIrr
  have htauiso : ∀ {φ ψ : ClassFunction ↥M ℂ}, φ.support ⊆ A0 → ψ.support ⊆ A0 →
      ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau φ)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau ψ)
        = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
      hφ hψ
  have hταnorm := htauiso hαsupp hαsupp
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  have hαorthS₃ : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner (γ - ψ₁) lam = 0 := by
    intro lam hlam
    have hψlam : ClassFunction.inner ψ₁ lam = 0 :=
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hψ₁sOfC') (hIKF hlam.1) (fun h => hlam.2 (h ▸ hψ₁S₂))
    rw [ClassFunction.inner_sub_left, hγorth lam hlam.1, hψlam, sub_zero]
  have hdiffsupp3 : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ lam' ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ((lam - lam' : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    intro lam hlam lam' hlam'
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF hlam.1) (hIKF hlam'.1) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS3deg lam hlam, hS3deg lam' hlam'])
    rwa [one_smul] at h
  have hconst : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ∀ lam' ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam)
        = ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam') := by
    intro lam hlam lam' hlam'
    have hdiffsupp := hdiffsupp3 lam hlam lam' hlam'
    have hzss : (lam - lam' : ClassFunction ↥M ℂ)
        ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
          (sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂) A0 :=
      OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr
        ⟨Submodule.sub_mem _ (Submodule.subset_span hlam) (Submodule.subset_span hlam'),
          hdiffsupp⟩
    have hagree := c₃.extends_on_supported _ hzss
    have hiso := htauiso hαsupp hdiffsupp
    have hz : ClassFunction.inner (γ - ψ₁) (lam - lam') = 0 := by
      rw [ClassFunction.inner_sub_right, hαorthS₃ lam hlam, hαorthS₃ lam' hlam', sub_zero]
    have hsub : ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam)
        - ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension lam') = 0 := by
      rw [← ClassFunction.inner_sub_right, ← map_sub, hagree, hiso, hz]
    exact sub_eq_zero.mp hsub
  by_cases hc : ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
        (c₃.extension lam) = 0
  · exact (h78 S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg
      hcount hFbound hS2deg N hNu c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc).elim
  · push Not at hc
    obtain ⟨lam₀, hlam₀, hlam₀ne⟩ := hc
    have hleC : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
      sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
    have hS4sub : caseASFour data chief S₂
        ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := fun ξ hξ =>
      ⟨sOf_antitone data hleC hξ.1, hξ.2.2⟩
    have hS4fin : (caseASFour data chief S₂).Finite :=
      (sOf_finite data (chief.H0 ⊔ cprimeSub data chief)).subset (fun ξ hξ => (hS4sub hξ).1)
    refine ⟨N, hNu, ?_⟩
    have hON1 : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ) = 1 := by
      intro ξ hξT
      have hξ := hS4fin.mem_toFinset.mp hξT
      have hξ3 := hS4sub hξ
      rw [c₃.extension_inner_eq ξ ξ (Submodule.subset_span hξ3) (Submodule.subset_span hξ3)]
      have h := irreducibleCharacter_inner_eq_ite
        (⟨ξ, hξ.2.1⟩ : IrreducibleCharacter ↥M) ⟨ξ, hξ.2.1⟩
      rwa [if_pos rfl] at h
    have hON2 : ∀ ξ ∈ hS4fin.toFinset, ∀ ξ' ∈ hS4fin.toFinset, ξ ≠ ξ' →
        ClassFunction.inner (c₃.extension ξ) (c₃.extension ξ') = 0 := by
      intro ξ hξT ξ' hξ'T hne
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      have hξ'3 := hS4sub (hS4fin.mem_toFinset.mp hξ'T)
      rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ3) (Submodule.subset_span hξ'3)]
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF hξ3.1) (hIKF hξ'3.1) hne
    have hint : ∀ ξ ∈ hS4fin.toFinset, ∃ m : ℤ,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension ξ) = (m : ℂ) := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      exact ClassFunction.inner_mem_ZIrr_int hταZIrr
        (c₃.extension_mem_ZIrr ξ (Submodule.subset_span hξ3))
    have hnec : ∀ ξ ∈ hS4fin.toFinset,
        ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
          (c₃.extension ξ) ≠ 0 := by
      intro ξ hξT
      have hξ3 := hS4sub (hS4fin.mem_toFinset.mp hξT)
      rw [hconst ξ hξ3 lam₀ hlam₀]
      exact hlam₀ne
    have hcount4 := OddOrder.Peterfalvi.S07.card_le_inner_self_re_of_orthonormal_inner_int_ne
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
      hS4fin.toFinset (fun ξ => c₃.extension ξ) hON1 hON2 hint hnec
    have hNre : (ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau (γ - ψ₁))).re
        = (N : ℝ) := by
      rw [hταnorm, ← hNval, Complex.natCast_re]
    rw [hNre] at hcount4
    have hcard : ((caseASFour data chief S₂).ncard : ℝ) ≤ (N : ℝ) := by
      rw [Set.ncard_eq_toFinset_card _ hS4fin]
      exact hcount4
    exact_mod_cast hcard

set_option maxHeartbeats 3200000 in
-- threads the `dadeIntegralCharacterMap` isometry through the ZIrr/support layers while
-- assembling the ~20 scalar inputs of the projection budget (same profile as the §13 version)
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.7)–(9.11.8), discharged at §9 level** — the §9 form of
`S13.nineElevenSevenEightRefutation` (Coq `PFsection9.v:2048-2227`, the tail of
`Ptype_core_coherence`).

In the orthogonal branch `α^τ ⊥ 𝒮₃^{τ₃}` of the (9.11.6) dichotomy: `𝒮₄ ≠ ∅` (else the
(9.11.2)–(9.11.5) arithmetic spine already refutes, since `|𝒮₄| = 0 ≤ N`); pick `λ₁ ∈ 𝒮₄`, put
`e = u/a = [U₁ : C] ≥ 2` (`a ∣ u` by the `C ≤ U₁ ≤ U` index chain; `u ≠ a` since a degree-`qa`
irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`) and `β = λ₁ − e·ψ₁`.  The projection budget
(`S07.exists_bridge_target_of_budget`) applied to `β^τ` and `α^τ` over the orthonormal families
`𝒮₂^{τ₁}` (`|𝒮₂| = 2e` by the (9.8.d) count at the equality configuration) and `𝒮₄^{τ₃}` —
cross-orthogonal by `sOf_coherent_extension_cross_orthogonal` — produces `Γ ∈ ℤ[Irr G]` with
`‖Γ‖² = 1`, `Γ ⊥ 𝒮₂^{τ₁}`, `⟨Γ, λ₁^{τ₃}⟩ − ⟨Γ, λ̄₁^{τ₃}⟩ = 1` and the bridge
`β^τ = Γ − e·τ₁ψ₁`.  The union-pair extension (`S07.isCoherent_union_pair_of_bridge`, with
`X = Γ`, `Xc = Γ − (λ₁ − λ̄₁)^τ`) then adjoins `{λ₁, λ̄₁}` coherently to `𝒮₂`, contradicting the
maximality pair clause `hpairs`.

**No type hypothesis remains.**  §13 uses `hncH0C`/`htype` in exactly one place — the rewrite
`hyp.C = cSub` inside `𝒮₄ ⊆ 𝒮₃` (`H₀C′ ≤ H₀C`) — and at §9 `chars.C` *is* `cSub data chief`, so
the rewrite and the hypotheses go together.  The (9.11.4) norm value `N` arrives as the carrier's
`hnorm` parameter instead of being rebuilt from `γ` a second time. -/
theorem caseA_sevenEightRefutation [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G)) :
    CaseASevenEightRefutation caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) := by
  classical
  have := derivedInG_subgroupOf_normal M
  set A0 : Set ↥M := OddOrder.Peterfalvi.S04.supportInSubgroup
    (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M with hA0def
  set tau : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau with htaudef
  intro S₂ hS₁sub hS₂sub hS₂conj hS₂coh hS₃ne hpairs h2a hCUprime hS3deg hcount hFbound hS2deg
    N hnorm c₃ γ ψ₁ hψ₁S₂ hψ₁irr hψ₁deg hγZIrr hγ1 hγorth hαsupp hc
  obtain ⟨c₁⟩ := hS₂coh
  -- ── ambient family facts
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {_} hx =>
    sOf_subset_inducedKernelFamily_bot hG hM data _ hx
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hSfin : (sOf data (chief.H0 ⊔ cprimeSub data chief)).Finite :=
    sOf_finite data (chief.H0 ⊔ cprimeSub data chief)
  have hS₂fin : S₂.Finite := hSfin.subset hS₂sub
  have hS₂cut := caseA_sTwo_subset_degreeQaCut hG hM caseA hS₁sub hS₂sub h2a hCUprime
    hcount hFbound
  have hψ₁sOf : ψ₁ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) := hS₂sub hψ₁S₂
  have hselfone : ∀ {χ : ClassFunction ↥M ℂ}, IsIrreducibleCharacter χ →
      ClassFunction.inner χ χ = 1 := by
    intro χ hχ
    have h := irreducibleCharacter_inner_eq_ite
      (⟨χ, hχ⟩ : IrreducibleCharacter ↥M) ⟨χ, hχ⟩
    rwa [if_pos rfl] at h
  -- ── the two `τ`-facts on the supported lattice, from `htau`
  have htauiso : ∀ {φ ψ : ClassFunction ↥M ℂ}, φ.support ⊆ A0 → ψ.support ⊆ A0 →
      ClassFunction.inner (tau φ) (tau ψ) = ClassFunction.inner φ ψ := by
    intro φ ψ hφ hψ
    rw [htaudef, htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_of_supported h46.dade0
      hφ hψ
  have htauZ : ∀ {φ : ClassFunction ↥M ℂ}, φ.support ⊆ A0 →
      φ ∈ OddOrder.RepresentationTheory.ZIrr ↥M → tau φ ∈ OddOrder.RepresentationTheory.ZIrr G := by
    intro φ hsupp hZ
    rw [htaudef, htau]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported h46.dade0
      hsupp hZ
  -- ── the (9.11.2) TI-witness supplies `U₁` with `C ≤ U₁ ≤ U`, `[U:U₁] = a`
  obtain ⟨U₁, hCU₁, hU₁U, hU₁a, -⟩ := caseA_nineElevenTwo_tiWitness caseA hS3deg hS2deg
  obtain ⟨e, hedef⟩ : ∃ e : ℕ, e = (cSub data chief).relIndex U₁ := ⟨_, rfl⟩
  have hue : e * caseA.a = chars.u := by
    rw [hedef]
    have h := Subgroup.relIndex_mul_relIndex (cSub data chief) U₁ data.U hCU₁ hU₁U
    rwa [hU₁a, relIndex_cSub_U_eq_u chars] at h
  -- ── the arithmetic spine refutes `|𝒮₄| ≤ N`, so `𝒮₄ ≠ ∅`
  obtain ⟨K₁, K₂, hK₁, hK₂, hCinf⟩ := caseA_two_summand_inertia_inputs caseA hS3deg hS2deg
  have hclass := caseA_nineElevenThree_count_inputs hG caseA hS₁sub hS3deg hS2deg
    hCUprime hcount
  have hqp : (data.q).Prime := data.nontrivial.2.1
  have hqodd : Odd data.q :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card data.typeP.W1)
  have hq3 : 3 ≤ data.q := by
    obtain ⟨k, hk⟩ := hqodd
    have h2 := hqp.two_le
    omega
  have hu1 : 1 ≤ chars.u := (u_odd hG chars).pos
  have hp1 : 1 < chief.p := chief.p_prime.one_lt
  have hpeq : chief.p = 2 * caseA.a + 1 := by omega
  have hS4ne : (caseASFour data chief S₂).Nonempty := by
    rcases Set.eq_empty_or_nonempty (caseASFour data chief S₂) with hemp | hne
    · exact absurd
        (nineElevenCaseA_equality_refutation caseA hq3 hu1 hpeq hK₁ hK₂ hCinf hclass rfl hnorm
          (by rw [hemp, Set.ncard_empty]; exact Nat.zero_le N))
        not_false
    · exact hne
  obtain ⟨lam₁, hlam₁S₄⟩ := hS4ne
  obtain ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩ := hlam₁S₄
  -- ── `𝒮₄ ⊆ 𝒮₃` along `H₀C′ ≤ H₀C`; the pair `{λ₁, λ̄₁}` lives in `𝒮₄`
  have hleC : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ cSub data chief :=
    sup_le_sup_left (cprimeSub_le_C data chief) chief.H0
  have hS4sub : caseASFour data chief S₂
      ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := fun ξ hξ =>
    ⟨sOf_antitone data hleC hξ.1, hξ.2.2⟩
  have hlam₁S₃ : lam₁ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ :=
    hS4sub ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩
  have hlam₁c_S₄ : lam₁.conj ∈ caseASFour data chief S₂ := by
    refine ⟨sOf_closedUnderConjugate data _ hlam₁sOfC, hlam₁irr.conj, ?_⟩
    intro hmem
    apply hlam₁nS₂
    have h := hS₂conj hmem
    rwa [ClassFunction.conj_conj] at h
  have hlam₁cS₃ : lam₁.conj ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ :=
    hS4sub hlam₁c_S₄
  have hlam₁ne : lam₁ ≠ lam₁.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF hlam₁S₃.1) h.symm
  have hlam₁deg : (lam₁ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) := hS3deg lam₁ hlam₁S₃
  -- ── `e ≥ 2`: `u ≠ a` since a degree-`qa` irreducible member would lie in `𝒮₁ ⊆ 𝒮₂`
  have hune : chars.u ≠ caseA.a := by
    intro huea
    apply hlam₁nS₂
    apply hS₁sub
    refine ⟨hlam₁S₃.1, hlam₁irr, ?_⟩
    rw [hlam₁deg, huea]
  have he2 : 2 ≤ e := by
    have ha1 : 1 ≤ caseA.a := caseA.a_pos
    rcases Nat.lt_or_ge e 2 with h | h
    · exfalso
      interval_cases e
      · rw [zero_mul] at hue
        omega
      · rw [one_mul] at hue
        exact hune hue.symm
    · exact h
  -- ── `|𝒮₂| = 2e` from the (9.8.d) count at the equality configuration
  have hS₂eq : S₂ = {φ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
      IsIrreducibleCharacter φ ∧ φ 1 = ((data.q * caseA.a : ℕ) : ℂ)} := by
    refine Set.Subset.antisymm hS₂cut ?_
    have hleU' : chief.H0 ⊔ cprimeSub data chief ≤ chief.H0 ⊔ uprimeSub data := by
      refine sup_le_sup_left ?_ chief.H0
      change derivedInG (cSub data chief) ≤ derivedInG data.U
      rw [derivedInG_eq_commutator (cSub data chief), derivedInG_eq_commutator data.U]
      exact Subgroup.commutator_mono (cSub_le_U data chief) (cSub_le_U data chief)
    exact fun φ hφ => hS₁sub ⟨sOf_antitone data hleU' hφ.1, hφ.2.1, hφ.2.2⟩
  have hcardS₂ : hS₂fin.toFinset.card = 2 * e := by
    have hrelu : (uprimeSub data).relIndex data.U = chars.u := by
      have hUpC : cSub data chief = uprimeSub data := hCUprime
      rw [← hUpC]
      exact relIndex_cSub_U_eq_u chars
    have hcount' : S₂.ncard * (caseA.a * caseA.a) = 2 * e * (caseA.a * caseA.a) := by
      rw [hS₂eq, hcount, hrelu, ← h2a, ← hue]
      ring
    have ha0 : 0 < caseA.a * caseA.a := Nat.mul_pos caseA.a_pos caseA.a_pos
    have hncard : S₂.ncard = 2 * e := Nat.eq_of_mul_eq_mul_right ha0 hcount'
    rw [← Set.ncard_eq_toFinset_card _ hS₂fin]
    exact hncard
  -- ── orthonormality of the source families
  have hON1 : ∀ φ ∈ S₂, ClassFunction.inner φ φ = 1 := fun φ hφ => hselfone (hS₂cut hφ).2.1
  have hON2 : ∀ φ ∈ S₂, ∀ ξ ∈ S₂, φ ≠ ξ → ClassFunction.inner φ ξ = 0 :=
    fun φ hφ ξ hξ hne =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF (hS₂sub hξ)) hne
  -- ── `𝒮₃` is conjugation-closed; cross-orthogonality of the coherent images
  have hS₃sub : sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂
      ⊆ sOf data (chief.H0 ⊔ cprimeSub data chief) := Set.sdiff_subset
  have hS₃conj : ∀ x ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      x.conj ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂ := by
    intro x hx
    refine ⟨sOf_closedUnderConjugate data _ hx.1, ?_⟩
    intro hcmem
    apply hx.2
    have h := hS₂conj hcmem
    rwa [ClassFunction.conj_conj] at h
  have hcross : ∀ φ ∈ S₂, ∀ lam ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) \ S₂,
      ClassFunction.inner (c₁.extension φ) (c₃.extension lam) = 0 := by
    intro φ hφ lam hlam
    exact sOf_coherent_extension_cross_orthogonal hG hM data h46 hKeq htau hKsupp hVsub
      hS₂sub hS₃sub c₁ c₃ hφ (hS₂conj hφ) hlam (hS₃conj lam hlam)
      (fun h => hlam.2 (h ▸ hφ)) (fun h => (hS₃conj lam hlam).2 (h ▸ hφ))
  -- ── `β = λ₁ − e·ψ₁`: support, integrality, `τ`-image
  have hβdegℂ : (lam₁ : ↥M → ℂ) 1 = ((e : ℕ) : ℂ) * (ψ₁ : ↥M → ℂ) 1 := by
    rw [hlam₁deg, hψ₁deg, ← hue]
    push_cast
    ring
  have hβsupp : ((lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF hlam₁S₃.1) (hIKF hψ₁sOf) hβdegℂ
  have hβsmul : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) = lam₁ - ((e : ℕ) : ℂ) • ψ₁ := by
    rw [Nat.cast_smul_eq_nsmul]
  have hβZIrr : (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hlam₁S₃.1))
      (nsmul_mem (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf)) e)
  have hτβZ : tau (lam₁ - e • ψ₁) ∈ ZIrr G := htauZ hβsupp hβZIrr
  have hαZIrr : (γ - ψ₁ : ClassFunction ↥M ℂ) ∈ ZIrr ↥M :=
    Submodule.sub_mem _ hγZIrr
      (OddOrder.Peterfalvi.S08.inducedKernelFamily_mem_ZIrr (hIKF hψ₁sOf))
  have hταZ : tau (γ - ψ₁) ∈ ZIrr G := htauZ hαsupp hαZIrr
  -- ── supported differences and their `τ₁`/`τ₃` images
  have hψdiffsupp : ∀ φ ∈ S₂, ((φ - ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    intro φ hφ
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support hKsupp
      (hIKF (hS₂sub hφ)) (hIKF hψ₁sOf) (d := 1)
      (by rw [Nat.cast_one, one_mul, hS2deg φ hφ, hψ₁deg])
    rwa [one_smul] at h
  have hτ₁diff : ∀ φ ∈ S₂, tau (φ - ψ₁) = c₁.extension φ - c₁.extension ψ₁ := by
    intro φ hφ
    rw [← map_sub]
    exact (c₁.extends_on_supported (φ - ψ₁)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hφ) (Submodule.subset_span hψ₁S₂),
        hψdiffsupp φ hφ⟩).symm
  have hDsupp : ((lam₁ - lam₁.conj : ClassFunction ↥M ℂ)).support ⊆ A0 := by
    rw [show (lam₁ - lam₁.conj : ClassFunction ↥M ℂ) = -(lam₁.conj - lam₁) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support hKsupp (hIKF hlam₁S₃.1)
  have hτD : tau (lam₁ - lam₁.conj) = c₃.extension lam₁ - c₃.extension lam₁.conj := by
    rw [← map_sub]
    exact (c₃.extends_on_supported (lam₁ - lam₁.conj)
      ⟨Submodule.sub_mem _ (Submodule.subset_span hlam₁S₃)
        (Submodule.subset_span hlam₁cS₃), hDsupp⟩).symm
  -- ── scalar values at the source
  have hll1 : ClassFunction.inner lam₁ lam₁ = 1 := hselfone hlam₁irr
  have hlclc : ClassFunction.inner lam₁.conj lam₁.conj = 1 := hselfone hlam₁irr.conj
  have hllc : ClassFunction.inner lam₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hlam₁S₃.1) (hIKF hlam₁cS₃.1) hlam₁ne
  have hψψ : ClassFunction.inner ψ₁ ψ₁ = 1 := hON1 ψ₁ hψ₁S₂
  have hψl : ClassFunction.inner ψ₁ lam₁ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hψ₁S₂))
  have hψlc : ClassFunction.inner ψ₁ lam₁.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψ₁sOf) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hψ₁S₂))
  have hlψ : ClassFunction.inner lam₁ ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁, hψl, star_zero]
  have hlcψ : ClassFunction.inner lam₁.conj ψ₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm ψ₁ lam₁.conj, hψlc, star_zero]
  have hlcl : ClassFunction.inner lam₁.conj lam₁ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm lam₁ lam₁.conj, hllc, star_zero]
  -- ── the budget inputs
  have hS4fin : (caseASFour data chief S₂).Finite := hSfin.subset (fun ξ hξ => (hS4sub hξ).1)
  have hτβnorm : ClassFunction.inner (tau (lam₁ - e • ψ₁)) (tau (lam₁ - e • ψ₁))
      = ((e : ℕ) : ℂ) ^ 2 + 1 := by
    rw [htauiso hβsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hll1, hlψ, hψl, hψψ, star_natCast, mul_zero, mul_one, sub_zero, zero_sub]
    ring
  have hτβconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (tau (lam₁ - e • ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (tau (lam₁ - e • ψ₁)) (c₁.extension ψ₁) + ((e : ℕ) : ℂ) := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hβφ : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁)
        = ((e : ℕ) : ℂ) := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hlψ, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm),
        show ClassFunction.inner lam₁ φ = 0 from by
          rw [OddOrder.RepresentationTheory.inner_conj_symm φ lam₁,
            OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
              (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)),
            star_zero],
        mul_zero, mul_one, sub_zero, zero_sub, sub_neg_eq_add, zero_add]
    have hiso := htauiso hβsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hβφ] at hiso
    linear_combination hiso
  have hτβD : ClassFunction.inner (tau (lam₁ - e • ψ₁)) (c₃.extension lam₁)
      - ClassFunction.inner (tau (lam₁ - e • ψ₁)) (c₃.extension lam₁.conj) = 1 := by
    have hβD : ClassFunction.inner (lam₁ - e • ψ₁ : ClassFunction ↥M ℂ)
        (lam₁ - lam₁.conj) = 1 := by
      rw [hβsmul]
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_smul_left, hll1, hllc, hψl, hψlc, mul_zero, sub_zero]
    have hiso := htauiso hβsupp hDsupp
    rw [hτD, ClassFunction.inner_sub_right, hβD] at hiso
    exact hiso
  have hτατβ : ClassFunction.inner (tau (γ - ψ₁)) (tau (lam₁ - e • ψ₁)) = ((e : ℕ) : ℂ) := by
    rw [htauiso hαsupp hβsupp, hβsmul]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, hγorth lam₁ hlam₁S₃.1,
      hγorth ψ₁ hψ₁sOf, hψl, hψψ, star_natCast, mul_zero, mul_one, zero_sub, sub_zero,
      sub_neg_eq_add, zero_add]
  have hταconst : ∀ φ ∈ hS₂fin.toFinset, φ ≠ ψ₁ →
      ClassFunction.inner (tau (γ - ψ₁)) (c₁.extension φ)
        = ClassFunction.inner (tau (γ - ψ₁)) (c₁.extension ψ₁) + 1 := by
    intro φ hφF hφne
    have hφ := hS₂fin.mem_toFinset.mp hφF
    have hαφ : ClassFunction.inner (γ - ψ₁ : ClassFunction ↥M ℂ) (φ - ψ₁) = 1 := by
      simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        hγorth φ (hS₂sub hφ), hγorth ψ₁ hψ₁sOf, hψψ,
        hON2 ψ₁ hψ₁S₂ φ hφ (fun h => hφne h.symm), zero_sub, sub_neg_eq_add,
        zero_add, sub_self]
    have hiso := htauiso hαsupp (hψdiffsupp φ hφ)
    rw [hτ₁diff φ hφ, ClassFunction.inner_sub_right, hαφ] at hiso
    linear_combination hiso
  -- ── run the projection budget
  obtain ⟨Γ0, hΓZ, hΓ1, hθ₁Γ, hΓD, hTBeq⟩ :=
    OddOrder.Peterfalvi.S07.exists_bridge_target_of_budget (Γ' := G)
      (SF := hS₂fin.toFinset) (S4F := hS4fin.toFinset)
      (fun φ => c₁.extension φ) (fun ξ => c₃.extension ξ)
      (TB := tau (lam₁ - e • ψ₁)) (TA := tau (γ - ψ₁))
      (ψ₁ := ψ₁) (l₁ := lam₁) (l₂ := lam₁.conj) (e := e)
      (hS₂fin.mem_toFinset.mpr hψ₁S₂)
      (hS4fin.mem_toFinset.mpr ⟨hlam₁sOfC, hlam₁irr, hlam₁nS₂⟩)
      (hS4fin.mem_toFinset.mpr hlam₁c_S₄)
      he2 hcardS₂
      (by
        intro φ hφF ξ hξF
        have hφ := hS₂fin.mem_toFinset.mp hφF
        have hξ := hS₂fin.mem_toFinset.mp hξF
        rw [c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ) (Submodule.subset_span hξ)]
        by_cases h : φ = ξ
        · subst h; rw [if_pos rfl]; exact hON1 φ hφ
        · rw [if_neg h]; exact hON2 φ hφ ξ hξ h)
      (by
        intro ξ hξF ξ' hξ'F
        have hξ := hS4sub (hS4fin.mem_toFinset.mp hξF)
        have hξ' := hS4sub (hS4fin.mem_toFinset.mp hξ'F)
        rw [c₃.extension_inner_eq ξ ξ' (Submodule.subset_span hξ) (Submodule.subset_span hξ')]
        by_cases h : ξ = ξ'
        · subst h
          rw [if_pos rfl]
          exact hselfone (hS4fin.mem_toFinset.mp hξF).2.1
        · rw [if_neg h]
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
            (hIKF hξ.1) (hIKF hξ'.1) h)
      (fun φ hφF ξ hξF => hcross φ (hS₂fin.mem_toFinset.mp hφF)
        ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      (fun ξ hξF => c₃.extension_mem_ZIrr ξ
        (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF))))
      (fun φ hφF => c₁.extension_mem_ZIrr φ
        (Submodule.subset_span (hS₂fin.mem_toFinset.mp hφF)))
      hτβZ hτβnorm hτβconst hτβD hτατβ
      (fun ξ hξF => hc ξ (hS4sub (hS4fin.mem_toFinset.mp hξF)))
      hταconst
      (ClassFunction.inner_mem_ZIrr_int hταZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₁.extension_mem_ZIrr ψ₁ (Submodule.subset_span hψ₁S₂)))
      (fun ξ hξF => ClassFunction.inner_mem_ZIrr_int hτβZ
        (c₃.extension_mem_ZIrr ξ
          (Submodule.subset_span (hS4sub (hS4fin.mem_toFinset.mp hξF)))))
  -- ── the pair targets `X = Γ0`, `Xc = Γ0 − (λ₁ − λ̄₁)^τ`
  have hΓτD : ClassFunction.inner Γ0 (tau (lam₁ - lam₁.conj)) = 1 := by
    rw [hτD, ClassFunction.inner_sub_right, hΓD]
  have hτDΓ : ClassFunction.inner (tau (lam₁ - lam₁.conj)) Γ0 = 1 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm Γ0 (tau (lam₁ - lam₁.conj)), hΓτD, star_one]
  have hτDτD : ClassFunction.inner (tau (lam₁ - lam₁.conj)) (tau (lam₁ - lam₁.conj)) = 2 := by
    rw [htauiso hDsupp hDsupp]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hll1, hllc, hlcl, hlclc, sub_zero, zero_sub, sub_neg_eq_add]
    norm_num
  have hτDZ : tau (lam₁ - lam₁.conj) ∈ ZIrr G := by
    rw [hτD]
    exact Submodule.sub_mem _
      (c₃.extension_mem_ZIrr lam₁ (Submodule.subset_span hlam₁S₃))
      (c₃.extension_mem_ZIrr lam₁.conj (Submodule.subset_span hlam₁cS₃))
  -- ── adjoin the pair `{λ₁, λ̄₁}` coherently to `𝒮₂` (the (5.6.3) union-pair extension)
  have hunion : OddOrder.Peterfalvi.S07.IsCoherent tau (S₂ ∪ {lam₁, lam₁.conj}) A0 := by
    refine OddOrder.Peterfalvi.S07.isCoherent_union_pair_of_bridge (E := ((e : ℕ) : ℤ))
      hS₂fin hON1 hON2
      (fun φ hφ ξ hξ => c₁.extension_inner_eq φ ξ (Submodule.subset_span hφ)
        (Submodule.subset_span hξ))
      (fun φ hφ => c₁.extends_on_supported φ hφ)
      (fun φ hφ => c₁.extension_mem_ZIrr φ (Submodule.subset_span hφ))
      hlam₁ne hll1 hlclc hllc
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁S₃.1) (fun h => hlam₁nS₂ (h ▸ hφ)))
      (fun φ hφ => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
        (hIKF (hS₂sub hφ)) (hIKF hlam₁cS₃.1) (fun h => hlam₁cS₃.2 (h ▸ hφ)))
      hΓ1 ?_ ?_ hΓZ
      (Submodule.sub_mem _ hΓZ hτDZ)
      (fun φ hφ => hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ)) ?_ ?_ hDsupp hψ₁S₂ ?_ ?_
    · -- `‖Xc‖² = 1`
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hΓ1, hΓτD, hτDΓ, hτDτD]
      norm_num
    · -- `⟨X, Xc⟩ = 0`
      rw [ClassFunction.inner_sub_right, hΓ1, hΓτD]
      norm_num
    · -- `τ₁𝒮₂ ⊥ Xc`
      intro φ hφ
      rw [ClassFunction.inner_sub_right, hθ₁Γ φ (hS₂fin.mem_toFinset.mpr hφ), hτD,
        ClassFunction.inner_sub_right, hcross φ hφ lam₁ hlam₁S₃, hcross φ hφ lam₁.conj hlam₁cS₃]
      norm_num
    · -- `(λ₁ − λ̄₁)^τ = X − Xc`
      exact (sub_sub_cancel Γ0 (tau (lam₁ - lam₁.conj))).symm
    · -- the bridge `(λ₁ − e·ψ₁)^τ = X − e·τ₁ψ₁` (`ℤ`-scalar form)
      show tau (lam₁ - ((e : ℕ) : ℤ) • ψ₁) = Γ0 - ((e : ℕ) : ℤ) • c₁.extension ψ₁
      simp only [natCast_zsmul]
      rw [← Nat.cast_smul_eq_nsmul ℂ e (c₁.extension ψ₁)]
      exact hTBeq
    · -- the bridge support (`ℤ`-scalar form)
      show ((lam₁ - ((e : ℕ) : ℤ) • ψ₁ : ClassFunction ↥M ℂ)).support ⊆ A0
      simp only [natCast_zsmul]
      exact hβsupp
  exact hpairs lam₁ hlam₁S₃ ⟨hunion⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.4)–(9.11.8), discharged at §9 level**: the case (9.7.a) norm bound
`|𝒮₄| ≤ ‖α‖²`, with the (9.11.7)–(9.11.8) residual supplied by `caseA_sevenEightRefutation`. -/
theorem caseA_normBound [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G)) :
    CaseANormBound caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) :=
  caseA_normBound_of_sevenEightRefutation hG hM caseA h46 hKeq htau hKsupp hVsub
    (caseA_sevenEightRefutation hG hM caseA h46 hKeq htau hKsupp hVsub)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11.2)–(9.11.8), discharged at §9 level**: the equality-configuration
refutation `CaseAEqualityRefutation`, i.e. the `hrefuteEq` input of `sOf_nineEleven_coherent`.

This closes issue 9083 Phases B–E at §9 level: the `𝒮₂ = 𝒮₁` extraction (`caseA_sTwoExtraction`)
and the norm bound (`caseA_normBound`) feed the arithmetic spine
`nineElevenCaseA_equality_refutation` through
`caseA_equalityRefutation_of_sTwoExtraction_normBound`. -/
theorem caseA_equalityRefutation [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G)) :
    CaseAEqualityRefutation caseA
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M) :=
  caseA_equalityRefutation_of_sTwoExtraction_normBound hG caseA _ _
    (caseA_sTwoExtraction hG hM caseA _ _)
    (caseA_normBound hG hM caseA h46 hKeq htau hKsupp hVsub)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11) at the `A₀` level, with the case (9.7.a) residual discharged.**

`nineEleven_coherent` is this composed with the descent `sOf_coherent_restrict` to `A(M)`.  The
`A₀` form is what the §11/§13 packaging states (`S13.coherent_sOf_H0Cprime`, whose `hyp.base.A0`
and `hyp.base.tau` are definitionally this support and this map), so it is the shape in which the
type III/IV packaged version becomes a corollary of the §9 argument (issue 1045, 着手順 3). -/
theorem nineEleven_coherent_A0 [Finite G] {M : Subgroup G} {A : Set G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hM : M ∈ maximalSubgroups G)
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 A M)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (hKeq : h46.K = huSub data)
    (hHle : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ h46.subH)
    (htau : h46.tau = h46.dade0.fullDadeIsometryData)
    (hAnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A)
    (hKsupp : ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 →
      x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)
    (hVsub : ∀ v ∈ (OddOrder.Peterfalvi.S06.ticVdiff h46).V, v ∉ (derivedInG M : Set G))
    (dd : OddOrder.Peterfalvi.S10.DadeSupportHypothesisData M A)
    (hdd : dd.dade = h46.dade0.restrict Set.subset_union_left hAnorm) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau)
      (sOf data (chief.H0 ⊔ chars.Cprime))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn M h46.tic.V) M)) :=
  sOf_nineEleven_coherent_A0 hG hM chars h46 hKeq hHle htau hAnorm hKsupp hVsub dd hdd
    (fun caseA => caseA_irrCut_two_le_ncard hG hM caseA)
    (fun caseA => caseA_equalityRefutation hG hM caseA h46 hKeq htau hKsupp hVsub)

end OddOrder.Peterfalvi.S11



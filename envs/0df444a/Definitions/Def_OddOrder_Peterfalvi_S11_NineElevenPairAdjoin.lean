-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenPairAdjoin
-- name    : OddOrder_Peterfalvi_S11_NineElevenPairAdjoin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:04:30.525207+00:00
-- url     : https://prove2.me/theorems/d27ca15b-08e2-4790-bb63-4dfd6b2817ff
-- title:
--   Peterfalvi (9.11.7)–(9.11.8): coherent-pair adjunction and the case (a) endgame
-- statement:
--   Formalizes the coherent-pair adjunction and the case (a) endgame (Peterfalvi, *Character Theory for the Odd Order Theorem*, §9, p. 57, (9.11.7)–(9.11.8)).
--
--   Main declarations: `SOf_coherent_extension_cross_orthogonal` (Cross-orthogonality of coherent images across two strata).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenPairAdjoin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenPairAdjoin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_UnionPairBridge
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenAlphaBound

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S11

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

section CoherentOrtho

variable [Finite G]

/-- **Peterfalvi (5.5) for a coherent subfamily of `𝒮(H₀C′)`** (Coq `mem_coherent_sum_subseq`,
`PFsection5.v:957`): a coherent extension of `T ⊆ 𝒮(H₀C′)` evaluates a member `ψ` (whose
conjugate is also in `T`) as a partial sum `∑_{α ∈ E} α` over the dispatched `R(ψ)`-family.
This is `CharacterPsiDecomposition.ofProjection` at `ψ = 0` (the auxiliary isometry is the
coherent extension itself, its lattice-relative isometry restricted from `ℤ[T]`, the
agreement on `ψ − ψ̄` from `extends_on_supported`), closed by `eq_sum_of_psi_eq_zero`. -/
theorem coherent_extension_eq_sum_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {T : Set (ClassFunction ↥M ℂ)}
    (hTsub : T ⊆ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime)
    (c' : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T hyp.base.A0)
    {ψ : ClassFunction ↥M ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (sOf_H0Cprime_memberRFamily hG hyp (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  have := hyp.base.finiteG
  classical
  have hψsOf := hTsub hψT
  have hψcsOf := hTsub hψcT
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0Cprime hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : ψ ≠ ψ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF hψsOf) h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hψsOf) (hIKF hψcsOf) hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (ψ - ψ.conj : ClassFunction ↥M ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hψsOf)
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥M ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (sOf_H0Cprime_memberRFamily hG hyp hψsOf) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

/-- **Peterfalvi (5.5) for a coherent subfamily of any stratum `S(N)`** (stratum-generic
`coherent_extension_eq_sum_memberRFamily`, issue 1023): a coherent extension of `T ⊆ S(N)`
evaluates a member `ψ` (whose conjugate is also in `T`) as a partial sum over the dispatched
`SOf_memberRFamily`. -/
theorem SOf_coherent_extension_eq_sum_memberRFamily
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N : Subgroup G} {T : Set (ClassFunction ↥M ℂ)} (hTsub : T ⊆ hyp.SOf N)
    (c' : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T hyp.base.A0)
    {ψ : ClassFunction ↥M ℂ} (hψT : ψ ∈ T) (hψcT : ψ.conj ∈ T) :
    ∃ E ⊆ (SOf_memberRFamily hG hyp (hTsub hψT)).imageSet,
      c'.extension ψ = ∑ α ∈ E, α := by
  have := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf N →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hx)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hne : ψ ≠ ψ.conj := fun h =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hModd _
      (hIKF (hTsub hψT)) h.symm
  have hχχbar : ClassFunction.inner ψ ψ.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hTsub hψT)) (hIKF (hTsub hψcT)) hne
  have hdiffsupp : ((ψ - ψ.conj : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    rw [show (ψ - ψ.conj : ClassFunction ↥M ℂ) = -(ψ.conj - ψ) from by abel,
      ClassFunction.support_neg]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF (hTsub hψT))
  have hle : OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
      ({ψ - ψ.conj, ψ - 0} : Set (ClassFunction ↥M ℂ))
      ≤ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) T :=
    Submodule.span_le.mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT)
      · exact Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.zero_mem _))
  obtain ⟨-, hτ1ψ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
        (SOf_memberRFamily hG hyp (hTsub hψT)) c'.extension
        (fun φ ζ hφ hζ => c'.extension_inner_eq φ ζ (hle hφ) (hle hζ))
        (c'.extends_on_supported (ψ - ψ.conj)
          ⟨Submodule.sub_mem _ (Submodule.subset_span hψT) (Submodule.subset_span hψcT),
            hdiffsupp⟩)
        (by rw [sub_zero]; exact c'.extension_mem_ZIrr ψ (Submodule.subset_span hψT))
        (by rw [ClassFunction.inner_zero_right])
        (by rw [ClassFunction.inner_zero_right])
        hχχbar)
  exact ⟨E, hEsub, hτ1ψ.trans hXsum⟩

set_option maxHeartbeats 1600000 in
-- the two (5.5) projections and the (5.2.e) dispatch thread the
-- `hyp.base.tau = dadeIntegralCharacterMap` defeq (as in `SOf_memberRFamily_orthogonal`)
/-- **Cross-orthogonality of coherent images across two strata** (the Coq `coherent_ortho`,
`PFsection5.v:986`, at two kernel-filter strata — issue 1023, the `hmixed` core of (11.8.6)):
for coherent subfamilies `T₁ ⊆ S(N₁)`, `T₂ ⊆ S(N₂)` and members `ψ ∈ T₁`, `λ ∈ T₂` with
`ψ ∉ {λ, λ̄}`, the coherent images are orthogonal: both are partial `R`-family sums by (5.5),
and the `R`-families are cross-orthogonal by (5.2.e). -/
theorem SOf_coherent_extension_cross_orthogonal
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    {N₁ N₂ : Subgroup G} {T₁ T₂ : Set (ClassFunction ↥M ℂ)}
    (hT₁sub : T₁ ⊆ hyp.SOf N₁) (hT₂sub : T₂ ⊆ hyp.SOf N₂)
    (c₁ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₁ hyp.base.A0)
    (c₂ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau T₂ hyp.base.A0)
    {ψ lam : ClassFunction ↥M ℂ}
    (hψT : ψ ∈ T₁) (hψcT : ψ.conj ∈ T₁) (hlamT : lam ∈ T₂) (hlamcT : lam.conj ∈ T₂)
    (hne1 : ψ ≠ lam) (hne2 : ψ ≠ lam.conj) :
    ClassFunction.inner (c₁.extension ψ) (c₂.extension lam) = 0 := by
  have := hyp.base.finiteG
  classical
  have hIKF : ∀ ⦃Nz : Subgroup G⦄ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf Nz →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun Nz x hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hx)
  have h1 : ClassFunction.inner ψ lam = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamT)) hne1
  have h2 : ClassFunction.inner ψ lam.conj = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF (hT₁sub hψT)) (hIKF (hT₂sub hlamcT)) hne2
  obtain ⟨E₁, hE₁sub, hE₁⟩ :=
    SOf_coherent_extension_eq_sum_memberRFamily hG hyp hT₁sub c₁ hψT hψcT
  obtain ⟨E₂, hE₂sub, hE₂⟩ :=
    SOf_coherent_extension_eq_sum_memberRFamily hG hyp hT₂sub c₂ hlamT hlamcT
  have horth := SOf_memberRFamily_orthogonal hG hyp
    (hT₁sub hψT) (hT₂sub hlamT) h1 h2
  rw [hE₁, hE₂, OddOrder.RepresentationTheory.inner_sum_left]
  refine Finset.sum_eq_zero fun α hα => ?_
  rw [OddOrder.RepresentationTheory.inner_sum_right]
  exact Finset.sum_eq_zero fun β hβ => horth α (hE₁sub hα) β (hE₂sub hβ)

end CoherentOrtho

end OddOrder.Peterfalvi.S13



-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsolateRepresentationAtCharacter
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:51.785011+00:00
-- url     : https://prove2.me/theorems/11debc9e-a9e9-5a29-a7b1-7ec4b819c9a0
-- title:
--   Isolate Representation At Character
-- statement:
--   Definitions and structural lemmas for Isolate Representation At Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsolateRepresentationAtCharacter.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HkMemFixed
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FinsumOutTranslate
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmulEqOnFinset
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IrreducibleHomFixedVectorsStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_IrreducibleSmoothAdmissibleGL
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeFix_hk_mem_fixed
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_finite_out_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_eq_sum
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_hk_hconv
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeMul_isHk_hconv
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
noncomputable section
namespace GlobalTheory.CompanionTheory.Isolate
open GlobalTheory.CompanionTheory.HeckeMul
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
theorem exists_finset {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (he : IsHk K e) :
    ∃ A : Finset (GL ι F ⧸ K), ∀ q : GL ι F ⧸ K, e q.out ≠ 0 → q ∈ A :=
  ⟨(finite_out_mem K he.1 he.2.2.1).toFinset, fun q hq => by
    simpa using subset_tsupport _ (Function.mem_support.2 hq)⟩
section Ops
variable {K : Subgroup (GL ι F)} {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL ι F) V)
theorem hk_add_right {e : GL ι F → ℂ} (he : IsHk K e) (v w : V) :
    hk ρ K e (v + w) = hk ρ K e v + hk ρ K e w := by
  obtain ⟨A, hA⟩ := exists_finset he
  simp only [hk_eq_sum ρ K e _ A hA, map_add, smul_add, Finset.sum_add_distrib]
theorem hk_smul_right {e : GL ι F → ℂ} (he : IsHk K e) (c : ℂ) (v : V) :
    hk ρ K e (c • v) = c • hk ρ K e v := by
  obtain ⟨A, hA⟩ := exists_finset he
  simp only [hk_eq_sum ρ K e _ A hA, map_smul, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm _ _ _
theorem hk_add_left {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) (v : V) :
    hk ρ K (e₁ + e₂) v = hk ρ K e₁ v + hk ρ K e₂ v := by
  classical
  obtain ⟨A₁, hA₁⟩ := exists_finset h₁
  obtain ⟨A₂, hA₂⟩ := exists_finset h₂
  have m₁ : ∀ q : GL ι F ⧸ K, e₁ q.out ≠ 0 → q ∈ A₁ ∪ A₂ :=
    fun q hq => Finset.mem_union_left _ (hA₁ q hq)
  have m₂ : ∀ q : GL ι F ⧸ K, e₂ q.out ≠ 0 → q ∈ A₁ ∪ A₂ :=
    fun q hq => Finset.mem_union_right _ (hA₂ q hq)
  have m : ∀ q : GL ι F ⧸ K, (e₁ + e₂) q.out ≠ 0 → q ∈ A₁ ∪ A₂ := by
    intro q hq
    by_cases h : e₁ q.out = 0
    · refine m₂ q fun h' => hq ?_
      simp [h, h']
    · exact m₁ q h
  rw [hk_eq_sum ρ K _ v _ m, hk_eq_sum ρ K _ v _ m₁, hk_eq_sum ρ K _ v _ m₂, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp [add_smul]
theorem hk_smul_left {e : GL ι F → ℂ} (he : IsHk K e) (c : ℂ) (v : V) :
    hk ρ K (c • e) v = c • hk ρ K e v := by
  obtain ⟨A, hA⟩ := exists_finset he
  have m : ∀ q : GL ι F ⧸ K, (c • e) q.out ≠ 0 → q ∈ A := by
    intro q hq
    refine hA q fun h => hq ?_
    simp [h]
  rw [hk_eq_sum ρ K _ v _ m, hk_eq_sum ρ K _ v _ hA, Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => by simp [mul_smul]
end Ops
theorem isHk_add {K : Subgroup (GL ι F)} {e₁ e₂ : GL ι F → ℂ} (h₁ : IsHk K e₁) (h₂ : IsHk K e₂) :
    IsHk K (e₁ + e₂) :=
  ⟨h₁.1, h₁.2.1, HasCompactSupport.add h₁.2.2.1 h₂.2.2.1, fun k₁ hk₁ k₂ hk₂ g => by
    simp [h₁.2.2.2 k₁ hk₁ k₂ hk₂ g, h₂.2.2.2 k₁ hk₁ k₂ hk₂ g]⟩
theorem isHk_smul {K : Subgroup (GL ι F)} {e : GL ι F → ℂ} (c : ℂ) (h : IsHk K e) :
    IsHk K (c • e) :=
  ⟨h.1, h.2.1, HasCompactSupport.of_support_subset_isCompact h.2.2.1 (by
      intro x hx
      refine subset_tsupport _ fun h0 => hx ?_
      simp [h0]), fun k₁ hk₁ k₂ hk₂ g => by
    simp [h.2.2.2 k₁ hk₁ k₂ hk₂ g]⟩
open Classical in

def unitFn (K : Subgroup (GL ι F)) (g : GL ι F) : ℂ := if g ∈ K then 1 else 0
theorem isHk_unitFn {K : Subgroup (GL ι F)} (hKo : IsOpen (K : Set (GL ι F)))
    (hKc : IsCompact (K : Set (GL ι F))) : IsHk K (unitFn K) := by
  refine ⟨hKo, hKc, HasCompactSupport.of_support_subset_isCompact hKc ?_, ?_⟩
  · intro x hx
    by_contra h
    exact hx (by simpa [unitFn] using h)
  · intro k₁ hk₁ k₂ hk₂ g
    have : k₁ * g * k₂ ∈ K ↔ g ∈ K := by
      rw [Subgroup.mul_mem_cancel_right K hk₂, Subgroup.mul_mem_cancel_left K hk₁]
    unfold unitFn
    by_cases h : g ∈ K
    · rw [if_pos h, if_pos (this.2 h)]
    · rw [if_neg h, if_neg fun h' => h (this.1 h')]
theorem hk_unitFn {K : Subgroup (GL ι F)} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL ι F) V) {v : V} (hv : v ∈ fixed ρ K) : hk ρ K (unitFn K) v = v := by
  classical
  have hvk : ∀ k ∈ K, ρ k v = v := fun k hk' => by
    have := hv ⟨k, hk'⟩
    simpa using this
  have m : ∀ q : GL ι F ⧸ K, unitFn K q.out ≠ 0 → q ∈ ({(QuotientGroup.mk 1 : GL ι F ⧸ K)} : Finset _) := by
    intro q hq
    have h1 : q.out ∈ K := by
      by_contra h
      exact hq (by simp [unitFn, h])
    rw [Finset.mem_singleton, ← QuotientGroup.out_eq' q]
    exact (QuotientGroup.eq.2 (by simpa using h1))
  rw [hk_eq_sum ρ K _ v _ m, Finset.sum_singleton]
  have h1 : (QuotientGroup.mk 1 : GL ι F ⧸ K).out ∈ K := by
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk 1 : GL ι F ⧸ K))
    simpa using this
  simp [unitFn, h1, hvk _ h1]
section Alg
variable {K : Subgroup (GL ι F)} {I : Type} {Y : I → Type} [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)]
  (ρ : ∀ i, Representation ℂ (GL ι F) (Y i))
def hkFix {X : Type} [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (GL ι F) X)
    {e : GL ι F → ℂ} (he : IsHk K e) : Module.End ℂ (fixed σ K) where
  toFun v := ⟨hk σ K e v, (GlobalTheory.CompanionTheory.HeckeFix.hk_mem_fixed F ι K e he X σ v v.2).1⟩
  map_add' v w := Subtype.ext (hk_add_right σ he v w)
  map_smul' c v := Subtype.ext (hk_smul_right σ he c v)
variable (K) in

def heckeAlg (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    Subalgebra ℂ (∀ i, Module.End ℂ (fixed (ρ i) K)) where
  carrier := {T | ∃ e, IsHk K e ∧ ∀ i (x : fixed (ρ i) K), ((T i x : fixed (ρ i) K) : Y i) = hk (ρ i) K e x}
  mul_mem' := by
    rintro a b ⟨e₁, h₁, ha⟩ ⟨e₂, h₂, hb⟩
    refine ⟨hconv K e₁ e₂, isHk_hconv h₁ h₂, fun i x => ?_⟩
    rw [hk_hconv h₁ h₂ (ρ i) x.2, ← hb i x, ← ha i]
    rfl
  add_mem' := by
    rintro a b ⟨e₁, h₁, ha⟩ ⟨e₂, h₂, hb⟩
    refine ⟨e₁ + e₂, isHk_add h₁ h₂, fun i x => ?_⟩
    rw [hk_add_left (ρ i) h₁ h₂, ← ha i, ← hb i]
    rfl
  algebraMap_mem' := by
    intro c
    refine ⟨c • unitFn K, isHk_smul c (isHk_unitFn hKo hKc), fun i x => ?_⟩
    rw [hk_smul_left (ρ i) (isHk_unitFn hKo hKc), hk_unitFn (ρ i) x.2]
    rfl
end Alg
structure BRep (F ι : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Fintype ι] [DecidableEq ι] where
  X : Type
  [g : AddCommGroup X]
  [m : Module ℂ X]
  ρ : Representation ℂ (GL ι F) X
attribute [instance] BRep.g BRep.m
end GlobalTheory.CompanionTheory.Isolate



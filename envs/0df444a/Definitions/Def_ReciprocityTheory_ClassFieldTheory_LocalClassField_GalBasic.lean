-- Prove2me | Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- name    : ReciprocityTheory_ClassFieldTheory_LocalClassField_GalBasic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:19.256805+00:00
-- url     : https://prove2.me/theorems/29fb2be7-fa40-49dc-a787-813c1fbe4652
-- title:
--   Gal Basic
-- statement:
--   Definitions and structural lemmas for Gal Basic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ClassFieldTheory/LocalClassField/GalBasic.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsIntEKMulVbar
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_mem_subG_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
scoped instance isGalois_GB : IsGalois K (PadicAlgCl p) := by
  have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
  infer_instance
scoped instance : CompactSpace (GK p K) := inferInstance
scoped instance : T2Space (GK p K) := inferInstance
scoped instance : TotallyDisconnectedSpace (GK p K) := inferInstance
variable {p K L}
variable (p K L) in
theorem totallySeparatedSpace_GalLK : TotallySeparatedSpace (GalLK p K L) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H a =>
  induction y using QuotientGroup.induction_on with
  | H b =>
  have hab : a⁻¹ * b ∉ subG p K L := fun hh => hxy (QuotientGroup.eq.2 hh)
  rw [mem_subG_iff] at hab
  push Not at hab
  obtain ⟨z, hz, hne⟩ := hab
  have hpre : (QuotientGroup.mk : GK p K → GalLK p K L) ⁻¹' (QuotientGroup.mk '' {g : GK p K | g z = a z}) =
      (fun g : GK p K => a⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K) z : Set (GK p K)) := by
    ext g
    have key : ∀ g : GK p K, (a⁻¹ * g) z = z ↔ g z = a z := fun g => by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    constructor
    · rintro ⟨g', hg', he⟩
      have hn : g'⁻¹ * g ∈ subG p K L := QuotientGroup.eq.1 he
      have h1 : (g'⁻¹ * g) z = z := hn z hz
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
      exact (key g).2 (h1.trans hg')
    · intro hg
      exact ⟨g, (key g).1 hg, rfl⟩
  have hop : IsOpen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    stabilizer_isOpen_of_isIntegral (K := K) z
  have hcl : IsClopen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
  refine ⟨QuotientGroup.mk '' {g : GK p K | g z = a z}, ?_, ⟨a, rfl, rfl⟩, ?_⟩
  · rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isClopen_preimage, hpre]
    exact hcl.preimage (continuous_const.mul continuous_id)
  · rintro ⟨g', hg', he⟩
    have hn : g'⁻¹ * b ∈ subG p K L := QuotientGroup.eq.1 he
    have h1 : (g'⁻¹ * b) z = z := hn z hz
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
    apply hne
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact h1.trans hg'
scoped instance [(subG p K L).Normal] : T2Space (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.t2Space
scoped instance [(subG p K L).Normal] : TotallyDisconnectedSpace (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.totallyDisconnectedSpace _
end ReciprocityTheory.DiscreteGroups.LocalClassField



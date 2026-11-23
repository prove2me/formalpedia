-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:03:43.635904+00:00
-- url     : https://prove2.me/theorems/7c9ec65b-2db2-438e-b417-404daa29f294
-- title:
--   Congruence Finite Index
-- statement:
--   Definitions and structural lemmas for Congruence Finite Index, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CongruenceFiniteIndex.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mul_mulVec (γ δ : GL (Fin r) E) (v : Fin r → E) :
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v =
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
omit [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec (γ : GL (Fin r) E) (v : Fin r → E) :
    (γ : Matrix (Fin r) (Fin r) E) *ᵥ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v)
      = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_one : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ 1 := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab
  exact ⟨fun x y => by simp, fun x => by simp⟩
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_mul {γ δ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) (hδ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ δ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ (γ * δ) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec, _root_.GlobalTheory.CongruenceIndex.mul_mulVec, hγ.1, hδ.1]
  · rw [_root_.GlobalTheory.CongruenceIndex.mul_mulVec]
    exact (hδ.2 x).trans (hγ.2 _)
open NumberField Matrix in
open scoped nonZeroDivisors in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)} in
theorem _root_.GlobalTheory.CongruenceIndex.isUStab_inv {γ : GL (Fin r) E} (hγ : _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ⁻¹ := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab at *
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · have h := hγ.1 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
      (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec, _root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm
  · have h := hγ.2 (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
    rw [_root_.GlobalTheory.CongruenceIndex.mulVec_inv_mulVec] at h
    exact h.symm
def congruenceSubgroup (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E))
    (M : ℕ) : Subgroup (GL (Fin r) E) where
  carrier := {γ | FD.IsUStab Gm Λ γ ∧
    (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)}
  one_mem' := ⟨isUStab_one, fun v _ => ⟨0, Λ.zero_mem, by simp⟩⟩
  mul_mem' := by
    rintro γ δ ⟨hγ, hγ'⟩ ⟨hδ, hδ'⟩
    refine ⟨isUStab_mul hγ hδ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hδ' v hv
    obtain ⟨w', hw', e'⟩ := hγ' _ ((hδ.2 v).1 hv)
    refine ⟨w + w', Λ.add_mem hw hw', ?_⟩
    rw [mul_mulVec, e', e, smul_add, add_assoc]
  inv_mem' := by
    rintro γ ⟨hγ, hγ'⟩
    refine ⟨isUStab_inv hγ, fun v hv => ?_⟩
    obtain ⟨w, hw, e⟩ := hγ' _ (((isUStab_inv hγ).2 v).1 hv)
    rw [mulVec_inv_mulVec] at e
    refine ⟨-w, Λ.neg_mem hw, ?_⟩
    rw [smul_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact e.symm
end GlobalTheory.CongruenceIndex



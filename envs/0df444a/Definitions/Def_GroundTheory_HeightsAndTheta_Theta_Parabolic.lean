-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
-- name    : GroundTheory_HeightsAndTheta_Theta_Parabolic
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:15.987005+00:00
-- url     : https://prove2.me/theorems/096ed770-b50a-4ded-af17-fff31542ac72
-- title:
--   Parabolic
-- statement:
--   Definitions and structural lemmas for Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Theta
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
section Form
variable (K) (H : Matrix ι ι E)
def hermPair (x y : ι → E) : E :=
  (fun i => conj K E (x i)) ⬝ᵥ (H *ᵥ y)
variable {K H}
theorem hermPair_add_right (x y z : ι → E) :
    hermPair K H x (y + z) = hermPair K H x y + hermPair K H x z := by
  simp [hermPair, mulVec_add, dotProduct_add]
theorem hermPair_smul_right (x y : ι → E) (c : E) :
    hermPair K H x (c • y) = c * hermPair K H x y := by
  simp [hermPair, mulVec_smul, dotProduct_smul, smul_eq_mul]
theorem hermPair_zero_right (x : ι → E) : hermPair K H x 0 = 0 := by
  simp [hermPair]
theorem hermPair_smul_left (x y : ι → E) (c : E) :
    hermPair K H (c • x) y = conj K E c * hermPair K H x y := by
  simp only [hermPair, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [show (fun i => conj K E c * conj K E (x i)) = conj K E c • (fun i => conj K E (x i)) from
    rfl, smul_dotProduct, smul_eq_mul]
variable (K H)
def orth (W : Submodule E (ι → E)) : Submodule E (ι → E) where
  carrier := {y | ∀ x ∈ W, hermPair K H x y = 0}
  add_mem' {y z} hy hz x hx := by rw [hermPair_add_right, hy x hx, hz x hx, add_zero]
  zero_mem' x _ := hermPair_zero_right x
  smul_mem' c y hy x hx := by
    change hermPair K H x (c • y) = 0
    rw [hermPair_smul_right, hy x hx, mul_zero]
variable {K H}
variable (K H)
def IsTotallyIsotropic (W : Submodule E (ι → E)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, hermPair K H x y = 0
def IsAnisotropic : Prop :=
  ∀ x : ι → E, hermPair K H x x = 0 → x = 0
def wittIndex : ℕ :=
  sSup {d | ∃ W : Submodule E (ι → E), IsTotallyIsotropic K H W ∧ finrank E W = d}
variable {K H}
theorem isTotallyIsotropic_span_singleton {x : ι → E} (hx : hermPair K H x x = 0) :
    IsTotallyIsotropic K H (E ∙ x) := by
  intro y hy z hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hy
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hz
  rw [hermPair_smul_left, hermPair_smul_right, hx, mul_zero, mul_zero]
end Form
section Flag
variable (K) (H : Matrix ι ι E)
structure IsotropicFlag where

  members : Finset (Submodule E (ι → E))

  isChain : IsChain (· ≤ ·) (members : Set (Submodule E (ι → E)))

  isotropic : ∀ W ∈ members, IsTotallyIsotropic K H W
variable {K H}
namespace IsotropicFlag
def IsProper (𝒲 : IsotropicFlag K H) : Prop := ∃ W ∈ 𝒲.members, W ≠ ⊥
def ofIsotropicVector {x : ι → E} (hx : hermPair K H x x = 0) : IsotropicFlag K H where
  members := {E ∙ x}
  isChain := by
    intro a ha b hb _
    simp only [Finset.coe_singleton, Set.mem_singleton_iff] at ha hb
    subst ha; subst hb
    exact Or.inl le_rfl
  isotropic W hW := by
    rw [Finset.mem_singleton] at hW
    subst hW
    exact isTotallyIsotropic_span_singleton hx
end IsotropicFlag
def fullChain (𝒲 : IsotropicFlag K H) : Finset (Submodule E (ι → E)) :=
  insert ⊥ (insert ⊤ (𝒲.members ∪ 𝒲.members.image (orth K H)))
def below (S : Finset (Submodule E (ι → E))) (B : Submodule E (ι → E)) :
    Submodule E (ι → E) :=
  (S.filter (· < B)).sup id
theorem below_le (S : Finset (Submodule E (ι → E))) (B : Submodule E (ι → E)) :
    below S B ≤ B := by
  apply Finset.sup_le
  intro A hA
  exact (Finset.mem_filter.1 hA).2.le
end Flag
section BaseChange
variable (K) (R : Type*) [CommRing R] [Algebra K R]
def toBase (x : ι → E) : ι → R ⊗[K] E :=
  fun i => Algebra.TensorProduct.includeRight (x i)
def extendScalars (W : Submodule E (ι → E)) : Submodule (R ⊗[K] E) (ι → R ⊗[K] E) :=
  Submodule.span (R ⊗[K] E) (toBase K R '' W)
variable {K R}
theorem extendScalars_mono {W W' : Submodule E (ι → E)} (h : W ≤ W') :
    extendScalars K R W ≤ extendScalars K R W' :=
  Submodule.span_mono (Set.image_mono h)
end BaseChange
section Groups
theorem unitaryMat_mul {H : Matrix ι ι E} {R : Type*} [CommRing R] [Algebra K R]
    (g h : unitaryPoints K E H R) : unitaryMat (g * h) = unitaryMat g * unitaryMat h := rfl
theorem unitaryMat_one {H : Matrix ι ι E} {R : Type*} [CommRing R] [Algebra K R] :
    unitaryMat (1 : unitaryPoints K E H R) = 1 := rfl
variable (H : Matrix ι ι E)
variable (R : Type*) [CommRing R] [Algebra K R]
def parabolic (𝒲 : IsotropicFlag K H) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ W ∈ 𝒲.members, ∀ x ∈ extendScalars K R W,
    unitaryMat g *ᵥ x ∈ extendScalars K R W ∧ unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R W}
  one_mem' W _ x hx := by
    rw [inv_one, unitaryMat_one, one_mulVec]
    exact ⟨hx, hx⟩
  mul_mem' {g h} hg hh W hW x hx := by
    refine ⟨?_, ?_⟩
    · have : unitaryMat (g * h) *ᵥ x = unitaryMat g *ᵥ (unitaryMat h *ᵥ x) := by
        rw [unitaryMat_mul, ← mulVec_mulVec]
      rw [this]
      exact (hg W hW _ (hh W hW x hx).1).1
    · have : unitaryMat (g * h)⁻¹ *ᵥ x = unitaryMat h⁻¹ *ᵥ (unitaryMat g⁻¹ *ᵥ x) := by
        rw [_root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]
      rw [this]
      exact (hh W hW _ (hg W hW x hx).2).2
  inv_mem' {g} hg W hW x hx := by
    simp only [inv_inv]
    exact ⟨(hg W hW x hx).2, (hg W hW x hx).1⟩
def unipotentRadical (𝒲 : IsotropicFlag K H) : Subgroup (unitaryPoints K E H R) where
  carrier := {g | ∀ B ∈ fullChain 𝒲, ∀ x ∈ extendScalars K R B,
    unitaryMat g *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B) ∧
    unitaryMat g⁻¹ *ᵥ x - x ∈ extendScalars K R (below (fullChain 𝒲) B)}
  one_mem' B _ x _ := by
    rw [inv_one, unitaryMat_one, one_mulVec, sub_self]
    exact ⟨Submodule.zero_mem _, Submodule.zero_mem _⟩
  mul_mem' {g h} hg hh B hB x hx := by
    have hbelow := extendScalars_mono (K := K) (R := R) (below_le (fullChain 𝒲) B)
    refine ⟨?_, ?_⟩
    · have hhx : unitaryMat h *ᵥ x ∈ extendScalars K R B := by
        have := hbelow (hh B hB x hx).1
        simpa using Submodule.add_mem _ this hx
      have : unitaryMat (g * h) *ᵥ x - x =
          (unitaryMat g *ᵥ (unitaryMat h *ᵥ x) - unitaryMat h *ᵥ x) +
            (unitaryMat h *ᵥ x - x) := by
        rw [unitaryMat_mul, ← mulVec_mulVec]; abel
      rw [this]
      exact Submodule.add_mem _ (hg B hB _ hhx).1 (hh B hB x hx).1
    · have hgx : unitaryMat g⁻¹ *ᵥ x ∈ extendScalars K R B := by
        have := hbelow (hg B hB x hx).2
        simpa using Submodule.add_mem _ this hx
      have : unitaryMat (g * h)⁻¹ *ᵥ x - x =
          (unitaryMat h⁻¹ *ᵥ (unitaryMat g⁻¹ *ᵥ x) - unitaryMat g⁻¹ *ᵥ x) +
            (unitaryMat g⁻¹ *ᵥ x - x) := by
        rw [_root_.mul_inv_rev, unitaryMat_mul, ← mulVec_mulVec]; abel
      rw [this]
      exact Submodule.add_mem _ (hh B hB _ hgx).2 (hg B hB x hx).2
  inv_mem' {g} hg B hB x hx := by
    simp only [inv_inv]
    exact ⟨(hg B hB x hx).2, (hg B hB x hx).1⟩
end Groups
section Rational
variable [NumberField K] (H : Matrix ι ι E)
def unipotentRational (𝒲 : IsotropicFlag K H) : Subgroup (unipotentRadical H 𝔸[K] 𝒲) :=
  (unitaryDiagonal K H).range.subgroupOf (unipotentRadical H 𝔸[K] 𝒲)
end Rational
end
end GroundTheory.Heights₂.Theta



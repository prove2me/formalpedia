-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
-- name    : Development_AbelianVarietyTheory_Statements_ThetaLevelCharacters_MemThetaLevelCharDimZero
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T17:08:50.122353+00:00
-- url     : https://prove2.me/theorems/0170a933-3527-4363-8e34-a76b400ec890
-- title:
--   Mem Theta Level Char Dim Zero
-- statement:
--   Definitions and structural lemmas for Mem Theta Level Char Dim Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Statements/ThetaLevelCharacters/MemThetaLevelCharDimZero.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply


set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory
def TorusAlgebraic : Prop :=
  ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ), τ.IsSymm → (τ.map Complex.im).PosDef →
    (∀ i, a i = 0 ∨ a i = 1 / 2) → (∀ i, b i = 0 ∨ b i = 1 / 2) →
    ∃ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L g) (th : P.L.Sec), P.g = g ∧
      (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧
      ((∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧
      u.IsFn th (thetaChar τ a b) ∧
      (∀ n : ℕ,
        (∀ s, ∃! θ, θ ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ ∧ u.IsFnPow n s θ) ∧
        ∀ θ ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) n τ, ∃! s, u.IsFnPow n s θ) ∧
      (∀ N : ℕ, 3 ≤ N → Out.VeryAmpleAt P.A P.L N) ∧
      ∀ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ l ∈ u.Λ, F l ∈ u.Λ) →
        ∃ f : P.A ⟶ P.A, IsMonHom f ∧ ∀ z, u.ex (F z) = u.ex z ≫ f
namespace TorusAlg
open ReciprocityTheory.PTheta
section Signs
variable {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ}
end Signs
section Hypotheses
end Hypotheses
section DimZero
open Out Out.Inh
theorem valAt'_id (f : Γ(Sp ℂ, ⊤)) :
    valAt' (𝟙 (Sp ℂ)) ⊤ f = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom f := by
  rw [valAt', dif_pos (show (⊤ : (Sp ℂ).Opens) ≤ 𝟙 (Sp ℂ) ⁻¹ᵁ ⊤ from le_rfl), valAt]
  congr 1
theorem valAt'_id_bijective (U : (Sp ℂ).Opens) (hU : U = ⊤) :
    Function.Bijective (valAt' (𝟙 (Sp ℂ)) U) ∧ valAt' (𝟙 (Sp ℂ)) U 1 = 1 := by
  subst hU
  refine ⟨?_, by rw [valAt'_id, map_one]⟩
  rw [show valAt' (𝟙 (Sp ℂ)) ⊤ = _ from funext valAt'_id]
  exact ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
def zeroUnif : HolUnif (zeroPolAV (Sp ℂ)).A (zeroPolAV (Sp ℂ)).L 0 where
  ex _ := 1
  ex_add _ _ := (_root_.mul_one _).symm
  ex_onto x := ⟨0, toUnit_unique _ _⟩
  Λ := ⊤
  ker _ := by simp
  discrete := inferInstance
  full := by simp
  hol U f := ⟨isOpen_discrete _, differentiableOn_const _⟩
  fr _ _ := 1
  fr_hol _ := differentiableOn_const _
  fr_ne _ _ _ := one_ne_zero
  fr_compat i j z _ := by
    rw [_root_.mul_one]
    exact (valAt'_id_bijective _ (inf_idem _)).2.symm
end DimZero
end TorusAlg
end GlobalTheory



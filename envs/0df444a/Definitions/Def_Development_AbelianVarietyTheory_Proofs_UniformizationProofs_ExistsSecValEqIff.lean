-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T15:14:19.277575+00:00
-- url     : https://prove2.me/theorems/1333c805-62c5-4658-9f15-2315eeb3a1f7
-- title:
--   Exists Sec Val Eq Iff
-- statement:
--   Definitions and structural lemmas for Exists Sec Val Eq Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_smul_def

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
noncomputable section
namespace GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
abbrev toField {U : X.Opens} (h : genericPoint X ∈ U) : Γ(X, U) →+* X.functionField :=
  (X.presheaf.germ U (genericPoint X) h).hom
theorem generic_inf {U V : X.Opens} (hU : genericPoint X ∈ U) (hV : genericPoint X ∈ V) :
    genericPoint X ∈ U ⊓ V := ⟨hU, hV⟩
theorem generic_top : genericPoint X ∈ (⊤ : X.Opens) := trivial
theorem toField_rs {U V : X.Opens} (h : V ≤ U) (hV : genericPoint X ∈ V) (a : Γ(X, U)) :
    toField hV (rs X h a) = toField (h hV) a :=
  X.presheaf.germ_res_apply (homOfLE h) _ hV a
variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)
def secVal {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) : X.functionField :=
  toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀)) (GlobalTheory.LB.coord σ k₀)
theorem secVal_smul {V : X.Opens} (hV : genericPoint X ∈ V) (a : Γ(X, V)) (σ : SecOn M V) :
    secVal h₀ hV (a • σ) = toField hV a * secVal h₀ hV σ :=
  (map_mul (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) (rs X inf_le_left a) _).trans
    (congrArg (· * secVal h₀ hV σ) (toField_rs _ _ _))
theorem secVal_add {V : X.Opens} (hV : genericPoint X ∈ V) (σ τ : SecOn M V) :
    secVal h₀ hV (σ + τ) = secVal h₀ hV σ + secVal h₀ hV τ :=
  map_add (toField (U := V ⊓ M.U k₀) (generic_inf (hV) (h₀))) _ _
def secValLin {K : Type} [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [Algebra K X.functionField]
    (hK : ∀ r, algebraMap K X.functionField r = toField generic_top (cst f ⊤ r)) :
    SecOnR f M ⊤ →ₗ[K] X.functionField where
  toFun σ := secVal h₀ generic_top σ
  map_add' σ τ := secVal_add h₀ generic_top σ τ
  map_smul' r σ := (secVal_smul h₀ generic_top (cst f ⊤ r) σ).trans (by
    rw [RingHom.id_apply, Algebra.smul_def, hK])
end GlobalTheory.FiniteCover



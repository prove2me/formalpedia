-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegZeroLoc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T05:21:56.568418+00:00
-- url     : https://prove2.me/theorems/1830245d-2f16-5ab7-8272-d05aff7763c1
-- title:
--   Statements Deg Zero Loc
-- statement:
--   Definitions and structural lemmas for Statements Deg Zero Loc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsDegZeroLoc.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDivPushForwardLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_contractFracMap_algebraMap_39d4c423cc7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_isMultiHomog_rename_fd9a6cb3fd55

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
section Loc
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
def degZeroLoc (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    Subalgebra F (FractionRing (MRing ι F ⧸ P)) :=
  Algebra.adjoin F {x | ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
    g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧
    x = algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
      algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)}
end Loc
section Fibre
variable {K K' : Type} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
  (j : K ↪ K') {ι' : K' → Type}
def fibrePrimes (P' : Ideal (MRing ι' F)) (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Set (Ideal (MRing ι' F)) :=
  {W' | IsMultiProjPrime W' ∧ P' ≤ W' ∧ contractPrime j W' = W}
theorem map_degZeroLoc_le (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    (degZeroLoc (contractPrime j P') {W}).map (contractFracMap j P') ≤
      degZeroLoc P' (fibrePrimes j P' W) := by
  unfold degZeroLoc
  rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
  rintro _ ⟨x, ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩, rfl⟩
  apply Algebra.subset_adjoin
  refine ⟨Function.extend j b 0, rename (blockIncl j ι') f, rename (blockIncl j ι') g,
    isMultiHomog_rename j ι' hf, isMultiHomog_rename j ι' hg, hgP, ?_, ?_⟩
  · rintro W' ⟨-, -, hc⟩ hgW'
    apply hgW W (Set.mem_singleton W)
    rw [← hc]
    exact hgW'
  · rw [map_div₀, contractFracMap_algebraMap, contractFracMap_algebraMap]
def degZeroLocContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    degZeroLoc (contractPrime j P') {W} →ₐ[F] degZeroLoc P' (fibrePrimes j P' W) :=
  ((contractFracMap j P').comp (degZeroLoc (contractPrime j P') {W}).val).codRestrict _
    (fun x => map_degZeroLoc_le j P' W (Subalgebra.mem_map.mpr ⟨x, x.2, rfl⟩))
instance degZeroLoc.algebraContract (P' : Ideal (MRing ι' F)) [P'.IsPrime]
    (W : Ideal (MRing (fun k => ι' (j k)) F)) :
    Algebra (degZeroLoc (contractPrime j P') {W}) (degZeroLoc P' (fibrePrimes j P' W)) :=
  (degZeroLocContract j P' W).toRingHom.toAlgebra
end Fibre
section Example
end Example
end
end GroundTheory.Heights₂.Heights.FieldNumbers



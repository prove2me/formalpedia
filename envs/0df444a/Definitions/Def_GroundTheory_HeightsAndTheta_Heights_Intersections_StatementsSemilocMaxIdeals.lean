-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:56:38.807898+00:00
-- url     : https://prove2.me/theorems/74d71c0b-b910-4142-bc8d-9328810de589
-- title:
--   Statements Semiloc Max Ideals
-- statement:
--   Definitions and structural lemmas for Statements Semiloc Max Ideals, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsSemilocMaxIdeals.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIncomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
theorem semiLocRing_le_locRing (P : Ideal (MRing ι)) {𝒲 : Set (Ideal (MRing ι))} {W : Ideal (MRing ι)}
    (hW : W ∈ 𝒲) : semiLocRing P 𝒲 ≤ locRing P W := by
  unfold semiLocRing locRing
  refine Subring.closure_mono ?_
  rintro _ ⟨u, w, a, hw, hwW, hu, hwa, rfl⟩
  exact ⟨u, w, a, hw, hwW W hW, hu, hwa, rfl⟩
def semiToLoc (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲) :
    semiLocRing P 𝒲 →+* locRing P W :=
  Subring.inclusion (semiLocRing_le_locRing P hW)
def semiMaxIdeal (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : Ideal (semiLocRing P 𝒲) :=
  (IsLocalRing.maximalIdeal (locRing P W)).comap (semiToLoc P 𝒲 W hW)
instance semiMaxIdeal.isPrime (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    [IsLocalRing (locRing P W)] : (semiMaxIdeal P 𝒲 W hW).IsPrime :=
  Ideal.comap_isPrime _ _
end Objects
def SemilocMaxIdeals.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ) (s : MRing ι) (α : K → ℕ)
    (W : Ideal (MRing ι)),
    IsBlockMap κ v → IsArithVar P' (n + 1) →
    IsArithVar (imageZ v P') (n + 1) → IsMultiHomog s α → s ∉ imageZ v P' → W ∈ divSupp (imageZ v P') s →
    (∀ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W) [IsLocalRing (locRing P' W')],
      (semiMaxIdeal P' (fibreOver v P' W) W' hW').IsMaximal ∧
      letI := (semiToLoc P' (fibreOver v P' W) W' hW').toAlgebra
      IsLocalization.AtPrime (locRing P' W') (semiMaxIdeal P' (fibreOver v P' W) W' hW')) ∧
    (∀ (W₁ W₂ : Ideal (MRing ι')) (h₁ : W₁ ∈ fibreOver v P' W) (h₂ : W₂ ∈ fibreOver v P' W)
      [IsLocalRing (locRing P' W₁)] [IsLocalRing (locRing P' W₂)],
      semiMaxIdeal P' (fibreOver v P' W) W₁ h₁ = semiMaxIdeal P' (fibreOver v P' W) W₂ h₂ → W₁ = W₂) ∧
    ∀ M : Ideal (semiLocRing P' (fibreOver v P' W)), M.IsMaximal →
      ∃ (W' : Ideal (MRing ι')) (hW' : W' ∈ fibreOver v P' W), ∀ [IsLocalRing (locRing P' W')],
        M = semiMaxIdeal P' (fibreOver v P' W) W' hW'
end GroundTheory.Heights₂.Heights.Inter



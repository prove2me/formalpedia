-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreSum
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResFibreSum
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:51.46872+00:00
-- url     : https://prove2.me/theorems/f2cd312e-e8e4-48bb-8b29-0c0f9bd230b7
-- title:
--   Statements Component Res Fibre Sum
-- statement:
--   Definitions and structural lemmas for Statements Component Res Fibre Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsComponentResFibreSum.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsComponentResBadNull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def ComponentResFibreSum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (L : Fin e → HermLine ι) (W : Ideal (MvPolynomial (Σ k, ι k) ℂ))
    (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) →
    W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes → IsGoodProj P Ψ →
    ∀ᵐ y, ∑ᶠ w ∈ fibre P Ψ y,
        sheetDensity P Ψ (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) y w =
      ∑ᶠ x ∈ resProj R Ψ ⁻¹' {y} \ resBad R Ψ,
        ReciprocityTheory.AnForm.M.pushDens R.atlas
          (fun j => R.pot (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.logH (L j))) (resProj R Ψ) x
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



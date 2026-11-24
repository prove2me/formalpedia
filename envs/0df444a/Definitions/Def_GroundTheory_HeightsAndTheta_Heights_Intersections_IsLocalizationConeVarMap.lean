-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_IsLocalizationConeVarMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:03.620485+00:00
-- url     : https://prove2.me/theorems/86f226ec-9745-440d-bb11-9da9d851d8b6
-- title:
--   Is Localization Cone Var Map
-- statement:
--   Definitions and structural lemmas for Is Localization Cone Var Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsLocalizationConeVarMap.lean

import Mathlib
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
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing
noncomputable section
namespace regularityLocalFlat_holds
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (P W : Ideal (MRing ι)) [P.IsPrime] [W.IsPrime]
def coneVarMap (hPW : P ≤ W) (v : ∀ k, ι k) : MvPolynomial K (locRing P W) →ₐ[locRing P W] coneLocRing P W hPW :=
  aeval fun k => algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P (X ⟨k, v k⟩))
def varMono (v : ∀ k, ι k) (e : K →₀ ℕ) : MRing ι :=
  ∏ k, (X ⟨k, v k⟩ : MRing ι) ^ e k
theorem isPrime_map_C {A : Type*} [CommRing A] (σ : Type*) (p : Ideal A) [p.IsPrime] :
    (p.map (C : A →+* MvPolynomial σ A)).IsPrime := by
  rw [← Ideal.mk_ker (I := p), ← MvPolynomial.ker_map]
  exact RingHom.ker_isPrime _
end regularityLocalFlat_holds
end
end GroundTheory.Heights₂.Heights.Inter



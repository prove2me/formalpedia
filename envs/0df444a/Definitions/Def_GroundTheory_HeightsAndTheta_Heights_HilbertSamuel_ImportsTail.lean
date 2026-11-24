-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsTail
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ImportsTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:52.691283+00:00
-- url     : https://prove2.me/theorems/248307dd-df8c-4448-b299-c67279c879a1
-- title:
--   Imports Tail
-- statement:
--   Definitions and structural lemmas for Imports Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ImportsTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_GeneratedModOfSubsingleton
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def H1VanishingDevissage.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (N : K → ℤ),
    IsNoetherianRing S →
    (∀ P : Ideal (MRingOver S ι), IsMultiProjPrime P → V ≤ P → ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c →
      Subsingleton (KH.cechHc ι (KH.quotPart S P) (e + c • N) 1)) →
    ∀ (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
      (𝓜 : (K → ℤ) → Submodule S M),
      Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → V ≤ Module.annihilator (MRingOver S ι) M →
      ∀ e : K → ℤ, ∃ c₁ : ℕ, ∀ c : ℕ, c₁ ≤ c → Subsingleton (KH.cechHc ι 𝓜 (e + c • N) 1)
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



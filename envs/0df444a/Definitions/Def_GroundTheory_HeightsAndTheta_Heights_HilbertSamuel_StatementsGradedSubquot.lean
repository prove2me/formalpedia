-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
-- name    : GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsGradedSubquot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:05:19.766591+00:00
-- url     : https://prove2.me/theorems/181e9e6e-d4f8-42de-8c33-8f7faaa87199
-- title:
--   Statements Graded Subquot
-- statement:
--   Definitions and structural lemmas for Statements Graded Subquot, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/StatementsGradedSubquot.lean

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
def subGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {M : Type*} [AddCommGroup M]
    [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (N : Submodule (MRingOver S ι) M) (c : K → ℤ) : Submodule S N :=
  (𝓜 c).comap (N.subtype.restrictScalars S)
def quotGrading {S : Type*} [CommRing S] {K : Type*} {ι : K → Type*} {N : Type*} [AddCommGroup N]
    [Module (MRingOver S ι) N] [Module S N] [IsScalarTower S (MRingOver S ι) N]
    (𝓝 : (K → ℤ) → Submodule S N) (L : Submodule (MRingOver S ι) N) (c : K → ℤ) : Submodule S (N ⧸ L) :=
  (𝓝 c).map (L.mkQ.restrictScalars S)
def GradedSubquot.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (G H : Set M),
    KH.IsMGraded S ι 𝓜 → (∀ x ∈ G, ∃ c, x ∈ 𝓜 c) → (∀ x ∈ H, ∃ c, x ∈ 𝓜 c) →
    Submodule.span (MRingOver S ι) G ≤ Submodule.span (MRingOver S ι) H →
    KH.IsMGraded S ι (subGrading 𝓜 (Submodule.span (MRingOver S ι) H)) ∧
      KH.IsMGraded S ι (quotGrading (subGrading 𝓜 (Submodule.span (MRingOver S ι) H))
        ((Submodule.span (MRingOver S ι) G).comap (Submodule.span (MRingOver S ι) H).subtype))
abbrev noIdx : Fin 0 → Type := fun _ => Fin 1
end
end GroundTheory.Heights₂.Heights.HilbertSamuel



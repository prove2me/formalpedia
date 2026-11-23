-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:04.637128+00:00
-- url     : https://prove2.me/theorems/8f8c910d-f197-4846-ae5b-b2abc5d9aea7
-- title:
--   Prod Norm Embeddings Eq Abs Norm
-- statement:
--   Definitions and structural lemmas for Prod Norm Embeddings Eq Abs Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.MainNotions.BridgeLemma₂
open NumberField Formalism.HermitianLatticesTheory Module
section Count
variable (K : Type) [Field K] [NumberField K]
def boundedIntegers (B : ℝ) : Set (𝓞 K) := {a | ∀ φ : K →+* ℂ, ‖φ (a : K)‖ ≤ B}
abbrev scaledFreeModule (d : 𝓞 K) : Submodule (𝓞 K) (Fin 2 → 𝓞 K) :=
  Ideal.span {d} • (⊤ : Submodule (𝓞 K) (Fin 2 → 𝓞 K))
end Count
section Geo
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)
def planeMapAlt (x y x' y' : V) : V →ₗ[K] V :=
  ((h x x)⁻¹ • (h x)).smulRight x' + ((h y y)⁻¹ • (h y)).smulRight y'
def pairCoords (x₁ y₁ : V) : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] V :=
  (LinearMap.proj 0 : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).smulRight x₁ +
    (LinearMap.proj 1 : (Fin 2 → 𝓞 K) →ₗ[𝓞 K] 𝓞 K).smulRight y₁
end Geo
section Iso
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)
end Iso
section Final
end Final
end Formalism.MainNotions.BridgeLemma₂
end



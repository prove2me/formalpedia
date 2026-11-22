-- Prove2me | Definitions.Def_Formalism_HermitianLattices_NeighbourConstruct
-- name    : Formalism_HermitianLattices_NeighbourConstruct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:55:26.064807+00:00
-- url     : https://prove2.me/theorems/9ba4b277-fc9c-4bb5-afcf-9f089e53c970
-- title:
--   Neighbour Construct
-- statement:
--   Definitions and structural lemmas for Neighbour Construct, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianLattices/NeighbourConstruct.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory
section Defs
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
def invIdeal (P : Ideal R) : Submodule R K :=
  ⨅ p ∈ P, (1 : Submodule R K).comap ((LinearMap.mulLeft R (algebraMap R K p)))
def neighbourCore (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  L ⊓ (Submodule.map (Algebra.linearMap R K) (conjIdeal (K := K) P)).comap ((h x).restrictScalars R)
def neighbourOf (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ⊔ neighbourCore h P L x
end Defs
def NeighbourConstruct : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ (P : Ideal R), P.IsMaximal → P ≠ ⊥ → ∀ L : Submodule R V, Submodule.IsLattice K L →
    IsUnimodular h L → ∀ x ∈ L, x ∉ P • L →
    (∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) →
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x
end Formalism.HermitianLatticesTheory



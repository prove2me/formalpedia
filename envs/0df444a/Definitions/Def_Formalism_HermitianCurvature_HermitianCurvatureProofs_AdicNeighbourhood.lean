-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:34:30.748504+00:00
-- url     : https://prove2.me/theorems/d9ce2ae8-96ce-4351-a5b4-bbb3be3bcba6
-- title:
--   Adic Neighbourhood
-- statement:
--   Definitions and structural lemmas for Adic Neighbourhood, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
def I (R : Subring K) (a : K) : Set K := {x | ∃ r ∈ R, x = a * r}
structure Adic (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  absorb : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  basis : ∀ W ∈ 𝓝 (0 : K), ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ W
variable {R : Subring K} {ϖ : Kˣ}
def Near (R : Subring K) (a x : K) : Prop := ∃ r ∈ R, x = 1 + a * r
end Top
section Avg
variable {K : Type} [CommRing K]
def Osc (N : AddSubgroup K) {d : ℕ} (F : (Fin d → K) → ℂ) (x : Fin d → K) : Prop :=
  (∀ v : Fin d → K, (∀ i, v i ∈ N) → F (x + v) = 0) ∨
    ∃ k : Fin d, ∃ n₀ ∈ N, ∃ c : ℂ, c ≠ 1 ∧ ∀ v : Fin d → K, (∀ i, v i ∈ N) →
      F (x + v + Pi.single k n₀) = c * F (x + v)
end Avg
section Main
variable {K : Type} [CommRing K]
end Main
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P



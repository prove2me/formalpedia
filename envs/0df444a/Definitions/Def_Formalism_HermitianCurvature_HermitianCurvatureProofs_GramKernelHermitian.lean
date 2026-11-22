-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:34:11.817912+00:00
-- url     : https://prove2.me/theorems/81665f41-bce7-4f3b-8809-2487e763224e
-- title:
--   Gram Kernel Hermitian
-- statement:
--   Definitions and structural lemmas for Gram Kernel Hermitian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean

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
namespace Formalism.FourierDecayAlt.P.A6x8
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
end Formalism.FourierDecayAlt.P.A6x8



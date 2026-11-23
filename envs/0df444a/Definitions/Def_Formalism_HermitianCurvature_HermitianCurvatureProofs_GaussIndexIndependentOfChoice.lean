-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:27.982434+00:00
-- url     : https://prove2.me/theorems/859754e8-b962-43f7-90c9-f18d1ac013a5
-- title:
--   Gauss Index Independent Of Choice
-- statement:
--   Definitions and structural lemmas for Gauss Index Independent Of Choice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussIndexIndependentOfChoice.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P.A6x7
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Formalism.FourierDecayAlt.P.A6x7
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
def quotE (b : Kˣ) (Λ : AddSubgroup K) : K ⧸ Λ ≃+ K ⧸ mulLat (b : K) Λ :=
  QuotientAddGroup.congr Λ (mulLat (b : K) Λ) (DistribMulAction.toAddEquiv K b) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩)
end Formalism.FourierDecayAlt.P.A6x7.Hess
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P.A6x7.Osc
variable {K : Type} [CommRing K]
end Formalism.FourierDecayAlt.P.A6x7.Osc
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P.A6x7.admitted
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end Formalism.FourierDecayAlt.P.A6x7.admitted
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
namespace Formalism.FourierDecayAlt.P.A6x7.Ind
section Alg
variable {K : Type} [CommRing K] {m : ℕ}
def qf (M : Matrix (Fin m) (Fin m) K) (ξ : Fin m → K) : K := Ring.inverse 2 * (ξ ⬝ᵥ (M *ᵥ ξ))
variable {ψ : AddChar K ℂ}
end Alg
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {m : ℕ}
end Formalism.FourierDecayAlt.P.A6x7.Ind



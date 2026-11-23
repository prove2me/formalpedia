-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussSumModulusOfLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:04.307828+00:00
-- url     : https://prove2.me/theorems/2580e84b-af57-45dd-8a9e-67cff01bf6ab
-- title:
--   Gauss Sum Modulus Of Lattice
-- statement:
--   Definitions and structural lemmas for Gauss Sum Modulus Of Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GaussSumModulusOfLattice.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P
namespace A6x6
section Jet
open MvPolynomial
variable {m : ℕ}
end Jet
open Formalism.FourierDecayAlt.P.A5x5
section Abs
end Abs
section Pi
variable {K : Type} [CommRing K] {m : ℕ}
def PL (L : AddSubgroup K) (m : ℕ) : AddSubgroup (Fin m → K) :=
  AddSubgroup.pi Set.univ (fun _ => L)
def prj (Λ : AddSubgroup K) (m : ℕ) : (Fin m → K) →+ (Fin m → K ⧸ Λ) :=
  (QuotientAddGroup.mk' Λ).compLeft (Fin m)
def sec (Λ : AddSubgroup K) (y : Fin m → K ⧸ Λ) : Fin m → K := fun i => Quotient.out (y i)
variable [TopologicalSpace K] [IsTopologicalRing K]
end Pi
section Main
variable {K : Type} [CommRing K] {m : ℕ} (ψ : AddChar K ℂ)
variable {M : Matrix (Fin m) (Fin m) K}
variable {L Λ : AddSubgroup K}
variable {ψ}
end Main
section Final
end Final
end A6x6
end Formalism.FourierDecayAlt.P



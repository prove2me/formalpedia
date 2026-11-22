-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:34:40.423268+00:00
-- url     : https://prove2.me/theorems/44b8b285-55cf-4d55-a206-0c3e5dc9bf98
-- title:
--   Germ Sum Lattices
-- statement:
--   Definitions and structural lemmas for Germ Sum Lattices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
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
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.GermSumLattices
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
end Top
section Alg
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
end Alg
section Mod
variable {K : Type} [CommRing K] (R : Subring K)
def MM : Prop := ∀ x y : Kˣ,
  0 < modK R (x : K) ∧ modK R ((x : K) * (y : K)) = modK R (x : K) * modK R (y : K)
variable {R}
variable (R) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
open Classical in

def amp (h h' : Point K) (t₁ ζ : Kˣ) (z : K) : ℂ :=
  if hz : IsUnit z then
    γ (hz.unit * t₁) * conj (γ (ζ * hz.unit * t₁)) *
      (((modK R ((m + 1 : ℕ) : K))⁻¹ * modK R z ^ (m ^ 2) : ℝ) : ℂ) *
      Kp R ψ (addBlock h (m + 1) hz.unit) (addBlock h' (m + 1) (ζ * hz.unit))
  else 0
end Mod
section Core
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ) (m : ℕ) (γ : Kˣ → ℂ)
def f1 (h h' : Point K) (d : K) (z : K) : ℂ :=
  (((modK R ((m + 1 : ℕ) : K))⁻¹ * (modK R z ^ m)⁻¹ : ℝ) : ℂ) *
    (NsK R ψ (m + 1) h h' z * ψ (z * d))
end Core
section Cut
variable {K : Type} [CommRing K]
end Cut
end Formalism.FourierDecayAlt.P.GermSumLattices
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.GermSumLattices
end Formalism.FourierDecayAlt.P



-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:07:53.293507+00:00
-- url     : https://prove2.me/theorems/39fa0484-7cda-496a-8843-28cdf4a3b3bb
-- title:
--   Weighted Sum Difference Identity
-- statement:
--   Definitions and structural lemmas for Weighted Sum Difference Identity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeightedSumDifferenceIdentity.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.Mx7
section PartT
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
section abs
variable {R : Type*} [Ring R] [Algebra ℂ R]
end abs
end PartT
section PartF
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
def pa (s : Finset ℕ) (ρ : ℕ → ℂ) : ℂ[X] := ∏ i ∈ s, (X + C (ρ i))
def DD (s : Finset ℕ) (ρ : ℕ → ℂ) (c : ℂ) (q1 : ℂ[X]) (N M : ℕ → ℂ) : ℂ[X] :=
  C c * q1 + (∑ l ∈ s, C (M l) * (pa (s.erase l) ρ * pa s (fun i => ρ i + 1))) -
    (∑ l ∈ s, C (N l) * (pa s ρ * pa (s.erase l) (fun i => ρ i + 1)))
def q1P (P : Par) : ℂ[X] :=
  ∏ i ∈ Icc 1 P.k, ((X + C (1 / 2 + (P.u i : ℂ))) * (X + C (1 / 2 + (P.u' i : ℂ))))
end
end PartF
section PartA
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
section Poly
variable {B : Type} [Ring B] [Algebra ℂ B]
noncomputable def ev (Y : ℂ) : B[X] →+* B :=
  eval₂RingHom' (RingHom.id B) (algebraMap ℂ B Y) (fun a => (Algebra.commutes Y a).symm)
def IsPoly (F : ℂ → B) : Prop := ∃ p : B[X], ∀ Y, F Y = ev Y p
end Poly
section AbsDet
variable {B : Type} [Ring B] [Algebra ℂ B]
end AbsDet
end PartA
section PartB
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
section abs2
variable {R : Type*} [Ring R] [Algebra ℂ R]
end abs2
noncomputable def ti (P : Par) (Y : ℂ) : A P := ggiA P * kap P fun π => (xC P π Y)⁻¹
noncomputable def Ul (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j
noncomputable def Um (P : Par) (Y : ℂ) : A P :=
  ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * star (SS P j)
end PartB
section PartC
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
noncomputable def bb (P : Par) (u : ℂ) (j : ℕ) : Ty P → ℂ := fun π => (u + (rho P π j : ℂ))⁻¹
def Det8 (P : Par) (Y : ℂ) : Prop :=
  t11 P (Y + 1) * t21 P Y - t21 P (Y + 1) * t11 P Y = 0 ∧
  t11 P (Y + 1) * t22 P Y - t21 P (Y + 1) * t12 P Y = algebraMap ℂ (A P) (qC P Y) ∧
  t12 P (Y + 1) * t21 P Y - t22 P (Y + 1) * t11 P Y = -algebraMap ℂ (A P) (qC P Y) ∧
  t12 P (Y + 1) * t22 P Y - t22 P (Y + 1) * t12 P Y = 0 ∧
  t11 P Y * t12 P (Y + 1) - t12 P Y * t11 P (Y + 1) = 0 ∧
  t11 P Y * t22 P (Y + 1) - t12 P Y * t21 P (Y + 1) = algebraMap ℂ (A P) (qC P Y) ∧
  t21 P Y * t12 P (Y + 1) - t22 P Y * t11 P (Y + 1) = -algebraMap ℂ (A P) (qC P Y) ∧
  t21 P Y * t22 P (Y + 1) - t22 P Y * t21 P (Y + 1) = 0
end PartC
section PartD
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable def badSet (P : Par) : Finset ℂ :=
  (Finset.univ : Finset (Ty P)).biUnion fun π => (Icc 1 (P.k - 1)).biUnion fun i =>
    {-(rho P π i : ℂ), -(rho P π i : ℂ) - 1, -(rho P π i : ℂ) - 2}
end PartD
end Formalism.FourierDecayAlt.P.Mx7
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P



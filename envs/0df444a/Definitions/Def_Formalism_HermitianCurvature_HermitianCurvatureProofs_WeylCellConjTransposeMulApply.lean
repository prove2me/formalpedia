-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:49:06.989792+00:00
-- url     : https://prove2.me/theorems/f1d2eb38-f03a-4216-a0e7-abb170f7e855
-- title:
--   Weyl Cell Conj Transpose Mul Apply
-- statement:
--   Definitions and structural lemmas for Weyl Cell Conj Transpose Mul Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WeylCellConjTransposeMulApply.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
def mulVecL (v : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
def LieLev (i : Fin (r + 1)) (X : Mx k r) : Prop := ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i
section Fam
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev XX (k r : ℕ) := (Fin r → ℂ) × Mx k r
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
def Pres (i : Fin (r + 1)) (U₀ : Set (XX k r)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ → SmoothFam k r i U₀ (fun c => T (Φ c))
end Fam
section Entries
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
end Entries
section Ops
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
end Ops
section W1
def sw (k : ℕ) {r : ℕ} (l : Fin r) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if q = eI k r l then esI k r l else if q = esI k r l then eI k r l else q
def dd (k : ℕ) {r : ℕ} (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) : ℂ :=
  if q = eI k r l then c else if q = esI k r l then (star c)⁻¹ else 1
end W1
section Res
def mulLeftL (w : Mx k r) : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ w)
variable {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
variable {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
end Res
end Formalism.FourierDecayAlt.P.Qx3
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P



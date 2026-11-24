-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:23.858098+00:00
-- url     : https://prove2.me/theorems/3280d0b5-214b-402c-a07f-83abe835b407
-- title:
--   Dilation Unipotent Weyl Measure
-- statement:
--   Definitions and structural lemmas for Dilation Unipotent Weyl Measure, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DilationUnipotentWeylMeasure.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.B4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable def dg (k r : ℕ) (t : ℝ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then ((t ^ (r - i.val) : ℝ) : ℂ)
    else if i.val ≤ r + k then 1 else (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ)
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def cv (b : Bool) (X : Mat k r) (t : ℝ) (g : Mat k r) : Mat k r :=
  match b with
  | true => NormedSpace.exp (-((t : ℂ) • X)) * g
  | false => g * NormedSpace.exp ((t : ℂ) • X)
def op (b : Bool) (X : Mat k r) (f : Mat k r → E) : Mat k r → E :=
  fun g => deriv (fun t : ℝ => f (cv b X t g)) 0
def mulL (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ X)
def mulR (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)
def vf (b : Bool) (X : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  match b with
  | true => -(mulL X)
  | false => mulR X
def op' (b : Bool) (X : Mat k r) (f' : Mat k r → E) : Mat k r → E :=
  fun g => fderiv ℝ f' g (vf b X g)
def W (w : List (Bool × Mat k r)) (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun x h => op x.1 x.2 h) f
def lr (u v : List (Mat k r)) : List (Bool × Mat k r) :=
  u.map (fun X => (true, X)) ++ v.map (fun X => (false, X))
def AllLie (w : List (Bool × Mat k r)) : Prop := ∀ x ∈ w, inLie k r x.2
def LRt (τ : List Bool) : Prop := ∃ a b, τ = List.replicate a true ++ List.replicate b false
def nrm (x : Bool × Mat k r) : Bool × Mat k r := (x.1, ((‖x.2‖⁻¹ : ℝ) : ℂ) • x.2)
def pn (w : List (Bool × Mat k r)) : ℝ := (w.map fun x => ‖x.2‖).prod
def sel (t : ℝ × ℝ) (b : Bool) : ℝ :=
  match b with
  | true => t.1
  | false => t.2
def adj (t : ℝ × ℝ) (x : Bool × Mat k r) : Bool × Mat k r :=
  (x.1, (aDil k r (sel t x.1))⁻¹ * x.2 * aDil k r (sel t x.1))
def dl (t : ℝ × ℝ) (f : Mat k r → E) (g : Mat k r) : E := f ((aDil k r t.1)⁻¹ * g * aDil k r t.2)
def zd (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℝ :=
  if i.val < r then ((r - i.val : ℕ) : ℝ) else if i.val ≤ r + k then 0 else -((i.val - (r + k) : ℕ) : ℝ)
def Zm (k r : ℕ) : Mat k r := Matrix.diagonal fun i => ((zd k r i : ℝ) : ℂ)
section
variable {t : ℝ × ℝ} (h1 : t.1 ∈ Set.Icc (1 / 2 : ℝ) 2) (h2 : t.2 ∈ Set.Icc (1 / 2 : ℝ) 2)
include h1 h2
end
end Formalism.FourierDecayAlt.P.B4
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4
end Formalism.FourierDecayAlt.P



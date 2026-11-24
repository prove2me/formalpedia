-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T14:43:25.009612+00:00
-- url     : https://prove2.me/theorems/21b353de-778d-46fe-9e87-5ec1eaa646f3
-- title:
--   Conjugation Continuous On Invertible
-- statement:
--   Definitions and structural lemmas for Conjugation Continuous On Invertible, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ConjugationContinuousOnInvertible.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
namespace Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
theorem detF_cont : Continuous (detF (k := k) (r := r)) := Continuous.matrix_det (continuous_id (X := Mat k r))
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := Continuous.matrix_adjugate (continuous_id (X := Mat k r))
theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mat k r).det • (Matrix.of x : Mat k r).adjugate : Mat k r) = _
  rw [Ring.inverse_eq_inv']; rfl
theorem invM_contOn : ContinuousOn (invM : Mt k r → Mt k r) {x | detF x ≠ 0} := by
  rw [invM_smul]
  exact (detF_cont.continuousOn.inv₀ (fun x hx => hx)).smul adjF_cont.continuousOn
theorem mulM_cont : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  unfold mulM
  exact Continuous.matrix_mul (A := fun p : Mt k r × Mt k r => (Matrix.of p.1 : Mat k r))
    (B := fun p : Mt k r × Mt k r => (Matrix.of p.2 : Mat k r)) continuous_fst continuous_snd
def amb (U : Set (Mat k r)) : Set (Mt k r) := {x | Matrix.of x ∈ U}
theorem amb_closed {U : Set (Mat k r)} (hU : IsClosedSubgroup U) : IsClosed (amb U) := hU.closed
def Gp (U : Set (Mat k r)) (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // x ∈ amb U}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
instance : TopologicalSpace (Gp U hU) := inferInstanceAs (TopologicalSpace {x : Mt k r // x ∈ amb U})
instance : MeasurableSpace (Gp U hU) := inferInstanceAs (MeasurableSpace {x : Mt k r // x ∈ amb U})
instance : BorelSpace (Gp U hU) := inferInstanceAs (BorelSpace {x : Mt k r // x ∈ amb U})
instance : SecondCountableTopology (Gp U hU) :=
  inferInstanceAs (SecondCountableTopology {x : Mt k r // x ∈ amb U})
instance : T2Space (Gp U hU) := inferInstanceAs (T2Space {x : Mt k r // x ∈ amb U})
def inc (x : Gp U hU) : Mt k r := x.1
theorem inc_closedEmb : IsClosedEmbedding (inc : Gp U hU → Mt k r) :=
  (amb_closed hU).isClosedEmbedding_subtypeVal
instance : LocallyCompactSpace (Gp U hU) := inc_closedEmb.locallyCompactSpace
instance : Group (Gp U hU) where
  mul a b := ⟨mulM (a.1, b.1), hU.mul_mem _ a.2 _ b.2⟩
  one := ⟨(1 : Mat k r), hU.one_mem⟩
  inv a := ⟨invM a.1, hU.inv_mem _ a.2⟩
  mul_assoc a b c := Subtype.ext (Matrix.mul_assoc (Matrix.of a.1 : Mat k r) (Matrix.of b.1) (Matrix.of c.1))
  one_mul a := Subtype.ext (Matrix.one_mul (Matrix.of a.1 : Mat k r))
  mul_one a := Subtype.ext (Matrix.mul_one (Matrix.of a.1 : Mat k r))
  inv_mul_cancel a := Subtype.ext (Matrix.nonsing_inv_mul (Matrix.of a.1 : Mat k r) (hU.unit _ a.2))
instance : IsTopologicalGroup (Gp U hU) where
  continuous_mul := by
    refine Continuous.subtype_mk (mulM_cont.comp ?_) _
    exact (continuous_subtype_val.comp continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Continuous.subtype_mk ?_ _
    exact invM_contOn.comp_continuous continuous_subtype_val (fun x => (hU.unit _ x.2).ne_zero)
def pull (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (Gp U hU) := μ.comap inc
def conj2 (p : Mt k r × Mt k r) : Mt k r := mulM (mulM (p.1, p.2), invM p.1)
end Formalism.FourierDecayAlt.P.B2x1
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P



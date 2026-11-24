-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:26:02.855816+00:00
-- url     : https://prove2.me/theorems/cfe50bf0-635b-4f0d-b4e7-2d43aeedc4c6
-- title:
--   Rank One Embeddings
-- statement:
--   Definitions and structural lemmas for Rank One Embeddings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RankOneEmbeddings.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
def sg (k : ℕ) : Fin (k + 1) → Bool := fun j => decide (j ≠ Fin.last k)
def Φ (k r : ℕ) (g : UJ (sg k)) : Mt k r :=
  embWb k r ((g : (Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)ˣ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.Wb
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
abbrev Vc (k r : ℕ) := Fin (2 * r + k + 1) → ℂ
def mvM (p : Mt k r × Vc k r) : Vc k r := (Matrix.of p.1 : Mat k r) *ᵥ p.2
theorem mulM_cont : Continuous (mulM (k := k) (r := r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
theorem detF_cont : Continuous (detF (k := k) (r := r)) := by
  first
    | exact continuous_id.matrix_det
    | (unfold detF; fun_prop)
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := by
  first
    | exact continuous_id.matrix_adjugate
    | (unfold adjF; fun_prop)
theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show ((Matrix.of x : Mat k r)⁻¹ : Mat k r) = (detF x)⁻¹ • adjF x
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rfl
theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  have h1 : Measurable fun x : Mt k r => (detF x)⁻¹ := detF_cont.measurable.inv
  have h2 : Measurable fun x : Mt k r => adjF x i j :=
    ((continuous_apply j).comp ((continuous_apply i).comp adjF_cont)).measurable
  exact h1.mul h2
def embF (k r : ℕ) (μ : Fin (k + 1) → Fin (k + 1) → ℂ) : Mt k r := embWb k r (Matrix.of μ)
example (U : Set (Mt k r)) (hU : IsClosed U) : StandardBorelSpace U := hU.measurableSet.standardBorel
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
def Om (k r : ℕ) (z z' : Vc k r) : Set ℂ := {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}
open Classical in

def secF (k r : ℕ) (z z' : Vc k r) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := if ζ ∈ Om k r z z' then μsec ζ else 1
def MeasSec (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : Prop :=
  @Measurable ℂ (Fin (k + 1) → Fin (k + 1) → ℂ) _ _ s
abbrev wd (k r : ℕ) (z z' : Vc k r) : Measure ℂ :=
  (volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)
def Phi (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (x : ℂ × (Mt k r × Mt k r)) : Mt k r :=
  mulM (mulM (invM x.2.1, embF k r (s x.1)), x.2.2)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
abbrev nu (z z' : Vc k r) (s : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (μW μW' : Measure (Mt k r)) :
    Measure (Mt k r) := ((wd k r z z').prod (μW.prod μW')).map (Phi s)
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
theorem mulM_meas : Measurable (mulM (k := k) (r := r)) := by
  exact mulM_cont.measurable
attribute [local fun_prop] mulM_meas invM_meas
def m1 (p : Mt k r × Mt k r) : Mt k r := mulM (p.2, p.1)
def sgF (x : SS k r × Mt k r) : Mt k r :=
  mulM (mulM (mulM (mulM (invM x.1.1.1, invM x.1.1.2), x.2), x.1.2.2), x.1.2.1)
theorem sgF_meas : Measurable (sgF (k := k) (r := r)) := by
  unfold sgF
  fun_prop
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1
variable {k r : ℕ}
attribute [local fun_prop] mulM_meas invM_meas sgF_meas
def bc1 (k r : ℕ) (c : Fin r → ℂ) : Mt k r := bigCell k r c 1
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.RankOneEmbeddings.R1 Formalism.FourierDecayAlt.P.RankOneEmbeddings.In
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P.RankOneEmbeddings.Nm
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
end Formalism.FourierDecayAlt.P



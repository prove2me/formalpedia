-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:07:25.099929+00:00
-- url     : https://prove2.me/theorems/ff13b239-0cd7-4a48-a87b-99241999b4ec
-- title:
--   Two By One Block
-- statement:
--   Definitions and structural lemmas for Two By One Block, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoByOneBlock.lean

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RankOneEmbeddings
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
namespace Formalism.FourierDecayAlt.P.TwoByOneBlock
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
section PartA
variable {k r : ℕ}
def jV (k r : ℕ) (u : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then u ⟨i.val - r, by omega⟩ else 0
abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k
end PartA
section PartB
section Herm
variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)
end Herm
def qrefl {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (c : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 + c • Matrix.vecMulVec d (star d ᵥ* H)
end PartB
section PartC
variable {k r : ℕ}
end PartC
section PartM
open Set
open scoped Pointwise
def Sq (k : ℕ) (x : Fin k → ℂ) : ℝ := ∑ i, Complex.normSq (x i)
def Vb (k : ℕ) : ℝ≥0∞ := volume {x : Fin k → ℂ | Sq k x ≤ 1}
def dens (n : ℕ) : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (t ^ n)
def Nq (k : ℕ) (u : Fin (k + 1) → ℂ) : ℝ :=
  Complex.normSq (u (Fin.last k)) - ∑ i : Fin k, Complex.normSq (u i.castSucc)
def cs (T T' s : ℝ) : ℂ := ((-(√T * √(T' / s)) : ℝ) : ℂ)
def Wf (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  {ζ : ℂ | T * T' < Complex.normSq ζ}.indicator fun ζ => ENNReal.ofReal ((Complex.normSq ζ - T * T') ^ n) * φ ζ
def Ff (T T' : ℝ) (φ : ℂ → ℝ≥0∞) (y : ℂ) : ℝ → ℝ≥0∞ := (Ioc 0 T').indicator fun s => φ (cs T T' s * y)
def Rf (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) (y : ℂ) : ℝ → ℝ≥0∞ :=
  (Ioc 0 T').indicator fun s => ENNReal.ofReal ((s / (T * T')) ^ n) * Wf n T T' φ (cs T T' s * y)
def Jc (n : ℕ) (T T' : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc 0 T', ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))
end PartM
section PartD
variable {k r : ℕ}
def scl (k : ℕ) (T' : ℝ) (u : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ := ((√(T' / Nq k u) : ℝ) : ℂ) • u
def shell (k : ℕ) (T' : ℝ) : Set (Fin (k + 1) → ℂ) := {u | 0 < Nq k u ∧ Nq k u ≤ T'}
def σb (k : ℕ) (T' : ℝ) : Measure (Fin (k + 1) → ℂ) := ((volume : Measure (Fin (k + 1) → ℂ)).restrict (shell k T')).map (scl k T')
end PartD
section PartE
variable {k r : ℕ}
def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det
def act (h : Mt k r) (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := ((Matrix.of h : Mat k r)⁻¹ : Mat k r) *ᵥ v
instance (T' : ℝ) : SFinite (σb k T') := by unfold σb; infer_instance
def σV (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (σb k T').map (jV k r)
instance (T' : ℝ) : SFinite (σV k r T') := by unfold σV; infer_instance
end PartE
end Formalism.FourierDecayAlt.P.TwoByOneBlock
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P



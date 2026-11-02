-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P100
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P100
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:23:20.566367+00:00
-- url     : https://prove2.me/theorems/dbfe3706-29f7-468f-8e17-7bb1993de9c8
-- title:
--   Definitions for Continuity of Relative Entropy of Entanglement
-- statement:
--   The objects the formalized statements of *Continuity of Relative Entropy of Entanglement* (arXiv:quant-ph/9910002) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `separableStates`: PDF pp.1–2, Remark (i): exactly the normalized separable states, using the accepted finite convex-combination definition.
--   - `pptStates`: PDF p.2, Remark (i): trace-one positive states with positive partial transpose. This is the normalized PPT optimization specified by the paper.
--   - `pptEntanglement`: PDF pp.1–2, Remark (i): the infimum over normalized PPT states, in bits to match the frozen relativeEntanglement interface. Bounds convert to nats. The support-aware entropy retains infinity before the infimum is taken.
-- source:
--   Continuity of Relative Entropy of Entanglement, arXiv:quant-ph/9910002v1, https://arxiv.org/abs/quant-ph/9910002v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_ExtendedQuantumEntropy
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15

/-!
Donald and Horodecki, arXiv:quant-ph/9910002v1, PDF pp.1–3.
Full trace norm throughout. The frozen entropy and distance interfaces below
use bits. Each quantitative real difference is explicitly multiplied by ln 2,
so the displayed bounds use nats exactly as in the chosen source convention.
Frozen relativeDistance is EReal-valued and supports unnormalized operators;
our feasible sets contain only normalized states. Nonnegativity and finiteness
are conclusions, not premises. The frozen normalized relativeEntanglement is
ENNReal-valued. Attainment is invariant under the positive conversion ln 2.
The accepted groupedTensorPower keeps the bipartition A^n:B^n.
-/

noncomputable section

open Filter
open scoped ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P100

open QAlgorithms.Papers.Independent.Dependency50.P15
  (relativeDistance relativeDistanceValue positiveOperatorRelativeEntropyBits groupedTensorPower)
open QAlgorithms.Papers.Independent.Information100.P54
  (relativeEntropyBits relativeEntanglement)

/-- PDF pp.1–2, Remark (i): exactly the normalized separable states,
using the accepted finite convex-combination definition. -/
def separableStates {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] : Set (Matrix (A × B) (A × B) ℂ) :=
  {rho | QAlgorithms.Entanglement.IsSeparableDensity rho}

/-- PDF p.2, Remark (i): trace-one positive states with positive partial
transpose. This is the normalized PPT optimization specified by the paper. -/
def pptStates {A B : Type*} [Fintype A] [Fintype B] :
    Set (Matrix (A × B) (A × B) ℂ) :=
  {rho | IsDensityMatrix rho ∧
    (QAlgorithms.Entanglement.partialTransposeFirst rho).PosSemidef}

/-- PDF pp.1–2, Remark (i): the infimum over normalized PPT states, in
bits to match the frozen relativeEntanglement interface. Bounds convert to nats.
The support-aware entropy retains infinity before the infimum is taken. -/
def pptEntanglement {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (sigma : Matrix (A × B) (A × B) ℂ) : ℝ≥0∞ :=
  sInf (relativeEntropyBits sigma '' pptStates)

/-- Sanity check, PDF p.1: the reused eta vanishes at zero and one. -/
example : Real.negMulLog 0 = 0 ∧ Real.negMulLog 1 = 0 := by simp

/-- Sanity check, PDF p.2: the frozen extended empty infimum is infinity. -/
example {I : Type*} [Fintype I] [DecidableEq I] (sigma : Matrix I I ℂ) :
    relativeDistance ∅ sigma = ⊤ := by simp [relativeDistance]

/-- Sanity check, PDF pp.1–2: separability membership is the accepted predicate. -/
example {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) :
    rho ∈ separableStates ↔ QAlgorithms.Entanglement.IsSeparableDensity rho := Iff.rfl

/-- Sanity check, PDF p.2: the zero scalar matrix is excluded by normalization. -/
example : (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ) ∉ pptStates := by
  simp [pptStates, IsDensityMatrix]

/-- Sanity check, PDF p.2: the local PPT infimum uses exactly the PPT feasible image. -/
example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (sigma : Matrix (A × B) (A × B) ℂ) :
    pptEntanglement sigma = sInf (relativeEntropyBits sigma '' pptStates) := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P100



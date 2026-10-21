-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P35
-- name    : QAlgorithms_Papers_Independent_Renew46_P35
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T21:56:20.596454+00:00
-- url     : https://prove2.me/theorems/77073218-d97c-4778-85af-3fe4e1ce3d56
-- title:
--   Definitions for Structure of states which satisfy strong subadditivity of quantum entropy with equality
-- statement:
--   The objects the formalized statements of *Structure of states which satisfy strong subadditivity of quantum entropy with equality* (arXiv:quant-ph/0304007) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `chiAfter`: PDF pp.3–4: a channel applied to every member of the same ensemble.
--   - `measurementLaw`: PDF p.3: actual joint label/measurement-outcome law.
--   - `quantumCMI`: PDF p.3, eq.(6): quantum conditional mutual information in bits.
--   - `MarkovTensorBlocks`: PDF pp.4,7–8: unitary decomposition of the entire finite H, into nonzero tensor blocks. Both unitary identities are required: unused kernel directions are included.
--   - `inclusion`: PDF p.5: orthogonal isometric inclusion of a tensor block.
--   - `outerInclusion`: PDF pp.4–5: inclusion of the jth block, with unchanged outer registers.
--   - `blockState`: PDF p.4, Theorem 6: direct sum transported back by the unitary on B.
--   - `HasMarkovBlocks`: PDF p.4: the block structure in Theorem 6; all factors and weights are conclusions.
--   - `traceAdjoint`: PDF p.4, eq.(8): trace adjoint, defined on all operators via matrix units.
--   - `pmfProduct`: PDF pp.2–3: product of two PMFs, including countably supported laws on infinite alphabets.
--   - `discreteMI`: PDF p.2: mutual information as extended nonnegative KL divergence, in bits. The full discrete sigma algebra is chosen explicitly.
--   - `classicalCMI`: PDF p.2: positive-event conditional KL information, averaged without infinity subtraction. `cond` is the conditional law, uniquely fixed on positive events by the theorem's hypothesis.
--   - `IsConditionalExpectation`: PDF p.8: unital CP projection with exact range and conditional-expectation bimodule law.
--   - `dualMean`: PDF p.8: Cesaro means start at the first iterate, not the zeroth.
--   - `embedTensorBlock`: PDF p.8: block embedding of an operator.
--   - `InBlockAlgebra`: PDF p.8, Lemma 13: the algebra associated with a tensor-block decomposition.
--   - `expectationFormula`: PDF p.8, Lemma 13: weighted partial trace, followed by tensoring with the identity.
-- source:
--   Structure of states which satisfy strong subadditivity of quantum entropy with equality, arXiv:quant-ph/0304007v2, https://arxiv.org/abs/quant-ph/0304007v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P06
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

noncomputable section

open scoped Matrix ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Renew46.P35

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted interfaces, inspected in the pinned library.
open QAlgorithms.Papers.Independent.Dependency50.P07
  (CQData ensembleMean ensembleInformation accessibleInformation)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)
open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAB marginalAC)
open QAlgorithms.Papers.Independent.Dependency50.P21 (petz)
open QAlgorithms.Papers.Independent.Information100.P06 (supportProjection)
open QAlgorithms.Papers.Independent.Information100.P22 (quantumMI)

/-- PDF pp.3–4: a channel applied to every member of the same ensemble. -/
def chiAfter {X H K : Type} [Fintype X] [Fintype H] [Fintype K]
    (e : CQData X H) (f : Superop H K) : ℝ :=
  vnEntropy (f (ensembleMean e)) - ∑ x, e.prob x * vnEntropy (f (e.state x))

/-- PDF p.3: actual joint label/measurement-outcome law. -/
def measurementLaw {X H Y : Type} [Fintype X] [Fintype H]
    (e : CQData X H) (m : Y → Matrix H H ℂ) : X × Y → ℝ :=
  fun xy => e.prob xy.1 * effectProb (m xy.2) (e.state xy.1)

/-- PDF p.3, eq.(6): quantum conditional mutual information in bits. -/
def quantumCMI {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) : ℝ :=
  vnEntropy (marginalAB rho) + vnEntropy (traceLeft rho) - vnEntropy rho -
    vnEntropy (traceLeft (marginalAB rho))

/-- PDF pp.4,7–8: unitary decomposition of the entire finite H, into nonzero tensor blocks.
Both unitary identities are required: unused kernel directions are included. -/
structure MarkovTensorBlocks (H : Type*) [Fintype H] where
  count : ℕ
  count_pos : 0 < count
  left : Fin count → ℕ
  right : Fin count → ℕ
  left_pos : ∀ j, 0 < left j
  right_pos : ∀ j, 0 < right j
  unitary : Matrix (Σ j : Fin count, Fin (left j) × Fin (right j)) H ℂ
  unitary_left : unitaryᴴ * unitary = 1
  unitary_right : unitary * unitaryᴴ = 1

/-- PDF p.5: orthogonal isometric inclusion of a tensor block. -/
def inclusion {H : Type*} [Fintype H] (d : MarkovTensorBlocks H) (j : Fin d.count) :
    Matrix H (Fin (d.left j) × Fin (d.right j)) ℂ :=
  fun h lr => star (d.unitary ⟨j, lr⟩ h)

/-- PDF pp.4–5: inclusion of the jth block, with unchanged outer registers. -/
def outerInclusion {A B C : Type*} [Fintype B] (d : MarkovTensorBlocks B) (j : Fin d.count) :
    Matrix (A × (B × C)) ((A × Fin (d.left j)) × (Fin (d.right j) × C)) ℂ :=
  fun abc lr => if abc.1 = lr.1.1 ∧ abc.2.2 = lr.2.2 then
    inclusion d j abc.2.1 (lr.1.2, lr.2.1) else 0

/-- PDF p.4, Theorem 6: direct sum transported back by the unitary on B. -/
def blockState {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (d : MarkovTensorBlocks B) (q : Fin d.count → ℝ)
    (alpha : (j : Fin d.count) → Matrix (A × Fin (d.left j)) (A × Fin (d.left j)) ℂ)
    (beta : (j : Fin d.count) → Matrix (Fin (d.right j) × C) (Fin (d.right j) × C) ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  ∑ j, (q j : ℂ) • (outerInclusion (A := A) (C := C) d j * Matrix.kronecker (alpha j) (beta j) *
    (outerInclusion (A := A) (C := C) d j)ᴴ)

/-- PDF p.4: the block structure in Theorem 6; all factors and weights are conclusions. -/
def HasMarkovBlocks {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (rho : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Prop :=
  ∃ d : MarkovTensorBlocks B, ∃ q : Fin d.count → ℝ,
    ∃ alpha : (j : Fin d.count) → Matrix (A × Fin (d.left j)) (A × Fin (d.left j)) ℂ,
    ∃ beta : (j : Fin d.count) → Matrix (Fin (d.right j) × C) (Fin (d.right j) × C) ℂ,
      (∀ j, 0 ≤ q j) ∧ (∑ j, q j) = 1 ∧
      (∀ j, IsDensityMatrix (alpha j) ∧ IsDensityMatrix (beta j)) ∧
      rho = blockState d q alpha beta

/-- PDF p.4, eq.(8): trace adjoint, defined on all operators via matrix units. -/
def traceAdjoint {H K : Type*} [Fintype H] [Fintype K]
    (f : Superop H K) : Superop K H :=
  fun x a b => (x * f (Matrix.single b a 1)).trace

/-- PDF pp.2–3: product of two PMFs, including countably supported laws on infinite alphabets. -/
def pmfProduct {A C : Type*} (p : PMF A) (q : PMF C) : PMF (A × C) :=
  p.bind fun a => q.map fun c => (a, c)

/-- PDF p.2: mutual information as extended nonnegative KL divergence, in bits.
The full discrete sigma algebra is chosen explicitly. -/
def discreteMI {A C : Type*} (p : PMF (A × C)) : ℝ≥0∞ :=
  letI : MeasurableSpace (A × C) := ⊤
  InformationTheory.klDiv p.toMeasure (pmfProduct (p.map Prod.fst) (p.map Prod.snd)).toMeasure /
    ENNReal.ofReal (Real.log 2)

/-- PDF p.2: positive-event conditional KL information, averaged without infinity subtraction.
`cond` is the conditional law, uniquely fixed on positive events by the theorem's hypothesis. -/
def classicalCMI {A B C : Type*} (p : PMF (A × (B × C)))
    (cond : B → PMF (A × C)) : ℝ≥0∞ :=
  ∑' b, if (p.map fun x => x.2.1) b = 0 then 0 else
    (p.map fun x => x.2.1) b * discreteMI (cond b)

/-- PDF p.8: unital CP projection with exact range and conditional-expectation bimodule law. -/
def IsConditionalExpectation {H : Type*} [Fintype H]
    (p : Matrix H H ℂ →ₗ[ℂ] Matrix H H ℂ)
    (a : StarSubalgebra ℂ (Matrix H H ℂ)) : Prop :=
  Entanglement.IsCompletelyPositive p ∧ p 1 = 1 ∧
    (∀ x, p (p x) = p x) ∧ Set.range p = (a : Set (Matrix H H ℂ)) ∧
    ∀ l ∈ a, ∀ r ∈ a, ∀ x, p (l * x * r) = l * p x * r

/-- PDF p.8: Cesaro means start at the first iterate, not the zeroth. -/
def dualMean {H : Type*} [Fintype H] (f : Superop H H) (n : ℕ)
    (x : Matrix H H ℂ) : Matrix H H ℂ :=
  (n : ℂ)⁻¹ • ∑ k ∈ Finset.range n, (traceAdjoint f)^[k + 1] x

/-- PDF p.8: block embedding of an operator. -/
def embedTensorBlock {H : Type*} [Fintype H] (d : MarkovTensorBlocks H) (j : Fin d.count)
    (x : Matrix (Fin (d.left j) × Fin (d.right j))
      (Fin (d.left j) × Fin (d.right j)) ℂ) : Matrix H H ℂ :=
  inclusion d j * x * (inclusion d j)ᴴ

/-- PDF p.8, Lemma 13: the algebra associated with a tensor-block decomposition. -/
def InBlockAlgebra {H : Type*} [Fintype H] (d : MarkovTensorBlocks H) (x : Matrix H H ℂ) : Prop :=
  ∃ z : (j : Fin d.count) → Matrix (Fin (d.left j)) (Fin (d.left j)) ℂ,
    x = ∑ j, embedTensorBlock d j (Matrix.kronecker (z j) 1)

/-- PDF p.8, Lemma 13: weighted partial trace, followed by tensoring with the identity. -/
def expectationFormula {H : Type*} [Fintype H] (d : MarkovTensorBlocks H)
    (omega : (j : Fin d.count) → Matrix (Fin (d.right j)) (Fin (d.right j)) ℂ)
    (x : Matrix H H ℂ) : Matrix H H ℂ :=
  ∑ j, embedTensorBlock d j (Matrix.kronecker
    (traceRight (((inclusion d j)ᴴ * x * inclusion d j) * Matrix.kronecker 1 (omega j))) 1)

/-- Sanity: ensembleMean uses the actual weights (PDF p.3). -/
example {X H : Type} [Fintype X] [Fintype H] (e : CQData X H) :
    ensembleMean e = ∑ x, (e.prob x : ℂ) • e.state x := rfl

/-- Sanity: label coherences are zero in the cq state (PDF p.3). -/
example {X H : Type} [Fintype X] [Fintype H] (e : CQData X H)
    (x y : X) (h : x ≠ y) (i j : H) : cqState e.prob e.state (x, i) (y, j) = 0 := by
  simp [cqState, h]

/-- Sanity: inclusion is the adjoint row of the full unitary (PDF p.5). -/
example {H : Type*} [Fintype H] (d : MarkovTensorBlocks H) (j : Fin d.count)
    (h : H) (lr : Fin (d.left j) × Fin (d.right j)) :
    inclusion d j h lr = star (d.unitary ⟨j, lr⟩ h) := rfl

/-- Sanity: the zero-length mean is zero; only the limit at infinity is used (PDF p.8). -/
example {H : Type*} [Fintype H] (f : Superop H H) (x : Matrix H H ℂ) :
    dualMean f 0 x = 0 := by
  simp [dualMean]

/-- Sanity: null B events contribute zero, even when their conditional KL is infinite (PDF p.2). -/
example {A B C : Type*} (p : PMF (A × (B × C))) (cond : B → PMF (A × C))
    (b : B) (h : (p.map fun x => x.2.1) b = 0) :
    (if (p.map fun x => x.2.1) b = 0 then (0 : ℝ≥0∞) else
      (p.map fun x => x.2.1) b * discreteMI (cond b)) = 0 := by
  simp [h]

end QAlgorithms.Papers.Independent.Renew46.P35



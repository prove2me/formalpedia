-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
-- name    : LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:33:52.565174+00:00
-- url     : https://prove2.me/theorems/151bcc1e-d442-4ab0-82b7-75b7b16151b1
-- title:
--   LIDT definitions: LDT / Pasting / Defs / Interpolation
-- statement:
--   This bundle defines the outcome data and witnesses for interpolation in the pasting construction. It handles tuple tails and fallback outcomes, extracts genuine slice polynomials, makes eligibility decidable, and reconstructs a global polynomial from enough supported slice values.
--
--   Principal definitions:
--   - `pointTupleTail`: the tail obtained by removing the first coordinate from a slice-question tuple.
--   - `gHatTupleOutcomeTail`: the corresponding tail operation on completed-slice outcomes.
--   - `fallbackInterpolatedPolynomial`: the distinguished fallback polynomial used for the completion outcome.
--   - `extractSlicePoly`: extraction of the genuine polynomial from a genuine slice outcome.
--   - `interpolationEligible_decidablePred`: the decidable eligibility predicate requiring at least `d+1` distinct genuine support values.
--   - `InterpolationSupportWitness`: the witness structure asserting that a suitable support exists.
--   - `interpolationSupportWitness`: construction of the support witness for an eligible tuple.
--   - `interpolateCompletedSlicesFromSupport`: Lagrange interpolation from a specified `d+1`-element support to a polynomial in the successor space.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Defs/Interpolation.lean#L21-L229

-- Generated from MIPStarRE/LDT/Pasting/Defs/Interpolation.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib

namespace LIDT

/-!
# Section 12 — Definitions: interpolation

Interpolation helpers extracted from `Pasting.Defs`.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Remove the first coordinate from a tuple of slice questions. -/
def pointTupleTail {params : Parameters} {k : ℕ}
    (xs : PointTuple params (k + 1)) : PointTuple params k :=
  fun i => xs i.succ

/-- Remove the first coordinate from a tuple of completed slice outcomes. -/
def gHatTupleOutcomeTail {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params (k + 1)) : GHatTupleOutcome params k :=
  fun i => gs i.succ

/-- The distinguished global polynomial `h₀` used for the pasted completion outcome.

It is also the default value on tuples that have already been filtered out of the
actual interpolation path (for example nonglobal tuples after the
`IsGloballyConsistent` restriction).  We take `h₀` to be the zero polynomial, which
trivially satisfies the low-individual-degree bound. -/
noncomputable def fallbackInterpolatedPolynomial (params : Parameters) [FieldModel params.q] :
    Polynomial params.next where
  poly := 0
  lowIndividualDegree := fun i =>
    (MvPolynomial.degreeOf_zero i).trans_le (Nat.zero_le params.d)

/-- Extract the polynomial from a genuine slice outcome. -/
def extractSlicePoly {params : Parameters} {k : ℕ}
    [FieldModel params.q]
    (gs : GHatTupleOutcome params k) (i : Fin k)
    (hi : i ∈ gHatTupleSupport gs) : Polynomial params := by
  have hisSome : (gs i).isSome = true := by
    simpa [gHatTupleSupport] using hi
  exact (gs i).get hisSome

/-- Each Lagrange basis polynomial has degree at most one less than the size of the
interpolation support, without requiring distinct interpolation nodes. -/
private theorem natDegree_lagrangeBasis_le_card_sub_one {K ρ : Type*} [Field K] [DecidableEq ρ]
    {s : Finset ρ} {v : ρ → K} {i : ρ} (hi : i ∈ s) :
    (Lagrange.basis s v i).natDegree ≤ s.card - 1 := by
  rw [Lagrange.basis]
  calc
    (∏ j ∈ s.erase i, Lagrange.basisDivisor (v i) (v j)).natDegree
        ≤ ∑ j ∈ s.erase i, (Lagrange.basisDivisor (v i) (v j)).natDegree := by
          exact _root_.Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ j ∈ s.erase i, 1 := by
          exact Finset.sum_le_sum fun j _ => by
            rw [Lagrange.basisDivisor]
            exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
              (_root_.Polynomial.natDegree_X_sub_C_le _)
    _ = s.card - 1 := by
          simp [Finset.card_erase_of_mem hi]

/-- `InterpolationEligible params` is decidable without invoking classical logic:
it is the finite inequality `d + 1 ≤ |support(gs)|`, where the support is computed
by filtering the finite index set. -/
instance interpolationEligible_decidablePred (params : Parameters) [FieldModel params.q]
    {k : ℕ} : DecidablePred (InterpolationEligible params (k := k)) := by
  intro gs
  unfold InterpolationEligible gHatTupleHammingWeight gHatTupleSupport
  infer_instance

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:473-482`
(interpolation step of the second construction, requiring `|w| \geq d+1`
genuine outcomes).

A `d+1`-element interpolation support together with the proof fields that show it
lies inside the genuine completed-slice support. The support is chosen from the
finite-set existence theorem `Finset.exists_subset_card_eq`. -/
structure InterpolationSupportWitness (params : Parameters) [FieldModel params.q]
    {k : ℕ} (gs : GHatTupleOutcome params k) where
  support : Finset (Fin k)
  subset_support : support ⊆ gHatTupleSupport gs
  card_eq : support.card = params.d + 1

/-- Paper origin: `references/ldt-paper/ld-pasting.tex:473-482`
(interpolation step of the second construction, requiring `|w| \geq d+1`
genuine outcomes).

Construct a `d+1`-point interpolation support inside the genuine support of an
interpolation-eligible tuple.

**Source:** This is the source-faithful finite-support selection required by the
interpolation step cited above; the paper assumes such a support after the
cardinality lower bound is known. -/
noncomputable def interpolationSupportWitness {params : Parameters} {k : ℕ}
    [FieldModel params.q] (gs : GHatTupleOutcome params k)
    (hEligible : InterpolationEligible params gs) :
    InterpolationSupportWitness params gs :=
  let hs := Finset.exists_subset_card_eq (s := gHatTupleSupport gs)
    (n := params.d + 1) (by
      simpa [InterpolationEligible, gHatTupleHammingWeight] using hEligible)
  { support := Classical.choose hs
    subset_support := (Classical.choose_spec hs).1
    card_eq := (Classical.choose_spec hs).2 }

/-- The Lagrange interpolation expression has individual degree at most `d`. -/
 theorem interpolateCompletedSlicesFromSupport_degree
    (params : Parameters) [FieldModel params.q] {k : ℕ} (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) (σ : Finset (Fin k))
    (hσsupport : σ ⊆ gHatTupleSupport gs) (hσcard : σ.card = params.d + 1)
    (coord : Fin params.next.m) :
    MvPolynomial.degreeOf coord
      (∑ idx ∈ σ.attach,
        let slicePoly :=
          MvPolynomial.rename (embedCoord params)
            (extractSlicePoly gs idx.1 (hσsupport idx.2)).poly
        let Li : _root_.Polynomial (Scalar params) :=
          Lagrange.basis σ (fun i => decodeScalar (xs i)) idx.1
        let LiMv := Li.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
        LiMv * slicePoly) ≤ params.d := by
  refine (MvPolynomial.degreeOf_sum_le coord σ.attach _).trans ?_
  refine Finset.sup_le fun idx _hidx => ?_
  let slice : Polynomial params := extractSlicePoly gs idx.1 (hσsupport idx.2)
  let slicePoly : PolynomialModel params.next :=
    MvPolynomial.rename (embedCoord params) slice.poly
  let Li : _root_.Polynomial (Scalar params) :=
    Lagrange.basis σ (fun i => decodeScalar (xs i)) idx.1
  let LiMv : PolynomialModel params.next :=
    Li.eval₂ MvPolynomial.C (MvPolynomial.X (lastCoord params))
  have hLi_natDegree : Li.natDegree ≤ params.d := by
    have hbasis : Li.natDegree ≤ σ.card - 1 := by
      exact natDegree_lagrangeBasis_le_card_sub_one idx.2
    simpa [Li, hσcard] using hbasis
  by_cases hcoord : coord.val < params.m
  · let oldCoord : Fin params.m := ⟨coord.val, hcoord⟩
    have hcoord_eq : embedCoord params oldCoord = coord := by
      ext
      simp [embedCoord, oldCoord]
    have hcoord_ne_last : coord ≠ lastCoord params := by
      rw [← hcoord_eq]
      exact embedCoord_ne_lastCoord params oldCoord
    have hLiMv_zero : MvPolynomial.degreeOf coord LiMv ≤ 0 := by
      have hdeg :=
        (degreeOf_eval₂_C_X_le_natDegree
          (p := Li) (i := coord) (j := lastCoord params))
      rw [if_neg hcoord_ne_last] at hdeg
      exact hdeg
    have hslice : MvPolynomial.degreeOf coord slicePoly ≤ params.d := by
      change MvPolynomial.degreeOf coord
          (MvPolynomial.rename (embedCoord params) slice.poly :
            PolynomialModel params.next) ≤ params.d
      rw [← hcoord_eq, MvPolynomial.degreeOf_rename_of_injective
        (embedCoord_injective params)]
      exact slice.lowIndividualDegree oldCoord
    calc
      MvPolynomial.degreeOf coord (LiMv * slicePoly)
          ≤ MvPolynomial.degreeOf coord LiMv + MvPolynomial.degreeOf coord slicePoly := by
            exact MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ 0 + params.d := Nat.add_le_add hLiMv_zero hslice
      _ = params.d := by simp
  · have hcoord_eq_last : coord = lastCoord params := by
      have hlt_succ : coord.val < params.m + 1 := by
        simpa [Parameters.next] using coord.isLt
      have hle : params.m ≤ coord.val := Nat.le_of_not_gt hcoord
      have hval : coord.val = params.m := le_antisymm (Nat.le_of_lt_succ hlt_succ) hle
      ext
      simp [lastCoord, hval]
    subst coord
    have hLiMv : MvPolynomial.degreeOf (lastCoord params) LiMv ≤ params.d := by
      have hLiMv_nat :
          MvPolynomial.degreeOf (lastCoord params) LiMv ≤ Li.natDegree := by
        have hdeg :=
          (degreeOf_eval₂_C_X_le_natDegree
            (p := Li) (i := lastCoord params) (j := lastCoord params))
        rw [if_pos rfl] at hdeg
        exact hdeg
      exact hLiMv_nat.trans hLi_natDegree
    have hslice_zero : MvPolynomial.degreeOf (lastCoord params) slicePoly ≤ 0 := by
      change MvPolynomial.degreeOf (lastCoord params)
          (MvPolynomial.rename (embedCoord params) slice.poly :
            PolynomialModel params.next) ≤ 0
      rw [degreeOf_rename_embedCoord_lastCoord]
    calc
      MvPolynomial.degreeOf (lastCoord params) (LiMv * slicePoly)
          ≤ MvPolynomial.degreeOf (lastCoord params) LiMv +
              MvPolynomial.degreeOf (lastCoord params) slicePoly := by
            exact MvPolynomial.degreeOf_mul_le _ _ _
      _ ≤ params.d + 0 := Nat.add_le_add hLiMv hslice_zero
      _ = params.d := by simp

/-- Interpolate from a specified `d+1`-element index set to recover
a polynomial in `m+1` variables via Lagrange interpolation.
The caller must provide `hσsupport : σ ⊆ gHatTupleSupport gs`, i.e. every
interpolation node is a genuine completed-slice outcome. This keeps the support
precondition explicit instead of silently falling back to the zero polynomial.

The degree bound (`lowIndividualDegree ≤ d`) holds for any `σ` with
`σ.card = d+1`; the interpolation correctness property (that `restrictAtHeight`
of the result agrees with each slice) additionally requires distinct evaluation
points, which are ensured by the caller together with `hσsupport`.

The coefficient is Mathlib's `Lagrange.basis σ v i`, the polynomial
`∏ j ∈ σ.erase i, (X - v j) / (v i - v j)`, evaluated at the appended
coordinate. -/
noncomputable def interpolateCompletedSlicesFromSupport (params : Parameters)
    [FieldModel params.q] {k : ℕ} (xs : PointTuple params k)
    (gs : GHatTupleOutcome params k) (σ : Finset (Fin k))
    (hσsupport : σ ⊆ gHatTupleSupport gs)
    (hσcard : σ.card = params.d + 1) : Polynomial params.next where
  poly := ∑ idx ∈ σ.attach,
    let slicePoly :=
      MvPolynomial.rename (embedCoord params)
        (extractSlicePoly gs idx.1 (hσsupport idx.2)).poly
    let Li : _root_.Polynomial (Scalar params) :=
      Lagrange.basis σ (fun i => decodeScalar (xs i)) idx.1
    let LiMv :=
      Li.eval₂ MvPolynomial.C
        (MvPolynomial.X (lastCoord params))
    LiMv * slicePoly
  lowIndividualDegree := by
    exact interpolateCompletedSlicesFromSupport_degree params xs gs σ hσsupport hσcard

end MIPStarRE.LDT.Pasting

end

end LIDT



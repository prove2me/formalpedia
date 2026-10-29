-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
-- name    : LIDT_MIPStarRE_LDT_Pasting_Sandwich_GHatSandwich
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:50:10.881656+00:00
-- url     : https://prove2.me/theorems/34bfa6c3-2fd5-4a3c-88cd-448d8af4b74b
-- title:
--   LIDT definitions: LDT / Pasting / Sandwich / GHatSandwich
-- statement:
--   This bundle defines the completed-slice sandwich families and their positivity and truncation properties. It proves positivity and identity domination for Bernoulli tail operators, restricts submeasurements to eligible outcomes, and provides full and half sandwich products for the pasted family.
--
--   Principal definitions:
--   - `binomialOperatorTerm_nonneg`: proves positivity of each binomial operator term.
--   - `bernoulliTailOperator_nonneg`: proves positivity of the Bernoulli tail operator.
--   - `bernoulliTailOperator_le_one`: bounds that operator by the identity.
--   - `gHatSandwichFamily`: defines the full completed-slice sandwich family.
--   - `restrictSubMeas`: restricts a submeasurement to outcomes satisfying a predicate.
--   - `interpolationEligibleSandwichFamily`: keeps only tuples eligible for interpolation.
--   - `gHatHalfSandwichLeft`: defines the left half-sandwich product.
--   - `gHatHalfSandwichRight`: defines the cyclically permuted right half-sandwich product.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean#L24-L284

-- Generated from MIPStarRE/LDT/Pasting/Sandwich/GHatSandwich.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomialEmbedding
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OperatorExpectations
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_PMFUniformAverages
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_SubMeasurementFamilies
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_TensorPlacement
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Tuples
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Sandwich_Switcheroo
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyPolynomialFamilies
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

/-!
# Section 12 — Sandwich constructions: `GHat` sandwich families

Completed-slice sandwich families and restriction helpers.
-/

@[expose] public section

namespace MIPStarRE.LDT.Pasting

open MIPStarRE.LDT
open MIPStarRE.LDT.ExpansionHypercubeGraph
open MIPStarRE.LDT.CommutativityPoints
open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Each binomial term in the Bernoulli tail operator is positive semidefinite. -/
lemma binomialOperatorTerm_nonneg {G : MIPStarRE.Quantum.Op ι} (n r : ℕ)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ (Nat.choose n r : ℂ) • (G ^ r * (1 - G) ^ (n - r)) := by
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  refine smul_nonneg ?_ ?_
  · positivity
  · have hGr : 0 ≤ G ^ r := by
      exact (Matrix.PosSemidef.pow (Matrix.nonneg_iff_posSemidef.mp hG) r).nonneg
    have hIG : 0 ≤ (1 - G) ^ (n - r) := by
      exact
        (Matrix.PosSemidef.pow
          (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hGle)) (n - r)).nonneg
    have hcommPow : Commute (G ^ r) ((1 - G) ^ (n - r)) :=
      (hcomm.pow_left r).pow_right (n - r)
    exact Commute.mul_nonneg hGr hIG hcommPow

/-- Positivity of the Bernoulli tail operator for a PSD contraction. -/
theorem bernoulliTailOperator_nonneg
    (k degree : ℕ) (G : MIPStarRE.Quantum.Op ι)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    0 ≤ bernoulliTailOperator k degree G := by
  unfold bernoulliTailOperator
  refine Finset.sum_nonneg fun r _ => ?_
  simpa using binomialOperatorTerm_nonneg (G := G) k r hG hGle

/-- The Bernoulli tail operator is bounded by the identity for a PSD contraction. -/
theorem bernoulliTailOperator_le_one
    (k degree : ℕ) (G : MIPStarRE.Quantum.Op ι)
    (hG : 0 ≤ G) (hGle : G ≤ 1) :
    bernoulliTailOperator k degree G ≤ 1 := by
  let term : ℕ → MIPStarRE.Quantum.Op ι := fun r =>
    (Nat.choose k r : ℂ) • (G ^ r * (1 - G) ^ (k - r))
  have hsubset : Finset.Icc (degree + 1) k ⊆ Finset.range (k + 1) := by
    intro r hr
    simp only [Finset.mem_Icc, Finset.mem_range] at hr ⊢
    exact Nat.lt_succ_of_le hr.2
  have htail_le_full :
      ∑ r ∈ Finset.Icc (degree + 1) k, term r ≤ ∑ r ∈ Finset.range (k + 1), term r := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro r hrange hrnot
    simpa [term] using binomialOperatorTerm_nonneg (G := G) k r hG hGle
  have hcomm : Commute G (1 - G) :=
    (Commute.one_right G).sub_right (Commute.refl G)
  have hfull :
      ∑ r ∈ Finset.range (k + 1), term r = 1 := by
    calc
      ∑ r ∈ Finset.range (k + 1), term r
          = ∑ r ∈ Finset.range (k + 1), G ^ r * (1 - G) ^ (k - r) * Nat.choose k r := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              let A := G ^ r * (1 - G) ^ (k - r)
              have hcast_comm : Commute (Nat.choose k r : MIPStarRE.Quantum.Op ι) A :=
                Nat.cast_commute (Nat.choose k r) A
              simpa [term, A, Algebra.smul_def] using hcast_comm.eq
      _ = (G + (1 - G)) ^ k := by
            symm
            exact Commute.add_pow hcomm k
      _ = 1 := by simp
  calc
    bernoulliTailOperator k degree G
        = ∑ r ∈ Finset.Icc (degree + 1) k, term r := by
            simp [bernoulliTailOperator, term]
    _ ≤ ∑ r ∈ Finset.range (k + 1), term r := htail_le_full
    _ = 1 := hfull

/-- Concrete family for the full sandwich
`\widehat G^{x_1}_{g_1} \cdots \widehat G^{x_k}_{g_k} \cdots \widehat G^{x_1}_{g_1}`. -/
noncomputable def gHatSandwichFamily (params : Parameters) [FieldModel.{v} params.q]
    (family : IdxPolyFamily.{u, v} params ι) (k : ℕ) :
    IdxSubMeas.{0, v, u} (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs => by
    refine
    { outcome := fun gs =>
        let half := gHatHalfProductOutcomeOperator params family k xs gs
        half * halfᴴ
      total :=
        let half := gHatHalfProductTotalOperator params family k xs
        half * halfᴴ
      outcome_pos := ?_
      sum_eq_total := ?_
      total_le_one := ?_ }
    · intro gs
      simpa using
        (Matrix.posSemidef_self_mul_conjTranspose
          (gHatHalfProductOutcomeOperator params family k xs gs)).nonneg
    · induction k with
      | zero =>
          simp [gHatHalfProductOutcomeOperator, gHatHalfProductTotalOperator]
      | succ k ih =>
          let α := fun _ : Fin (k + 1) => GHatOutcome params
          have hsplit :
              (∑ gs : GHatTupleOutcome params (k + 1),
                  let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                  half * halfᴴ) =
                ∑ p : GHatOutcome params × GHatTupleOutcome params k,
                  (gHatIdxMeas params family (xs 0)).outcome p.1 *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) p.2)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome p.1 := by
            symm
            exact Fintype.sum_equiv (Fin.consEquiv α)
              (fun p =>
                (gHatIdxMeas params family (xs 0)).outcome p.1 *
                  (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) p.2 *
                    (gHatHalfProductOutcomeOperator
                      params family k (pointTupleTail xs) p.2)ᴴ) *
                  (gHatIdxMeas params family (xs 0)).outcome p.1)
              (fun gs =>
                let half := gHatHalfProductOutcomeOperator params family (k + 1) xs gs
                half * halfᴴ)
              (by
                intro p
                have htail :
                    gHatTupleOutcomeTail ((Fin.consEquiv α) p) = p.2 := by
                  funext i
                  rfl
                simp [gHatHalfProductOutcomeOperator, htail,
                  Matrix.conjTranspose_mul,
                  Matrix.mul_assoc, (gHatIdxMeas params family (xs 0)).outcome_hermitian])
          rw [hsplit]
          rw [← Finset.univ_product_univ, Finset.sum_product]
          calc
            ∑ g : GHatOutcome params,
                ∑ gs : GHatTupleOutcome params k,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                      (gHatHalfProductOutcomeOperator
                        params family k (pointTupleTail xs) gs)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g
              = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (∑ gs : GHatTupleOutcome params k,
                      gHatHalfProductOutcomeOperator params family k (pointTupleTail xs) gs *
                        (gHatHalfProductOutcomeOperator
                          params family k (pointTupleTail xs) gs)ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  calc
                    ∑ gs : GHatTupleOutcome params k,
                        (gHatIdxMeas params family (xs 0)).outcome g *
                          (gHatHalfProductOutcomeOperator
                            params family k (pointTupleTail xs) gs *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs)ᴴ) *
                          (gHatIdxMeas params family (xs 0)).outcome g
                      = (∑ gs : GHatTupleOutcome params k,
                          (gHatIdxMeas params family (xs 0)).outcome g *
                            (gHatHalfProductOutcomeOperator
                              params family k (pointTupleTail xs) gs *
                              (gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs)ᴴ)) *
                          (gHatIdxMeas params family (xs 0)).outcome g := by
                            rw [Finset.sum_mul]
                      _ = (gHatIdxMeas params family (xs 0)).outcome g *
                            (∑ gs : GHatTupleOutcome params k,
                              gHatHalfProductOutcomeOperator
                                params family k (pointTupleTail xs) gs *
                                (gHatHalfProductOutcomeOperator
                                  params family k (pointTupleTail xs) gs)ᴴ) *
                            (gHatIdxMeas params family (xs 0)).outcome g := by
                            rw [Matrix.mul_sum]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatHalfProductTotalOperator params family k (pointTupleTail xs) *
                      (gHatHalfProductTotalOperator
                        params family k (pointTupleTail xs))ᴴ) *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  rw [ih (pointTupleTail xs)]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g * 1 *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  simp [gHatHalfProductTotalOperator_eq_one]
            _ = ∑ g : GHatOutcome params,
                  (gHatIdxMeas params family (xs 0)).outcome g *
                    (gHatIdxMeas params family (xs 0)).outcome g := by
                  simp
            _ = ∑ g : GHatOutcome params, (gHatIdxMeas params family (xs 0)).outcome g := by
                  refine Finset.sum_congr rfl ?_
                  intro g _hg
                  exact gHatIdxMeas_proj params family (xs 0) g
            _ = (gHatIdxMeas params family (xs 0)).total := by
                  rw [(gHatIdxMeas params family (xs 0)).sum_eq_total]
            _ = (1 : MIPStarRE.Quantum.Op ι) := by
                  simp [gHatIdxMeas, completeSubMeas]
            _ =
                gHatHalfProductTotalOperator params family (k + 1) xs *
                  (gHatHalfProductTotalOperator params family (k + 1) xs)ᴴ := by
                  simp [gHatHalfProductTotalOperator_eq_one]
    · simp [gHatHalfProductTotalOperator_eq_one]

/-- Restrict a submeasurement to the outcomes satisfying `p`, dropping all other
mass from the total operator. -/
noncomputable def restrictSubMeas {α : Type*} [Fintype α]
    (A : SubMeas α ι) (p : α → Prop) [DecidablePred p] :
    SubMeas α ι := by
  refine
  { outcome := fun a => if p a then A.outcome a else 0
    total := ∑ a ∈ Finset.univ.filter p, A.outcome a
    outcome_pos := ?_
    sum_eq_total := ?_
    total_le_one := ?_ }
  · intro a
    by_cases ha : p a <;> simp [ha, A.outcome_pos a]
  · simp [Finset.sum_filter]
  · calc
      ∑ a ∈ Finset.univ.filter p, A.outcome a ≤ ∑ a : α, A.outcome a := by
        exact Finset.sum_le_univ_sum_of_nonneg
          (s := Finset.univ.filter p)
          (w := fun a => A.outcome_pos a)
      _ = A.total := A.sum_eq_total
      _ ≤ 1 := A.total_le_one



/-- Restrict the sandwiched completed-slice family to tuples with support of size at
least `d + 1`, matching the `|τ| ≥ d+1` filter in the paper before interpolation. -/
noncomputable def interpolationEligibleSandwichFamily (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxSubMeas (PointTuple params k) (GHatTupleOutcome params k) ι :=
  fun xs =>
    restrictSubMeas
      (gHatSandwichFamily params family k xs)
      (InterpolationEligible params)

/-- Concrete family for the half-sandwich product of `k` completed slices. -/
noncomputable def gHatHalfSandwichLeft (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatHalfProductOutcomeOperator params family k xs gs
        total := gHatHalfProductTotalOperator params family k xs
      }

/-- Concrete family for the cyclically permuted half-sandwich product. -/
noncomputable def gHatHalfSandwichRight (params : Parameters) [FieldModel params.q]
    (family : IdxPolyFamily params ι) (k : ℕ) :
    IdxOpFamily (PointTuple params k) (GHatTupleOutcome params k) (ι × ι) :=
  fun xs =>
    OpFamily.leftPlacedOpFamily (ιB := ι) <|
      { outcome := fun gs => gHatRotatedHalfProductOutcomeOperator params family k xs gs
        total := gHatRotatedHalfProductTotalOperator params family k xs
      }

end MIPStarRE.LDT.Pasting

end

end LIDT



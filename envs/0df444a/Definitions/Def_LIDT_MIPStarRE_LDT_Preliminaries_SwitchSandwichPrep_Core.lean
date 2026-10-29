-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:41:11.688104+00:00
-- url     : https://prove2.me/theorems/ade7c144-4f7d-4a11-9c51-c6976d5c8bcd
-- title:
--   LIDT definitions: LDT / Preliminaries / SwitchSandwichPrep / Core
-- statement:
--   This bundle collects the elementary Cauchy-Schwarz, mass, and projection identities used in switch and sandwich estimates. It turns submeasurement and projective-measurement structure into the diagonal-mass and contraction bounds required by later commutativity and pasting proofs.
--
--   Principal definitions:
--   - `weightedFinsetCauchySchwarz`: A weighted finite-sum Cauchy-Schwarz inequality for operator expectations.
--   - `weightedFinsetCauchySchwarz_on_selectedSupport`: The same inequality after restricting the summands to a selected support.
--   - `subMeas_diagMass_le_mass`: The diagonal outcome mass of a submeasurement is at most its total mass.
--   - `subMeas_diagMass_le_one`: On a normalized state, that diagonal mass is at most one.
--   - `projSubMeas_diagMass_eq_mass`: For projective outcomes, the diagonal mass equals the total mass because $P_a^2=P_a$.
--   - `projSubMeas_outcome_mul_total_eq_outcome`: A projective outcome is unchanged when multiplied by the total projector.
--   - `projSubMeas_total_proj`: The total operator of a projective submeasurement is itself a projection.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean#L15-L192

-- Generated from MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/Core.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionAvg
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DistributionUniformSums
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_MeasurementLift
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-! ### Bridge lemmas for `prop:switch-sandwich` -/

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

@[expose] public section

lemma weightedFinsetCauchySchwarz
    {Question Outcome : Type*}
    [Fintype Outcome]
    (𝒟 : Distribution Question)
    (t x y : Question → Outcome → Error)
    (ht : ∀ q a, |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, 0 ≤ x q a)
    (hy : ∀ q a, 0 ≤ y q a) :
    |avgOver 𝒟 (fun q => ∑ a : Outcome, t q a)| ≤
      Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, x q a)) *
        Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
  unfold avgOver
  calc
    |∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, t q a|
      ≤ ∑ q ∈ 𝒟.support, |𝒟.weight q * ∑ a : Outcome, t q a| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ 𝒟.support, 𝒟.weight q * |∑ a : Outcome, t q a| := by
          refine Finset.sum_congr rfl ?_
          intro q _
          rw [abs_mul, abs_of_nonneg (𝒟.nonnegative q)]
    _ ≤ ∑ q ∈ 𝒟.support,
          𝒟.weight q *
            (Real.sqrt (∑ a : Outcome, x q a) *
              Real.sqrt (∑ a : Outcome, y q a)) := by
          refine Finset.sum_le_sum ?_
          intro q _
          have hq :
              |∑ a : Outcome, t q a| ≤
                Real.sqrt (∑ a : Outcome, x q a) *
                  Real.sqrt (∑ a : Outcome, y q a) := by
            calc
              |∑ a : Outcome, t q a|
                ≤ ∑ a : Outcome, |t q a| := by
                    exact Finset.abs_sum_le_sum_abs _ _
              _ ≤ ∑ a : Outcome, Real.sqrt (x q a) * Real.sqrt (y q a) := by
                    refine Finset.sum_le_sum ?_
                    intro a _
                    exact ht q a
              _ ≤ Real.sqrt (∑ a : Outcome, x q a) *
                    Real.sqrt (∑ a : Outcome, y q a) := by
                    exact Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                      (f := fun a => x q a) (g := fun a => y q a)
                      (fun a => hx q a) (fun a => hy q a)
          exact mul_le_mul_of_nonneg_left hq (𝒟.nonnegative q)
    _ = ∑ q ∈ 𝒟.support,
          Real.sqrt (𝒟.weight q * ∑ a : Outcome, x q a) *
            Real.sqrt (𝒟.weight q * ∑ a : Outcome, y q a) := by
          refine Finset.sum_congr rfl ?_
          intro q _
          have hsx : 0 ≤ ∑ a : Outcome, x q a := by
            exact Finset.sum_nonneg fun a _ => hx q a
          have hsy : 0 ≤ ∑ a : Outcome, y q a := by
            exact Finset.sum_nonneg fun a _ => hy q a
          rw [Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, x q a)
                (𝒟.nonnegative q),
              Real.sqrt_mul (x := 𝒟.weight q) (y := ∑ a : Outcome, y q a)
                (𝒟.nonnegative q)]
          ring_nf
          rw [Real.sq_sqrt (𝒟.nonnegative q)]
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ ≤ Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, y q a) := by
            exact Real.sum_sqrt_mul_sqrt_le (s := 𝒟.support)
              (f := fun q => 𝒟.weight q * ∑ a : Outcome, x q a)
              (g := fun q => 𝒟.weight q * ∑ a : Outcome, y q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hx q a)
              (fun q =>
                mul_nonneg (𝒟.nonnegative q) <|
                  Finset.sum_nonneg fun a _ => hy q a)
    _ = Real.sqrt (∑ q ∈ 𝒟.support, 𝒟.weight q * ∑ a : Outcome, x q a) *
          Real.sqrt (avgOver 𝒟 (fun q => ∑ a : Outcome, y q a)) := by
            rfl

/-- Weighted finite Cauchy--Schwarz with the summand restricted to a selected
support.

The statement is the ordinary weighted finite Cauchy--Schwarz inequality
applied to the zero-extension of `t`, `x`, and `y` away from `selected`. -/
lemma weightedFinsetCauchySchwarz_on_selectedSupport
    {Question Outcome : Type*} [Fintype Outcome]
    (𝒟 : Distribution Question)
    (selected : Question → Outcome → Prop)
    [∀ q a, Decidable (selected q a)]
    (t x y : Question → Outcome → Error)
    (ht :
      ∀ q a, selected q a →
        |t q a| ≤ Real.sqrt (x q a) * Real.sqrt (y q a))
    (hx : ∀ q a, selected q a → 0 ≤ x q a)
    (hy : ∀ q a, selected q a → 0 ≤ y q a) :
    |avgOver 𝒟 (fun q =>
      ∑ a : Outcome, if selected q a then t q a else 0)| ≤
      Real.sqrt
        (avgOver 𝒟 (fun q =>
          ∑ a : Outcome, if selected q a then x q a else 0)) *
      Real.sqrt
        (avgOver 𝒟 (fun q =>
          ∑ a : Outcome, if selected q a then y q a else 0)) := by
  refine weightedFinsetCauchySchwarz
    𝒟
    (fun q a => if selected q a then t q a else 0)
    (fun q a => if selected q a then x q a else 0)
    (fun q a => if selected q a then y q a else 0)
    ?_ ?_ ?_
  · intro q a
    by_cases hsel : selected q a
    · simpa [hsel] using ht q a hsel
    · simp [hsel]
  · intro q a
    by_cases hsel : selected q a
    · simpa [hsel] using hx q a hsel
    · simp [hsel]
  · intro q a
    by_cases hsel : selected q a
    · simpa [hsel] using hy q a hsel
    · simp [hsel]

/-- The diagonal mass of a sub-measurement is bounded by its total mass. -/
lemma subMeas_diagMass_le_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_le_sum ?_
          intro a _
          exact ev_mono ψ _ _ <|
            MIPStarRE.Quantum.sq_le_self
                  (A.outcome_pos a) (A.outcome_le_one a)
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- The diagonal mass of a sub-measurement is at most `1` on a normalized state. -/
lemma subMeas_diagMass_le_one
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized) (A : SubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) ≤ 1 := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      ≤ ev ψ A.total := subMeas_diagMass_le_mass ψ A
    _ ≤ ev ψ (1 : MIPStarRE.Quantum.Op ι) := by
          exact ev_mono ψ _ _ A.total_le_one
    _ = 1 := ev_one_of_isNormalized ψ hψ

/-- Projective outcomes satisfy `P_a^2 = P_a`, so diagonal mass equals total mass. -/
lemma projSubMeas_diagMass_eq_mass
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (A : ProjSubMeas Outcome ι) :
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a) = ev ψ A.total := by
  calc
    ∑ a : Outcome, ev ψ (A.outcome a * A.outcome a)
      = ∑ a : Outcome, ev ψ (A.outcome a) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          simp [A.proj a]
    _ = ev ψ A.total := by
          rw [← ev_sum ψ A.outcome, A.sum_eq_total]

/-- Each projective outcome is absorbed by the total projector. -/
lemma projSubMeas_outcome_mul_total_eq_outcome
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) (a : Outcome) :
    A.outcome a * A.total = A.outcome a := by
  simpa using ProjSubMeas.outcome_mul_total_eq_outcome A a

/-- The total operator of a projective sub-measurement is itself a projector. -/
lemma projSubMeas_total_proj
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (A : ProjSubMeas Outcome ι) :
    A.total * A.total = A.total := by
  simpa using ProjSubMeas.total_proj A







end

end MIPStarRE.LDT.Preliminaries

end LIDT



-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_CompletionTransfer
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:54:20.674515+00:00
-- url     : https://prove2.me/theorems/c7b226e0-6a91-41f1-9d40-4b2028fd8cab
-- title:
--   LIDT definitions: LDT / Preliminaries / CompletionTransfer
-- statement:
--   This bundle provides transfer principles for state-dependent operator distance and for completing submeasurements. It supports replacing intermediate raw operator families, chaining several approximations, and passing from incomplete outcome families to completed measurements.
--
--   Principal definitions:
--   - `sddOpRel_triangle`: State-dependent operator distance satisfies the triangle inequality under a common question distribution.
--   - `sddOpRel_mono`: An SDD operator relation remains true when its error bound is increased.
--   - `questionSDDOp_chain`: A questionwise chain of raw operator families has squared distance bounded by the chain length times the sum of its edge squared distances.
--   - `sddOpRel_chain`: The averaged SDD operator relation for an $n$-step chain, obtained by Cauchy-Schwarz from the questionwise estimate.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean#L260-L378

-- Generated from MIPStarRE/LDT/Preliminaries/CompletionTransfer.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Completion
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_BipartiteSelfConsistency_Local
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_ComparisonCore
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_DistanceBounds
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichMain_Completeness
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_ApproxDelta
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_QuantumNonneg
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_BlockDiagonal
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Order
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_TracePairing
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Preliminary comparison theorems: completion and chain rules

Completion lemmas and final chain inequalities from the preliminaries chapter.
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT








/-- Triangle inequality for state-dependent operator distance. -/
lemma sddOpRel_triangle
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B C : IdxOpFamily Question Outcome ι) (δ₁ δ₂ : Error) :
    SDDOpRel ψ 𝒟 A B δ₁ →
    SDDOpRel ψ 𝒟 B C δ₂ →
    SDDOpRel ψ 𝒟 A C (2 * (δ₁ + δ₂)) :=
  stateDependentDistanceOpRel_triangle ψ 𝒟 A B C δ₁ δ₂

/-- Monotonicity for `SDDOpRel`. -/
lemma sddOpRel_mono
    {Question Outcome : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Outcome]
    (ψ : QuantumState ι) (𝒟 : Distribution Question)
    (A B : IdxOpFamily Question Outcome ι) (δ δ' : Error) :
    SDDOpRel ψ 𝒟 A B δ → δ ≤ δ' → SDDOpRel ψ 𝒟 A B δ' := by
  intro h hle
  exact stateDependentDistanceOpRel_mono ψ 𝒟 A B δ δ' hle h

/-- Questionwise n-step chain bound: the squared distance between the
first and last operator family telescopes and is bounded by
`n * ∑ individual squared distances` via `ev_sum_conjTranspose_mul_sum_le`. -/
private lemma questionSDDOp_chain
    {Outcome : Type*} {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Outcome]
    (ψ : QuantumState ι) (n : ℕ)
    (families : Fin (n + 1) → OpFamily Outcome ι) :
    qSDDOp ψ (families 0) (families (Fin.last n)) ≤
      (n : ℝ) * ∑ i : Fin n,
        qSDDOp ψ (families i.castSucc) (families i.succ) := by
  -- Define the per-step difference operators
  let D : Fin n → Outcome → MIPStarRE.Quantum.Op ι := fun i a =>
    (families i.castSucc).outcome a - (families i.succ).outcome a
  -- Telescoping: total difference = sum of step differences
  have htelescope : ∀ a,
      (families 0).outcome a - (families (Fin.last n)).outcome a =
        ∑ i : Fin n, D i a := by
    intro a
    change (families 0).outcome a -
        (families (Fin.last n)).outcome a =
      ∑ i : Fin n, ((families i.castSucc).outcome a -
        (families i.succ).outcome a)
    rw [Finset.sum_sub_distrib, sub_eq_sub_iff_add_eq_add]
    exact (Fin.sum_univ_succ
      (fun j => (families j).outcome a)).symm.trans
      (Fin.sum_univ_castSucc
        (fun j => (families j).outcome a))
  unfold qSDDOp qSDDCore
  calc ∑ a : Outcome,
        ev ψ (((families 0).outcome a -
            (families (Fin.last n)).outcome a)ᴴ *
          ((families 0).outcome a -
            (families (Fin.last n)).outcome a))
      = ∑ a, ev ψ ((∑ i : Fin n, D i a)ᴴ *
          (∑ i : Fin n, D i a)) := by
        exact Finset.sum_congr rfl fun a _ => by
          rw [htelescope a]
    _ ≤ ∑ a, ((n : ℝ) * ∑ i : Fin n,
          ev ψ ((D i a)ᴴ * D i a)) := by
        refine Finset.sum_le_sum fun a _ => ?_
        have := ev_sum_conjTranspose_mul_sum_le ψ
          (fun i => D i a)
        rwa [Fintype.card_fin] at this
    _ = (n : ℝ) * ∑ i : Fin n, ∑ a,
          ev ψ ((D i a)ᴴ * D i a) := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm

/-- n-step SDDOpRel chain lemma via vector Cauchy-Schwarz.

Given `n` consecutive SDDOpRel bounds, the endpoints satisfy an SDDOpRel
bound with error `n * (∑ individual errors)`.  This improves on naive
triangle-inequality chaining, which would give exponential blowup.

Paper reference: `prop:triangle-inequality-for-approx_delta` in
`references/ldt-paper/preliminaries.tex`.

Proof sketch: telescoping + `‖∑ dᵢ|ψ⟩‖² ≤ n · ∑ ‖dᵢ|ψ⟩‖²`
(vector Cauchy-Schwarz / norm triangle inequality). -/
lemma sddOpRel_chain
    {Question Outcome : Type*} {ι' : Type*}
    [Fintype ι'] [DecidableEq ι'] [Fintype Outcome]
    (ψ : QuantumState ι') (𝒟 : Distribution Question)
    (n : ℕ)
    (families : Fin (n + 1) → IdxOpFamily Question Outcome ι')
    (errors : Fin n → Error)
    (hsteps : ∀ i : Fin n,
      SDDOpRel ψ 𝒟 (families i.castSucc) (families i.succ)
        (errors i)) :
    SDDOpRel ψ 𝒟 (families 0) (families (Fin.last n))
      ((n : Error) * ∑ i : Fin n, errors i) := by
  constructor
  unfold sddErrorOp at *
  -- Lift the questionwise chain bound through avgOver
  calc avgOver 𝒟 (fun q =>
        qSDDOp ψ (families 0 q) (families (Fin.last n) q))
      ≤ avgOver 𝒟 (fun q => (n : ℝ) * ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        exact avgOver_mono 𝒟 _ _ fun q =>
          questionSDDOp_chain ψ n (fun j => families j q)
    _ = (n : ℝ) * avgOver 𝒟 (fun q => ∑ i : Fin n,
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        rw [avgOver_const_mul]
    _ = (n : ℝ) * ∑ i : Fin n, avgOver 𝒟 (fun q =>
          qSDDOp ψ (families i.castSucc q)
            (families i.succ q)) := by
        congr 1
        simp only [avgOver, Finset.mul_sum]
        exact Finset.sum_comm
    _ ≤ (n : ℝ) * ∑ i : Fin n, errors i := by
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun i _ =>
            (hsteps i).squaredDistanceBound)
          (Nat.cast_nonneg n)


end MIPStarRE.LDT.Preliminaries

end

end LIDT



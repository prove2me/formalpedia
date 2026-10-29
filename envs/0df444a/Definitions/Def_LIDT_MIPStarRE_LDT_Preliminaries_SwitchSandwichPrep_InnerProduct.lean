-- Prove2me | Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
-- name    : LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_InnerProduct
-- status  : Definition
-- author  : @Dengnifer
-- created : 2026-10-27T11:42:49.443337+00:00
-- url     : https://prove2.me/theorems/21d58c08-05b4-4e34-825c-84dd79bb996e
-- title:
--   LIDT definitions: LDT / Preliminaries / SwitchSandwichPrep / InnerProduct
-- statement:
--   This bundle supplies the average square-root and one-sided inner-product comparison facts used in switch-sandwich preparation.
--
--   Principal definitions:
--   - `avgOver_abs_le_sqrt_of_pointwise`: bounds an average absolute value by an averaged square-root control.
--   - `closenessOfInnerProduct_left`: controls replacement of the left operator family.
--   - `closenessOfInnerProduct_right`: controls replacement of the right operator family.
--
--   Formalization credit: Sirui Lu, Ruixuan Deng, Yanqiao Zhu, and Zhengfeng Ji (arXiv:2609.19814). Mathematical source: Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright, and Henry Yuen (arXiv:2009.12982).
-- source:
--   https://github.com/LionSR/MIPStarRE/blob/f382c801026f53a9efc260fdee707cb35e0adb15/MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/InnerProduct.lean#L25-L279

-- Generated from MIPStarRE/LDT/Preliminaries/SwitchSandwichPrep/InnerProduct.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_SwitchSandwichPrep_Core
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

open scoped _root_.Matrix

namespace LIDT

namespace MIPStarRE.LDT.Preliminaries
end MIPStarRE.LDT.Preliminaries

/-!
# Switch-sandwich preparation: inner-product bounds

Cauchy–Schwarz-style inner-product bounds in the `avgOver` formulation used by
the switch-sandwich argument.

## References

- `references/ldt-paper/preliminaries.tex`, `prop:switch-sandwich`
- `blueprint/src/chapter/ch03_preliminaries.tex`
-/

@[expose] public section

open scoped BigOperators MatrixOrder _root_.Matrix ComplexOrder

namespace MIPStarRE.LDT.Preliminaries

open MIPStarRE.LDT

lemma avgOver_abs_le_sqrt_of_pointwise
    {Question : Type*}
    (𝒟 : Distribution Question) (f g : Question → Error)
    (hf : ∀ q, |f q| ≤ Real.sqrt (g q))
    (hg : ∀ q, 0 ≤ g q)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1) :
    |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 g) := by
  have hcs :=
    weightedFinsetCauchySchwarz
      (Question := Question) (Outcome := Unit) 𝒟
      (t := fun q _ => f q)
      (x := fun q _ => g q)
      (y := fun _ _ => 1)
      (ht := by
        intro q _
        simpa using hf q)
      (hx := by
        intro q _
        exact hg q)
      (hy := by
        intro _ _
        positivity)
  have hmass : avgOver 𝒟 (fun _ => (1 : Error)) ≤ 1 := by
    simpa [avgOver] using h𝒟
  have hsqrt_mass : Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hmass
  calc
    |avgOver 𝒟 f|
      ≤ Real.sqrt (avgOver 𝒟 g) *
          Real.sqrt (avgOver 𝒟 (fun _ => (1 : Error))) := by
            simpa using hcs
    _ ≤ Real.sqrt (avgOver 𝒟 g) * 1 := by
          exact mul_le_mul_of_nonneg_left hsqrt_mass (Real.sqrt_nonneg _)
    _ = Real.sqrt (avgOver 𝒟 g) := by ring

/-- `ev` is invariant under taking adjoints. -/
private lemma ev_adjoint_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : QuantumState ι) (X : MIPStarRE.Quantum.Op ι) :
    ev ψ Xᴴ = ev ψ X := by
  have hρ : ψ.densityᴴ = ψ.density :=
    (Matrix.nonneg_iff_posSemidef.mp ψ.density_psd).isHermitian.eq
  have htrace :
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ) =
        star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
    calc
      MIPStarRE.Quantum.normalizedTrace (ψ.density * Xᴴ)
        = MIPStarRE.Quantum.normalizedTrace ((X * ψ.density)ᴴ) := by
            rw [Matrix.conjTranspose_mul, hρ]
      _ = star (MIPStarRE.Quantum.normalizedTrace (X * ψ.density)) := by
            unfold MIPStarRE.Quantum.normalizedTrace
            simpa [star_div₀, star_natCast] using
              congrArg (fun z : ℂ => z / (Fintype.card ι : ℂ))
                (Matrix.trace_conjTranspose (X * ψ.density))
      _ = star (MIPStarRE.Quantum.normalizedTrace (ψ.density * X)) := by
            rw [MIPStarRE.Quantum.normalizedTrace_mul_comm]
  simpa [ev, Complex.star_def, Complex.conj_re] using congrArg Complex.re htrace

/-- `prop:closeness-of-ip`, left-action clause `eq:closeness3`. -/
theorem closenessOfInnerProduct_left
    {Question OutcomeA OutcomeB : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB : avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, (∑ b : OutcomeB, C q a b) * (∑ b : OutcomeB, C q a b)ᴴ) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      ≤ Real.sqrt γ := by
  have hpointwise :
      ∀ q,
        |(∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)| ≤
          Real.sqrt (qSDDCore ψ (A q) (B q)) := by
    intro q
    let Csum : OutcomeA → MIPStarRE.Quantum.Op ι := fun a => ∑ b : OutcomeB, C q a b
    let D : OutcomeA → MIPStarRE.Quantum.Op ι := fun a => A q a - B q a
    have haux :
        |∑ a : OutcomeA, ev ψ (Csum a * D a)| ≤
          Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
            Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
      calc
        |∑ a : OutcomeA, ev ψ (Csum a * D a)|
          ≤ ∑ a : OutcomeA, |ev ψ (Csum a * D a)| := by
              exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ a : OutcomeA,
              Real.sqrt (ev ψ (Csum a * (Csum a)ᴴ)) *
                Real.sqrt (ev ψ ((D a)ᴴ * D a)) := by
              refine Finset.sum_le_sum ?_
              intro a _
              exact ev_abs_mul_le_sqrt ψ (Csum a) (D a)
        _ ≤ Real.sqrt
              (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
            Real.sqrt
              (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              exact
                Real.sum_sqrt_mul_sqrt_le (s := Finset.univ)
                  (f := fun a => ev ψ (Csum a * (Csum a)ᴴ))
                  (g := fun a => ev ψ ((D a)ᴴ * D a))
                  (fun a => by
                    simpa using ev_adjoint_self_nonneg ψ ((Csum a)ᴴ))
                  (fun a => ev_adjoint_self_nonneg ψ (D a))
    have hCsum_le_one :
        ∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ) ≤ 1 := by
      calc
        ∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)
          = ev ψ (∑ a : OutcomeA, Csum a * (Csum a)ᴴ) := by
              rw [← ev_sum ψ (fun a : OutcomeA => Csum a * (Csum a)ᴴ)]
        _ ≤ ev ψ 1 := ev_mono ψ _ _ (hC q)
        _ = 1 := ev_one_of_isNormalized ψ hψ
    have hsqrt_C :
        Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) ≤ 1 := by
      simpa using Real.sqrt_le_sqrt hCsum_le_one
    have haux' :
        |∑ a : OutcomeA, ev ψ (Csum a * D a)| ≤
          Real.sqrt (qSDDCore ψ (A q) (B q)) := by
      calc
        |∑ a : OutcomeA, ev ψ (Csum a * D a)|
          ≤ Real.sqrt (∑ a : OutcomeA, ev ψ (Csum a * (Csum a)ᴴ)) *
              Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := haux
        _ ≤ 1 * Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              exact mul_le_mul_of_nonneg_right hsqrt_C (Real.sqrt_nonneg _)
        _ = Real.sqrt (∑ a : OutcomeA, ev ψ ((D a)ᴴ * D a)) := by
              ring
        _ = Real.sqrt (qSDDCore ψ (A q) (B q)) := by
              simp [qSDDCore, D]
    convert haux' using 1
    refine congrArg abs ?_
    have hleft :
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a) =
          ∑ a : OutcomeA, ev ψ (Csum a * A q a) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [← ev_sum ψ (fun b : OutcomeB => C q a b * A q a), Finset.sum_mul]
    have hright :
        ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a) =
          ∑ a : OutcomeA, ev ψ (Csum a * B q a) := by
      refine Finset.sum_congr rfl ?_
      intro a _
      rw [← ev_sum ψ (fun b : OutcomeB => C q a b * B q a), Finset.sum_mul]
    rw [hleft, hright, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [(ev_sub ψ (Csum a * A q a) (Csum a * B q a)).symm]
    simp [Csum, D, mul_sub]
  have hsdd_nonneg :
      ∀ q, 0 ≤ qSDDCore ψ (A q) (B q) := by
    intro q
    unfold qSDDCore
    exact Finset.sum_nonneg fun a _ => ev_adjoint_self_nonneg ψ (A q a - B q a)
  let f : Question → Error := fun q =>
    (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)
  have hf :
      |avgOver 𝒟 f| ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := by
    exact
      avgOver_abs_le_sqrt_of_pointwise 𝒟 f
        (fun q => qSDDCore ψ (A q) (B q))
        (by
          intro q
          simpa [f] using hpointwise q)
        hsdd_nonneg
        h𝒟
  have havg_sub :
      avgOver 𝒟 f =
        avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
          avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a)) := by
    unfold avgOver f
    rw [show
      (∑ x ∈ 𝒟.support,
          𝒟.weight x *
            ((∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * A x a)) -
              ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * B x a))) =
        ∑ x ∈ 𝒟.support,
          (𝒟.weight x * (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * A x a)) -
            𝒟.weight x * (∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C x a b * B x a))) by
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring]
    rw [Finset.sum_sub_distrib]
  have havg_nonneg :
      0 ≤ avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q)) := by
    exact avgOver_nonneg 𝒟 _ hsdd_nonneg
  calc
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * A q a)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (C q a b * B q a))|
      = |avgOver 𝒟 f| := by
            rw [havg_sub]
    _ ≤ Real.sqrt (avgOver 𝒟 (fun q => qSDDCore ψ (A q) (B q))) := hf
    _ ≤ Real.sqrt γ := by
          simpa using Real.sqrt_le_sqrt hAB

/-- `prop:closeness-of-ip`, right-action clause `eq:closeness4`. -/
theorem closenessOfInnerProduct_right
    {Question OutcomeA OutcomeB : Type*}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype OutcomeA] [Fintype OutcomeB]
    (ψ : QuantumState ι) (hψ : ψ.IsNormalized)
    (𝒟 : Distribution Question)
    (h𝒟 : ∑ q ∈ 𝒟.support, 𝒟.weight q ≤ 1)
    (A B : Question → OutcomeA → MIPStarRE.Quantum.Op ι)
    (C : Question → OutcomeA → OutcomeB → MIPStarRE.Quantum.Op ι)
    (γ : Error)
    (hAB :
      avgOver 𝒟
        (fun q => qSDDCore ψ (fun a : OutcomeA => (A q a)ᴴ) (fun a : OutcomeA => (B q a)ᴴ))
        ≤ γ)
    (hC :
      ∀ q,
        (∑ a : OutcomeA, (∑ b : OutcomeB, C q a b)ᴴ * (∑ b : OutcomeB, C q a b)) ≤ 1) :
    |avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) -
      avgOver 𝒟 (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b))|
      ≤ Real.sqrt γ := by
  have hleft :=
    closenessOfInnerProduct_left ψ hψ 𝒟 h𝒟
      (fun q a => (A q a)ᴴ)
      (fun q a => (B q a)ᴴ)
      (fun q a b => (C q a b)ᴴ)
      γ hAB (by
        intro q
        simpa [Matrix.conjTranspose_sum] using hC q)
  have hA :
      avgOver 𝒟
          (fun q =>
            ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (A q a)ᴴ)) =
        avgOver 𝒟
          (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (A q a * C q a b)) := by
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    simpa [Matrix.conjTranspose_mul] using ev_adjoint_eq ψ (A q a * C q a b)
  have hB :
      avgOver 𝒟
          (fun q =>
            ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ ((C q a b)ᴴ * (B q a)ᴴ)) =
        avgOver 𝒟
          (fun q => ∑ a : OutcomeA, ∑ b : OutcomeB, ev ψ (B q a * C q a b)) := by
    apply avgOver_congr
    intro q
    refine Finset.sum_congr rfl ?_
    intro a _
    refine Finset.sum_congr rfl ?_
    intro b _
    simpa [Matrix.conjTranspose_mul] using ev_adjoint_eq ψ (B q a * C q a b)
  simpa [hA, hB] using hleft

end MIPStarRE.LDT.Preliminaries

end

end LIDT



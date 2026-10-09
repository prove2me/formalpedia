-- Prove2me | Definitions.Def_OAIHecke78B002
-- name    : OAIHecke78B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T20:18:25.456736+00:00
-- url     : https://prove2.me/theorems/d84fe4d1-8ae2-48d7-9b8f-7a018dba4af2
-- title:
--   OpenAI Hecke 7/8 split, definitions bundle 4 of 29
-- statement:
--   Definitions bundle 4 of 29 of the split of OpenAI's proof that finite-order Hecke $L$-functions over $\mathbb{Q}(\zeta_3)$ do not vanish for $\operatorname{Re} s > 7/8$: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/NumberTheory/DirichletL` (OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane $\operatorname{Re} s > 7/8$*, September 30, 2026, family 003 of [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (definitions that choose witnesses of existence theorems or build structures carrying proofs need those proofs) and the instances and attribute-tagged lemmas of the same modules.
--
--   It imports the bundles `OAIHecke78B001` of this split, and through them their definitions. It also imports wurtle's published bundle `HeckeSevenEighths` (the comparator definitions of OpenAI's challenge statement: `Character`, `LFunction` and the theta-function pairs they are built from), which OpenAI's development defines identically.
--
--   Modules: `GaussSum.ThetaLocalRows`, `GaussSum.CubicTrace`, `GaussSum.MixedConversion`, `GaussSum.SquarePhaseFactorization`, `QuadraticSieve.CrossSeparation`, `Arithmetic.IdealMobius`, `GaussSum.CompletedExpansion`, `GaussSum.RayCharacters`, `QuadraticSieve.CoefficientCancellation`, `QuadraticSieve.InitialBound`, `Mellin.ReflectedKernel`, `Arithmetic.SquarefreeDivisors`, `QuadraticSieve.MainTermDifference`, `Reciprocity.CubicJacobi`, `CubicSieve.NormalizedMass`, `CubicSieve.Initial`, `CubicSieve.Gcd`, `CubicSieve.Smoothed`, `CubicSieve.ZeroMode`, `Descent.Completion`, `Descent.DivisorSum`, `Descent.FirstCommonProfile`, `Descent.GeneratorTransport`, `Descent.ReopenedBins`, `Descent.SecondNormalizedEnergy`, `Detector.Completed`, `IdealLogDerivative`, `Detector.ContourShear`, `Detector.LowInverseEnergy`, `GaussianTheta`, `Hecke.DetectorProfilesCutoffs`, `Moments.Primary`, `Moments.Rectangle`, `Moments.MobiusRegroup`, `Moments.DivisorAllocation`, `Moments.DivisorExtraction`, `Moments.Active`, `Moments.Cauchy`, `Moments.RankinRadical`, `Moments.ChildAssembly`, `Inversion.InitialCanonicalState`, `Inversion.TerminalWidths`, `Moments.AddedZero`, `Moments.AddedZeroUniform`, `Moments.SourceProfileMass`, `Moments.CommonProfile`, `Moments.RemainingBox`, `Moments.AmplificationLiveMask`, `Moments.CommonAllowance`, `Moments.CommonHarmonicMass`, `Moments.CommonRadicalHarmonicMass`, `Moments.CommonRawScale`, `Moments.DivisorTensor`, `Moments.DivisorRectangle`, `Moments.DivisorRaw`, `Moments.DivisorWitness`, `Moments.NaturalPrimitive`, `Moments.PrimeElements`, `Moments.SecondBlockRadicalHarmonicMass`, `Moments.UncenteredTerminal`, `PrimeLogProfile`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission. Comments are removed; no statement of OpenAI's was changed.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B001

/-!
# OpenAI Hecke 7/8 split: definitions bundle OAIHecke78B002

OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane
Re s > 7/8*, OpenAI Math Release, September 30, 2026, https://github.com/openai/math (family 003;
Lean in `lean/OAI/NumberTheory/DirichletL`, Apache License 2.0; vendored modules of
PrimeNumberTheoremAnd and rellich-kondrachov). Carved from the port to Lean 4.33.1 / Mathlib
0df444a, comments removed. Modules:
  GaussSum.ThetaLocalRows
  GaussSum.CubicTrace
  GaussSum.MixedConversion
  GaussSum.SquarePhaseFactorization
  QuadraticSieve.CrossSeparation
  Arithmetic.IdealMobius
  GaussSum.CompletedExpansion
  GaussSum.RayCharacters
  QuadraticSieve.CoefficientCancellation
  QuadraticSieve.InitialBound
  Mellin.ReflectedKernel
  Arithmetic.SquarefreeDivisors
  QuadraticSieve.MainTermDifference
  Reciprocity.CubicJacobi
  CubicSieve.NormalizedMass
  CubicSieve.Initial
  CubicSieve.Gcd
  CubicSieve.Smoothed
  CubicSieve.ZeroMode
  Descent.Completion
  Descent.DivisorSum
  Descent.FirstCommonProfile
  Descent.GeneratorTransport
  Descent.ReopenedBins
  Descent.SecondNormalizedEnergy
  Detector.Completed
  IdealLogDerivative
  Detector.ContourShear
  Detector.LowInverseEnergy
  GaussianTheta
  Hecke.DetectorProfilesCutoffs
  Moments.Primary
  Moments.Rectangle
  Moments.MobiusRegroup
  Moments.DivisorAllocation
  Moments.DivisorExtraction
  Moments.Active
  Moments.Cauchy
  Moments.RankinRadical
  Moments.ChildAssembly
  Inversion.InitialCanonicalState
  Inversion.TerminalWidths
  Moments.AddedZero
  Moments.AddedZeroUniform
  Moments.SourceProfileMass
  Moments.CommonProfile
  Moments.RemainingBox
  Moments.AmplificationLiveMask
  Moments.CommonAllowance
  Moments.CommonHarmonicMass
  Moments.CommonRadicalHarmonicMass
  Moments.CommonRawScale
  Moments.DivisorTensor
  Moments.DivisorRectangle
  Moments.DivisorRaw
  Moments.DivisorWitness
  Moments.NaturalPrimitive
  Moments.PrimeElements
  Moments.SecondBlockRadicalHarmonicMass
  Moments.UncenteredTerminal
  PrimeLogProfile
-/

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology

namespace ActualEisensteinCubic

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_fixed_kernel_eq_dualFixedTerm
    (a b k l : ℤ) (η : ℝ) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let y : O := dualFrequencyEquiv (k,l)
    Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) *
      fixedDualPhase c y =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) (k,l) := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let y : O := dualFrequencyEquiv (k,l)
  have hnormC : ((‖eisEmbedding y‖ : ℂ)^2) =
      (((k^2+k*l+l^2 : ℤ) : ℂ)) := by
    exact_mod_cast dualFrequencyEquiv_norm_sq k l
  have hreal : Complex.exp (-(Real.pi : ℂ) *
        (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
        (‖eisEmbedding y‖ ^ 2 : ℂ)) =
      (OscSpecial.dualAmp η (a : ℝ) (b : ℝ) (k,l) : ℂ) := by
    rw [hnormC]
    dsimp [OscSpecial.dualAmp, OscSpecial.dualScale, OscSpecial.dualQ]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hphase : fixedDualPhase c y =
      Complex.exp (Complex.I *
        (OscSpecial.phaseAngle (a : ℝ) (b : ℝ) (k,l) : ℂ)) := by
    have h := breveE_dual_quadratic_real_scale 1 a b k l
    have harg : fixedDualPhase c y =
        Complex.exp (-(2 * Real.pi * Complex.I *
          (((a-b)*k^2+2*a*k*l+b*l^2 : ℤ) : ℂ)) / (4 : ℂ)) := by
      change ShortDraftTrace.breveE
        (eisEmbedding (-(ActualEisensteinCoordinates.eval a b *
          (ActualEisensteinCoordinates.eval (k+l) k)^2)) /
          eisLam / (4 : ℂ)) = _
      simpa using h
    rw [harg]
    congr 1
    dsimp [OscSpecial.phaseAngle, OscSpecial.dualTrace]
    push_cast
    ring
  dsimp only
  rw [hreal, hphase]
  rfl

open EisensteinEmbedding ConcreteTraceCRT Complex
open scoped Topology
open Filter

noncomputable def actualVariableDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  ShortDraftTrace.breveE
    (eisEmbedding (-(ActualEisensteinCoordinates.eval a b * y^2)) /
      eisLam /
      ((4 * OscSpecial.r η (a : ℝ) (b : ℝ) : ℝ) : ℂ))

noncomputable def actualFixedDualKernel (a b : ℤ) (η : ℝ) (y : O) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) *
    (OscSpecial.dualScale η (a : ℝ) (b : ℝ) : ℂ) *
    (‖eisEmbedding y‖ ^ 2 : ℂ)) *
  fixedDualPhase (ActualEisensteinCoordinates.eval a b) y

theorem dualScale_cast (η a b : ℝ) :
    (OscSpecial.dualScale η a b : ℂ) =
      (η : ℂ) * (OscSpecial.q a b : ℂ) /
        (4 * (OscSpecial.r η a b : ℂ)) := by
  dsimp [OscSpecial.dualScale]
  push_cast
  ring

theorem actual_variable_kernel_eq_dualVarTerm
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) (z : ℤ × ℤ) :
    actualVariableDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have h := (dual_gaussian_is_actual_trace_phase
    a b z.1 z.2 hc η hη).symm.trans
      (OscSpecial.dualGaussian_eq_dualVarTerm hη hq z)
  unfold actualVariableDualKernel
  rw [dualScale_cast]
  exact h

theorem actual_fixed_kernel_eq_dualFixedTerm_point
    (a b : ℤ) (η : ℝ) (z : ℤ × ℤ) :
    actualFixedDualKernel a b η (dualFrequencyEquiv z) =
      OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
  rcases z with ⟨k,l⟩
  exact actual_fixed_kernel_eq_dualFixedTerm a b k l η

theorem actual_dual_phase_error_tendsto_zero
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    Tendsto
      (fun η : ℝ => η * ‖
        (∑' y : O, actualVariableDualKernel a b η y) -
        (∑' y : O, actualFixedDualKernel a b η y)‖)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  have hbase := OscSpecial.normalized_dual_phase_sum_error_tendsto_zero hq
  apply hbase.congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  have hvar :
      (∑' y : O, actualVariableDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualVarTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualVariableDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualVariableDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualVariableDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_variable_kernel_eq_dualVarTerm a b hc η hη z
  have hfixed :
      (∑' y : O, actualFixedDualKernel a b η y) =
        ∑' z : ℤ × ℤ, OscSpecial.dualFixedTerm η (a : ℝ) (b : ℝ) z := by
    calc
      (∑' y : O, actualFixedDualKernel a b η y) =
          ∑' z : ℤ × ℤ,
            actualFixedDualKernel a b η (dualFrequencyEquiv z) :=
        (dualFrequencyEquiv.tsum_eq (actualFixedDualKernel a b η)).symm
      _ = _ := by
        apply tsum_congr
        intro z
        exact actual_fixed_kernel_eq_dualFixedTerm_point a b η z
  rw [hvar, hfixed]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualFixedAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' y : O, actualFixedDualKernel a b η y))
      (𝓝[>] (0 : ℝ))
      (𝓝 (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
        fixedDualPhase c (GaussianShiftedPartition.representative 2 r))) := by
  simpa only [actualFixedDualKernel, mul_comm] using
    variableDualPhase_abel_limit a b hc

end

section

open EisensteinEmbedding ConcreteTraceCRT Complex

theorem actual_oscillatory_poisson_kernel
    (a b : ℤ) (hc : ActualEisensteinCoordinates.eval a b ≠ 0)
    (η : ℝ) (hη : 0 < η) :
    let c : O := ActualEisensteinCoordinates.eval a b
    (∑' z : O,
      (eisTraceModChar ShortDraftTrace.breveE
        ConcreteBreveE.breveE_period_coordinates c hc)
        (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
      Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
        (‖eisEmbedding z‖ ^ 2 : ℂ))) =
      (1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1 / 2 : ℂ))) *
        ∑' y : O, actualVariableDualKernel a b η y := by
  dsimp only
  rw [actual_oscillatory_poisson a b hc η hη]
  congr 1
  apply tsum_congr
  intro y
  unfold actualVariableDualKernel
  rw [dualScale_cast]

end

section
open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem actualVariableAbelLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      ((1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ))) *
        (∑' y : O, actualVariableDualKernel a b η y)))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by
      simpa only [pow_two] using hqZ)
  exact abel_transfer
    (fun η => 1 / ((OscSpecial.R η (a : ℝ) (b : ℝ) : ℂ) ^ (1/2 : ℂ)))
    (fun η => ∑' y : O, actualVariableDualKernel a b η y)
    (fun η => ∑' y : O, actualFixedDualKernel a b η y)
    _ _ (OscSpecial.prefactor_tendsto hq)
    (actualFixedAbelLimit a b hc)
    (actual_dual_phase_error_tendsto_zero a b hc)

theorem actualOriginalAbelDualLimit (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    letI : Finite (O ⧸ Ideal.span {(2 : O)}) :=
      finite_quotient_span (by norm_num : (2 : O) ≠ 0)
    letI : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
    let c : O := ActualEisensteinCoordinates.eval a b
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    let L2 : ℂ := ((2 / (Real.sqrt 3 *
      (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
    let K : ℂ := (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) * L2)
    Tendsto (fun η : ℝ => (η : ℂ) *
      (∑' z : O,
        (eisTraceModChar ShortDraftTrace.breveE
          ConcreteBreveE.breveE_period_coordinates c hc)
          (Ideal.Quotient.mk (Ideal.span {c}) z ^ 2) *
        Complex.exp (-(Real.pi : ℂ) * (η : ℂ) *
          (‖eisEmbedding z‖ ^ 2 : ℂ))))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((((Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) / 2 : ℝ) : ℂ) *
        (K * ∑ r : O ⧸ Ideal.span {(2 : O)},
          fixedDualPhase c (GaussianShiftedPartition.representative 2 r))))) := by
  apply (actualVariableAbelLimit a b hc).congr'
  filter_upwards [self_mem_nhdsWithin] with η hη
  change 0 < η at hη
  rw [actual_oscillatory_poisson_kernel a b hc η hη]

end

section

theorem dual_abel_coefficient (a b : ℤ)
    (hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ)) :
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((4 / OscSpecial.q (a : ℝ) (b : ℝ) : ℝ) : ℂ) *
      ((2 / (Real.sqrt 3 *
        (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)) =
      ((2 / (Real.sqrt 3 * OscSpecial.q (a : ℝ) (b : ℝ)) : ℝ) : ℂ) := by
  dsimp only
  rw [two_coordinate_norm_four]
  have hqC : (OscSpecial.q (a : ℝ) (b : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hq.ne'
  have hsC : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hqC, hsC]

theorem full_dual_abel_coefficient (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    let c : O := ActualEisensteinCoordinates.eval a b
    let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
    let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
    let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
    (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) *
        ((2 / (Real.sqrt 3 *
          (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ))) =
      (((2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding c‖) : ℝ) : ℂ) / 2) := by
  dsimp only
  have hqZ := coordinate_norm_pos_of_nonzero a b hc
  have hq : 0 < OscSpecial.q (a : ℝ) (b : ℝ) := by
    change 0 < (a : ℝ)^2 - (a : ℝ)*(b : ℝ)+(b : ℝ)^2
    exact_mod_cast (show 0 < a^2-a*b+b^2 by simpa only [pow_two] using hqZ)
  rw [dual_abel_coefficient a b hq]
  have hqnorm := osc_q_eq_eis_norm_sq a b
  have hsqrt : Real.sqrt (OscSpecial.q (a : ℝ) (b : ℝ)) =
      ‖ConcreteTraceCRT.eisEmbedding
        (ActualEisensteinCoordinates.eval a b)‖ := by
    rw [hqnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rw [hsqrt, hqnorm]
  have hn : (‖ConcreteTraceCRT.eisEmbedding
      (ActualEisensteinCoordinates.eval a b)‖ : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (norm_pos_iff.mpr
      (ConcreteTraceCRT.eisEmbedding_ne_zero hc)))
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 3)))
  push_cast
  field_simp [hn, hs]

open scoped Topology
open Filter EisensteinEmbedding ConcreteTraceCRT Complex

theorem quadraticGammaO_eq_fourTerms (a b : ℤ)
    (hc : ActualEisensteinCoordinates.eval a b ≠ 0) :
    quadraticGammaO (ActualEisensteinCoordinates.eval a b) hc =
      breveGaussianFourTerms a b := by
  let c : O := ActualEisensteinCoordinates.eval a b
  let n : ℝ := ‖eisEmbedding c‖
  let q : ℝ := OscSpecial.q (a : ℝ) (b : ℝ)
  let a2 := (ActualEisensteinCoordinates.coords (2 : O)).1
  let b2 := (ActualEisensteinCoordinates.coords (2 : O)).2
  let L2 : ℂ := ((2 / (Real.sqrt 3 *
    (((a2*a2-a2*b2+b2*b2 : ℤ) : ℝ))) : ℝ) : ℂ)
  let : Finite (O ⧸ Ideal.span {(2 : O)}) :=
    finite_quotient_span (by norm_num : (2 : O) ≠ 0)
  let : Fintype (O ⧸ Ideal.span {(2 : O)}) := Fintype.ofFinite _
  let S : ℂ := ∑ r : O ⧸ Ideal.span {(2 : O)},
    fixedDualPhase c (GaussianShiftedPartition.representative 2 r)
  have hEq0 := tendsto_nhds_unique
    (original_abel_gamma_limit c hc)
    (actualOriginalAbelDualLimit a b hc)
  have hEq : (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc) =
      (((Real.sqrt q / 2 : ℝ) : ℂ) *
        ((((4 / q : ℝ) : ℂ) * L2) * S)) := by
    simpa only [c, n, q, a2, b2, L2, S, mul_assoc] using hEq0
  have hC : (((Real.sqrt q / 2 : ℝ) : ℂ) *
      (((4 / q : ℝ) : ℂ) * L2)) =
      (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) := by
    simpa only [c, n, q, a2, b2, L2] using
      full_dual_abel_coefficient a b hc
  have hA : ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) ≠ 0 := by
    have hn : 0 < n := norm_pos_iff.mpr (eisEmbedding_ne_zero hc)
    have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    exact_mod_cast (ne_of_gt (div_pos (by norm_num : (0 : ℝ) < 2)
      (mul_pos hs hn)))
  have hG : quadraticGammaO c hc = S / 2 := by
    apply mul_left_cancel₀ hA
    calc
      ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * quadraticGammaO c hc =
          ((Real.sqrt q / 2 : ℝ) : ℂ) *
            ((((4 / q : ℝ) : ℂ) * L2) * S) := hEq
      _ = (((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) / 2) * S := by rw [← mul_assoc, hC]
      _ = ((2 / (Real.sqrt 3 * n) : ℝ) : ℂ) * (S / 2) := by ring
  change quadraticGammaO c hc = breveGaussianFourTerms a b
  calc
    quadraticGammaO c hc = S / 2 := hG
    _ = breveGaussianFourTerms a b := fixedDualPhase_four_terms a b

end

end ActualEisensteinCubic

open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

open MulChar AddChar

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical

namespace ActualEisensteinCubic

theorem cubicChar_reduce_ne_one (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q) :
    (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q) ≠ 1 := by
  intro hred
  apply cubicChar_ne_one P hPgood
  apply MulChar.ext
  intro u
  apply cubic_roots_reduce_injective Q hQgood
  · rw [← (cubicChar P hPgood).pow_apply_coe, cubicChar_pow_three]
    exact MulChar.one_apply_coe u
  · simp
  · have h := congrArg (fun χ : MulChar (O ⧸ P) (O ⧸ Q) => χ (u : O ⧸ P)) hred
    simpa only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one] using h

theorem cubicGauss_cube_of_nontrivial {E : Type*} [Field E] (ι : O →+* E)
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (hξ : (cubicChar P hgood).ringHomComp ι ≠ 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hξ3 : ξ ^ 3 = 1 := by
    rw [MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
  have hξ2 : ξ * ξ ≠ 1 := by
    intro h2
    apply hξ
    calc
      ξ = ξ * (ξ * ξ) := by rw [h2, mul_one]
      _ = ξ ^ 3 := by rw [pow_succ, pow_two]; ac_rfl
      _ = 1 := hξ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hξ3
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hξneg : ξ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hξ3
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξ hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary, map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

theorem cubicGauss_cube_reduce {E : Type*} [Field E]
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1)
    (η : (O ⧸ Q) →+* E) (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hPgood).ringHomComp (η.comp (Ideal.Quotient.mk Q))) ψ ^ 3 =
      -(η (Ideal.Quotient.mk Q p)) * (Nat.card (O ⧸ P) : E) := by
  apply cubicGauss_cube_of_nontrivial _ P hPgood p hP hprimary _ ψ hψ
  have h := (MulChar.ringHomComp_ne_one_iff η.injective).mpr
    (cubicChar_reduce_ne_one P Q hPgood hQgood)
  exact h

end ActualEisensteinCubic

namespace CubicFrobenius

theorem card_cast_ne_zero (F F' : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] (hchar : ringChar F' ≠ ringChar F) :
    (Fintype.card F : F') ≠ 0 := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  rw [hcard, Nat.cast_pow]
  apply pow_ne_zero
  intro hz
  have hd := (CharP.cast_eq_zero_iff F' (ringChar F') (ringChar F)).mp hz
  exact hchar ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime F' _) hp).mp hd)

theorem gaussSum_pow_card (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (χ : MulChar F F') (ψ : AddChar F E) :
    gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' E))
        (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F' (ringChar F')
  have hchar := Algebra.ringChar_eq F' E
  have hpE : (ringChar E).Prime := hchar ▸ hp
  let : Fact (ringChar E).Prime := ⟨hpE⟩
  have hcardE : Fintype.card F' = ringChar E ^ (n : ℕ) := by simpa only [hchar] using hcard
  unfold gaussSum
  rw [hcardE, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← hcardE]
  change (algebraMap F' E (χ x)) ^ Fintype.card F' * ψ x ^ Fintype.card F' = _
  rw [← map_pow, FiniteField.pow_card, ← AddChar.mulShift_spec']
  rfl

theorem gauss_cube_residue_relation (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (hchar : ringChar F' ≠ ringChar F)
    (χ : MulChar F F') (hχ : χ ≠ 1) (ψ : AddChar F E) (hψ : ψ.IsPrimitive)
    (a : F') (m : ℕ) (hm : Fintype.card F' = 3 * m + 1)
    (hcube : gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ 3 = algebraMap F' E a) :
    χ (Fintype.card F' : F) * a ^ m = 1 := by
  let ξ := χ.ringHomComp (algebraMap F' E)
  have hξ : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff (algebraMap F' E).injective).mpr hχ
  have hcard : (Fintype.card F : E) ≠ 0 := by
    rw [← map_natCast (algebraMap F' E)]
    exact (map_ne_zero (algebraMap F' E)).mpr (card_cast_ne_zero F F' hchar)
  have hg : gaussSum ξ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hξ hψ
  have hq : (Fintype.card F' : F) ≠ 0 := card_cast_ne_zero F' F hchar.symm
  let u : Fˣ := (isUnit_iff_ne_zero.mpr hq).unit
  have hu : (u : F) = Fintype.card F' := (isUnit_iff_ne_zero.mpr hq).unit_spec
  have hshift := gaussSum_mulShift ξ ψ u
  rw [hu, ← gaussSum_pow_card F F' E χ ψ] at hshift
  have hp : gaussSum ξ ψ ^ Fintype.card F' =
      algebraMap F' E (a ^ m) * gaussSum ξ ψ := by
    rw [hm, pow_succ, pow_mul, hcube, map_pow]
  rw [hp] at hshift
  have hone : ξ (Fintype.card F' : F) * algebraMap F' E (a ^ m) = 1 := by
    apply mul_right_cancel₀ hg
    simpa only [mul_assoc, one_mul] using hshift
  apply (algebraMap F' E).injective
  simpa only [ξ, map_mul, map_one, MulChar.ringHomComp_apply] using hone

end CubicFrobenius

namespace ActualEisensteinCubic

theorem cubic_primary_frobenius_relation (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O))) = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Field (O ⧸ Q) := Ideal.Quotient.field Q
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fintype (O ⧸ Q) := Fintype.ofFinite _
  let ψ := AddChar.FiniteField.primitiveChar (O ⧸ P) (O ⧸ Q) hchar
  let E := CyclotomicField ψ.n (O ⧸ Q)
  let η : (O ⧸ Q) →+* E := algebraMap (O ⧸ Q) E
  let χ := (cubicChar P hPgood).ringHomComp (Ideal.Quotient.mk Q)
  let a : O ⧸ Q := -(Ideal.Quotient.mk Q p) * (Fintype.card (O ⧸ P) : O ⧸ Q)
  let m := (Fintype.card (O ⧸ Q) - 1) / 3
  have hqdiv : 3 ∣ Fintype.card (O ⧸ Q) - 1 := by
    simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three Q hQgood
  have hqpos : 0 < Fintype.card (O ⧸ Q) := Fintype.card_pos
  have hm : Fintype.card (O ⧸ Q) = 3 * m + 1 := by
    dsimp [m]
    omega
  have hcube : gaussSum (χ.ringHomComp η) ψ.char ^ 3 = η a := by
    have hc := cubicGauss_cube_reduce P Q hPgood hQgood p hP hprimary η ψ.char ψ.prim
    convert (preTransparency := .instances) hc using 1
    · rfl
    · simp only [a, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card]
  have hrel := CubicFrobenius.gauss_cube_residue_relation (O ⧸ P) (O ⧸ Q) E
    hchar χ (cubicChar_reduce_ne_one P Q hPgood hQgood) ψ.char ψ.prim a m hm hcube
  have heuler := cubicChar_reduce Q hQgood
    (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))
  have heuler' : Ideal.Quotient.mk Q
      (cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = a ^ m := by
    simpa only [a, m, map_mul, map_neg, map_natCast, Nat.card_eq_fintype_card] using heuler
  rw [← heuler'] at hrel
  change Ideal.Quotient.mk Q (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) *
    Ideal.Quotient.mk Q (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) = 1 at hrel
  have hx : (Fintype.card (O ⧸ Q) : O ⧸ P) ≠ 0 :=
    CubicFrobenius.card_cast_ne_zero (O ⧸ Q) (O ⧸ P) hchar.symm
  have hy : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) ≠ 0 := by
    intro hz
    rw [hz, MulChar.map_zero, map_zero, mul_zero] at hrel
    exact zero_ne_one hrel
  have hxcube : (cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P)) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
  have hycube : (cubicChar Q hQgood
      (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)))) ^ 3 = 1 := by
    rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)
  have hprod : cubicChar P hPgood (Fintype.card (O ⧸ Q) : O ⧸ P) *
      cubicChar Q hQgood (Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O))) = 1 := by
    apply cubic_roots_reduce_injective Q hQgood
    · rw [mul_pow, hxcube, hycube, mul_one]
    · simp
    · simpa only [map_mul, map_one] using hrel
  have hminus : cubicChar Q hQgood (-1 : O ⧸ Q) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) (cubicChar_pow_three Q hQgood)
  have hneg : Ideal.Quotient.mk Q (-p * (Nat.card (O ⧸ P) : O)) =
      (-1) * Ideal.Quotient.mk Q (p * (Nat.card (O ⧸ P) : O)) := by
    simp only [map_mul, map_neg, map_natCast]
    ring
  rw [hneg, map_mul, hminus, one_mul] at hprod
  simpa only [Nat.card_eq_fintype_card] using hprod

theorem cubic_reciprocity_distinct_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hchar : ringChar (O ⧸ Q) ≠ ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  have hPQ := cubic_primary_frobenius_relation P Q hPgood hQgood hchar p hP hpprimary
  have hQP := cubic_primary_frobenius_relation Q P hQgood hPgood hchar.symm q hQ hqprimary
  simp only [map_mul, map_natCast] at hPQ hQP
  let U := cubicChar P hPgood (Nat.card (O ⧸ Q) : O ⧸ P)
  let V := cubicChar Q hQgood (Nat.card (O ⧸ P) : O ⧸ Q)
  have hB : cubicChar Q hQgood (Ideal.Quotient.mk Q p) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hPQ
  have hA : cubicChar P hPgood (Ideal.Quotient.mk P q) * (U * V) = 1 := by
    simpa only [U, V, mul_comm, mul_left_comm, mul_assoc] using hQP
  have hUV : U * V ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hA
    exact zero_ne_one hA
  exact mul_right_cancel₀ hUV (hA.trans hB.symm)

end ActualEisensteinCubic

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

theorem norm_eisEmbedding_unit (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

@[simp] theorem norm_eisEmbedding_unit_mul (u : Oˣ) (a : O) :
    ‖eisEmbedding ((u : O) * a)‖ = ‖eisEmbedding a‖ := by
  rw [map_mul, norm_mul, norm_eisEmbedding_unit, one_mul]

theorem finiteSexticRow_unit_mul_star {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ) (u : Oˣ) :
    finiteSexticRow P hgood j (u : O) * star (finiteSexticRow P hgood j (u : O)) = 1 := by
  unfold finiteSexticRow
  rw [star_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
  exact MulChar.one_apply (u.isUnit.map (Ideal.Quotient.mk (P i)))

def principalNormalizedGauss {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c : O) (hc : Ideal.span {c} = ∏ i, P i) (hc0 : c ≠ 0) : ℂ := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  exact (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
    eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) /
      (‖eisEmbedding c‖ : ℂ)

theorem principal_gauss_sum_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n)
    [Fintype (O ⧸ Ideal.span {c})] [Fintype (O ⧸ Ideal.span {n})] :
    (∑ r : O ⧸ Ideal.span {c}, principalSexticRow P hcop hgood j c hc r *
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates c hc0 r) =
      finiteSexticRow P hgood j (u : O) *
        ∑ r : O ⧸ Ideal.span {n}, principalSexticRow P hcop hgood j n hn r *
          eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0 r := by
  let e₀ := Ideal.quotEquivOfEq (hn.trans hc.symm)
  let ū : (O ⧸ Ideal.span {n})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {n})).toMonoidHom u
  let e : (O ⧸ Ideal.span {n}) ≃ (O ⧸ Ideal.span {c}) := ū.mulLeft.trans e₀.toEquiv
  have he (a : O) : e (Ideal.Quotient.mk (Ideal.span {n}) a) =
      Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a) := by
    change e₀ (Ideal.Quotient.mk (Ideal.span {n}) (u : O) *
      Ideal.Quotient.mk (Ideal.span {n}) a) = _
    rw [← map_mul, Ideal.quotEquivOfEq_mk]
  rw [← Equiv.sum_comp e, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [he, principalSexticRow_mk, principalSexticRow_mk, finiteSexticRow_mul]
  have hphase : eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates c hc0
      (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * a)) =
      eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hn0
        (Ideal.Quotient.mk (Ideal.span {n}) a) := by
    rw [eisTraceModChar_eq_paperE, eisTraceModChar_eq_paperE, hcn, map_mul, map_mul]
    congr 1
    field_simp [eisEmbedding_ne_zero u.ne_zero]
  rw [hphase]
  ring

theorem principalNormalizedGauss_unit_change {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime P))
    (hgood : ∀ i, lambda ∉ P i) (j : ι → ℕ)
    (c n : O) (hc : Ideal.span {c} = ∏ i, P i) (hn : Ideal.span {n} = ∏ i, P i)
    (hc0 : c ≠ 0) (hn0 : n ≠ 0) (u : Oˣ) (hcn : c = (u : O) * n) :
    principalNormalizedGauss P hcop hgood j c hc hc0 =
      finiteSexticRow P hgood j (u : O) *
        principalNormalizedGauss P hcop hgood j n hn hn0 := by
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc0
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hn0
  let : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  unfold principalNormalizedGauss
  rw [principal_gauss_sum_unit_change P hcop hgood j c n hc hn hc0 hn0 u hcn]
  rw [hcn, norm_eisEmbedding_unit_mul]
  ring

theorem exists_modulus_unit {ι : Type*} [Fintype ι] (p : ι → O) :
    ∃ u : Oˣ, finitePrimeModulus (fun i => Ideal.span {p i}) = (u : O) * ∏ i, p i := by
  have hs : Ideal.span {∏ i, p i} =
      Ideal.span {finitePrimeModulus (fun i => Ideal.span {p i})} := by
    rw [span_finitePrimeModulus, span_finset_prod]
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

def modulusUnit {ι : Type*} [Fintype ι] (p : ι → O) : Oˣ :=
  Classical.choose (exists_modulus_unit p)

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase

end GaussGeneratorTransport

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical

open scoped BigOperators Classical

namespace MixedGaussConversion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase

def localGauss (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  ConcreteBreveE.normalizedTraceGauss p hp (canonicalSextic (Ideal.span {p}) hg ^ j)

def localCoefficient (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  star (angularFactor p) * localGauss p hp hg 2

def localG (p : O) (hp : p ≠ 0) [ (Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) : ℂ :=
  breveLocalG (Ideal.span {p}) hg p rfl hp

def convertedLocal (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hg : lambda ∉ Ideal.span {p}) (inverse : Bool) : ℂ :=
  if inverse then
    (canonicalSextic (Ideal.span {p}) hg (Ideal.Quotient.mk (Ideal.span {p}) (-1 : O)) *
      localCoefficient p hp hg) / localG p hp hg
  else star (localCoefficient p hp hg) / star (localG p hp hg)

end MixedGaussConversion

open scoped BigOperators Classical SchwartzMap ContDiff

namespace GaussGeneratorTransport
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson FiniteGaussPhase
open MixedGaussConversion

def activeConvertedGauss
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hgood : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) : ℂ :=
  (∏ i : activeSupport S T,
    ∏ k ∈ @Finset.erase (activeSupport S T)
      (fun a b => Classical.propDecidable (a = b)) Finset.univ i,
    (canonicalSextic (Ideal.span {p i.val}) (hgood i.val) ^ activeExponent S T i)
      (Ideal.Quotient.mk (Ideal.span {p i.val}) (p k.val))) *
    ∏ i : activeSupport S T,
      convertedLocal (p i.val) (hp i.val) (hgood i.val) (decide (i.val ∈ S \ T))

end GaussGeneratorTransport

open scoped BigOperators Classical SchwartzMap ContDiff

namespace ConcretePrimeRowBridge
open ActualEisensteinCubic ShortDraftHeckeBridge ConcreteTraceCRT EisensteinSchwartzPoisson

noncomputable def mobiusIdealColumn (C : Ideal O → ℂ) (I : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius I : ℂ) * C I

noncomputable def conjugateIdealRowSum
    (F : Finset (Ideal O)) (hFpos : ∀ I ∈ F, I ≠ ⊥)
    (hFgood : ∀ I ∈ F,
      ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ P)
    (C : Ideal O → ℂ) (y : O) : ℂ :=
  ∑ I ∈ F, mobiusIdealColumn C I * star (idealSexticRow F hFpos hFgood I y)

end ConcretePrimeRowBridge

open MeasureTheory Set
open scoped BigOperators

namespace EisensteinSchwartzPoisson

theorem scaled_cauchy_antitone (b : ℝ) :
    AntitoneOn (fun x : ℝ => (1 + (b * x) ^ 2)⁻¹) (Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  apply inv_anti₀ (by positivity)
  nlinarith [sq_nonneg b, sq_nonneg (y - x),
    mul_nonneg (sq_nonneg b) (show 0 ≤ y ^ 2 - x ^ 2 by nlinarith)]

theorem scaled_cauchy_nat_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / (2 * b) := by
  have hi := (integrable_inv_one_add_mul_sq hb.ne').integrableOn (s := Ioi 0)
  have ht := (scaled_cauchy_antitone b).tsum_le_integral hi
    (fun t ht => by positivity)
  have he : (∫ x : ℝ in Ioi 0, (1 + (b * x) ^ 2)⁻¹) = Real.pi / (2 * b) := by
    rw [integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero,
      smul_eq_mul]
    ring
  simpa [he] using ht

theorem summable_scaled_cauchy_nat (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℕ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  exact (scaled_cauchy_antitone b).summable_of_integrableOn_Ioi_zero
    (integrable_inv_one_add_mul_sq hb.ne').integrableOn (fun _ _ => by positivity)

theorem summable_scaled_cauchy_int (b : ℝ) (hb : 0 < b) :
    Summable (fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹) := by
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · simpa using summable_scaled_cauchy_nat b hb
  · simpa [mul_neg] using summable_scaled_cauchy_nat b hb

theorem scaled_cauchy_int_bound (b : ℝ) (hb : 0 < b) :
    (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ≤ 1 + Real.pi / b := by
  have hs := summable_scaled_cauchy_nat b hb
  have hs1 := (summable_nat_add_iff 1).mpr hs
  have hneg : Summable (fun n : ℕ =>
      (1 + (b * ((-(n + 1) : ℤ) : ℝ)) ^ 2)⁻¹) := by
    convert (preTransparency := .instances) hs1 using 1
    ext n
    push_cast
    congr 1
    ring
  rw [tsum_of_nat_of_neg_add_one
    (f := fun n : ℤ => (1 + (b * (n : ℝ)) ^ 2)⁻¹)
    (by simpa only [Int.cast_natCast] using hs) hneg]
  simp only [Int.cast_natCast, Int.cast_neg, Int.cast_add, Int.cast_one, mul_neg,
    neg_sq]
  have hz := hs.tsum_eq_zero_add
  have he : (∑' n : ℕ, (1 + (b * (↑n + 1)) ^ 2)⁻¹) =
      (∑' n : ℕ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) - 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [add_comm] using hz.symm
  rw [he]
  have := scaled_cauchy_nat_bound b hb
  have hh : Real.pi / (2 * b) = (Real.pi / b) / 2 := by ring
  rw [hh] at this
  linarith

open ConcreteTraceCRT ActualEisensteinCubic

theorem scaled_eisenstein_cauchy_summable (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  apply (latticeCoordEquiv.symm.summable_iff).mp
  change Summable (fun p : ℤ × ℤ =>
    ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hp.mul_left 4)
  intro p
  apply inverse_square_le_cauchy_product (b * (p.1 : ℝ)) (b * (p.2 : ℝ))
    (K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) (by positivity)
  change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
    K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
  rw [eisEmbedding_eval_norm_sq]
  push_cast
  nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]

theorem scaled_eisenstein_cauchy_bound (K : ℝ) (hK : 0 < K) :
    (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi / Real.sqrt K) ^ 2 := by
  let b := Real.sqrt K
  have hb : 0 < b := Real.sqrt_pos.mpr hK
  have hbsq : b ^ 2 = K := Real.sq_sqrt hK.le
  have hs := summable_scaled_cauchy_int b hb
  have hp := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  have he : (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) =
      ∑' p : ℤ × ℤ, ((1 + K * ‖eisEmbedding (latticeCoordEquiv.symm p)‖ ^ 2) ^ 2)⁻¹ :=
    (latticeCoordEquiv.symm.tsum_eq _).symm
  rw [he]
  calc
    _ ≤ ∑' p : ℤ × ℤ, 4 * ((1 + (b * (p.1 : ℝ)) ^ 2)⁻¹ *
          (1 + (b * (p.2 : ℝ)) ^ 2)⁻¹) := by
      apply ((latticeCoordEquiv.symm.summable_iff).mpr
        (scaled_eisenstein_cauchy_summable K hK)).tsum_le_tsum _ (hp.mul_left 4)
      intro p
      apply inverse_square_le_cauchy_product _ _ _ (by positivity)
      change ((b * (p.1 : ℝ)) ^ 2 + (b * (p.2 : ℝ)) ^ 2) / 2 ≤
        K * ‖eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2)‖ ^ 2
      rw [eisEmbedding_eval_norm_sq]
      push_cast
      nlinarith [mul_nonneg hK.le (sq_nonneg ((p.1 : ℝ) - (p.2 : ℝ)))]
    _ = 4 * (∑' n : ℤ, (1 + (b * (n : ℝ)) ^ 2)⁻¹) ^ 2 := by
      rw [tsum_mul_left, ← hs.tsum_mul_tsum hs hp, pow_two]
    _ ≤ 4 * (1 + Real.pi / b) ^ 2 := by
      gcongr
      exact scaled_cauchy_int_bound b hb

theorem scaled_eisenstein_cauchy_small (K : ℝ) (hK : 0 < K) (hK1 : K ≤ 1) :
    K * (∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) ≤
      4 * (1 + Real.pi) ^ 2 := by
  have hs := scaled_eisenstein_cauchy_bound K hK
  have hb : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hb1 : Real.sqrt K ≤ 1 := by simpa using Real.sqrt_le_sqrt hK1
  have hsq := Real.sq_sqrt hK.le
  calc
    _ ≤ K * (4 * (1 + Real.pi / Real.sqrt K) ^ 2) :=
      mul_le_mul_of_nonneg_left hs hK.le
    _ = 4 * (Real.sqrt K + Real.pi) ^ 2 := by
      nth_rw 1 [← hsq]
      field_simp
    _ ≤ _ := by gcongr

theorem one_le_eisenstein_norm_sq (h : O) (hh : h ≠ 0) :
    1 ≤ ‖eisEmbedding h‖ ^ 2 := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {h}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hh)

theorem cauchy_large_scale_pointwise (K q : ℝ) (hK : 1 ≤ K) (hq : 1 ≤ q) :
    K * ((1 + K * q) ^ 2)⁻¹ ≤ 4 * ((1 + q) ^ 2)⁻¹ := by
  have hKp : 0 < K := by linarith
  have hqp : 0 < q := by linarith
  have h1 : K * (1 + q) ≤ 2 * (1 + K * q) := by nlinarith
  have h2 := pow_le_pow_left₀ (by positivity : 0 ≤ K * (1 + q)) h1 2
  have h3 : K * (1 + q) ^ 2 ≤ K ^ 2 * (1 + q) ^ 2 := by
    nlinarith [sq_nonneg (1 + q)]
  apply (div_le_div_iff₀ (by positivity : 0 < (1 + K * q) ^ 2)
    (by positivity : 0 < (1 + q) ^ 2)).mpr
  nlinarith

theorem lattice_profile_nonzero_scaled_bound
    (F : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ t : ℝ, 0 ≤ t → (1 + t) ^ 2 * ‖F t‖ ≤ B)
    (K : ℝ) (hK : 0 < K) :
    K * (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
      (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * B := by
  have hm (h : O) : ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      B * ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (by positivity)).mpr
    simpa only [mul_comm] using hF (K * ‖eisEmbedding h‖ ^ 2) (by positivity)
  have hs := scaled_eisenstein_cauchy_summable K hK
  have hf : Summable (fun h : O => ‖F (K * ‖eisEmbedding h‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hm (hs.mul_left B)
  have hsub := hf.subtype (fun h : O => h ≠ 0)
  have hc := eisenstein_cauchy_summable.subtype (fun h : O => h ≠ 0)
  by_cases hK1 : K ≤ 1
  · have htotal : (∑' h : {h : O // h ≠ 0}, ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
        ∑' h : O, ‖F (K * ‖eisEmbedding h‖ ^ 2)‖ :=
      hsub.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) hf
    have hbound := hf.tsum_le_tsum hm (hs.mul_left B)
    rw [tsum_mul_left] at hbound
    calc
      _ ≤ K * (B * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left (htotal.trans hbound) hK.le
      _ = B * (K * ∑' h : O, ((1 + K * ‖eisEmbedding h‖ ^ 2) ^ 2)⁻¹) := by ring
      _ ≤ B * (4 * (1 + Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_left (scaled_eisenstein_cauchy_small K hK hK1) hB
      _ ≤ _ := by nlinarith [eisensteinCauchyMass_nonneg]
  · have hp (h : {h : O // h ≠ 0}) :
        K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := by
      calc
        _ ≤ K * (B * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (hm h.val) hK.le
        _ = B * (K * ((1 + K * ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) := by ring
        _ ≤ B * (4 * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left (cauchy_large_scale_pointwise K _
            (le_of_not_ge hK1) (one_le_eisenstein_norm_sq h.val h.property)) hB
        _ = _ := by ring
    calc
      _ = ∑' h : {h : O // h ≠ 0}, K * ‖F (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left.symm
      _ ≤ ∑' h : {h : O // h ≠ 0}, (4 * B) * ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ :=
        (hsub.mul_left K).tsum_le_tsum hp (hc.mul_left (4 * B))
      _ = (4 * B) * ∑' h : {h : O // h ≠ 0}, ((1 + ‖eisEmbedding h.val‖ ^ 2) ^ 2)⁻¹ := tsum_mul_left
      _ ≤ (4 * B) * eisensteinCauchyMass := mul_le_mul_of_nonneg_left
        (eisensteinCauchyMass_subtype (fun h : O => h ≠ 0)) (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (1 + Real.pi)]

theorem paperRadialFourier_nonzero_lattice_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : SchwartzMap ℝ ℂ) (K : ℝ), 0 < K →
        K * (∑' h : {h : O // h ≠ 0},
          ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) ≤
            C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨s, (4 * (1 + Real.pi) ^ 2 + 4 * eisensteinCauchyMass) * C, ?_, ?_⟩
  · have := eisensteinCauchyMass_nonneg
    have := Real.pi_pos
    positivity
  · intro W K hK
    simpa only [mul_assoc] using lattice_profile_nonzero_scaled_bound
      (paperRadialFourier W) (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
        (by positivity) (hb W) K hK

end EisensteinSchwartzPoisson

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

namespace ActualEisensteinCubic

theorem primary_associated_eq (x y : O) (hxy : Associated x y)
    (hx : lambda ^ 2 ∣ x - 1) (hy : lambda ^ 2 ∣ y - 1) : x = y := by
  obtain ⟨u, hu⟩ := hxy
  have huprimary : lambda ^ 2 ∣ (u : O) - 1 := by
    have heq : (u : O) - 1 = (y - 1) - (x - 1) * (u : O) := by
      rw [← hu]
      ring
    rw [heq]
    exact dvd_sub hy (dvd_mul_of_dvd_left hx _)
  have huone : (u : O) = 1 := A3_primary_unit_eq_one _ u.isUnit huprimary
  simpa only [huone, mul_one] using hu

theorem primary_multiset_prod (s : Multiset O)
    (hs : ∀ x ∈ s, lambda ^ 2 ∣ x - 1) : lambda ^ 2 ∣ s.prod - 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have hb := ih (fun x hx => hs x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.prod_cons]
    have heq : a * s.prod - 1 = (a - 1) * s.prod + (s.prod - 1) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem primary_maximal_divisor_good (t : O) (ht : lambda ^ 2 ∣ t - 1)
    (P : Ideal O) [P.IsMaximal] (htP : t ∈ P) : lambda ∉ P := by
  intro hlam
  have hlam2 : lambda ^ 2 ∈ P := by
    simpa only [pow_two] using P.mul_mem_left lambda hlam
  have hsub : t - 1 ∈ P := Ideal.mem_of_dvd P ht hlam2
  have hone : (1 : O) ∈ P := by simpa using P.sub_mem htP hsub
  exact (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal))
    ((Ideal.eq_top_iff_one _).mpr hone)

theorem exists_primary_prime_factorization (t : O) (ht0 : t ≠ 0)
    (ht : lambda ^ 2 ∣ t - 1) :
    ∃ s : Multiset O, s.prod = t ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
  classical
  obtain ⟨f, hf, hft⟩ := UniqueFactorizationMonoid.exists_prime_factors t ht0
  have hfgood : ∀ r ∈ f, lambda ∉ (Ideal.span {r} : Ideal O) := by
    intro r hr
    have hp := hf r hr
    let : (Ideal.span {r} : Ideal O).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    apply primary_maximal_divisor_good t ht
    exact Ideal.mem_span_singleton.mpr ((Multiset.dvd_prod hr).trans hft.dvd)
  have hreplace : ∃ s : Multiset O, Associated s.prod f.prod ∧
      ∀ r ∈ s, Prime r ∧ lambda ^ 2 ∣ r - 1 := by
    clear hft
    induction f using Multiset.induction_on with
    | empty => exact ⟨0, Associated.refl _, by simp⟩
    | @cons a f ih =>
      have ha := hf a (Multiset.mem_cons_self _ _)
      let : (Ideal.span {a} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible ha.irreducible
      obtain ⟨r, hrspan, hrprimary, _⟩ := cubicJacobi_exists_primary_generator
        (Ideal.span {a}) (hfgood a (Multiset.mem_cons_self _ _))
      have har : Associated a r := Ideal.span_singleton_eq_span_singleton.mp hrspan
      obtain ⟨s, hsf, hs⟩ := ih
        (fun r hr => hf r (Multiset.mem_cons_of_mem hr))
        (fun r hr => hfgood r (Multiset.mem_cons_of_mem hr))
      refine ⟨r ::ₘ s, ?_, ?_⟩
      · simpa only [Multiset.prod_cons] using har.symm.mul_mul hsf
      · intro x hx
        rcases Multiset.mem_cons.mp hx with rfl | hx
        · exact ⟨har.prime_iff.mp ha, hrprimary⟩
        · exact hs x hx
  obtain ⟨s, hsf, hs⟩ := hreplace
  refine ⟨s, ?_, hs⟩
  exact primary_associated_eq _ _ (hsf.trans hft)
    (primary_multiset_prod s (fun r hr => (hs r hr).2)) ht

theorem residue_char_mem (P : Ideal O) :
    (ringChar (O ⧸ P) : O) ∈ P := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_natCast]
  exact CharP.cast_eq_zero (O ⧸ P) (ringChar (O ⧸ P))

theorem maximal_eq_or_eq_of_same_residue_char
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (hRP : ringChar (O ⧸ R) = ringChar (O ⧸ P)) : R = P ∨ R = Q := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  obtain ⟨a, b, _, _, _, _, hcover⟩ := rational_prime_ideal_cover
    (ringChar (O ⧸ P)) (CharP.char_is_prime (O ⧸ P) _)
  have hp := hcover P inferInstance (residue_char_mem P)
  have hq := hcover Q inferInstance (by rw [← hPQ]; exact residue_char_mem Q)
  have hr := hcover R inferInstance (by rw [← hRP]; exact residue_char_mem R)
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    rcases hr with hr | hr <;> simp_all

theorem prime_divisor_residue_char_ne
    (P Q R : Ideal O) [P.IsMaximal] [Q.IsMaximal] [R.IsMaximal]
    (hne : P ≠ Q) (hPQ : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (t : O) (htP : t ∉ P) (htQ : t ∉ Q) (htR : t ∈ R) :
    ringChar (O ⧸ R) ≠ ringChar (O ⧸ P) := by
  intro hRP
  rcases maximal_eq_or_eq_of_same_residue_char P Q R hne hPQ hRP with rfl | rfl
  · exact htP htR
  · exact htQ htR

theorem lambda_sq_dvd_three : lambda ^ 2 ∣ (3 : O) := by
  have hlam : lambda ^ 2 = -3 * omega := by
    change (omega - 1) ^ 2 = -3 * omega
    linear_combination omega_sq_for_norm
  refine ⟨-omega ^ 2, ?_⟩
  rw [hlam]
  calc
    (3 : O) = 3 * omega ^ 3 := by rw [omega_primitive.pow_eq_one]; ring
    _ = -3 * omega * -omega ^ 2 := by ring

theorem neg_two_primary : lambda ^ 2 ∣ (-2 : O) - 1 := by
  convert (preTransparency := .instances) dvd_neg.mpr lambda_sq_dvd_three using 1 ; ring

theorem neg_add_primary (p q : O)
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1) :
    lambda ^ 2 ∣ -(p + q) - 1 := by
  have hd := dvd_neg.mpr (dvd_add (dvd_add hp hq) lambda_sq_dvd_three)
  convert (preTransparency := .instances) hd using 1 ; ring

theorem prime_generator_not_mem_of_ne (P Q : Ideal O)
    [P.IsMaximal] [Q.IsMaximal] (hne : P ≠ Q)
    (q : O) (hQ : Q = Ideal.span {q}) : q ∉ P := by
  intro hq
  have hle : Q ≤ P := by
    rw [hQ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hq
  exact hne (Ideal.IsMaximal.eq_of_le (inferInstance : Q.IsMaximal)
    (Ideal.IsMaximal.ne_top (inferInstance : P.IsMaximal)) hle).symm

theorem cubic_reciprocity_equal_residue_char
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (hne : P ≠ Q) (hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P))
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  classical
  let t : O := -(p + q)
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hqP : q ∉ P := prime_generator_not_mem_of_ne P Q hne q hQ
  have hpQ : p ∉ Q := prime_generator_not_mem_of_ne Q P hne.symm p hP
  have htP : t ∉ P := by
    intro ht
    have hs : p + q ∈ P := by simpa only [t, neg_neg] using P.neg_mem ht
    exact hqP (by simpa only [add_sub_cancel_left] using P.sub_mem hs hpP)
  have htQ : t ∉ Q := by
    intro ht
    have hs : p + q ∈ Q := by simpa only [t, neg_neg] using Q.neg_mem ht
    exact hpQ (by simpa only [add_sub_cancel_right] using Q.sub_mem hs hqQ)
  have ht0 : t ≠ 0 := fun h => htP (h ▸ P.zero_mem)
  obtain ⟨s, hst, hs⟩ := exists_primary_prime_factorization t ht0
    (neg_add_primary p q hpprimary hqprimary)
  have hlocal : ∀ r ∈ s,
      cubicChar P hPgood (Ideal.Quotient.mk P r) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q r) := by
    intro r hr
    let R : Ideal O := Ideal.span {r}
    let : R.IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hs r hr).1.irreducible
    have hrR : r ∈ R := Ideal.subset_span (by simp)
    have htR : t ∈ R := Ideal.mem_span_singleton.mpr (hst ▸ Multiset.dvd_prod hr)
    have hRgood : lambda ∉ R := primary_maximal_divisor_good t
      (neg_add_primary p q hpprimary hqprimary) R htR
    have hRP := prime_divisor_residue_char_ne P Q R hne hchar t htP htQ htR
    have hRQ : ringChar (O ⧸ R) ≠ ringChar (O ⧸ Q) := by rwa [hchar]
    rw [cubic_reciprocity_distinct_residue_char P R hPgood hRgood hRP
      p r hP rfl hpprimary (hs r hr).2,
      cubic_reciprocity_distinct_residue_char Q R hQgood hRgood hRQ
      q r hQ rfl hqprimary (hs r hr).2]
    have hsum : Ideal.Quotient.mk R p + Ideal.Quotient.mk R q = 0 := by
      have hz := Ideal.Quotient.eq_zero_iff_mem.mpr htR
      simpa only [t, map_neg, map_add, neg_eq_zero] using hz
    have heq : Ideal.Quotient.mk R p = -Ideal.Quotient.mk R q := eq_neg_of_add_eq_zero_left hsum
    rw [heq, ← neg_one_mul (Ideal.Quotient.mk R q), map_mul,
      A3_cubicChar_neg_one, one_mul]
  have hmul : ∀ f : Multiset O,
      (∀ r ∈ f, cubicChar P hPgood (Ideal.Quotient.mk P r) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q r)) →
      cubicChar P hPgood (Ideal.Quotient.mk P f.prod) =
        cubicChar Q hQgood (Ideal.Quotient.mk Q f.prod) := by
    intro f
    induction f using Multiset.induction_on with
    | empty => intro _; simp
    | @cons r f ih =>
      intro hf
      simp only [Multiset.prod_cons, map_mul]
      rw [hf r (Multiset.mem_cons_self _ _), ih
        (fun x hx => hf x (Multiset.mem_cons_of_mem hx))]
  have htval := hmul s hlocal
  rw [hst] at htval
  have hpzero : Ideal.Quotient.mk P p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hpP
  have hqzero : Ideal.Quotient.mk Q q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hqQ
  simp only [t, map_neg, map_add, hpzero, hqzero, zero_add, add_zero] at htval
  rw [← neg_one_mul (Ideal.Quotient.mk P q), map_mul, A3_cubicChar_neg_one, one_mul,
    ← neg_one_mul (Ideal.Quotient.mk Q p), map_mul, A3_cubicChar_neg_one, one_mul] at htval
  exact htval

theorem cubic_reciprocity_primary
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hPgood : lambda ∉ P) (hQgood : lambda ∉ Q)
    (p q : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hpprimary : lambda ^ 2 ∣ p - 1) (hqprimary : lambda ^ 2 ∣ q - 1) :
    cubicChar P hPgood (Ideal.Quotient.mk P q) =
      cubicChar Q hQgood (Ideal.Quotient.mk Q p) := by
  by_cases hPQ : P = Q
  · have hqP : q ∈ P := by rw [hPQ, hQ]; exact Ideal.subset_span (by simp)
    have hpQ : p ∈ Q := by rw [← hPQ, hP]; exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hqP,
      Ideal.Quotient.eq_zero_iff_mem.mpr hpQ, MulChar.map_zero, MulChar.map_zero]
  · by_cases hchar : ringChar (O ⧸ Q) = ringChar (O ⧸ P)
    · exact cubic_reciprocity_equal_residue_char P Q hPgood hQgood hPQ hchar
        p q hP hQ hpprimary hqprimary
    · exact cubic_reciprocity_distinct_residue_char P Q hPgood hQgood hchar
        p q hP hQ hpprimary hqprimary

def cubicTwoIdeal : Ideal O := Ideal.span {(-2 : O)}

instance cubicTwoIdeal_isMaximal : cubicTwoIdeal.IsMaximal := by
  rcases rational_prime_factor_cases 2 Nat.prime_two with hm |
      ⟨a, b, _, _, _, ha, _, _, _⟩
  · simpa only [cubicTwoIdeal, Ideal.span_singleton_neg, Nat.cast_ofNat] using hm
  · have hin : (Ideal.span {a} : Ideal O) ∈ {I : Ideal O | Ideal.absNorm I = 2} := by
      change Ideal.absNorm (Ideal.span {a}) = 2
      rwa [← qNat_eq_absNorm_span]
    rw [ShortDraftHeckeBridge.norm_p_fiber_inert Nat.prime_two (by decide)] at hin
    exact False.elim hin

theorem cubicTwoIdeal_good : lambda ∉ cubicTwoIdeal := by
  apply primary_maximal_divisor_good (-2 : O) neg_two_primary
  exact Ideal.subset_span (by simp)

theorem cubicTwoIdeal_residue_char : ringChar (O ⧸ cubicTwoIdeal) = 2 := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field cubicTwoIdeal
  let : Fintype (O ⧸ cubicTwoIdeal) := Fintype.ofFinite _
  have hmem : (2 : O) ∈ cubicTwoIdeal := by
    rw [cubicTwoIdeal, Ideal.span_singleton_neg]
    exact Ideal.subset_span (by simp)
  have hz : (2 : O ⧸ cubicTwoIdeal) = 0 := by
    simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ cubicTwoIdeal) _)
    Nat.prime_two).mp ((ringChar.spec (O ⧸ cubicTwoIdeal) 2).mp hz)

theorem canonicalSextic_four_eq_fixed_two
    (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P)
    (p : O) (hP : P = Ideal.span {p}) (hprimary : lambda ^ 2 ∣ p - 1) :
    canonicalSextic P hgood (Ideal.Quotient.mk P (4 : O)) =
      ConcreteTraceCRT.eisEmbedding
        (cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal p)) := by
  have hfour : Ideal.Quotient.mk P (4 : O) = (Ideal.Quotient.mk P (-2 : O)) ^ 2 := by
    simp only [map_ofNat, map_neg]
    ring
  rw [hfour, map_pow, ← MulChar.pow_apply' _ (by decide : (2 : ℕ) ≠ 0),
    canonicalSextic_pow_two]
  change ConcreteTraceCRT.eisEmbedding (cubicChar P hgood (Ideal.Quotient.mk P (-2 : O))) = _
  congr 1
  exact cubic_reciprocity_primary P cubicTwoIdeal hgood cubicTwoIdeal_good
    p (-2) hP rfl hprimary neg_two_primary

end ActualEisensteinCubic

open scoped BigOperators Classical

namespace IdealGaussCRT

theorem sum_square_phase_finite_crt {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, CommRing (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ) :
    (∑ x : T, ψ (x ^ 2)) =
      ∏ i, ∑ y : R i, coordinateAddChar R e ψ i (y ^ 2) := by
  calc
    _ = ∑ x : T, ∏ i, coordinateAddChar R e ψ i ((e x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [addChar_finite_crt_factor R e ψ (x ^ 2)]
      simp only [map_pow, Pi.pow_apply]
    _ = ∑ x : ∀ i, R i, ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2) :=
      Equiv.sum_comp e.toEquiv
        (fun x : ∀ i, R i => ∏ i, coordinateAddChar R e ψ i ((x i) ^ 2))
    _ = _ := (Fintype.prod_sum (fun i (x : R i) => coordinateAddChar R e ψ i (x ^ 2))).symm

theorem quadratic_gauss_finite_crt_eq_square_sum {ι T : Type*} [Fintype ι]
    (R : ι → Type*) [CommRing T] [∀ i, Field (R i)]
    [Fintype T] [∀ i, Fintype (R i)]
    (e : T ≃+* ∀ i, R i) (ψ : AddChar T ℂ)
    (hψ : ψ.IsPrimitive) (hchar : ∀ i, ringChar (R i) ≠ 2) :
    (∑ x : T, (∏ i, ((quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) =
      ∑ x : T, ψ (x ^ 2) := by
  rw [gauss_sum_finite_crt R e
    (fun i => (quadraticChar (R i)).ringHomComp (Int.castRingHom ℂ)) ψ,
    sum_square_phase_finite_crt R e ψ]
  apply Finset.prod_congr rfl
  intro i _
  have hp := coordinateAddChar_isPrimitive R e ψ hψ i
  have hn : coordinateAddChar R e ψ i ≠ 1 := by
    simpa only [AddChar.mulShift_one] using hp (a := 1) one_ne_zero
  exact ShortDraftQuadraticGauss.quadratic_gauss_as_square_phase _ (hchar i) hn

end IdealGaussCRT

namespace QuadraticGaussRay

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

theorem canonicalProductGauss_three_eq_quadraticGamma
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticGammaO (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let (i : ι) : Fintype (O ⧸ Ideal.span {p i}) := Fintype.ofFinite _
  let (i : ι) : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field _
  let e := productElementCRT p hcop
  let ψ := eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, (canonicalSextic (Ideal.span {p i}) (hgood i) ^ 3) (e x i)) * ψ x) /
      (‖eisEmbedding c‖ : ℂ) = (∑ x : O ⧸ Ideal.span {c}, ψ (x ^ 2)) / (‖eisEmbedding c‖ : ℂ)
  congr 1
  simp_rw [canonicalSextic_pow_three_quadratic]
  exact IdealGaussCRT.quadratic_gauss_finite_crt_eq_square_sum
    (fun i => O ⧸ Ideal.span {p i}) e ψ
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc) hchar

theorem I_zpow_eq_of_mod_four {a b : ℤ} (h : (a : ZMod 4) = b) :
    Complex.I ^ a = Complex.I ^ b := by
  obtain ⟨k, hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub b a 4).mp h.symm
  have ha : a = b + 4 * k := by omega
  rw [ha, zpow_add₀ Complex.I_ne_zero, zpow_mul]
  norm_num

theorem fourTerms_eq_of_mod_four {a b c d : ℤ}
    (ha : (a : ZMod 4) = c) (hb : (b : ZMod 4) = d) :
    breveGaussianFourTerms a b = breveGaussianFourTerms c d := by
  have hn : ((-b : ℤ) : ZMod 4) = (-d : ℤ) := by simpa using congrArg Neg.neg hb
  have hs : ((b-a : ℤ) : ZMod 4) = (d-c : ℤ) := by
    push_cast
    rw [ha, hb]
  rw [breveGaussianFourTerms_formula, breveGaussianFourTerms_formula,
    I_zpow_eq_of_mod_four ha, I_zpow_eq_of_mod_four hn, I_zpow_eq_of_mod_four hs]

def quadraticRayValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  breveGaussianFourTerms (r.1.val : ℤ) (r.2.val : ℤ)

theorem quadraticGammaO_eq_rayValue (c : O) (hc : c ≠ 0) :
    quadraticGammaO c hc = quadraticRayValue (residue c) := by
  have h := quadraticGammaO_eq_fourTerms (coords c).1 (coords c).2 (by rwa [eval_coords])
  have h' : quadraticGammaO c hc = breveGaussianFourTerms (coords c).1 (coords c).2 := by
    simpa only [eval_coords] using h
  rw [h']
  unfold quadraticRayValue residue
  exact fourTerms_eq_of_mod_four (by simp) (by simp)

theorem canonicalProductGauss_three_eq_rayValue
    {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hgood : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    canonicalProductGauss p hp hcop hgood (fun _ => 3) =
      quadraticRayValue (residue (∏ i, p i)) := by
  rw [canonicalProductGauss_three_eq_quadraticGamma p hp hcop hgood hchar,
    quadraticGammaO_eq_rayValue]

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase ActualEisensteinCoordinates

def fixedGValue (r : EisensteinEPrimaryPhase.Coord) : ℂ :=
  (eisEmbedding (cubicChar cubicTwoIdeal cubicTwoIdeal_good
    (Ideal.Quotient.mk cubicTwoIdeal (lift r))))⁻¹ * quadraticRayValue r

theorem residue_eq_of_four_dvd_sub (c d : O) (h : (4 : O) ∣ c - d) :
    residue c = residue d := by
  obtain ⟨z, hz⟩ := h
  have he : c = eval ((coords d).1 + 4 * (coords z).1)
      ((coords d).2 + 4 * (coords z).2) := by
    calc
      c = d + 4 * z := by linear_combination hz
      _ = eval (coords d).1 (coords d).2 + 4 * eval (coords z).1 (coords z).2 := by
        rw [eval_coords, eval_coords]
      _ = _ := by simp only [eval]; push_cast; ring
  rw [he, residue_eval]
  simp only [residue, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    show (4 : ZMod 4) = 0 by decide, zero_mul, add_zero]

theorem residue_eq_of_quotient_four_eq (c d : O)
    (h : Ideal.Quotient.mk (Ideal.span {(4 : O)}) c =
      Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) : residue c = residue d :=
  residue_eq_of_four_dvd_sub c d (Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h))

def residueQuotientFour : (O ⧸ Ideal.span {(4 : O)}) → EisensteinEPrimaryPhase.Coord :=
  Quotient.lift residue (fun c d h => residue_eq_of_quotient_four_eq c d (Quotient.sound h))

@[simp] theorem residueQuotientFour_mk (c : O) :
    residueQuotientFour (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = residue c := rfl

def fixedGQuotientValue (r : O ⧸ Ideal.span {(4 : O)}) : ℂ :=
  fixedGValue (residueQuotientFour r)

end QuadraticGaussRay

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators

open scoped BigOperators Classical

namespace MixedCrossSeparation

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

def crossSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (i k : ι) : ℂ :=
  canonicalSextic (Ideal.span {p i}) (hg i)
    (Ideal.Quotient.mk (Ideal.span {p i}) (p k))

def convertedColumnBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (inverse : Bool) : ℂ :=
  ∏ i ∈ S, (∏ k ∈ S.erase i, crossSymbol p hg i k ^ (if inverse then 5 else 1)) *
    convertedLocal (p i) (hp i) (hg i) inverse

def quadraticCrossPhase {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 * crossSymbol p hg k i ^ 3

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open QuadraticGaussRay ActualEisensteinCoordinates

theorem prod_subtype_erase {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (A : Finset ι) (i : A) (f : ι → M) :
    (∏ k ∈ (Finset.univ : Finset A).erase i, f k.val) = ∏ k ∈ A.erase i.val, f k := by
  apply Finset.prod_bij (fun k _ => k.val)
  · intro k hk
    apply Finset.mem_erase.mpr
    refine ⟨?_, k.property⟩
    exact fun h => (Finset.mem_erase.mp hk).1 (Subtype.ext h)
  · intro a ha b hb h
    exact Subtype.ext h
  · intro k hk
    refine ⟨⟨k, (Finset.mem_erase.mp hk).2⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    exact ⟨fun h => (Finset.mem_erase.mp hk).1 (congrArg Subtype.val h), Finset.mem_univ _⟩
  · intro a ha
    rfl

theorem restricted_prime_coprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (A : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : A => Ideal.span {p i.val})) := by
  intro i k hik
  exact hcop (fun h => hik (Subtype.ext h))

def quadraticBlock {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) : ℂ :=
  ∏ i ∈ A, (∏ k ∈ A.erase i, crossSymbol p hg i k ^ 3) *
    localGauss (p i) (hp i) (hg i) 3

theorem quadraticBlock_eq_productGauss
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A : Finset ι) :
    quadraticBlock p hp hg A =
      canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
        (restricted_prime_coprime p hcop A) (fun i => hg i.val)
        (fun _ => 3) := by
  rw [canonicalProductGauss_cross_factors, ← Finset.prod_mul_distrib]
  unfold quadraticBlock
  rw [← Finset.prod_coe_sort A]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [← prod_subtype_erase A i (fun k => crossSymbol p hg i.val k ^ 3)]
  apply Finset.prod_congr
  · ext k; simp
  · intro k hk
    exact (MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0) _).symm

theorem quadraticBlock_eq_rayValue
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    quadraticBlock p hp hg A = quadraticRayValue (residue (∏ i ∈ A, p i)) := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A,
    canonicalProductGauss_three_eq_rayValue (fun i : A => p i.val) (fun i => hp i.val)
      (restricted_prime_coprime p hcop A) (fun i => hg i.val)
      (fun i => hchar i.val), Finset.prod_coe_sort]

theorem quadraticBlock_union
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticBlock p hp hg (A ∪ B) = quadraticBlock p hp hg A *
      quadraticBlock p hp hg B * quadraticCrossPhase p hg A B := by
  let x := crossSymbol p hg
  let l := fun i => localGauss (p i) (hp i) (hg i) 3
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ A.erase i, x i k ^ 3) * (∏ k ∈ B, x i k ^ 3) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : (A ∪ B).erase i = A.erase i ∪ B := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ (A ∪ B).erase i, x i k ^ 3) =
        (∏ k ∈ B.erase i, x i k ^ 3) * (∏ k ∈ A, x i k ^ 3) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : (A ∪ B).erase i = B.erase i ∪ A := by
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ 3) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ 3) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  change (∏ i ∈ A ∪ B, ((∏ k ∈ (A ∪ B).erase i, x i k ^ 3) * l i)) = _
  rw [Finset.prod_union hd, hpA, hpB, Finset.prod_comm (s := B) (t := A)]
  unfold quadraticBlock quadraticCrossPhase
  simp only [Finset.prod_mul_distrib]
  dsimp only [x, l]
  ring

theorem norm_quadraticBlock
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A : Finset ι) :
    ‖quadraticBlock p hp hg A‖ = 1 := by
  rw [quadraticBlock_eq_productGauss p hp hcop hg A]
  exact norm_canonicalProductGauss (fun i : A => p i.val) (fun i => hp i.val)
    (restricted_prime_coprime p hcop A) (fun i => hg i.val)
    (fun i => hchar i.val) (fun _ => 3) (fun _ => by decide) (fun _ => by decide)

def quadraticRayPair (a b : EisensteinEPrimaryPhase.Coord) : ℂ :=
  quadraticRayValue (EisensteinEPrimaryPhase.mul a b) /
    (quadraticRayValue a * quadraticRayValue b)

theorem quadraticCrossPhase_eq_rayPair
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (A B : Finset ι) (hd : Disjoint A B) :
    quadraticCrossPhase p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) := by
  have hA0 : quadraticBlock p hp hg A ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar A
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have hB0 : quadraticBlock p hp hg B ≠ 0 := by
    intro hz
    have hn := norm_quadraticBlock p hp hcop hg hchar B
    rw [hz, norm_zero] at hn
    exact zero_ne_one hn
  have h := quadraticBlock_union p hp hg A B hd
  have hdiv : quadraticCrossPhase p hg A B = quadraticBlock p hp hg (A ∪ B) /
      (quadraticBlock p hp hg A * quadraticBlock p hp hg B) := by
    apply (eq_div_iff (mul_ne_zero hA0 hB0)).mpr
    rw [h]
    ring
  rw [hdiv, quadraticBlock_eq_rayValue p hp hcop hg hchar (A ∪ B),
    quadraticBlock_eq_rayValue p hp hcop hg hchar A,
    quadraticBlock_eq_rayValue p hp hcop hg hchar B, Finset.prod_union hd,
    residue_mul]
  rfl

end MixedCrossSeparation

open scoped BigOperators Classical

namespace CoprimeMobiusExtension
abbrev O := ActualEisensteinCubic.O

theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem disjoint_indicator_expansion {ι : Type*} [DecidableEq ι]
    (B S T : Finset ι) (hS : S ⊆ B) (_hT : T ⊆ B) :
    (if Disjoint S T then (1 : ℂ) else 0) =
      ∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  have heq : (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
    calc
      _ = ∑ D ∈ (S ∩ T).powerset,
            if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro D hD hnot
        have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
        simp [hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        have hh : D ⊆ S ∧ D ⊆ T := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
        simp [hh]
  rw [heq, sum_subset_sign]
  simp only [Finset.disjoint_iff_inter_eq_empty]

open ActualEisensteinCubic

end CoprimeMobiusExtension

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

def idealDivisors (I : Ideal O) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) (Ideal.absNorm I)).toFinset.filter
    (fun J => J ∣ I)

theorem mem_idealDivisors {I J : Ideal O} (hI : I ≠ ⊥) :
    J ∈ idealDivisors I ↔ J ∣ I := by
  simp only [idealDivisors, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · exact And.right
  · intro hJI
    have hn : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
      (fun hz => hI (Ideal.absNorm_eq_zero_iff.mp hz))
    exact ⟨Nat.le_of_dvd hn (map_dvd Ideal.absNorm hJI), hJI⟩

def primeSupport (I : Ideal O) : Finset (Ideal O) := (normalizedFactors I).toFinset

theorem support_prime {I : Ideal O} {P : Ideal O} (hP : P ∈ primeSupport I) : Prime P :=
  prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

theorem support_product_ne_zero {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun _P hP => (support_prime (hS hP)).ne_zero)

theorem factors_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : normalizedFactors (∏ P ∈ S, P) = S.val := by
  have hp : ∀ P ∈ S.val, Prime P := fun P hP => support_prime (hS hP)
  simpa using normalizedFactors_prod_of_prime hp

theorem squarefree_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : Squarefree (∏ P ∈ S, P) := by
  apply (squarefree_iff_nodup_normalizedFactors (support_product_ne_zero hS)).mpr
  rw [factors_support_product hS]
  exact S.nodup

theorem support_product_dvd {I : Ideal O} (hI : I ≠ ⊥) {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) : (∏ P ∈ S, P) ∣ I := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (support_product_ne_zero hS) hI).mpr
  rw [factors_support_product hS]
  apply (Multiset.le_iff_subset S.nodup).mpr
  intro P hP
  exact Multiset.mem_toFinset.mp (hS hP)

theorem moebius_support_product {I : Ideal O} {S : Finset (Ideal O)}
    (hS : S ⊆ primeSupport I) :
    (moebius (∏ P ∈ S, P) : ℂ) = (-1 : ℂ) ^ S.card := by
  rw [(squarefree_support_product hS).moebius_eq, factors_eq_normalizedFactors,
    factors_support_product hS]
  simp

theorem support_product_injective {I : Ideal O}
    {S T : Finset (Ideal O)} (hS : S ⊆ primeSupport I) (hT : T ⊆ primeSupport I)
    (h : (∏ P ∈ S, P) = ∏ P ∈ T, P) : S = T := by
  have hf := congrArg normalizedFactors h
  rw [factors_support_product hS, factors_support_product hT] at hf
  exact Finset.val_inj.mp hf

theorem squarefree_divisor_support {I J : Ideal O} (hI : I ≠ ⊥)
    (hJ : Squarefree J) (hJI : J ∣ I) : primeSupport J ⊆ primeSupport I := by
  have hf := (dvd_iff_normalizedFactors_le_normalizedFactors hJ.ne_zero hI).mp hJI
  intro P hP
  exact Multiset.mem_toFinset.mpr (Multiset.mem_of_le hf (Multiset.mem_toFinset.mp hP))

theorem squarefree_support_product_self {J : Ideal O} (hJ : Squarefree J) :
    (∏ P ∈ primeSupport J, P) = J := by
  have hn : (normalizedFactors J).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hJ.ne_zero).mp hJ
  have hv : (primeSupport J).val = normalizedFactors J := by
    simpa only [primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = (primeSupport J).val.prod := (Finset.prod_val _).symm
    _ = (normalizedFactors J).prod := by rw [hv]
    _ = J := Ideal.prod_normalizedFactors_eq_self hJ.ne_zero

theorem squarefree_divisors_eq_image (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).filter Squarefree =
      (primeSupport I).powerset.image (fun S => ∏ P ∈ S, P) := by
  ext J
  simp only [Finset.mem_filter, mem_idealDivisors hI, Finset.mem_image, Finset.mem_powerset]
  constructor
  · rintro ⟨hJI, hJ⟩
    exact ⟨primeSupport J, squarefree_divisor_support hI hJ hJI,
      squarefree_support_product_self hJ⟩
  · rintro ⟨S, hS, rfl⟩
    exact ⟨support_product_dvd hI hS, squarefree_support_product hS⟩

theorem primeSupport_empty_iff (I : Ideal O) (hI : I ≠ ⊥) :
    primeSupport I = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    have hz : normalizedFactors I = 0 := by
      apply Multiset.toFinset_eq_empty.mp
      exact h
    have hp := Ideal.prod_normalizedFactors_eq_self hI
    rw [hz, Multiset.prod_zero] at hp
    simpa only [Ideal.one_eq_top] using hp.symm
  · intro h
    subst I
    simp [primeSupport, ← Ideal.one_eq_top]

theorem sum_moebius_divisors (I : Ideal O) (hI : I ≠ ⊥) :
    (∑ J ∈ idealDivisors I, (moebius J : ℂ)) = if I = ⊤ then 1 else 0 := by
  have hfilter : (∑ J ∈ idealDivisors I, (moebius J : ℂ)) =
      ∑ J ∈ (idealDivisors I).filter Squarefree, (moebius J : ℂ) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro J hJ hnot
    have hn : ¬ Squarefree J := by simpa [hJ] using hnot
    rw [moebius_of_not_squarefree hn, Int.cast_zero]
  rw [hfilter, squarefree_divisors_eq_image I hI, Finset.sum_image]
  · have heq : (∑ S ∈ (primeSupport I).powerset, (moebius (∏ P ∈ S, P) : ℂ)) =
        ∑ S ∈ (primeSupport I).powerset, (-1 : ℂ) ^ S.card := by
      exact Finset.sum_congr rfl (fun S hS => moebius_support_product (Finset.mem_powerset.mp hS))
    rw [heq, CoprimeMobiusExtension.sum_subset_sign]
    simp only [primeSupport_empty_iff I hI]
  · intro S hS T hT hST
    exact support_product_injective (Finset.mem_powerset.mp hS)
      (Finset.mem_powerset.mp hT) hST

end IdealMobiusDivisorSum

open scoped BigOperators Classical

namespace CompletedGauss

section

abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def primaryPrime (P : Ideal O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    (cubicJacobi_exists_primary_generator P h.2).choose
  else 0

theorem primaryPrime_spec (P : Ideal O) (h : primaryPrime P ≠ 0) :
    P.IsMaximal ∧ lambda ∉ P ∧
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
  classical
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    have hs := (cubicJacobi_exists_primary_generator P hg.2).choose_spec
    simpa only [primaryPrime, dif_pos hg] using ⟨hg.1, hg.2, hs.1.symm, hs.2.1⟩
  · simp only [primaryPrime, dif_neg hg, ne_eq, not_true_eq_false] at h

theorem primaryPrime_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) :
    primaryPrime P ≠ 0 := by
  classical
  have hs := (cubicJacobi_exists_primary_generator P hg).choose_spec
  have htest : P.IsMaximal ∧ lambda ∉ P := ⟨inferInstance, hg⟩
  intro hz
  have hp0 : (cubicJacobi_exists_primary_generator P hg).choose = 0 := by
    simpa only [primaryPrime, dif_pos htest] using hz
  rw [hp0] at hs
  exact (NeZero.ne P) (by simpa using hs.1)

def primaryGenerator (I : Ideal O) : O :=
  if I = 0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod

@[simp] theorem primaryGenerator_zero : primaryGenerator 0 = 0 := by rw [primaryGenerator, if_pos rfl]

@[simp] theorem primaryGenerator_bot : primaryGenerator ⊥ = 0 := primaryGenerator_zero

@[simp] theorem primaryGenerator_one : primaryGenerator 1 = 1 := by
  rw [primaryGenerator, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl

theorem primaryGenerator_mul (I J : Ideal O) :
    primaryGenerator (I * J) = primaryGenerator I * primaryGenerator J := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [primaryGenerator, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add, Multiset.prod_add]

def primaryGeneratorHom : Ideal O →*₀ O where
  toFun := primaryGenerator
  map_zero' := primaryGenerator_zero
  map_one' := primaryGenerator_one
  map_mul' := primaryGenerator_mul

theorem primaryGenerator_ne_zero_ideal (I : Ideal O) (h : primaryGenerator I ≠ 0) : I ≠ 0 := by
  intro hI
  exact h (by simp [hI])

theorem primaryPrime_factor_ne_zero (I P : Ideal O) (hI : primaryGenerator I ≠ 0)
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) : primaryPrime P ≠ 0 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hprod : ((UniqueFactorizationMonoid.normalizedFactors I).map primaryPrime).prod ≠ 0 := by
    simpa only [primaryGenerator, if_neg hI0] using hI
  intro hz
  exact hprod (Multiset.prod_eq_zero_iff.mpr (Multiset.mem_map.mpr ⟨P, hP, hz⟩))

theorem span_multiset_prod (s : Multiset O) :
    Ideal.span {s.prod} = (s.map (fun x => Ideal.span {x})).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih => simp only [Multiset.prod_cons, Multiset.map_cons,
      ← Ideal.span_singleton_mul_span_singleton, ih]

theorem primaryGenerator_spec (I : Ideal O) (h : primaryGenerator I ≠ 0) :
    Ideal.span {primaryGenerator I} = I ∧ lambda ^ 2 ∣ primaryGenerator I - 1 := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I h
  have hprime : ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Ideal.span {primaryPrime P} = P ∧ lambda ^ 2 ∣ primaryPrime P - 1 := by
    intro P hP
    exact (primaryPrime_spec P (primaryPrime_factor_ne_zero I P h hP)).2.2
  rw [primaryGenerator, if_neg hI0]
  constructor
  · rw [span_multiset_prod, Multiset.map_map]
    have hm : (UniqueFactorizationMonoid.normalizedFactors I).map
        ((fun x => Ideal.span {x}) ∘ primaryPrime) =
        UniqueFactorizationMonoid.normalizedFactors I := by
      calc
        _ = (UniqueFactorizationMonoid.normalizedFactors I).map id :=
          Multiset.map_congr rfl (fun P hP => (hprime P hP).1)
        _ = _ := Multiset.map_id' _
    rw [hm]
    exact Ideal.prod_normalizedFactors_eq_self hI0
  · apply primary_multiset_prod
    intro r hr
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hr
    exact (hprime P hP).2

theorem primaryGenerator_span (n : O) (hn : n ≠ 0)
    (hprimary : lambda ^ 2 ∣ n - 1) : primaryGenerator (Ideal.span {n}) = n := by
  classical
  have hI0 : (Ideal.span {n} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hn
  have hgen : primaryGenerator (Ideal.span {n}) ≠ 0 := by
    rw [primaryGenerator, if_neg hI0]
    apply Multiset.prod_ne_zero
    intro hzero
    obtain ⟨P, hP, hz⟩ := Multiset.mem_map.mp hzero
    have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hle := ((Ideal.mem_normalizedFactors_iff hI0).mp hP).2
    have hnP : n ∈ P := hle (Ideal.subset_span (by simp))
    exact primaryPrime_ne_zero P (primary_maximal_divisor_good n hprimary P hnP) hz
  have hspec := primaryGenerator_spec (Ideal.span {n}) hgen
  exact primary_associated_eq _ _ (Ideal.span_singleton_eq_span_singleton.mp hspec.1)
    hspec.2 hprimary

open ActualEisensteinCubic

theorem compact_window_bound (W : ℝ → ℂ) (hW : HasCompactSupport W) :
    ∃ B : ℝ, 0 < B ∧ ∀ y, W y ≠ 0 → y ≤ B := by
  obtain ⟨B, hB⟩ := hW.bddAbove
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro y hy
  exact (hB (subset_tsupport W hy)).trans (le_max_left _ _)

end
section

open ActualEisensteinCubic ConcreteTraceCRT

def primeSupport (I : Ideal O) : Finset (Ideal O) :=
  (UniqueFactorizationMonoid.normalizedFactors I).toFinset

abbrev PrimeIndex (I : Ideal O) := {P : Ideal O // P ∈ primeSupport I}

instance primeIndexMaximal (I : Ideal O) (P : PrimeIndex I) : P.val.IsMaximal := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P.val
    (Multiset.mem_toFinset.mp P.property)
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem primeIndex_good (I : Ideal O) (hI : primaryGenerator I ≠ 0) (P : PrimeIndex I) :
    lambda ∉ P.val :=
  (primaryPrime_spec P.val (primaryPrime_factor_ne_zero I P.val hI
    (Multiset.mem_toFinset.mp P.property))).2.1

theorem primeIndex_le (I : Ideal O) (hI : I ≠ 0) (P : PrimeIndex I) : I ≤ P.val :=
  ((Ideal.mem_normalizedFactors_iff hI).mp (Multiset.mem_toFinset.mp P.property)).2

def cubicRow (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O ⧸ I) : ℂ :=
  ∏ P : PrimeIndex I,
    (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
      (Ideal.Quotient.factor (primeIndex_le I (primaryGenerator_ne_zero_ideal I hI) P) x)

def gaussTwo (I : Ideal O) (hI : primaryGenerator I ≠ 0) : ℂ := by
  let n := primaryGenerator I
  letI : Finite (O ⧸ Ideal.span {n}) := finite_quotient_span hI
  letI : Fintype (O ⧸ Ideal.span {n}) := Fintype.ofFinite _
  let e := Ideal.quotEquivOfEq (primaryGenerator_spec I hI).1
  let ψ := eisTraceModChar ShortDraftTrace.breveE ConcreteBreveE.breveE_period_coordinates n hI
  exact (∑ x : O ⧸ Ideal.span {n}, cubicRow I hI (e x) * ψ x) / (‖eisEmbedding n‖ : ℂ)

def squarefreeGaussCoefficient (I : Ideal O) : ℂ :=
  if h : Squarefree I ∧ primaryGenerator I ≠ 0 then
    star (FiniteGaussPhase.angularFactor (primaryGenerator I)) * gaussTwo I h.2
  else 0

@[simp] theorem squarefreeGaussCoefficient_zero : squarefreeGaussCoefficient 0 = 0 := by
  simp [squarefreeGaussCoefficient]

@[simp] theorem squarefreeGaussCoefficient_bot : squarefreeGaussCoefficient ⊥ = 0 :=
  squarefreeGaussCoefficient_zero

theorem angularFactor_mul (a b : O) :
    FiniteGaussPhase.angularFactor (a * b) =
      FiniteGaussPhase.angularFactor a * FiniteGaussPhase.angularFactor b := by
  simp only [FiniteGaussPhase.angularFactor, map_mul, norm_mul, Complex.ofReal_mul]
  ring

def cubeWeight (Ψ : O →* ℂ) : Ideal O →* ℂ where
  toFun I := star (FiniteGaussPhase.angularFactor (primaryGenerator I)) ^ 3 *
    Ψ (primaryGenerator I) ^ 3 / (Ideal.absNorm I : ℂ)
  map_one' := by
    simp only [primaryGenerator_one, FiniteGaussPhase.angularFactor, map_one,
      norm_one, Complex.ofReal_one, div_one, star_one, one_pow, one_mul, Nat.cast_one]
  map_mul' I J := by
    simp only [primaryGenerator_mul, angularFactor_mul, map_mul, star_mul, mul_pow, Nat.cast_mul]
    ring

@[simp] theorem cubeWeight_zero (Ψ : O →* ℂ) : cubeWeight Ψ 0 = 0 := by
  simp [cubeWeight, FiniteGaussPhase.angularFactor]

@[simp] theorem cubeWeight_bot (Ψ : O →* ℂ) : cubeWeight Ψ ⊥ = 0 := cubeWeight_zero Ψ

def columnWeight (Ψ : O →* ℂ) (I : Ideal O) : ℂ :=
  squarefreeGaussCoefficient I * Ψ (primaryGenerator I)

@[simp] theorem columnWeight_zero (Ψ : O →* ℂ) : columnWeight Ψ 0 = 0 := by
  simp [columnWeight]

@[simp] theorem columnWeight_bot (Ψ : O →* ℂ) : columnWeight Ψ ⊥ = 0 := columnWeight_zero Ψ

def Vstar (W : ℝ → ℂ) (y : ℝ) : ℂ := (Real.sqrt y : ℂ) * W y

def summand (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) * cubeWeight Ψ J *
    Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm J : ℝ) ^ 3 / X)

def completedT (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : Ideal O, ∑' J : Ideal O, summand Ψ W X I J

theorem cubicRow_mk (I : Ideal O) (hI : primaryGenerator I ≠ 0) (a : O) :
    cubicRow I hI (Ideal.Quotient.mk I a) =
      ∏ P : PrimeIndex I, (canonicalSextic P.val (primeIndex_good I hI P) ^ 2)
        (Ideal.Quotient.mk P.val a) := by
  simp only [cubicRow, Ideal.Quotient.factor_mk]

end

open ActualEisensteinCubic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors sum_moebius_divisors)

def MulFiber (B : Ideal O) := {p : Ideal O × Ideal O // p.1 * p.2 = B}

def mulFiberDivisorEquiv (B : Ideal O) (hB : B ≠ 0) :
    MulFiber B ≃ {D : Ideal O // D ∈ idealDivisors B} := by
  let f : MulFiber B → {D : Ideal O // D ∈ idealDivisors B} :=
    fun p => ⟨p.val.1, (mem_idealDivisors hB).mpr ⟨p.val.2, p.property.symm⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hfst : p.val.1 = q.val.1 := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Prod.ext hfst
    have hn : p.val.1 ≠ 0 := by
      intro hz
      have he := p.property
      rw [hz, zero_mul] at he
      exact hB he.symm
    apply mul_left_cancel₀ hn
    rw [p.property, hfst, q.property]
  · intro D
    obtain ⟨J, hJ⟩ := (mem_idealDivisors hB).mp D.property
    exact ⟨⟨(D.val, J), hJ.symm⟩, rfl⟩

theorem mulFiber_moebius_sum (B : Ideal O) (hB : B ≠ 0) :
    (∑' p : MulFiber B, (UniqueFactorizationMonoid.moebius p.val.1 : ℂ)) =
      if B = 1 then 1 else 0 := by
  let e := mulFiberDivisorEquiv B hB
  calc
    _ = ∑' D : {D : Ideal O // D ∈ idealDivisors B},
        (UniqueFactorizationMonoid.moebius D.val : ℂ) := by
      exact e.tsum_eq (fun D => (UniqueFactorizationMonoid.moebius D.val : ℂ))
    _ = ∑ D ∈ idealDivisors B, (UniqueFactorizationMonoid.moebius D : ℂ) := by
      rw [tsum_fintype]
      exact (Finset.sum_subtype (idealDivisors B) (fun D => Iff.rfl)
        (fun D => (UniqueFactorizationMonoid.moebius D : ℂ))).symm
    _ = if B = 1 then 1 else 0 := by
      simpa only [Ideal.one_eq_top] using sum_moebius_divisors B hB

end CompletedGauss

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace CompletedGauss

open ActualEisensteinCubic

def expandedTerm (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (I H J : Ideal O) : ℂ :=
  (UniqueFactorizationMonoid.moebius H : ℂ) * cubeWeight Ψ (H * J) *
    (columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I : ℝ) : ℂ) *
      Vstar W ((Ideal.absNorm I : ℝ) * (Ideal.absNorm H : ℝ) ^ 3 *
        (Ideal.absNorm J : ℝ) ^ 3 / X))

open ActualEisensteinCubic ConcreteTraceCRT

theorem normalizedFactors_product {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal] :
    UniqueFactorizationMonoid.normalizedFactors (Ideal.span {∏ i, p i}) =
      Finset.univ.val.map (fun i => Ideal.span {p i}) := by
  have hp (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have h := UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
    (m := Finset.univ.val.map (fun i => Ideal.span {p i})) (by
      intro P hP
      obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hP
      exact hp i)
  rw [FiniteGaussPhase.span_finset_prod]
  exact h

def productPrimeIndexEquiv {ι : Type*} [Fintype ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) :
    ι ≃ PrimeIndex (Ideal.span {∏ i, p i}) := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hmem (i : ι) : (Ideal.span {p i} : Ideal O) ∈ primeSupport (Ideal.span {∏ i, p i}) := by
    rw [primeSupport, normalizedFactors_product]
    exact Multiset.mem_toFinset.mpr (Multiset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let f : ι → PrimeIndex (Ideal.span {∏ i, p i}) := fun i => ⟨Ideal.span {p i}, hmem i⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    exact hinj (congrArg Subtype.val hij)
  · intro P
    have hm := Multiset.mem_toFinset.mp P.property
    rw [normalizedFactors_product] at hm
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hm
    exact ⟨i, Subtype.ext hi⟩

end CompletedGauss

namespace FiniteRayExpansion

variable {R : Type*} [CommRing R] [Fintype R]
noncomputable local instance : Fintype (MulChar R ℂ) := Fintype.ofFinite _

def unitFourierCoeff (f : Rˣ → ℂ) (χ : MulChar R ℂ) : ℂ :=
  (∑ u : Rˣ, f u * star (χ (u : R))) / (Fintype.card Rˣ : ℂ)

theorem unit_fourier_inversion (f : Rˣ → ℂ) (v : Rˣ) :
    (∑ χ : MulChar R ℂ, unitFourierCoeff f χ * χ (v : R)) = f v := by
  have hN : (Fintype.card Rˣ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp_rw [unitFourierCoeff, div_mul_eq_mul_div, Finset.sum_mul, mul_assoc]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, FiniteRingSieve.unit_char_orthogonal]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact mul_div_cancel_right₀ (f v) hN

theorem norm_char_unit (χ : MulChar R ℂ) (u : Rˣ) : ‖χ (u : R)‖ = 1 := by
  simpa only [MulChar.coe_equivToUnitHom] using
    Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

theorem norm_char_le_one (χ : MulChar R ℂ) (r : R) : ‖χ r‖ ≤ 1 := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    exact (norm_char_unit χ u).le
  · rw [MulChar.map_nonunit χ hr, norm_zero]
    norm_num

theorem unitFourierCoeff_norm_le_average (f : Rˣ → ℂ) (χ : MulChar R ℂ) :
    ‖unitFourierCoeff f χ‖ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := by
  rw [unitFourierCoeff, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ u : Rˣ, ‖f u * star (χ (u : R))‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_mul, norm_star, norm_char_unit, mul_one]

theorem unitFourierCoeff_norm_le (f : Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u, ‖f u‖ ≤ B) (χ : MulChar R ℂ) : ‖unitFourierCoeff f χ‖ ≤ B := by
  have hN : (Fintype.card Rˣ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ (∑ u : Rˣ, ‖f u‖) / (Fintype.card Rˣ : ℝ) := unitFourierCoeff_norm_le_average f χ
    _ ≤ (∑ _u : Rˣ, B) / (Fintype.card Rˣ : ℝ) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun u _ => hf u)) (by positivity)
    _ = B := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem character_card_eq_units : Fintype.card (MulChar R ℂ) = Fintype.card Rˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity R ℂ

def zeroExtendUnits (f : Rˣ → ℂ) (r : R) : ℂ :=
  if hr : IsUnit r then f hr.unit else 0

@[simp] theorem zeroExtendUnits_unit (f : Rˣ → ℂ) (u : Rˣ) :
    zeroExtendUnits f (u : R) = f u := by
  rw [zeroExtendUnits, dif_pos u.isUnit]
  congr 1
  exact Units.ext u.isUnit.unit_spec

@[simp] theorem zeroExtendUnits_nonunit (f : Rˣ → ℂ) (r : R) (hr : ¬ IsUnit r) :
    zeroExtendUnits f r = 0 := dif_neg hr

theorem zeroExtendUnits_restrict (f : R → ℂ) (r : R) :
    zeroExtendUnits (fun u : Rˣ => f (u : R)) r = (if IsUnit r then 1 else 0) * f r := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnits_unit, u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

def unitTensorCoeff (f : Rˣ → Rˣ → ℂ) (χ η : MulChar R ℂ) : ℂ :=
  unitFourierCoeff (fun u => unitFourierCoeff (f u) η) χ

theorem unit_tensor_fourier_inversion (f : Rˣ → Rˣ → ℂ) (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ (u : R) * η (v : R)) = f u v := by
  calc
    _ = ∑ η : MulChar R ℂ,
        (∑ χ : MulChar R ℂ, unitTensorCoeff f χ η * χ (u : R)) * η (v : R) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ = ∑ η : MulChar R ℂ, unitFourierCoeff (f u) η * η (v : R) := by
      apply Finset.sum_congr rfl
      intro η _
      change (∑ χ : MulChar R ℂ,
        unitFourierCoeff (fun a => unitFourierCoeff (f a) η) χ * χ (u : R)) * η (v : R) = _
      rw [unit_fourier_inversion]
    _ = _ := unit_fourier_inversion (f u) v

theorem unitTensorCoeff_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) (χ η : MulChar R ℂ) :
    ‖unitTensorCoeff f χ η‖ ≤ B :=
  unitFourierCoeff_norm_le _ B (fun u => unitFourierCoeff_norm_le (f u) B (hf u) η) χ

theorem unitTensorCoeff_sum_norm_le (f : Rˣ → Rˣ → ℂ) (B : ℝ)
    (hf : ∀ u v, ‖f u v‖ ≤ B) :
    (∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ, ‖unitTensorCoeff f χ η‖) ≤
      (Fintype.card Rˣ : ℝ) ^ 2 * B := by
  calc
    _ ≤ ∑ _χ : MulChar R ℂ, ∑ _η : MulChar R ℂ, B :=
      Finset.sum_le_sum (fun χ _ => Finset.sum_le_sum (fun η _ => unitTensorCoeff_norm_le f B hf χ η))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, character_card_eq_units]
      ring

def zeroExtendUnitPair (f : Rˣ → Rˣ → ℂ) (r s : R) : ℂ :=
  zeroExtendUnits (fun u => zeroExtendUnits (f u) s) r

theorem zeroExtendUnitPair_fourier (f : Rˣ → Rˣ → ℂ) (r s : R) :
    zeroExtendUnitPair f r s = ∑ χ : MulChar R ℂ, ∑ η : MulChar R ℂ,
      unitTensorCoeff f χ η * χ r * η s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    by_cases hs : IsUnit s
    · obtain ⟨v, rfl⟩ := hs
      simp only [zeroExtendUnitPair, zeroExtendUnits_unit]
      exact (unit_tensor_fourier_inversion f u v).symm
    · simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_nonunit _ _ hs,
        MulChar.map_nonunit _ hs, mul_zero, Finset.sum_const_zero]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr,
      MulChar.map_nonunit _ hr, mul_zero, zero_mul, Finset.sum_const_zero]

theorem zeroExtendUnitPair_restrict (f : R → R → ℂ) (r s : R) :
    zeroExtendUnitPair (fun u v : Rˣ => f (u : R) (v : R)) r s =
      (if IsUnit r then 1 else 0) * (if IsUnit s then 1 else 0) * f r s := by
  by_cases hr : IsUnit r
  · obtain ⟨u, rfl⟩ := hr
    simp only [zeroExtendUnitPair, zeroExtendUnits_unit, zeroExtendUnits_restrict,
      u.isUnit, ite_true, one_mul]
  · simp only [zeroExtendUnitPair, zeroExtendUnits_nonunit _ _ hr, hr, ite_false, zero_mul]

end FiniteRayExpansion

open scoped BigOperators Classical

namespace RayFourExpansion
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT ActualEisensteinCoordinates QuadraticGaussRay
open FiniteRayExpansion

abbrev RayRing := O ⧸ Ideal.span {(4 : O)}

noncomputable instance rayRingFintype : Fintype RayRing := by
  letI : Finite RayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _

abbrev RayCharacter := MulChar RayRing ℂ
noncomputable instance rayCharacterFintype : Fintype RayCharacter := Fintype.ofFinite _

def rayCharacter (χ : RayCharacter) (a : O) : ℂ :=
  χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)

theorem rayCharacter_mul (χ : RayCharacter) (a b : O) :
    rayCharacter χ (a * b) = rayCharacter χ a * rayCharacter χ b := by
  simp only [rayCharacter, map_mul]

def rayMask (a : O) : ℂ :=
  if IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a) then 1 else 0

theorem rayRing_card : Fintype.card RayRing = 16 := by
  have h := rational_modulus_card 4 (by decide)
  simpa only [Nat.card_eq_fintype_card, Nat.cast_ofNat, show (4 : ℕ) ^ 2 = 16 by decide] using h

theorem rayUnit_card_le : Fintype.card RayRingˣ ≤ 16 := by
  calc
    _ ≤ Fintype.card RayRing := Fintype.card_le_of_injective _ Units.val_injective
    _ = 16 := rayRing_card

def phaseCoeff (f : RayRing → ℂ) (χ : RayCharacter) : ℂ :=
  unitFourierCoeff (fun u : RayRingˣ => f (u : RayRing)) χ

def pairCoeff (f : RayRing → RayRing → ℂ) (χ η : RayCharacter) : ℂ :=
  unitTensorCoeff (fun u v : RayRingˣ => f (u : RayRing) (v : RayRing)) χ η

theorem pair_phase_expansion (f : RayRing → RayRing → ℂ) (a b : O) :
    rayMask a * rayMask b *
      f (Ideal.Quotient.mk (Ideal.span {(4 : O)}) a)
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        pairCoeff f χ η * rayCharacter χ a * rayCharacter η b := by
  rw [rayMask, rayMask, ← zeroExtendUnitPair_restrict]
  exact zeroExtendUnitPair_fourier _ _ _

theorem pairCoeff_sum_norm_le (f : RayRing → RayRing → ℂ) (B : ℝ)
    (hf : ∀ u v : RayRingˣ, ‖f (u : RayRing) (v : RayRing)‖ ≤ B) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖pairCoeff f χ η‖) ≤ 256 * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hf 1 1)
  have hcard : (Fintype.card RayRingˣ : ℝ) ^ 2 ≤ 256 := by
    have h : (Fintype.card RayRingˣ : ℝ) ≤ 16 := by exact_mod_cast rayUnit_card_le
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card RayRingˣ)]
  exact (unitTensorCoeff_sum_norm_le _ B hf).trans (mul_le_mul_of_nonneg_right hcard hB)

theorem quadraticRayValue_bounds (r : EisensteinEPrimaryPhase.Coord) :
    ‖quadraticRayValue r‖ ≤ 2 ∧ ‖(quadraticRayValue r)⁻¹‖ ≤ 1 := by
  rcases r with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    norm_num [quadraticRayValue, breveGaussianFourTerms_formula, zpow_neg,
      Complex.I_sq, Complex.I_pow_three, Complex.inv_I,
      ZMod.val] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.inv_I]

def gCoeff : RayCharacter → ℂ := phaseCoeff fixedGQuotientValue

def crossQuotientPhase (r s : RayRing) : ℂ :=
  MixedCrossSeparation.quadraticRayPair (residueQuotientFour r) (residueQuotientFour s)

theorem crossQuotientPhase_norm_le_two (r s : RayRing) : ‖crossQuotientPhase r s‖ ≤ 2 := by
  unfold crossQuotientPhase MixedCrossSeparation.quadraticRayPair
  rw [div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  calc
    _ ≤ 2 * (1 * 1) :=
      mul_le_mul (quadraticRayValue_bounds _).1
        (mul_le_mul (quadraticRayValue_bounds _).2 (quadraticRayValue_bounds _).2
          (norm_nonneg _) (by norm_num))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = 2 := by norm_num

def crossCoeff : RayCharacter → RayCharacter → ℂ := pairCoeff crossQuotientPhase

theorem crossCoeff_sum_norm_le :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) ≤ 512 := by
  exact (pairCoeff_sum_norm_le _ 2 (fun u v => crossQuotientPhase_norm_le_two u v)).trans_eq (by norm_num)

theorem quadraticRayPair_character_expansion (a b : O) :
    rayMask a * rayMask b * MixedCrossSeparation.quadraticRayPair (residue a) (residue b) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ a * rayCharacter η b := by
  simpa only [crossCoeff, crossQuotientPhase, residueQuotientFour_mk] using
    pair_phase_expansion crossQuotientPhase a b

end RayFourExpansion

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace RayFourExpansion
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase QuadraticGaussRay
open ActualEisensteinCoordinates MixedCrossSeparation

theorem prime_unit_mod_four (p : O) [(Ideal.span {p}).IsMaximal]
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) p) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have h2 : (2 : O) ∉ Ideal.span {p} := by
    intro hm
    have hz : (2 : O ⧸ Ideal.span {p}) = 0 := by
      simpa only [map_ofNat] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
    apply hchar
    exact (Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime (O ⧸ Ideal.span {p}) _)
      Nat.prime_two).mp ((ringChar.spec (O ⧸ Ideal.span {p}) 2).mp hz)
  let : (Ideal.span {(2 : O)}).IsMaximal := by
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using cubicTwoIdeal_isMaximal
  have hcop : IsCoprime (Ideal.span {p}) (Ideal.span {(2 : O)}) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    apply h2
    rw [heq]
    exact Ideal.subset_span (by simp)
  obtain ⟨a, b, hab⟩ := IdealGaussCRT.bezout_of_principal_coprime hcop
  have hcp : IsCoprime p (2 : O) := ⟨a, b, hab⟩
  have hcp4 : IsCoprime p (4 : O) := by
    simpa only [show (2 : O) ^ 2 = 4 by norm_num] using
      (hcp.pow_right : IsCoprime p ((2 : O) ^ 2))
  obtain ⟨a, b, hab⟩ := hcp4
  have hz : Ideal.Quotient.mk (Ideal.span {(4 : O)}) (4 : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hm := congrArg (Ideal.Quotient.mk (Ideal.span {(4 : O)})) hab
  simp only [map_add, map_mul, map_one, hz, mul_zero, add_zero] at hm
  exact IsUnit.of_mul_eq_one_right _ hm

theorem prime_product_unit_mod_four {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  rw [map_prod]
  exact IsUnit.prod_iff.mpr (fun i _ => prime_unit_mod_four (p i) (hchar i))

theorem rayMask_prime_product {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S : Finset ι) :
    rayMask (∏ i ∈ S, p i) = 1 := by
  rw [rayMask, if_pos (prime_product_unit_mod_four p hchar S)]

end RayFourExpansion

namespace FirstCauchyArithmetic

section
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic CoprimeMobiusExtension

def supportMobius {ι : Type*} (P : ι → Ideal O) (S : Finset ι) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏ i ∈ S, P i) : ℂ)

def supportConjugateSum {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) (C : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ S ∈ B.powerset, supportMobius P S * C S * star (finiteSquarefreeRow P hg S h)

end
section

open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedCrossSeparation RayFourExpansion

def supportRay {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) : ℂ :=
  rayCharacter χ (∏ i ∈ S, p i)

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem family_prime {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (i : ι) :
    Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance

theorem family_prod_ne_zero {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) :
    (∏ i ∈ S, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => (family_prime P i).ne_zero)

def supportIdealFamily {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) : Finset (Ideal O) :=
  B.powerset.image (fun S => ∏ i ∈ S, P i)

theorem supportIdealFamily_pos {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B, I ≠ ⊥ := by
  intro I hI
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  exact family_prod_ne_zero P S

theorem factor_family_product_iff {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset ι) (Q : Ideal O) :
    Q ∈ UniqueFactorizationMonoid.normalizedFactors (∏ i ∈ S, P i) ↔
      ∃ i ∈ S, Q = P i := by
  rw [UniqueFactorizationMonoid.mem_normalizedFactors_iff (family_prod_ne_zero P S)]
  constructor
  · rintro ⟨hQ, hd⟩
    obtain ⟨i, hi, hdiv⟩ := (hQ.dvd_finsetProd_iff P).mp hd
    exact ⟨i, hi, associated_iff_eq.mp (hQ.associated_of_dvd (family_prime P i) hdiv)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨family_prime P i, Finset.dvd_prod_of_mem P hi⟩

theorem supportIdealFamily_good {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (B : Finset ι) :
    ∀ I ∈ supportIdealFamily P B,
      ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I, goodLambda ∉ Q := by
  intro I hI Q hQ
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨i, hi, rfl⟩ := (factor_family_product_iff P S Q).mp hQ
  exact hg i

def recoveredSupport {ι : Type*} [DecidableEq ι]
    (P : ι → Ideal O) (B : Finset ι) (I : Ideal O) : Finset ι :=
  B.filter (fun i => P i ∣ I)

end FirstCauchyArithmetic

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace MixedCrossSeparation
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion

theorem columnPrimeCoprime {ι : Type*} (p : ι → O)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (S : Finset ι) :
    Pairwise (Function.onFun IsCoprime (fun i : S => Ideal.span {p i.val})) := by
  intro i j hij
  exact hcop (fun h => hij (Subtype.ext h))

def columnCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductCoefficient (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

def columnG {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) : ℂ :=
  canonicalProductG (fun i : S => p i.val) (fun i => hp i.val)
    (columnPrimeCoprime p hcop S) (fun i => hg i.val)

end MixedCrossSeparation

open scoped BigOperators Classical SchwartzMap ContDiff
namespace FirstCauchyArithmetic
open ActualEisensteinCubic ConcreteTraceCRT FiniteGaussPhase MixedGaussConversion
open MixedCrossSeparation GaussGeneratorTransport ConcretePrimeRowBridge EisensteinSchwartzPoisson

def firstPassColumnMinus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S (-1)) *
    columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

def firstPassColumnPlus {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  columnG p hp hcop hg S * finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d * C S

def activeGaussRowFactor
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S T : Finset ι) (d h : O) : ℂ :=
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let row := finiteSexticRow (activePrimes P S T) (fun i => hg i.val) (activeExponent S T)
  canonicalProductGauss (fun i : activeSupport S T => p i.val) (fun i => hp i.val)
    (activePrimes_pairwise_isCoprime P hinj S T) (fun i => hg i.val) (activeExponent S T) *
      (row d * star (row h))

end FirstCauchyArithmetic

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def pvSeminorms : Finset (ℕ × ℕ) :=
  Classical.choose paperRadialFourier_nonzero_lattice_uniform

def pvConstant : ℝ :=
  Classical.choose (Classical.choose_spec paperRadialFourier_nonzero_lattice_uniform)

def pvControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  pvConstant * pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) W

end QuadraticInitialBound

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson

def quadraticRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 3

theorem quadraticRow_eq_canonical {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    quadraticRow P hg S z =
      finiteSexticRow (fun i : S => P i.val) (fun i => hg i.val) (fun _ => 3) z := by
  simp only [quadraticRow, finiteSexticRow, finiteSquarefreeRow,
    MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), Finset.prod_pow]
  rw [Finset.prod_coe_sort (s := S) (f := fun i => canonicalSextic (P i) (hg i) (Ideal.Quotient.mk (P i) z))]

theorem quadraticRow_star {α : Type*}
    (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, lambda ∉ P i) (S : Finset α) (z : O) :
    star (quadraticRow P hg S z) = quadraticRow P hg S z := by
  rw [quadraticRow_eq_canonical]
  simp only [finiteSexticRow, star_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [canonicalSextic_pow_three_quadratic]
  simp only [MulChar.ringHomComp_apply, Int.coe_castRingHom, star_intCast]

def supportNorm {α : Type*} (P : α → Ideal O) (S : Finset α) : ℝ :=
  Ideal.absNorm (∏ i ∈ S, P i)

def diagonalControl (W : 𝓢(ℝ, ℂ)) : ℝ :=
  16 * (1 + Real.pi) ^ 2 *
    (Finset.Iic (2, 0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) W

def sieveBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def sieveCutoff : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun t : ℝ => (sieveBump t : ℂ)) :=
    sieveBump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hs : ContDiff ℝ ∞ (fun t : ℝ => (sieveBump t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp sieveBump.contDiff
  exact hc.toSchwartzMap hs

@[simp] theorem sieveCutoff_apply (t : ℝ) : sieveCutoff t = (sieveBump t : ℂ) := rfl

theorem sieveBump_eq_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : sieveBump t = 1 := by
  apply sieveBump.one_of_mem_closedBall
  change dist t 0 ≤ 1
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht0] using ht1

open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open ConcretePrimeRowBridge ShortDraftHeckeBridge

def initialSieveConstant : ℝ :=
  diagonalControl sieveCutoff + 128 * pvControl sieveCutoff + 1

end QuadraticInitialBound

open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory

namespace CubicReflectionKernel

def gammaMultiplier (s : ℂ) : ℂ :=
  Complex.Gamma ((7 / 6 : ℂ) + s) * Complex.Gamma ((5 / 6 : ℂ) + s) /
    (Complex.Gamma ((7 / 6 : ℂ) - s) * Complex.Gamma ((5 / 6 : ℂ) - s))

def axisMultiplier (u : ℝ) : ℂ := gammaMultiplier ((2 * Real.pi * u : ℝ) * Complex.I)

def spectralProfile (logSource : SchwartzMap ℝ ℂ) (u : ℝ) : ℂ := axisMultiplier u * (𝓕 logSource) u

def reflectedLogProfile (logSource : SchwartzMap ℝ ℂ) : ℝ → ℂ := 𝓕 (spectralProfile logSource)

end CubicReflectionKernel

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Asymptotics

def paperScale : ℝ := (2 * Real.pi) ^ 4 / 27

def paperKernel (V : ℝ → ℂ) (x : ℝ) : ℂ :=
  mellinInv 0 (fun t => mellin V (-t) * gammaMultiplier t) (paperScale * x)

theorem logProfile_compact (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) :
    HasCompactSupport (fun u : ℝ => V (Real.exp u)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (K := Set.Icc (Real.log a) (Real.log b)) isCompact_Icc
  intro u hu
  have huv : V (Real.exp u) ≠ 0 := hu
  have hm := hsupp huv
  constructor
  · simpa only [Real.log_exp] using Real.log_le_log ha hm.1
  · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos u) hm.2

def logSchwartz (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) :
    SchwartzMap ℝ ℂ :=
  (logProfile_compact V a b ha hsupp).toSchwartzMap (hV.comp Real.contDiff_exp)

@[simp] theorem logSchwartz_apply (V : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hsupp : Function.support V ⊆ Set.Icc a b) (hV : ContDiff ℝ ∞ V) (u : ℝ) :
    logSchwartz V a b ha hsupp hV u = V (Real.exp u) := rfl

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter

open scoped BigOperators Classical

namespace DescentWeightedCauchy

abbrev O := ActualEisensteinCubic.O

def firstElementRowMap (e : O) (x : Ideal O × O) : O :=
  x.2 * ConcretePrimeRowBridge.idealGenerator x.1 ^ 2 * e

end DescentWeightedCauchy

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

namespace SquarefreeDivisorBound
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum

abbrev O := ActualEisensteinCubic.O

theorem prime_support_subsets_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal O, I ≠ ⊥ →
      (2 : ℝ) ^ (primeSupport I).card ≤ C * (Ideal.absNorm I : ℝ) ^ ε := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  let small : Finset (Ideal O) :=
    (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset
  refine ⟨(2 : ℝ) ^ small.card, by positivity, ?_⟩
  intro I hI
  let S := primeSupport I
  let A := S ∩ small
  let B := S \ small
  have hBS : B ⊆ primeSupport I := Finset.sdiff_subset
  have hlarge (P : Ideal O) (hP : P ∈ B) : (2 : ℝ) ≤ (Ideal.absNorm P : ℝ) ^ ε := by
    apply hN
    have hn : P ∉ small := (Finset.mem_sdiff.mp hP).2
    have hgt : N < Ideal.absNorm P := by
      apply Nat.lt_of_not_ge
      intro hp
      exact hn (by simpa [small] using hp)
    exact hgt.le
  have hpowB : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm (∏ P ∈ B, P) : ℝ) ^ ε := by
    calc
      _ = ∏ P ∈ B, (2 : ℝ) := by simp
      _ ≤ ∏ P ∈ B, (Ideal.absNorm P : ℝ) ^ ε :=
        Finset.prod_le_prod (fun _ _ => by positivity) hlarge
      _ = (∏ P ∈ B, (Ideal.absNorm P : ℝ)) ^ ε :=
        (Real.finsetProd_rpow B (fun P => (Ideal.absNorm P : ℝ))
          (fun _ _ => by positivity) ε)
      _ = _ := by simp only [map_prod, Nat.cast_prod]
  have hNI : 0 < Ideal.absNorm I := Nat.pos_iff_ne_zero.mpr
    (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have hnorm : Ideal.absNorm (∏ P ∈ B, P) ≤ Ideal.absNorm I :=
    Nat.le_of_dvd hNI (map_dvd Ideal.absNorm (support_product_dvd hI hBS))
  have hpowBI : (2 : ℝ) ^ B.card ≤ (Ideal.absNorm I : ℝ) ^ ε :=
    hpowB.trans (Real.rpow_le_rpow (by positivity) (by exact_mod_cast hnorm) hε.le)
  have hAc : A.card ≤ small.card := Finset.card_le_card Finset.inter_subset_right
  have hcard : S.card = A.card + B.card := by
    simp [A, B]
  change (2 : ℝ) ^ S.card ≤ _
  rw [hcard, pow_add]
  exact mul_le_mul (pow_le_pow_right₀ (by norm_num) hAc) hpowBI
    (by positivity) (by positivity)

open DescentWeightedCauchy

end SquarefreeDivisorBound

open scoped BigOperators Classical
namespace FirstPassCubeLabels
abbrev O := ActualEisensteinCubic.O
open ActualEisensteinCubic

def bit (b : Bool) : ℕ := if b then 1 else 0

def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

section Rows
variable {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

include hg

def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  rowCoprimeMask P S a *
    finiteSquarefreeRow P hg S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    finiteSquarefreeRow P hg S a ^ crtExponent side parityBit ε₁ ε₂ *
    finiteSquarefreeRow P hg S a ^ dilationExponent parityBit ε₁ ε₂

end Rows

def parity (m : ℕ) : Bool := decide (m % 2 = 1)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)

section Reassembly
variable {ι κ : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
  (hg : ∀ i, lambda ∉ P i) (S : Finset ι)

def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j

def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j

def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))

def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))

def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))

def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))

def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))

def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))

def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))

end Reassembly

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap
namespace QuadraticInitialBound
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open FiniteGaussPhase MixedCrossSeparation ActualEisensteinCoordinates QuadraticGaussRay
open RayFourExpansion

def quadraticSymbol {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) : ℂ :=
  quadraticRow (fun i => Ideal.span {p i}) hg A (∏ i ∈ B, p i)

theorem quadraticSymbol_eq_cross_product {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B = ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 := by
  simp only [quadraticSymbol, quadraticRow, finiteSquarefreeRow, map_prod,
    ← Finset.prod_pow, crossSymbol]

theorem quadraticSymbol_mul_reverse {ι : Type*}
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) :
    quadraticSymbol p hg A B * quadraticSymbol p hg B A = quadraticCrossPhase p hg A B := by
  rw [quadraticSymbol_eq_cross_product, quadraticSymbol_eq_cross_product]
  rw [Finset.prod_comm (s := B) (t := A)]
  simp only [quadraticCrossPhase, Finset.prod_mul_distrib]

theorem quadraticSymbol_eq_zero_of_not_disjoint {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (h : ¬ Disjoint A B) :
    quadraticSymbol p hg A B = 0 := by
  obtain ⟨i, hiA, hiB⟩ := Finset.not_disjoint_iff.mp h
  rw [quadraticSymbol_eq_cross_product]
  apply Finset.prod_eq_zero hiA
  apply Finset.prod_eq_zero hiB
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (p i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  simp only [crossSymbol, hz, MulChar.map_zero, zero_pow (by decide : 3 ≠ 0)]

theorem quadraticSymbol_sq_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (A B : Finset ι) (hd : Disjoint A B) :
    quadraticSymbol p hg A B ^ 2 = 1 := by
  rw [quadraticSymbol_eq_cross_product, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro k hk
  have hik : i ≠ k := by
    intro h
    subst k
    exact Finset.disjoint_left.mp hd hi hk
  rw [← pow_mul]
  simpa only [crossSymbol, show 3 * 2 = 6 by decide, map_pow,
    if_neg (prime_generator_not_mem_other p hcop i k hik)] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)

theorem quadraticSymbol_reciprocity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      quadraticRayPair (residue (∏ i ∈ A, p i)) (residue (∏ i ∈ B, p i)) *
        quadraticSymbol p hg B A := by
  by_cases hd : Disjoint A B
  · have hprod := quadraticSymbol_mul_reverse p hg A B
    rw [quadraticCrossPhase_eq_rayPair p hp hcop hg hc A B hd] at hprod
    have hsq := quadraticSymbol_sq_eq_one p hcop hg B A hd.symm
    calc
      _ = quadraticSymbol p hg A B * (quadraticSymbol p hg B A) ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSymbol_eq_zero_of_not_disjoint p hg A B hd,
      quadraticSymbol_eq_zero_of_not_disjoint p hg B A (fun h => hd h.symm), mul_zero]

theorem quadraticSymbol_reciprocity_characters {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (A B : Finset ι) :
    quadraticSymbol p hg A B =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayCharacter χ (∏ i ∈ A, p i) *
          rayCharacter η (∏ i ∈ B, p i) * quadraticSymbol p hg B A := by
  rw [quadraticSymbol_reciprocity p hp hcop hg hc]
  have hr := quadraticRayPair_character_expansion (∏ i ∈ A, p i) (∏ i ∈ B, p i)
  rw [rayMask_prime_product p hc A, rayMask_prime_product p hc B, one_mul, one_mul] at hr
  rw [hr]
  simp only [Finset.sum_mul]

end QuadraticInitialBound

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
namespace CubicReflectionKernel

def realBeta (a b : ℝ) : ℝ :=
  ∫ x : ℝ in 0..1, x ^ (a - 1) * (1 - x) ^ (b - 1)

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def mellinLogFamily (V : ℝ → ℂ) (σ u : ℝ) : ℂ :=
  Real.exp (-σ * u) • V (Real.exp (-u))

end CubicReflectionKernel

open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter Set
namespace CubicReflectionKernel

def mellinData (V : ℝ → ℂ) (s : ℂ) : ℂ := mellin V (-s) * gammaMultiplier s

def mellinEulerData (V : ℝ → ℂ) (j : ℕ) (s : ℂ) : ℂ := (-s) ^ j * mellinData V s

end CubicReflectionKernel

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical

namespace CubicJacobiGlobal
abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CompletedGauss

def primeValue (P : Ideal O) (x : O) : O :=
  if h : P.IsMaximal ∧ lambda ∉ P then
    letI : P.IsMaximal := h.1
    cubicChar P h.2 (Ideal.Quotient.mk P x)
  else 0

@[simp] theorem primeValue_eq (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O) :
    primeValue P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  simp only [primeValue, dif_pos (show P.IsMaximal ∧ lambda ∉ P from
    ⟨inferInstance, hgood⟩)]

def idealSymbol (I : Ideal O) (x : O) : O :=
  if I = 0 then 0 else
    ((UniqueFactorizationMonoid.normalizedFactors I).map (fun P => primeValue P x)).prod

@[simp] theorem idealSymbol_zero (x : O) : idealSymbol 0 x = 0 := by simp [idealSymbol]
@[simp] theorem idealSymbol_bot (x : O) : idealSymbol ⊥ x = 0 := idealSymbol_zero x
@[simp] theorem idealSymbol_one (x : O) : idealSymbol 1 x = 1 := by
  rw [idealSymbol, if_neg one_ne_zero, UniqueFactorizationMonoid.normalizedFactors_one]
  rfl
@[simp] theorem idealSymbol_top (x : O) : idealSymbol ⊤ x = 1 := by
  simpa only [Ideal.one_eq_top] using idealSymbol_one x

theorem idealSymbol_mul (I J : Ideal O) (x : O) :
    idealSymbol (I * J) x = idealSymbol I x * idealSymbol J x := by
  classical
  by_cases hI : I = 0
  · simp [hI]
  by_cases hJ : J = 0
  · simp [hJ]
  simp only [idealSymbol, if_neg hI, if_neg hJ, if_neg (mul_ne_zero hI hJ),
    UniqueFactorizationMonoid.normalizedFactors_mul hI hJ, Multiset.map_add,
    Multiset.prod_add]

def symbol (x y : O) : O := idealSymbol (Ideal.span {y}) x

@[simp] theorem symbol_one (x : O) : symbol x 1 = 1 := by simp [symbol]
@[simp] theorem symbol_zero (x : O) : symbol x 0 = 0 := by simp [symbol]

theorem symbol_mul_denominator (x y z : O) :
    symbol x (y * z) = symbol x y * symbol x z := by
  rw [symbol, ← Ideal.span_singleton_mul_span_singleton, idealSymbol_mul]
  rfl

theorem idealSymbol_prime (P : Ideal O) [P.IsMaximal] (hgood : lambda ∉ P) (x : O) :
    idealSymbol P x = cubicChar P hgood (Ideal.Quotient.mk P x) := by
  have hP0 : P ≠ 0 := NeZero.ne _
  have hp : Prime P := Ideal.prime_of_isPrime hP0 (inferInstance : P.IsPrime)
  rw [idealSymbol, if_neg hP0,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible]
  simpa using primeValue_eq P hgood x

theorem factor_good (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (P : Ideal O) (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I) :
    P.IsMaximal ∧ lambda ∉ P := by
  exact ⟨(primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).1,
    (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.1⟩

theorem idealSymbol_map_mul (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x y : O) :
    idealSymbol I (x * y) = idealSymbol I x * idealSymbol I y := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  simp only [idealSymbol, if_neg hI0]
  rw [← Multiset.prod_map_mul]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_mul]

theorem idealSymbol_map_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) :
    idealSymbol I 1 = 1 := by
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  rw [idealSymbol, if_neg hI0]
  apply Multiset.prod_eq_one
  intro y hy
  obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp hy
  have hg := factor_good I hI P hP
  let : P.IsMaximal := hg.1
  simp only [primeValue_eq P hg.2, map_one]

theorem idealSymbol_map_multiset_prod (I : Ideal O) (hI : primaryGenerator I ≠ 0)
    (s : Multiset O) :
    idealSymbol I s.prod = (s.map (idealSymbol I)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [idealSymbol_map_one I hI]
  | @cons a s ih => simp [idealSymbol_map_mul I hI, ih]

theorem symbol_prime (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) (x : O) :
    symbol x p = primeValue (Ideal.span {p}) x := by
  let : (Ideal.span {p} : Ideal O).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg : lambda ∉ (Ideal.span {p} : Ideal O) :=
    primary_maximal_divisor_good p hprimary _ (Ideal.subset_span (by simp))
  rw [symbol, idealSymbol_prime _ hg, primeValue_eq _ hg]

theorem idealSymbol_reciprocity (I J : Ideal O)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealSymbol I (primaryGenerator J) = idealSymbol J (primaryGenerator I) := by
  classical
  have hI0 := primaryGenerator_ne_zero_ideal I hI
  have hJ0 := primaryGenerator_ne_zero_ideal J hJ
  rw [primaryGenerator, if_neg hJ0, idealSymbol_map_multiset_prod I hI,
    primaryGenerator, if_neg hI0, idealSymbol_map_multiset_prod J hJ]
  simp only [Multiset.map_map, Function.comp_def, idealSymbol, if_neg hI0, if_neg hJ0]
  rw [Multiset.prod_map_prod_map]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro Q hQ
  have hgP := factor_good I hI P hP
  have hgQ := factor_good J hJ Q hQ
  let : P.IsMaximal := hgP.1
  let : Q.IsMaximal := hgQ.1
  have hp := (primaryPrime_spec P (primaryPrime_factor_ne_zero I P hI hP)).2.2
  have hq := (primaryPrime_spec Q (primaryPrime_factor_ne_zero J Q hJ hQ)).2.2
  rw [primeValue_eq P hgP.2, primeValue_eq Q hgQ.2]
  exact cubic_reciprocity_primary P Q hgP.2 hgQ.2
    (primaryPrime P) (primaryPrime Q) hp.1.symm hq.1.symm hp.2 hq.2

theorem symbol_reciprocity (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hap : lambda ^ 2 ∣ a - 1) (hbp : lambda ^ 2 ∣ b - 1) :
    symbol a b = symbol b a := by
  have haG := primaryGenerator_span a ha hap
  have hbG := primaryGenerator_span b hb hbp
  have h := idealSymbol_reciprocity (Ideal.span {b}) (Ideal.span {a})
    (by rwa [hbG]) (by rwa [haG])
  simpa only [symbol, haG, hbG] using h

theorem idealSymbol_congr (I : Ideal O) {x y : O} (hxy : x - y ∈ I) :
    idealSymbol I x = idealSymbol I y := by
  classical
  by_cases hI : I = 0
  · simp only [hI, idealSymbol_zero]
  simp only [idealSymbol, if_neg hI]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro P hP
  have hle := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
  by_cases hg : P.IsMaximal ∧ lambda ∉ P
  · let : P.IsMaximal := hg.1
    rw [primeValue_eq P hg.2, primeValue_eq P hg.2,
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (hle hxy)]
  · simp only [primeValue, dif_neg hg]

theorem symbol_congr {x y d : O} (hxy : d ∣ x - y) :
    symbol x d = symbol y d :=
  idealSymbol_congr _ (Ideal.mem_span_singleton.mpr hxy)

end CubicJacobiGlobal

namespace CubicRamified

abbrev O := ActualEisensteinCubic.O
abbrev K := ActualEisensteinCubic.K
open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma lambda_def : lambda = omega - 1 := rfl

theorem cubicValue_cube (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    (cubicChar P hg (Ideal.Quotient.mk P x)) ^ 3 = 1 := by
  rw [← MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0), cubicChar_pow_three]
  exact MulChar.one_apply (isUnit_iff_ne_zero.mpr
    (Ideal.Quotient.eq_zero_iff_mem.not.mpr hx))

theorem cubicValue_ne_zero (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P)
    (x : O) (hx : x ∉ P) :
    cubicChar P hg (Ideal.Quotient.mk P x) ≠ 0 := by
  have h := cubicValue_cube P hg x hx
  intro hz
  rw [hz, zero_pow (by decide)] at h
  exact zero_ne_one h

theorem ramified_comparison
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hqP : q ∉ P) (_hpQ : p ∉ Q)
    (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hp0 : p ≠ 0 := by
    intro hz
    apply (NeZero.ne P)
    simp [hP, hz]
  have hq0 : q ≠ 0 := by
    intro hz
    apply (NeZero.ne Q)
    simp [hQ, hz]
  have hpP : p ∈ P := by rw [hP]; exact Ideal.subset_span (by simp)
  have hqQ : q ∈ Q := by rw [hQ]; exact Ideal.subset_span (by simp)
  have hrP : r ∉ P := by
    intro hrP
    have hd : p - q ∈ P := by rw [hfactor]; exact P.mul_mem_left _ hrP
    have hmem := P.sub_mem hpP hd
    exact hqP (by convert (preTransparency := .instances) hmem using 1 ; ring)
  have hrr : cubicChar P hgP (Ideal.Quotient.mk P r) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q r) := by
    have heq : symbol p r = symbol q r := symbol_congr
      (by rw [hfactor]; exact dvd_mul_left r _)
    have h := (symbol_reciprocity r p hr0 hp0 hr hp).trans
      (heq.trans (symbol_reciprocity q r hq0 hr0 hq hr))
    simpa only [symbol, ← hP, ← hQ, idealSymbol_prime _ hgP,
      idealSymbol_prime _ hgQ] using h
  have heq : cubicChar P hgP (Ideal.Quotient.mk P (p - q)) =
      cubicChar Q hgQ (Ideal.Quotient.mk Q (p - q)) := by
    rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hpP, zero_sub,
      neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one P hgP, one_mul,
      map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hqQ, sub_zero]
    exact cubic_reciprocity_primary P Q hgP hgQ p q hP hQ hp hq
  simp only [hfactor, map_mul, map_pow] at heq
  rw [← hrr] at heq
  exact mul_right_cancel₀ (cubicValue_ne_zero P hgP r hrP) heq

def sevenPrime : O := 1 + 3 * omega
def sevenIdeal : Ideal O := Ideal.span {sevenPrime}

theorem sevenPrime_norm : ShortDraftLatticeCount.qNat sevenPrime = 7 := by
  change ShortDraftLatticeCount.qNat (ActualEisensteinCoordinates.eval 1 3) = 7
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem sevenPrime_ne_zero : sevenPrime ≠ 0 := by
  intro hz
  change ActualEisensteinCoordinates.eval 1 3 = 0 at hz
  have hh : ActualEisensteinCoordinates.eval 1 3 =
      ActualEisensteinCoordinates.eval 0 0 :=
    hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hh).1
  norm_num at h

theorem sevenIdeal_norm : Ideal.absNorm sevenIdeal = 7 := by
  rw [sevenIdeal, ← qNat_eq_absNorm_span, sevenPrime_norm]

instance sevenIdeal_isMaximal : sevenIdeal.IsMaximal := by
  have hp : sevenIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [sevenIdeal_norm, Nat.irreducible_iff_nat_prime]
    decide)
  exact hp.isMaximal (Ideal.span_singleton_eq_bot.not.mpr sevenPrime_ne_zero)

theorem sevenPrime_primary : lambda ^ 2 ∣ sevenPrime - 1 := by
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

theorem sevenIdeal_good : lambda ∉ sevenIdeal :=
  primary_maximal_divisor_good sevenPrime sevenPrime_primary sevenIdeal
    (Ideal.subset_span (by simp []))

theorem twoIdeal_card : Nat.card (O ⧸ cubicTwoIdeal) = 4 := by
  change Ideal.absNorm cubicTwoIdeal = 4
  rw [cubicTwoIdeal, ← qNat_eq_absNorm_span]
  rw [show (-2 : O) = ActualEisensteinCoordinates.eval (-2) 0 by
    simp [ActualEisensteinCoordinates.eval]]
  unfold ShortDraftLatticeCount.qNat
  rw [ShortDraftLatticeCount.coords_eval]
  norm_num [ShortDraftLatticeCount.q]

theorem sevenIdeal_card : Nat.card (O ⧸ sevenIdeal) = 7 := sevenIdeal_norm

theorem cubicValue_lambda_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal lambda) =
      omega ^ 2 := by
  have heq : Ideal.Quotient.mk cubicTwoIdeal lambda =
      Ideal.Quotient.mk cubicTwoIdeal (omega ^ 2) := by
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
    rw [cubicTwoIdeal, Ideal.mem_span_singleton]
    refine ⟨-omega, ?_⟩
    rw [lambda_def]
    linear_combination -omega_sq_for_norm
  rw [heq, map_pow, map_pow, cubicChar_omega, twoIdeal_card]
  norm_num

theorem cubicValue_lambda_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal lambda) = 1 := by
  apply cubic_roots_reduce_injective sevenIdeal sevenIdeal_good
    (cubicValue_cube sevenIdeal sevenIdeal_good lambda sevenIdeal_good) (by simp)
  rw [cubicChar_reduce, sevenIdeal_card]
  norm_num only [Nat.reduceSub, Nat.reduceDiv]
  rw [← map_pow]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  rw [sevenIdeal, Ideal.mem_span_singleton]
  refine ⟨-1, ?_⟩
  rw [lambda_def]
  dsimp [sevenPrime]
  linear_combination omega_sq_for_norm

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

def primaryCoord (A B : ℤ) : O := ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B)

theorem primaryCoord_eq (A B : ℤ) :
    primaryCoord A B = 1 + 3 * (A : O) + 3 * (B : O) * omega := by
  simp only [primaryCoord, ActualEisensteinCoordinates.eval]
  push_cast
  rfl

theorem primaryCoord_primary (A B : ℤ) : lambda ^ 2 ∣ primaryCoord A B - 1 := by
  rw [primaryCoord_eq]
  apply lambda_sq_dvd_three.trans
  exact ⟨(A : O) + (B : O) * omega, by ring⟩

theorem primaryCoord_ne_zero (A B : ℤ) : primaryCoord A B ≠ 0 := by
  intro hz
  have hcoord : ActualEisensteinCoordinates.eval (1 + 3 * A) (3 * B) =
      ActualEisensteinCoordinates.eval 0 0 := by
    exact hz.trans (by simp [ActualEisensteinCoordinates.eval])
  have h := (ActualEisensteinCoordinates.unique_coordinates hcoord).1
  omega

lemma primary_card_exponent (N : ℕ) (A B : ℤ) (hN : 1 < N)
    (hn : (N : ℤ) = 1 + 9*(A^2-A*B+B^2)+3*(2*A-B)) :
    ((N-1)/3)%3 = ((2*A-B)%3).toNat %3 := by
  have hsub : ((N-1 : ℕ) : ℤ) = (N : ℤ)-1 := by omega
  have hdiv : (((N-1)/3 : ℕ) : ℤ) = 3*(A^2-A*B+B^2)+(2*A-B) := by
    rw [Int.natCast_ediv, hsub]
    have hh : (N : ℤ)-1 = 3*(3*(A^2-A*B+B^2)+(2*A-B)) := by omega
    rw [hh]
    omega
  have hrem : (((2*A-B)%3).toNat : ℤ) = (2*A-B)%3 :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  omega

theorem cubicValue_omega_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ) (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P omega) =
      omega ^ ((2 * A - B) % 3).toNat := by
  have hn : (Nat.card (O ⧸ P) : ℤ) =
      (1 + 3 * A)^2 - (1 + 3 * A)*(3 * B) + (3 * B)^2 := by
    change (Ideal.absNorm P : ℤ) = _
    rw [hP, ← qNat_eq_absNorm_span]
    unfold ShortDraftLatticeCount.qNat
    rw [Int.toNat_of_nonneg (ShortDraftLatticeCount.qO_nonneg _)]
    rw [primaryCoord, ShortDraftLatticeCount.coords_eval]
    rfl
  have hn' : (Nat.card (O ⧸ P) : ℤ) =
      1 + 9*(A^2 - A*B + B^2) + 3*(2*A-B) := by nlinarith [hn]
  rw [cubicChar_omega]
  apply ((omega_primitive.isOfFinOrder (by decide)).pow_inj_mod).mpr
  rw [← omega_primitive.eq_orderOf]
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hcard : 1 < Nat.card (O ⧸ P) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  exact primary_card_exponent (Nat.card (O ⧸ P)) A B hcard hn'

theorem ramified_comparison_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : u ≠ 0) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r) :
    (cubicChar P hgP (Ideal.Quotient.mk P lambda)) ^ 2 *
        cubicChar P hgP (Ideal.Quotient.mk P u) =
      (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) := by
  have hlam : lambda ≠ 0 := fun hz => hgP (hz ▸ P.zero_mem)
  have hne : P ≠ Q := by
    intro heq
    have hpq : p = q := primary_associated_eq p q
      (Ideal.span_singleton_eq_span_singleton.mp (hP.symm.trans (heq.trans hQ))) hp hq
    have hz : lambda ^ 2 * u * r = 0 := by rw [← hfactor, hpq, sub_self]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hlam) hu) hr0 hz
  exact ramified_comparison P Q hgP hgQ p q u r hP hQ hp hq
    (prime_generator_not_mem_of_ne P Q hne q hQ)
    (prime_generator_not_mem_of_ne Q P hne.symm p hP) hr0 hr hfactor

open ActualEisensteinCubic CubicJacobiGlobal CompletedGauss

lemma omega_isUnit : IsUnit omega := omega_primitive.isUnit (by decide)
lemma omega_four : omega ^ 4 = omega := by
  calc
    _ = omega ^ 3 * omega := by ring
    _ = omega := by rw [omega_primitive.pow_eq_one, one_mul]
lemma omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    _ = omega ^ 3 * omega ^ 2 := by ring
    _ = _ := by rw [omega_primitive.pow_eq_one, one_mul]

lemma cubicValue_neg (P : Ideal O) [P.IsMaximal] (hg : lambda ∉ P) (x : O) :
    cubicChar P hg (Ideal.Quotient.mk P (-x)) =
      cubicChar P hg (Ideal.Quotient.mk P x) := by
  rw [map_neg, neg_eq_neg_one_mul, map_mul, A3_cubicChar_neg_one, one_mul]

lemma cubicValue_omega_two :
    cubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal omega) =
      omega := by rw [cubicChar_omega, twoIdeal_card] ; norm_num
lemma cubicValue_omega_seven :
    cubicChar sevenIdeal sevenIdeal_good (Ideal.Quotient.mk sevenIdeal omega) =
      omega ^ 2 := by rw [cubicChar_omega, sevenIdeal_card]

lemma eq_of_cube_one_of_sq_eq (z w : O) (hz : z ^ 3 = 1)
    (hw : w ^ 3 = 1) (hsq : z ^ 2 = w ^ 2) : z = w := by
  have hw0 : w ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at hw; exact zero_ne_one hw
  apply mul_right_cancel₀ (pow_ne_zero 2 hw0)
  calc
    z * w ^ 2 = z ^ 3 := by rw [← hsq]; ring
    _ = 1 := hz
    _ = w * w ^ 2 := by rw [← hw]; ring

lemma supplement_of_factor
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hgP : lambda ∉ P) (hgQ : lambda ∉ Q)
    (p q u r : O) (hP : P = Ideal.span {p}) (hQ : Q = Ideal.span {q})
    (hp : lambda ^ 2 ∣ p - 1) (hq : lambda ^ 2 ∣ q - 1)
    (hu : IsUnit u) (hr0 : r ≠ 0) (hr : lambda ^ 2 ∣ r - 1)
    (hfactor : p - q = lambda ^ 2 * u * r)
    (j : ℕ)
    (hscalar : (cubicChar Q hgQ (Ideal.Quotient.mk Q lambda)) ^ 2 *
        cubicChar Q hgQ (Ideal.Quotient.mk Q u) =
      (omega ^ j)^2 * cubicChar P hgP (Ideal.Quotient.mk P u)) :
    cubicChar P hgP (Ideal.Quotient.mk P lambda) = omega ^ j := by
  apply eq_of_cube_one_of_sq_eq
  · exact cubicValue_cube P hgP lambda hgP
  · rw [← pow_mul, Nat.mul_comm j, pow_mul, omega_primitive.pow_eq_one, one_pow]
  · apply mul_right_cancel₀ (cubicValue_ne_zero P hgP u (Ideal.notMem_of_isUnit P hu))
    exact (ramified_comparison_of_factor P Q hgP hgQ p q u r hP hQ hp hq
      hu.ne_zero hr0 hr hfactor).trans hscalar

lemma omega_six : omega ^ 6 = 1 := by
  calc
    _ = omega ^ 3 * omega ^ 3 := by ring
    _ = 1 := by rw [omega_primitive.pow_eq_one, one_mul]

theorem supplement_case00 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+0)) (-2) (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, ]
    all_goals ring_nf
    all_goals simp only [  omega_six,
      ]

theorem supplement_case01 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+0) (3*l+1)) (-2) (omega ^ 1)
    (primaryCoord (l) (-k + l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

theorem supplement_case02 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+0) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 0 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+0) (3*l+2)) sevenPrime (-(omega ^ 0))
    (primaryCoord (-k + l) (-k)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 0 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
        pow_zero,  map_one]

theorem supplement_case10 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+0)) (-2) (omega ^ 2)
    (primaryCoord (-k - 1) (-l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 2) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [ map_pow, cubicValue_lambda_two,
      cubicValue_omega_two, hw,  pow_one]
    all_goals ring_nf

theorem supplement_case11 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+1) (3*l+1)) sevenPrime (-(omega ^ 2))
    (primaryCoord (k) (l)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 2).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [omega_five, omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg, map_pow, cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf

theorem supplement_case12 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+1) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 1 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+1) (3*l+2)) (-2) (-(omega ^ 1))
    (primaryCoord (-l - 1) (k - l)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 1 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
      cubicValue_omega_two, hw, pow_zero, pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

theorem supplement_case20 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+0)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 1 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P sevenIdeal hg sevenIdeal_good
    (primaryCoord (3*k+2) (3*l+0)) sevenPrime (-(omega ^ 1))
    (primaryCoord (-l) (k - l + 1)) hP rfl (primaryCoord_primary _ _) sevenPrime_primary
    (omega_isUnit.pow 1).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def, sevenPrime]
    push_cast
    all_goals ring_nf
    all_goals simp only [ omega_four, omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_seven,
      cubicValue_omega_seven, hw,  pow_one]
    all_goals ring_nf
    all_goals simp only [   omega_five,
       omega_sq_for_norm]

theorem supplement_case21 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+1)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 0 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+1)) (-2) (-(omega ^ 0))
    (primaryCoord (-k + l - 1) (-k - 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0).neg (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [cubicValue_neg,  cubicValue_lambda_two,
        pow_zero,  map_one]

theorem supplement_case22 (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (k l : ℤ)
    (hP : P = Ideal.span {primaryCoord (3*k+2) (3*l+2)}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ 2 := by
  have hw : cubicChar P hg (Ideal.Quotient.mk P omega) = omega ^ 2 := by
    rw [cubicValue_omega_primary P hg _ _ hP]
    congr 1
    omega
  refine supplement_of_factor P cubicTwoIdeal hg cubicTwoIdeal_good
    (primaryCoord (3*k+2) (3*l+2)) (-2) (omega ^ 0)
    (primaryCoord (k - l) (k + 1)) hP rfl (primaryCoord_primary _ _) neg_two_primary
    (omega_isUnit.pow 0) (primaryCoord_ne_zero _ _) (primaryCoord_primary _ _) ?_ 2 ?_
  · simp only [primaryCoord_eq, lambda_def]
    push_cast
    all_goals ring_nf
    all_goals simp only [  omega_primitive.pow_eq_one, omega_sq_for_norm]
    all_goals ring
  · simp only [  cubicValue_lambda_two,
        pow_zero,  map_one]

theorem cubicValue_lambda_primary (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (A B : ℤ)
    (hP : P = Ideal.span {primaryCoord A B}) :
    cubicChar P hg (Ideal.Quotient.mk P lambda) = omega ^ (A % 3).toNat := by
  have hA : A = 3 * (A / 3) + A % 3 := by omega
  have hB : B = 3 * (B / 3) + B % 3 := by omega
  have hAa : A % 3 = 0 ∨ A % 3 = 1 ∨ A % 3 = 2 := by omega
  have hBb : B % 3 = 0 ∨ B % 3 = 1 ∨ B % 3 = 2 := by omega
  rcases hAa with ha | ha | ha <;> rcases hBb with hb | hb | hb
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case00 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case01 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+0) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+0 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case02 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case10 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case11 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+1) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+1 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case12 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+0)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+0 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case20 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+1)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+1 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case21 P hg (A/3) (B/3) hp
  · have hp : P = Ideal.span {primaryCoord (3*(A/3)+2) (3*(B/3)+2)} := by
      rw [show 3*(A/3)+2 = A by omega, show 3*(B/3)+2 = B by omega]
      exact hP
    simpa only [ha, Int.reduceToNat] using supplement_case22 P hg (A/3) (B/3) hp

end CubicRamified

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace CompletedGauss

open ActualEisensteinCubic UniqueFactorizationMonoid

def nonresidualGain (I P : Ideal O) : Ideal O := if P∣I then P^2 else P

open ActualEisensteinCubic UniqueFactorizationMonoid

def completedLocalExponent (I F P : Ideal O) : ℕ :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3) : Ideal O :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) : Ideal O :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) : ℝ :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

end CompletedGauss

end

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CompletedGauss ConcretePrimeRowBridge ShortDraftHeckeBridge QuadraticInitialBound
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicFiniteRow {α : Type*} (P : α → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (S : Finset α) (z : O) : ℂ :=
  (finiteSquarefreeRow P hg S z) ^ 2

def activeCubicExponent {α : Type*} [DecidableEq α]
    (S T : Finset α) (i : activeSupport S T) : ℕ :=
  if i.val ∈ S \ T then 4 else 2

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicRow (I : Ideal O) (z : O) : ℂ :=
  eisEmbedding (CubicJacobiGlobal.idealSymbol I z)

def cubicGcdTerm {n : Type*} (D : Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (z : O) (j k : n) : ℂ :=
  if gcd (cols j) (cols k) = D then
    star (cubicRow (cols j) z * a j) * (cubicRow (cols k) z * a k) else 0

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

def cubicSmoothedCoprime {n : Type*} [Fintype n] (cols : n → Ideal O)
    (a : n → ℂ) (W : 𝓢(ℝ, ℂ)) (M : ℝ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j) * a k * ∑' z : O, (star (cubicRow (cols j) z) * cubicRow (cols k) z) *
      W (‖eisEmbedding z‖ ^ 2 / M) else 0

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open EisensteinSchwartzPoisson
noncomputable section
local notation "O" => ActualEisensteinCubic.O

@[simp] lemma cubicRow_one (z : O) : cubicRow 1 z = 1 := by
  simp only [cubicRow, CubicJacobiGlobal.idealSymbol_one, map_one]

end
end SevenEighths.CubicSieve

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss

local notation "Eis" => ActualEisensteinCubic.O

def markedCompletedT (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) : ℂ :=
  ∑' I : Ideal Eis, ∑' J : Ideal Eis, summand Ψ W X I J * d (I * J ^ 3)

def markedExpandedTerm (Ψ : Eis →* ℂ) (W : ℝ → ℂ) (X : ℝ)
    (d : Ideal Eis → ℂ) (I H J : Ideal Eis) : ℂ :=
  expandedTerm Ψ W X I H J * d (I * (H * J) ^ 3)

end

end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def hybridDivisorPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis) :=
  rows.biUnion idealDivisors

def hybridDivisorPairPool (rows : Finset (Ideal Eis)) : Finset (Ideal Eis × Ideal Eis) :=
  rows.biUnion fun k => (idealDivisors k) ×ˢ (idealDivisors k)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstCoupledRayColumns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (H : Finset ι → Finset ι → ℂ) (h : Eis) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius (fun i => Ideal.span {p i}) D * rowCoprimeMask (fun i => Ideal.span {p i}) D h *
      ∑ U ∈ (F \ D).powerset, ∑ V ∈ (F \ D).powerset,
        H (D ∪ U) (D ∪ V) *
        star (supportMobius (fun i => Ideal.span {p i}) U *
          (star (supportRay p r.1 (D ∪ U))*C₁ (D ∪ U)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U h)) *
        (supportMobius (fun i => Ideal.span {p i}) V *
          (supportRay p r.2 (D ∪ V)*C₂ (D ∪ V)) * star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg V h))

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem generator_eq_unit_primary (I : Ideal Eis) (e : Eis)
    (he : Ideal.span {e} = I) (hI : primaryGenerator I ≠ 0) :
    ∃ u : Eisˣ, e = (u:Eis)*primaryGenerator I := by
  have ha : Associated (primaryGenerator I) e :=
    Ideal.span_singleton_eq_span_singleton.mp ((primaryGenerator_spec I hI).1.trans he.symm)
  obtain ⟨u,hu⟩ := ha
  exact ⟨u,by simpa only [mul_comm] using hu.symm⟩

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss
open ConcretePrimeRowBridge SecondPassArithmetic FirstPassCubeLabels
local notation "O" => ActualEisensteinCubic.O

variable {σ : Type*}
  [DecidableEq σ]
  (S : Finset (Ideal O))
  (D : ℕ)
  (Ψ : O→*ℂ)
  (m f z : O)
  (W : ℝ→ℂ)
  (b X H₀ : ℝ)
  (slots : Finset σ)

def markedShortCompletedSum (Ψrow : O→*ℂ) (W : ℝ→ℂ) (X H₀ : ℝ) (mark : Ideal O→ℂ) : ℂ :=
  ∑' H:Ideal O,if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψrow H*
      markedCompletedT Ψrow W (X/(Ideal.absNorm H:ℝ)^3) (fun I=>mark (H^3*I)) else 0

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondLabelWeight (K : ℕ) (f : Ideal Eis) : ℝ := ((idealDivisors f).card : ℝ)^(9+4*K)

end
end SevenEighths.InverseMoment

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompleted
open ActualEisensteinCubic CompletedGauss
open RayFourExpansion QuadraticGaussRay SecondPassArithmetic

local notation "O" => ActualEisensteinCubic.O

def completedIndex (I J : Ideal O) : O := primaryGenerator I * primaryGenerator J ^ 3

def completedMask (S : Finset (Ideal O)) (D I J : Ideal O) : ℂ :=
  if D ∣ I * J ^ 3 ∧ ∀ p ∈ S, ¬p ∣ I * J ^ 3 then 1 else 0

def completedCorrection (I J : Ideal O) : ℂ :=
  rayMask (completedIndex I J) *
    star (fixedGQuotientValue
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (completedIndex I J)))

def markedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedMask S D I J * summand Ψ W X I J

def correctedSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) (I J : Ideal O) : ℂ :=
  completedCorrection I J * markedSummand S D Ψ W X I J

def markedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, markedSummand S D Ψ W X p.1 p.2

def correctedCompletedT (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' p : Ideal O × Ideal O, correctedSummand S D Ψ W X p.1 p.2

def correctionCoeff (χ : RayCharacter) : ℂ :=
  phaseCoeff (fun r => star (fixedGQuotientValue r)) χ

end SevenEighths.ProbeCompleted
end

end OAI
end

section

namespace OAI

namespace SevenEighths.IdealLogDerivative

open ActualEisensteinCubic UniqueFactorizationMonoid
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open scoped BigOperators Classical Topology

noncomputable section

def coeff (a : Ideal O →*₀ ℂ) (n : ℕ) : ℂ :=
  ShortDraftHeckeBridge.normFiberCoeff (fun I => (IdealMangoldt.value I : ℂ) * a I) n

end
end SevenEighths.IdealLogDerivative

end OAI
end

section

namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary

def sourceHeightShear : HeightSpace ≃ᵐ HeightSpace where
  toFun p := ((p.1.1+p.1.2,p.1.2),p.2)
  invFun p := ((p.1.1-p.1.2,p.1.2),p.2)
  left_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  right_inv p := by rcases p with ⟨⟨t,v⟩,w⟩;simp
  measurable_toFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1+p.1.2,p.1.2),p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : HeightSpace=>((p.1.1-p.1.2,p.1.2),p.2))
    fun_prop

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open RayFourExpansion CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowCorrectionEnergy : ℝ := ∑χ : RayCharacter,‖ProbeCompleted.correctionCoeff χ‖^2

end SevenEighths.ProbePhysical
end

end OAI
end

section

namespace OAI

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace SevenEighths.GaussianTheta

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def gaussian (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * omega3

theorem omega3_re : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]

theorem coordinate_norm_sq (x y : ℝ) :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, omega3_im, zero_mul, zero_add,
    add_zero, sub_zero]
  unfold RankTwoEisShift.Q
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem exists_coordinate (w : ℂ) : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv omega3 omega3_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv omega3 omega3_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase (x y : ℝ) (p : ℤ × ℤ) :
    paperE (coordinate x y * eisEmbedding (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  rw [paperE_eq_exp, dualFrequencyEquiv_coordinates]
  simp only [coordinate, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, omega3_re, omega3_im,
    zero_mul, zero_add, add_zero, sub_zero, complexPoint]
  unfold RankTwoEisShift.dualPhase
  congr 1
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  field_simp
  ring

theorem gaussian_coordinate_shift (a x y : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [eisEmbedding_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

theorem gaussian_dual_coordinate (a : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  unfold gaussian
  rw [← Complex.ofReal_pow, dualFrequencyEquiv_norm_sq]
  unfold RankTwoPoisson.eisQ
  congr 1
  push_cast
  ring

theorem shifted_prefactor (a : ℝ) (ha : 0 < a) :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' z : O, gaussian a (eisEmbedding z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * eisEmbedding h) *
          gaussian (4 / (3 * a)) (eisEmbedding h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      intro p
      rw [coordinate_dual_phase, gaussian_dual_coordinate]
      exact mul_comm _ _

theorem gaussian_mul (a : ℝ) (z w : ℂ) :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => gaussian a (eisEmbedding z)) := by
  exact eis_gaussian_summable ha

theorem paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ) (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (eisEmbedding z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson (a : ℝ) (ha : 0 < a) (c : O) (hc : c ≠ 0) (r : O) :
    (∑' z : O, gaussian a (eisEmbedding (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (eisEmbedding r * eisEmbedding h / eisEmbedding c) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hc' := eisEmbedding_ne_zero hc
  have hscale : 0 < a * ‖eisEmbedding c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : eisEmbedding (r + c * z) =
      eisEmbedding c * (eisEmbedding z + eisEmbedding r / eisEmbedding c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ) (K : ℂ) :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * eisEmbedding h)) *
        gaussian a (eisEmbedding h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (eisEmbedding z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (eisEmbedding z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖eisEmbedding c‖ ^ 2)) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) hd
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r) / eisEmbedding c) P
    (((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, eisTraceModChar_frequency]
  convert (preTransparency := .instances) h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (a : ℝ) (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ) : ℝ := 2 * t / (Real.sqrt 3 * ‖eisEmbedding c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (eisEmbedding z)

theorem parameter_pos (t : ℝ) (ht : 0 < t) : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))

theorem parameter_dual (t : ℝ) (ht : 0 < t) :
    4 / (3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) = parameter c (1 / t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

theorem parameter_prefactor (t : ℝ) (ht : 0 < t) :
    2 / (Real.sqrt 3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) =
      1 / (‖eisEmbedding c‖ * t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp

theorem theta_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖eisEmbedding c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

theorem theta_inversion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  have h := theta_functional_equation c χ hχ (1 / t) (one_div_pos.mpr ht)
  simpa only [one_div, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, one_mul] using h

theorem theta_root_nonzero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

end SevenEighths.GaussianTheta

end

end OAI
end

section

namespace OAI

namespace SevenEighths.HeckeDetectorProfiles
open scoped BigOperators Classical ContDiff FourierTransform SchwartzMap
noncomputable section

abbrev cutoff : SchwartzMap ℝ ℂ := QuadraticInitialBound.sieveCutoff

lemma cutoff_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) : cutoff x = 1 := by
  simp only [cutoff, QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1, Complex.ofReal_one]

lemma cutoff_zero (x : ℝ) (hx : 2 ≤ x) : cutoff x = 0 := by
  rw [QuadraticInitialBound.sieveCutoff_apply]
  have hh := QuadraticInitialBound.sieveBump.zero_of_le_dist (x := x)
    (show QuadraticInitialBound.sieveBump.rOut ≤ dist x 0 by
      change 2 ≤ dist x 0
      simpa [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ x)] using hx)
  rw [hh, Complex.ofReal_zero]

end
end SevenEighths.HeckeDetectorProfiles

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open scoped ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentPrimary
open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss

def primaryIdealCharacter (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    Ideal O →* ℂ :=
  χ.toMonoidHom.comp ((Ideal.Quotient.mk (Ideal.span {c})).toMonoidHom.comp
    primaryGeneratorHom.toMonoidHom)

@[simp] theorem primaryIdealCharacter_apply (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (I : Ideal O) :
    primaryIdealCharacter c χ I =
      χ (Ideal.Quotient.mk (Ideal.span {c}) (primaryGenerator I)) := rfl

end SevenEighths.CenteredMomentPrimary
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentRectangle
open CenteredMomentPrimary

def idealWeight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I : Ideal O) : ℂ :=
  (if IsCoprime I R then (1 : ℂ) else 0) *
    primaryIdealCharacter c χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) : ℂ :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

end SevenEighths.CenteredMomentRectangle
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O

def divisorPool {β : Type*} (T : Finset β) (B : β → Ideal O) : Finset (Ideal O) :=
  T.biUnion (fun j => idealDivisors (B j))

end SevenEighths.CenteredMomentMobiusRegroup

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorAllocation
open IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def nonemptySelections (s : Finset ι) : Finset (Finset ι) := s.powerset.erase ∅

abbrev Allocation (D : Ideal O) (s : Finset ι) :=
  (P : primeSupport D) → nonemptySelections s

def allocationTerm (D : Ideal O) (s : Finset ι) (v : ι → Ideal O)
    (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)*
    ∏ i ∈ (a P).val, if (P:Ideal O)∣v i then (1:ℂ) else 0

end SevenEighths.CenteredMomentDivisorAllocation

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorExtraction
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def selectedPrimes (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    Finset (primeSupport D) := Finset.univ.filter (fun P => i ∈ (a P).val)

def selectedDivisor (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) : Ideal O :=
  ∏ P ∈ selectedPrimes D s a i, (P:Ideal O)

theorem selectedDivisor_ne_zero (D : Ideal O) (s : Finset ι) (a : Allocation D s) (i : ι) :
    selectedDivisor D s a i ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P _ => (support_prime P.property).ne_zero)

end SevenEighths.CenteredMomentDivisorExtraction

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentActive
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6

def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)

def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)

variable {ι : Type*}

theorem activePrimes_pairwise_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))

open ConcreteTraceCRT EisensteinSchwartzPoisson

end SevenEighths.CenteredMomentActive
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.CenteredMomentCauchy
open CenteredMomentSmooth FourierBridge

def leftColumn {α : Type*} (S : Finset α) (c : α → ℂ)
    (V : ℝ → ℂ) (u : α → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ S, c i * columnPhase V (u i) t

def rightColumn {β : Type*} (T : Finset β) (d : β → ℂ)
    (V : ℝ → ℂ) (v : β → ℝ) (t : ℝ) : ℂ :=
  ∑ j ∈ T, star (d j) * columnPhase V (v j) t

end SevenEighths.CenteredMomentCauchy
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentRankinRadical
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentDivisorAllocation
local notation "O" => ActualEisensteinCubic.O

def commonRadical (I J : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I ∩ primeSupport J,P

end SevenEighths.CenteredMomentRankinRadical

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentChildAssembly
open CenteredMomentMobiusRegroup RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

def divisorCoefficient {α : Type*} (L : Ideal O) (a : α → O) (c : α → ℂ)
    (χ : RayCharacter) (i : α) : ℂ :=
  if L ∣ Ideal.span {a i} then c i * rayCharacter χ (a i) else 0

end SevenEighths.CenteredMomentChildAssembly

end

end OAI
end

section

namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialCanonicalState
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT InverseMoment
local notation "O"=>ActualEisensteinCubic.O
local notation "λ₀"=>ConcretePrimeRowBridge.goodLambda

def fullPunctureWidth (Z:ℝ)(t:Ideal O)(j:O):ℝ :=
  Real.logb Z (Ideal.absNorm (Ideal.span {j*primaryGenerator t}):ℝ)

end SevenEighths.InverseInitialCanonicalState

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseTerminalWidths
open ActualEisensteinCubic CompletedGauss UniqueFactorizationMonoid
open InverseMoment
local notation "O" => ActualEisensteinCubic.O

def normWidth (Z : ℝ) (I : Ideal O) : ℝ := Real.logb Z (Ideal.absNorm I : ℝ)

def reflectionWidth {ι : Type*} [Fintype ι] (Z : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * normWidth Z (∏ i, P i) - normWidth Z (reflectionExtractedDivisor P j e 1) -
    normWidth Z (reflectionExtractedDivisor P j e 0) -
      4 * normWidth Z (reflectionExtractedDivisor P j e 2)

def terminalDualWidth {ι : Type*} [Fintype ι] (Z H za Nstar : ℝ)
    (P : ι → Ideal O) (j : ι → ℕ) (e : ι → Fin 3) : ℝ :=
  2 * H + 2 * normWidth Z (∏ i, P i) + 2 * za - Nstar -
    normWidth Z (reflectionExtractedDivisor P j e 1) -
      3 * normWidth Z (reflectionExtractedDivisor P j e 2)

def widthConstant (B : Ideal O) (Ck CO CH Cf : ℝ) : ℝ :=
  CH ^ 2 * (Ideal.absNorm B : ℝ) * Ck ^ 2 * CO * Cf

def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))

def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2

def ramifiedWidth (Z : ℝ) (m : ℕ) : ℝ := ((m : ℝ) - 4) * Real.logb Z 3

end SevenEighths.InverseTerminalWidths

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentAddedZero
open CompletedGauss
open CenteredMomentCommonSupport
open CenteredExceptionalCount CenteredMomentRectangle
open UniqueFactorizationMonoid IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

def tupleProduct {r : ℕ} (v : Fin r → Ideal O) : Ideal O := ∏ i, v i

def originalCoefficient (N : ℕ) (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (ν : Fin N → Ideal O → ℂ)
    (Wslot : Fin N → ℝ → ℂ) (P : Fin N → ℝ) (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Fin (N + 2) → Ideal O) : ℂ :=
  (∏ j : Fin N, ν j (v (j.castAdd 2)) *
      Wslot j ((Ideal.absNorm (v (j.castAdd 2)) : ℝ) / P j)) *
    idealWeight c χ R t (tupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂
      (b₁ * v ⟨N, by omega⟩) (b₂ * v ⟨N + 1, by omega⟩) *
    (if s ∣ tupleProduct v then 1 else 0)

end SevenEighths.CenteredMomentAddedZero

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentAddedZeroUniform
open CompletedGauss
open CenteredMomentAddedZero CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

abbrev Tuple (ι : Type*) := (ι ⊕ Fin 2) → Ideal O

def coordinateEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    ι ⊕ Fin 2 ≃ Fin (n + 2) := (e.sumCongr (Equiv.refl (Fin 2))).trans finSumFinEquiv

def tupleEquiv {ι : Type*} {n : ℕ} (e : ι ≃ Fin n) :
    Tuple ι ≃ (Fin (n + 2) → Ideal O) :=
  (coordinateEquiv e).arrowCongr (Equiv.refl (Ideal O))

def finiteTupleProduct {ι : Type*} [Fintype ι] (v : Tuple ι) : Ideal O := ∏ i, v i

def originalFiniteCoefficient {ι : Type*} [Fintype ι]
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (b₁ b₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j, ν j (v (Sum.inl j)) * Wslot j ((Ideal.absNorm (v (Sum.inl j)) : ℝ) / P j)) *
    idealWeight c χ R t (finiteTupleProduct v) *
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (b₁ * v (Sum.inr 0)) (b₂ * v (Sum.inr 1)) *
    (if s ∣ finiteTupleProduct v then 1 else 0)

end SevenEighths.CenteredMomentAddedZeroUniform

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical ContDiff

namespace SevenEighths.CenteredMomentSourceProfileMass
open ActualEisensteinCubic CenteredMomentPrimary CenteredMomentRectangle
open CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O

def profileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁*v (Sum.inr 0)) (B₂*v (Sum.inr 1))*
    (if s∣finiteTupleProduct v then 1 else 0)

end SevenEighths.CenteredMomentSourceProfileMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonProfile
open ActualEisensteinCubic CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def liveIndices (B : Tuple ι) : Finset ι := Finset.univ.filter (fun i => B (Sum.inl i)=1)

def remainingTuple (B u : Tuple ι) : Tuple (liveIndices B) :=
  Sum.elim (fun i => u (Sum.inl i.val)) (fun j => u (Sum.inr j))

@[simp] theorem remainingTuple_slot (B u : Tuple ι) (i : liveIndices B) :
    remainingTuple B u (Sum.inl i)=u (Sum.inl i.val) := rfl

@[simp] theorem remainingTuple_plain (B u : Tuple ι) (j : Fin 2) :
    remainingTuple B u (Sum.inr j)=u (Sum.inr j) := rfl

end SevenEighths.CenteredMomentCommonProfile

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentRemainingBox
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def restoreTuple (B : Tuple ι) (v : Tuple (liveIndices B)) : Tuple ι :=
  Sum.elim (fun i => if h : i∈liveIndices B then v (Sum.inl ⟨i,h⟩) else 1)
    (fun j => v (Sum.inr j))

@[simp] theorem remaining_restore (B : Tuple ι) (v : Tuple (liveIndices B)) :
    remainingTuple B (restoreTuple B v)=v := by
  funext i
  rcases i with i|j
  · simp [remainingTuple,restoreTuple]
  · rfl

def remainingSets (B : Tuple ι) (S : (ι ⊕ Fin 2) → Finset (Ideal O)) :
    (liveIndices B ⊕ Fin 2) → Finset (Ideal O) :=
  Sum.elim (fun i => S (Sum.inl i.val)) (fun j => S (Sum.inr j))

end SevenEighths.CenteredMomentRemainingBox

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLiveMask
open CenteredMomentSourceProfileMass
open CenteredMomentAddedZeroUniform
open CenteredMomentRemainingBox CenteredMomentCommonProfile
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

 def maskedLiveProfile (B : Tuple ι) (C R s : Ideal O)
    (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    Tuple (liveIndices B) → ℂ :=
  profileCoefficient (R*C) (fun i : liveIndices B => ν i.val)
    (fun i => Wslot i.val) (fun i => P i.val) W₁ W₂ X₁ X₂ Y₁ Y₂
    (B₁*B (Sum.inr 0)) (B₂*B (Sum.inr 1)) s

end SevenEighths.CenteredMomentAmplificationLiveMask

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonAllowance
open CenteredMomentActive
local notation "O" => ActualEisensteinCubic.O

def activeIndicator (c d : ℕ) : ℝ := if netExponent c d ≠ 0 then 1 else 0

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end SevenEighths.CenteredMomentCommonAllowance

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical
open CenteredMomentDivisorAllocation CenteredMomentWholeDivisorShell
open CenteredMomentDyadicCount
local notation "O" => ActualEisensteinCubic.O
abbrev Label := (Ideal O × Ideal O) × Finset (Ideal O)

def Valid (s : Ideal O) (v : Label) : Prop :=
  v.1.1 ≠ 0 ∧ v.1.2 ≠ 0 ∧ primeSupport v.1.1 = primeSupport v.1.2 ∧
  s ∣ v.1.1 ∧ s ∣ v.1.2 ∧ v.2 ⊆ primeSupport (commonRadical v.1.1 v.1.2)

def weight (v : Label) : ℝ := 1 / Real.sqrt ((v.1.1.absNorm:ℝ)*v.1.2.absNorm)

def key (v : Label) : ℤ×ℤ := (normKey v.1.1,normKey v.1.2)
def keys (S : Finset Label) : Finset (ℤ×ℤ) := S.image key
def shell (S : Finset Label) (n : ℤ×ℤ) : Finset Label := S.filter (fun v=>key v=n)

end SevenEighths.CenteredMomentCommonHarmonicMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadicalHarmonicMass
open IdealMobiusDivisorSum UniqueFactorizationMonoid
open CenteredMomentRankinRadical
open CenteredMomentWholeDivisorShell CenteredMomentDyadicCount
open CenteredMomentCommonHarmonicMass (Label Valid )
local notation "O" => ActualEisensteinCubic.O

def weight (v : Label) : ℝ := 1/(Ideal.absNorm (commonRadical v.1.1 v.1.2):ℝ)
def key (v : Label) : ℤ := normKey (commonRadical v.1.1 v.1.2)
def keys (S : Finset Label) : Finset ℤ := S.image key
def shell (S : Finset Label) (n : ℤ) : Finset Label := S.filter (fun v=>key v=n)

end SevenEighths.CenteredMomentCommonRadicalHarmonicMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentAddedZeroUniform
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]

def frozenScale (B : Tuple ι) (P : ι → ℝ) (i : ι) : ℝ :=
  if B (Sum.inl i)=1 then 1 else P i

def plainNorm (B : Tuple ι) : ℝ :=
  (Ideal.absNorm (B (Sum.inr 0)):ℝ)*Ideal.absNorm (B (Sum.inr 1))

def rawReduction (B : Tuple ι) (P : ι → ℝ) : ℝ := plainNorm B*∏ i,frozenScale B P i

def remainingRaw (B : Tuple ι) (T : ℝ) (P : ι → ℝ) : ℝ :=
  (T/plainNorm B)*∏ i : liveIndices B,P i

end SevenEighths.CenteredMomentCommonRawScale

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorTensor
open IdealMobiusDivisorSum CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def allocationSign (D : Ideal O) (s : Finset ι) (a : Allocation D s) : ℂ :=
  ∏ P : primeSupport D, (-1:ℂ)^((a P).val.card+1)

end SevenEighths.CenteredMomentDivisorTensor

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDivisorRectangle
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorTensor
open CenteredMomentRectangle HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def factorTuple (v : ι → Ideal O) (I J : Ideal O) : (ι ⊕ Fin 2) → Ideal O :=
  Sum.elim v (fun j => if j=0 then I else J)

def selectedPlain (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (j : Fin 2) : Ideal O := selectedDivisor D Finset.univ a (Sum.inr j)

def selectedSlot (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (i : ι) : Ideal O := selectedDivisor D Finset.univ a (Sum.inl i)

end SevenEighths.CenteredMomentDivisorRectangle

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRectangle
open HeckeFamily
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def frozenIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => (selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def liveIndices (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : Finset ι :=
  Finset.univ.filter (fun i => ¬(selectedPrimes D Finset.univ a (Sum.inl i)).Nonempty)

def selectedNorm (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2))) : ℝ :=
  (Ideal.absNorm (selectedPlain D a 0):ℝ)*(Ideal.absNorm (selectedPlain D a 1):ℝ)

def rawRemaining (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (T : ℝ) (P : ι → ℝ) : ℝ := (T/selectedNorm D a)*∏ i∈liveIndices D a,P i

def formalReductionFactor (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (P : ι → ℝ) : ℝ := selectedNorm D a*∏ i∈frozenIndices D a,P i

end SevenEighths.CenteredMomentDivisorRaw

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentDivisorWitness
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw
open CenteredMomentRectangle HeckeFamily IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualExtracted (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (v : ι → Ideal O) : Ideal O :=
  (selectedPlain D a 0*selectedPlain D a 1)*∏ i∈frozenIndices D a,v i

end SevenEighths.CenteredMomentDivisorWitness

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentNaturalPrimitive
open HeckeFamily IdealMobiusDivisorSum UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def redundantSet (M C : Ideal O) : Finset (Ideal O) := primeSupport M\primeSupport C

def redundantIdeal (M C : Ideal O) : Ideal O := ∏P∈redundantSet M C,P

lemma redundantSet_prime (M C : Ideal O) : ∀P∈redundantSet M C,Prime P :=
  fun _ h=>support_prime (Finset.mem_sdiff.mp h).1

end SevenEighths.CenteredMomentNaturalPrimitive
end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentPrimeElements
open HeckeFamily CompletedGauss
local notation "O" => ActualEisensteinCubic.O

def elementPool (P : Finset (Ideal O)) : Finset O := P.image primaryPrime

end SevenEighths.CenteredMomentPrimeElements

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentSecondBlockRadicalHarmonicMass
open CompletedGauss
open CenteredMomentRankinRadical
open CenteredMomentCommonHarmonicMass
local notation "O" => ActualEisensteinCubic.O

def radicalWeight (C D:Ideal O):ℝ:=1/(Ideal.absNorm (commonRadical C D):ℝ)

end SevenEighths.CenteredMomentSecondBlockRadicalHarmonicMass

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentUncenteredTerminal
open HeckeFamily
open CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentRectangle
local notation "O" => ActualEisensteinCubic.O

def uncenteredProfileCoefficient {ι : Type*} [Fintype ι]
    (R : Ideal O) (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (B₁ B₂ s : Ideal O) (v : Tuple ι) : ℂ :=
  (∏ j,ν j (v (Sum.inl j))*Wslot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/P j))*
    (if IsCoprime (finiteTupleProduct v) R then 1 else 0)*
    (W₁ ((Ideal.absNorm (B₁*v (Sum.inr 0)):ℝ)/X₁)*
      W₂ ((Ideal.absNorm (B₂*v (Sum.inr 1)):ℝ)/X₂))*
    (if s∣finiteTupleProduct v then 1 else 0)

def comparisonScale (b : ℝ) : ℝ := 1/(2*max 1 b)

end SevenEighths.CenteredMomentUncenteredTerminal

end

end OAI
end

section

namespace OAI

noncomputable section
open scoped Classical ContDiff Topology FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace SevenEighths.PrimeLogProfile

def safeInverse (x : ℝ) : ℂ :=
  (1-QuadraticInitialBound.sieveCutoff (4*x))/(x : ℂ)

def profile (W : ℝ→ℂ) (A y : ℝ) : ℂ :=
  W y * (A : ℂ) * safeInverse (1+A*Real.log y)

def logFamily (W : ℝ→ℂ) (p : ℝ×ℝ) (u : ℝ) : ℂ :=
  Real.exp (-p.2*u) • (W (Real.exp (-u)) * (p.1 : ℂ) * safeInverse (1-p.1*u))

end SevenEighths.PrimeLogProfile

end

end OAI
end



-- Prove2me | Definitions.Def_InfoLossLAR_ReciprocallyScaledGaussianSource
-- name    : InfoLossLAR_ReciprocallyScaledGaussianSource
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:52:34.001849+00:00
-- url     : https://prove2.me/theorems/a49279c5-e0d7-4750-bd28-bfcfd5256500
-- title:
--   Register interface for reversible rectangular Gaussian preparation
-- statement:
--   These definitions specify a native circuit source for a Gaussian on a fine dual lattice. The input consists of a nonsingular integer basis, Gaussian widths, an accuracy budget and a serialized table of lattice vectors. Polynomially computable size and gate descriptions must prepare a correctly framed finite-register Gaussian from the all-zero state. The state is measured in Hilbert-space norm before the oracle step, allowing independent unit spectator states. The interface includes the capacities for the complete request and answer encodings and can pad the prepared register to any larger requested width.
-- source:
--   Rectangular Gaussian source for the physical Fourier row of https://prove2.me/theorems/23174e03-6b1d-4113-b6b9-4dab17fa850a

import Definitions.Def_InfoLossLAR_BDD_Coordinates
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_06_Optimized
import Definitions.Def_InfoLossLAR_FirstBridgeBundle_08
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_InfoLossLAR_RegevSearch_CoherentCopy
import Definitions.Def_InfoLossLAR_RegevSearch_FourierGrid
import Definitions.Def_InfoLossLAR_RegevSearch_PhysicalFourierReadout
import Definitions.Def_InfoLossLAR_RegevSearch_UniformFourierRow
import Definitions.Def_InfoLossLAR_RegevSketch_DGS
import Definitions.Def_InfoLossLAR_RuntimeBundle_03
import Definitions.Def_InfoLossLAR_WorstCase_Encoding
import Definitions.Def_InfoLossLAR_WorstCase_Family
import Definitions.Def_LARLLL_CurrentData
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_ShorAlgorithms_QFT_Circuit
import Mathlib
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section

namespace InfoLossLAR.WorstCase.ControlledNativeCode

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

/-- Tags 0,1,2,3,4 mean H,S,T,X,CNOT. Natural addresses use binary coding. -/
abbrev GateCode := ℕ×ℕ×ℕ

def encodeInstr {n : ℕ} : Instr n → GateCode
  | .h i => (0,i.val,0)
  | .s i => (1,i.val,0)
  | .t i => (2,i.val,0)
  | .x i => (3,i.val,0)
  | .cnot i j _ => (4,i.val,j.val)

end InfoLossLAR.WorstCase.ControlledNativeCode

end

section

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

instance image_discrete (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    DiscreteTopology (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

instance image_full_rank (lattice : Submodule ℤ (Space (dimension := dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :
    IsZLattice ℝ (imageLattice lattice transform) := by
  unfold imageLattice
  infer_instance

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open MeasureTheory FourierTransform RegevLWE.GaussConv

open scoped FourierTransform SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- The genuine lattice periodization admits a Schwartz Gaussian with the
actual Regev pi/width convention, for every positive real width. -/
private theorem exists_schwartz_rho (width : ℝ) (hwidth : 0 < width) :
    ∃ function : 𝓢(Space (dimension:=dimension),ℂ),
      ∀ point,function point=(rho width point : ℂ) := by
  obtain ⟨gaussian,hgaussian⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin dimension)
  let unit : ℝˣ := Units.mk0 width⁻¹ (inv_ne_zero hwidth.ne')
  let dilation : Space (dimension:=dimension) ≃L[ℝ] Space (dimension:=dimension) := ContinuousLinearEquiv.smulLeft unit
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ dilation gaussian,fun point => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply,hgaussian,rho]
  congr 2
  have hdilation : dilation point=width⁻¹ • point := rfl
  rw [hdilation,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hwidth)]
  ring

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Schwartz decay gives absolute convergence on the actual lattice;
no Gaussian normalizer or sampling algorithm is assumed. -/
private theorem summable_schwartz_lattice
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (function : 𝓢(Space (dimension:=dimension),ℂ)) :
    Summable (fun point : lattice => function (point : Space (dimension:=dimension))) := by
  let exponent := Module.finrank ℤ lattice+1
  have hs := ZLattice.summable_norm_pow_inv lattice exponent (Nat.lt_succ_self _)
  apply Summable.of_norm
  apply Summable.of_norm_bounded_eventually (g:=fun point : lattice =>
    SchwartzMap.seminorm ℝ exponent 0 function*‖point‖⁻¹^exponent) (hs.mul_left _)
  rw [Filter.eventually_cofinite]
  apply Set.Finite.subset (Set.finite_singleton (0 : lattice))
  intro point hnot
  simp only [Set.mem_ofPred_eq,Set.mem_singleton_iff] at hnot ⊢
  by_contra hne
  apply hnot
  have hpositive : 0<‖point‖^exponent := pow_pos (norm_pos_iff.mpr hne) _
  have hdecay := SchwartzMap.norm_pow_mul_le_seminorm ℝ function exponent (point : Space (dimension:=dimension))
  change ‖point‖^exponent*‖function (point : Space (dimension:=dimension))‖ ≤ _ at hdecay
  rw [norm_norm,inv_pow,←div_eq_mul_inv,le_div_iff₀ hpositive,mul_comm]
  exact hdecay

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

open scoped SchwartzMap

noncomputable section

variable {dimension : ℕ}

/-- Every translate has absolutely summable genuine Gaussian mass. -/
private theorem summable_gaussian_coset
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0<width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => rho width ((point : Space (dimension:=dimension))+shift)) := by
  obtain ⟨function,hfunction⟩ := exists_schwartz_rho (dimension:=dimension) width hwidth
  let translated := SchwartzMap.compSubConstCLM ℂ (-shift) function
  have h := summable_schwartz_lattice lattice translated
  have hvalue (point : lattice) : translated point=(rho width ((point : Space (dimension:=dimension))+shift) : ℂ) := by
    simp only [translated,SchwartzMap.compSubConstCLM_apply,sub_neg_eq_add,hfunction]
  simp only [hvalue] at h
  exact Complex.summable_ofReal.mp h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

/-- The actual positive square-root Gaussian amplitude on the complete
lattice, at a specified shift, with its genuine coset normalizer. -/
def gaussianAmplitude (lattice : Submodule ℤ (Space (dimension:=dimension)))
    (width : ℝ) (shift : Space (dimension:=dimension)) (point : lattice) : ℝ :=
  Real.exp (-Real.pi*‖(point : Space (dimension:=dimension))+shift‖^2/(2*width^2))/
    Real.sqrt (rhoCoset width lattice shift)

private theorem rhoCoset_pos (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice] (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    0 < rhoCoset width lattice shift := by
  exact (summable_gaussian_coset lattice width hwidth shift).tsum_pos
    (fun _ => (Real.exp_pos _).le) (0 : lattice) (Real.exp_pos _)

private theorem gaussianAmplitude_sq (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) (point : lattice) :
    (gaussianAmplitude lattice width shift point)^2=
      rho width ((point : Space (dimension:=dimension))+shift)/rhoCoset width lattice shift := by
  rw [gaussianAmplitude,div_pow,Real.sq_sqrt (rhoCoset_pos lattice width hwidth shift).le,←Real.exp_nat_mul]
  congr 1
  unfold rho
  congr 1
  field_simp
  ring

/-- The complete true Gaussian amplitude has square norm exactly one. -/
private theorem gaussianAmplitude_square_sum (lattice : Submodule ℤ (Space (dimension:=dimension)))
    [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) :
    Summable (fun point : lattice => (gaussianAmplitude lattice width shift point)^2) ∧
      (∑' point : lattice,(gaussianAmplitude lattice width shift point)^2)=1 := by
  simp_rw [gaussianAmplitude_sq lattice width hwidth shift]
  refine ⟨(summable_gaussian_coset lattice width hwidth shift).div_const _,?_⟩
  rw [tsum_div_const]
  exact div_self (rhoCoset_pos lattice width hwidth shift).ne'

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

noncomputable section

/-- The complete countable Hilbert space of square-summable complex
amplitudes; used only for exact mathematical error transfer. -/
abbrev Hilbert (Index : Type*) := lp (fun _ : Index => ℂ) 2

variable {dimension : ℕ}

/-- The genuine normalized positive Gaussian amplitude is an actual
square-summable Hilbert vector on the complete lattice. -/
def gaussianHilbertState
    (lattice : Submodule ℤ (Space (dimension:=dimension))) [DiscreteTopology lattice] [IsZLattice ℝ lattice]
    (width : ℝ) (hwidth : 0 < width) (shift : Space (dimension:=dimension)) : Hilbert lattice := by
  refine ⟨fun point => (gaussianAmplitude lattice width shift point : ℂ),?_⟩
  apply memℓp_gen
  have h := (gaussianAmplitude_square_sum lattice width hwidth shift).1
  simpa using h

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

instance dual_input_discrete (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    DiscreteTopology (dual (inputLattice basis hdet)) := by
  rw [dual_lattice_eq_span]
  infer_instance

instance dual_input_full_rank (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    IsZLattice ℝ (dual (inputLattice basis hdet)) := by
  constructor
  rw [dual_lattice_eq_span]
  exact ZSpan.span_top (dualRealBasis basis hdet)

end

end InfoLossLAR.WorstCase.IntegerBasis

end

section

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- Total native rational list dot product; malformed lengths truncate. -/
def dot (input : List ℚ × List ℚ) : ℚ :=
  ((input.1.zip input.2).map (fun pair => pair.1*pair.2)).sum

def projectionEntry (input : (List ℚ × List ℚ) × ℕ) : ℚ :=
  dot (input.1.1,input.1.2)/dot (input.1.1,input.1.1)*input.1.1[input.2]?.getD 0

def rowValue (input : (List (List ℚ) × List ℚ) × ℕ) : ℚ :=
  input.1.2[input.2]?.getD 0-
    (input.1.1.map (fun previous => projectionEntry ((previous,input.1.2),input.2))).sum

/-- One native materialized Gram--Schmidt step uses its original current
column throughout and stores the complete new rational vector. -/
def orthogonalStep (input : List (List ℚ) × List ℚ) : List ℚ :=
  (List.range input.2.length).map (fun row => rowValue (input,row))

def vectorTicks (vector : List ℚ) : List Unit :=
  vector.flatMap (fun value => rationalTicks value++rationalTicks value++[()])

def matrixTicks (matrix : List (List ℚ)) : List Unit :=
  matrix.flatMap (fun vector => vectorTicks vector++vectorTicks vector++[()])

/-- Every intermediate cache is size-guarded, giving an unconditional
polynomial-time loop on arbitrary encodings. Valid matrix correctness will
be discharged using the independently proved integer-Gram height bound. -/
def cacheStep (state : List Unit × List (List ℚ)) (current : List ℚ) : List Unit × List (List ℚ) :=
  let next := state.2++[orthogonalStep (state.2,current)]
  (state.1,if (matrixTicks next).length ≤ state.1.length then next else [])

/-- Actual guarded list cache program. The guard's complete runtime bound
holds for every encoded input, including malformed or singular matrices. -/
def cached (input : List (List ℚ) × List Unit) : List (List ℚ) :=
  (input.1.foldl cacheStep (input.2,[])).2

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end

section

namespace InfoLossLAR.WorstCase.RationalGramSchmidt.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open scoped BigOperators

/-- The guard budget is generated in unary polynomial size from the
actual binary input length, not from an exponentially large entry value. -/
def inputBudget (input : List (List ℤ)) : List Unit :=
  let slots := integerMatrixTicks input++[()]
  slots.flatMap (fun _ => slots.flatMap (fun _ => slots.flatMap
    (fun _ => slots.flatMap (fun _ => List.replicate 128 ()))))

def rationalColumn (column : List ℤ) : List ℚ := column.map (fun value : ℤ => (value : ℚ))

def rationalColumns (input : List (List ℤ)) : List (List ℚ) := input.map rationalColumn

/-- Complete unconditional native cached orthogonalization of original
integer input columns, with all guards and loop sizes computed publicly. -/
def inputCache (input : List (List ℤ)) : List (List ℚ) := cached (rationalColumns input,inputBudget input)

def transposeColumn (input : List (List ℤ) × ℕ) : List ℤ :=
  input.1.map (fun row => row[input.2]?.getD 0)

def transpose (input : List (List ℤ)) : List (List ℤ) :=
  (List.range input.length).map (fun column => transposeColumn (input,column))

/-- Actual row-encoded matrix input is transposed by a native program
before the cached column orthogonalization. -/
def basisCache (input : List (List ℤ)) : List (List ℚ) := inputCache (transpose input)

noncomputable section

end

end InfoLossLAR.WorstCase.RationalGramSchmidt.Native

end

section

namespace InfoLossLAR.WorstCase.RationalInverse.Native

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics

open RationalGramSchmidt

open RationalGramSchmidt.Native

open scoped BigOperators

abbrev Context := List (List ℚ) × List (List ℚ)

abbrev State := Context × (List Unit × List (List ℚ))

/-- One rational summand of reverse triangular substitution. -/
def term (input : (((Context × List (List ℚ)) × ℕ) × ℕ) × ℕ) : ℚ :=
  let source := input.1
  let gs := source.1.1.1.2[source.1.2]?.getD []
  if source.1.2< input.2 then
    dot (gs,source.1.1.1.1[input.2]?.getD [])/dot (gs,gs)*
      (source.1.1.2[input.2]?.getD [])[source.2]?.getD 0 else 0

/-- One entry uses only native rational operations and bounded index lists. -/
def entry (input : ((Context × List (List ℚ)) × ℕ) × ℕ) : ℚ :=
  let gs := input.1.1.1.2[input.1.2]?.getD []
  gs[input.2]?.getD 0/dot (gs,gs)-
    ((List.range input.1.1.1.1.length).map (fun j => term (input,j))).sum

def column (input : (Context × List (List ℚ)) × ℕ) : List ℚ :=
  (List.range input.1.1.1.length).map (fun row => entry (input,row))

def replaceColumn (input : (List (List ℚ) × ℕ) × List ℚ) : List (List ℚ) :=
  (List.range input.1.1.length).map (fun j => if j=input.1.2 then input.2 else input.1.1[j]?.getD [])

/-- A public encoding-length guard bounds every fold state, including
malformed and singular inputs. Correctness proves that it never fires on
nonsingular original integer matrices. -/
def step (state : State) (counter : ℕ) : State :=
  let index := state.1.1.length-1-counter
  let next := replaceColumn ((state.2.2,index),column ((state.1,state.2.2),index))
  (state.1,(state.2.1,if (matrixTicks next).length≤ state.2.1.length then next else []))

/-- The actual cache consumes the original row-major integer input. The
only preprocessing is the previously certified native orthogonalization. -/
def cached (input : List (List ℤ)) : List (List ℚ) :=
  let original := rationalColumns (transpose input)
  let gs := basisCache input
  let zeros := original.map (fun row => row.map (fun _ => (0 : ℚ)))
  ((List.range input.length).foldl step ((original,gs),(inputBudget input,zeros))).2.2

def transposeRational (input : List (List ℚ)) : List (List ℚ) :=
  (List.range input.length).map (fun row => input.map (fun column => column[row]?.getD 0))

/-- Native row-major output for the original integer matrix's inverse
transpose. No determinant, real dual-basis or arbitrary real oracle is
called by this program. -/
def current (input : List (List ℤ)) : List (List ℚ) := transposeRational (cached input)

end InfoLossLAR.WorstCase.RationalInverse.Native

end

section

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open RationalGramSchmidt.Native

open scoped BigOperators

def denominators (input : List (List ℤ)) : List ℕ :=
  (RationalInverse.Native.current input).flatMap (fun row => row.map Rat.den)

/-- The positive integer denominator is the product of the actual native
inverse output denominators. The implementation uses the certified binary
rational product and numerator extraction, never a determinant oracle. -/
def denominator (input : List (List ℤ)) : ℕ :=
  ((denominators input).map (fun value : ℕ => (value : ℚ))).prod.num.natAbs

end InfoLossLAR.WorstCase.NativeDualQuotient

end

section

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

def originalDenominator {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : ℕ :=
  denominator (RationalInverse.Native.inputRows B)

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end

section

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open AFT.RationalNumerics RationalGramSchmidt RationalInverse

open scoped BigOperators

noncomputable section

def quotientVector {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : Fin n → ℤ :=
  fun i => ⌊((B.transpose.mulVec v) i : ℚ)/(originalDenominator B : ℚ)⌋

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end

section

namespace InfoLossLAR.WorstCase.NativeDualQuotient

open RationalGramSchmidt RationalInverse RegevLWE.GaussConv

open GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

/-- Retained canonical integer representatives. No residue enumeration or
choice of representatives is used by the native quotient program. -/
def Residual {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) :=
  {r : Fin n → ℤ // quotientVector B r=0}

/-- Coordinate equivalence for an actual image lattice under a public
continuous linear equivalence. -/
def imageEquiv {n : ℕ} (L : Submodule ℤ (IntegerBasis.Space (dimension:=n)))
    (T : IntegerBasis.Space (dimension:=n) ≃L[ℝ] IntegerBasis.Space (dimension:=n)) :
    L ≃ GaussianLatticeTransport.imageLattice L T where
  toFun point := ⟨T point,by change T.symm (T point)∈L;simpa using point.property⟩
  invFun point := ⟨T.symm point,point.property⟩
  left_inv point := by apply Subtype.ext;exact T.symm_apply_apply point
  right_inv point := by apply Subtype.ext;exact T.apply_symm_apply point

end

end InfoLossLAR.WorstCase.NativeDualQuotient

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open scoped Classical

noncomputable section

variable {FiniteIndex Index : Type*} [Fintype FiniteIndex]

def finiteRestrict (embedding : FiniteIndex ↪ Index) (value : Hilbert Index) : EuclideanSpace ℂ FiniteIndex :=
  WithLp.toLp 2 (fun index => value (embedding index))

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

namespace InfoLossLAR.WorstCase.NativePaddedWords

open QAlgorithms.Complexity

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2PlatformSerialization

def current (x : List Unit×Str) : Str := (x.2++x.1.map (fun _ => false)).take x.1.length

end InfoLossLAR.WorstCase.NativePaddedWords

end

section

namespace InfoLossLAR.WorstCase.GaussianPoissonSeries

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension modulus : ℕ} [NeZero modulus]

/-- The true Euclidean point on the fine input lattice L/modulus. -/
def fineGridPoint (point : Space (dimension:=dimension)) : Space (dimension:=dimension) :=
  (modulus : ℝ)⁻¹ • point

end

end InfoLossLAR.WorstCase.GaussianPoissonSeries

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection CoherentComputeUncompute GaussianProjection.CosetGeometry

open GaussianProjection GaussianLatticeTransport NativeDualQuotient

noncomputable section

variable {n M : ℕ} [NeZero M]

abbrev Retained (L : Submodule ℤ (PointSpace n)) (M : ℕ) (R : ℝ) :=
  {x : L // ‖fineGridPoint (modulus:=M) (x : PointSpace n)‖ < R}

abbrev fineMap (L : Submodule ℤ (PointSpace n)) (M : ℕ) [NeZero M] :=
  NativeDualQuotient.imageEquiv L (dilation ((M : ℝ)⁻¹) (inv_pos.mpr (by exact_mod_cast NeZero.pos M)))

abbrev fineLattice (L : Submodule ℤ (PointSpace n)) (M : ℕ) [NeZero M] :=
  GaussianLatticeTransport.imageLattice L (dilation ((M : ℝ)⁻¹) (inv_pos.mpr (by exact_mod_cast NeZero.pos M)))

def fineEmbedding (L : Submodule ℤ (PointSpace n)) (M : ℕ) [NeZero M] (R : ℝ) : Retained L M R ↪ fineLattice L M :=
  ⟨fun x => fineMap L M x.val,fun _ _ e => Subtype.ext ((fineMap L M).injective e)⟩

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

namespace InfoLossLAR.WorstCase.RegevSearch.FineCodec

open QAlgorithms QAlgorithms.Complexity QMCNumericRuntime

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization Integration9_9.TM2NativeAffineEncoding

open Integration9_9.TM2NativeAffineEmitter

/-- Public bit and answer widths, query buffer width, encoded R, unary precision, and fixed pool. -/
abbrev Config := (List Unit × List Unit × List Unit) × (Str × Str × Str)

def header (p : Config) : Str :=
  lengthToken p.1.1 ++ lengthToken p.1.2.1 ++ lengthToken p.1.2.2 ++
    encS p.2.1 ++ encS p.2.2.1 ++ encS p.2.2.2

/-- The header, original Gaussian-input length, basis and residual are preserved.
Only the signed fine coefficient list is replaced. -/
abbrev Source := ((Str × List Unit) × (Str × Str)) × List ℤ

def pack (s : Source) : Str :=
  encS s.1.1.1 ++ lengthToken s.1.1.2 ++ encS s.1.2.1 ++ encS (serializeVector s.2) ++ encS s.1.2.2

end InfoLossLAR.WorstCase.RegevSearch.FineCodec

end

section

open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch

open scoped BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.FineGridDecoding

noncomputable section

variable {n : ℕ}

def ratTranspose (B : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  ((Int.castRingHom ℚ).mapMatrix B).transpose

def point (B : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) : Fin n → ℚ :=
  (ratTranspose B)⁻¹.mulVec (fun i => (z i : ℚ))

def residue (M : ℕ) (z : Fin n → ℤ) : Fin n → ℤ := fun i => z i % (M : ℤ)

def answer (M : ℕ) (z : Fin n → ℤ) : Fin n → ℤ := fun i => -(z i / (M : ℤ))

/-- This rational input is computed from the public residue alone. -/
def input (B : Matrix (Fin n) (Fin n) ℤ) (M : ℕ) (c : Fin n → ℤ) : Fin n → ℚ :=
  (M : ℚ)⁻¹ • point B c

private theorem pairing (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (z : Fin n → ℤ) (j : Fin n) :
    ∑ i, (B i j : ℚ) * point B z i = (z j : ℚ) := by
  have hdet : IsUnit (ratTranspose B).det := by
    rw [ratTranspose, Matrix.det_transpose, ← RingHom.map_det]
    apply isUnit_iff_ne_zero.mpr
    change (B.det : ℚ) ≠ 0
    exact_mod_cast hB
  have h := congrFun (Matrix.mulVec_mulVec (fun i => (z i : ℚ)) (ratTranspose B) (ratTranspose B)⁻¹) j
  rw [Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] at h
  exact h

private theorem reconstruct (M : ℕ) (z : Fin n → ℤ) (i : Fin n) :
    residue M z i - (M : ℤ) * answer M z i = z i := by
  simpa [residue, answer] using Int.emod_add_mul_ediv (z i) M

private theorem physical_error (B : Matrix (Fin n) (Fin n) ℤ) {M : ℕ} (hM : 0 < M) (z : Fin n → ℤ) :
    input B M (residue M z) - point B (answer M z) = input B M z := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hsplit : (fun i => (residue M z i : ℚ)) - (M : ℚ) • (fun i => (answer M z i : ℚ)) = (fun i => (z i : ℚ)) := by
    funext i
    change (residue M z i : ℚ) - (M : ℚ) * (answer M z i : ℚ) = (z i : ℚ)
    exact_mod_cast reconstruct M z i
  unfold input point
  rw [← hsplit, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub, smul_smul, inv_mul_cancel₀ hM', one_smul]

/-- A retained short fine-grid point gives a promised rational decoder call with
integer answer equal to its negative coarse quotient in the original basis. -/
def query (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) {M : ℕ} (hM : 0 < M)
    (R : ℚ) (z : Fin n → ℤ)
    (hshort : (R : ℝ)^2 * (∑ i, ((input B M z i : ℚ) : ℝ)^2) < (famσ n : ℝ)^2 / 4) :
    SharedPoolCoherence.Query B R where
  input := input B M (residue M z)
  nearest := point B (answer M z)
  answer := answer M z
  coords := pairing B hB _
  close := by
    have he (i : Fin n) := congrFun (physical_error B hM z) i
    simp only [Pi.sub_apply] at he
    simpa only [he] using hshort

/-- Rational synthesis of the physical decoder input uses the very same dual
point as the Fourier identity. -/
private theorem point_real (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (z : Fin n → ℤ) :
    (WithLp.toLp 2 (fun i => ((point B z i : ℚ) : ℝ)) : IntegerBasis.Space) =
      IntegerBasis.dualCoordinates B hB z := by
  apply (IntegerBasis.dualRealBasis B hB).ext_elem
  intro j
  simp only [IntegerBasis.dualRealBasis, LinearMap.BilinForm.dualBasis_repr_apply]
  change inner ℝ _ (IntegerBasis.realBasis B hB j) = inner ℝ _ (IntegerBasis.realBasis B hB j)
  have hpair (i : Fin n) : inner ℝ (IntegerBasis.dualRealBasis B hB i) (IntegerBasis.realBasis B hB j) = if j = i then 1 else 0 :=
    LinearMap.BilinForm.apply_dualBasis_left IntegerBasis.inner_nondegenerate (IntegerBasis.realBasis B hB) i j
  rw [IntegerBasis.dualCoordinates_apply, sum_inner]
  simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_left, hpair]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [IntegerBasis.realBasis_apply, PiLp.inner_apply]
  simp only [WithLp.ofLp_toLp, Real.inner_apply]
  have h := congrArg (fun a : ℚ => (a : ℝ)) (pairing B hB z j)
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h
  simpa only [mul_comm] using h

private theorem fine_norm (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (M : ℕ) (z : Fin n → ℤ) :
    ∑ i, ((input B M z i : ℚ) : ℝ)^2 = ‖(M : ℝ)⁻¹ • IntegerBasis.dualCoordinates B hB z‖^2 := by
  rw [← point_real B hB z, EuclideanSpace.real_norm_sq_eq]
  simp [input]

/-- The norm cutoff used for Gaussian truncation suffices for the exact strict
promise in the platform decoder, also at a non-dyadic terminal width. -/
def queryOfNorm (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) {M : ℕ} (hM : 0 < M)
    (R : ℚ) (hR : 0 < R) (z : Fin n → ℤ)
    (hshort : ‖(M : ℝ)⁻¹ • IntegerBasis.dualCoordinates B hB z‖ < (famσ n : ℝ)/(2*(R : ℝ))) :
    SharedPoolCoherence.Query B R :=
  query B hB hM R z (by
    rw [fine_norm B hB M z]
    have hR' : 0 < (R : ℝ) := by exact_mod_cast hR
    have hr := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*(R : ℝ))).mp hshort
    have hpos : (0 : ℝ) ≤ (R : ℝ) * ‖(M : ℝ)⁻¹ • IntegerBasis.dualCoordinates B hB z‖ := by positivity
    have hlt : ((R : ℝ)*‖(M : ℝ)⁻¹ • IntegerBasis.dualCoordinates B hB z‖)^2 < ((famσ n : ℝ)/2)^2 :=
      (sq_lt_sq₀ hpos (by positivity)).2 (by linarith)
    nlinarith only [hlt])

end

end InfoLossLAR.WorstCase.RegevSearch.FineGridDecoding

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open RegevLWE.GaussConv GaussianPoissonSeries GaussianProjection NativeDualQuotient IntegerBasis

noncomputable section

variable {n M : ℕ} [NeZero M]

def shortCoordinate (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℝ)
    (p : Retained (dual (inputLattice B hB)) M R) : Fin n → ℤ := (dualIntegerEquiv B hB).symm p.val

private theorem coordinate_short (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℝ)
    (p : Retained (dual (inputLattice B hB)) M R) :
    ‖(M:ℝ)⁻¹ • dualCoordinates B hB (shortCoordinate B hB R p)‖ < R := by
  have he := congrArg (fun x : dual (inputLattice B hB) => (x : PointSpace n)) ((dualIntegerEquiv B hB).apply_symm_apply p.val)
  change dualCoordinates B hB (shortCoordinate B hB R p)=(p.val : PointSpace n) at he
  rw [he]
  exact p.property

def promisedShort (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det ≠ 0) (R : ℚ) (hR : 0<R) (cut : ℝ)
    (hcut : cut ≤ (famσ n : ℝ)/(2*(R:ℝ))) (p : Retained (dual (inputLattice B hB)) M cut) : SharedPoolCoherence.Query B R :=
  FineGridDecoding.queryOfNorm B hB (NeZero.pos M) R hR (shortCoordinate B hB cut p) ((coordinate_short B hB cut p).trans_le hcut)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity NativeQFTPlanCompile GridReadout.Axis FineCodec

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open QMCNumericRuntime OAI.MetricKMedian.Binary

open RegevLWE.GaussConv GaussianPoissonSeries IntegerBasis

noncomputable section

variable {n m : ℕ}

def queryConfig (bt k l : List Unit) (R : ℚ) (prec : ℕ) (pool : Fin m → Fin n → ℤ) : Config :=
  ((bt,k,l),(encQ R,unary prec,encVec (encVec encI) pool))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

open GaussianPoissonSeries RationalInverse GridReadout

noncomputable section

def delta (d : ℕ) : ℝ := 1/(2:ℝ)^d

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalGrid

end

section

noncomputable section

namespace InfoLossLAR.WorstCase.RectangularSource.Settings

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic QAlgorithms.Complexity

open NativeDualQuotient GaussianPoissonSeries RegevSearch.PhysicalGrid GaussianRandomizedRounding.Wide

open Integration9_9.TM2NativeFiniteDraw RationalGramSchmidt.Native

open scoped BigOperators

abbrev Settings := Setup × List Unit

def base (p : Settings) := p.1.1.map (fun _ => ())++p.2++List.replicate 4 ()

def atBasis {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (r : ℚ) (d : ℕ) (precision : List Unit) : Settings := (setup B r d,precision)

end InfoLossLAR.WorstCase.RectangularSource.Settings

end

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.Public

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianRandomizedRounding.Wide GaussianRandomizedRounding.Wide.Coherent

open RegevLWE.GaussConv GaussianPoissonSeries NativeDualQuotient GaussianProjection CoherentProjection CoherentComputeUncompute

open FiniteGateTransport ControlledNativeGates RegevSearch.PhysicalFourier

open Settings

open RegevSearch.PhysicalGrid

noncomputable section

def gap (p : Settings.Settings) (d n : ℕ) := 2/((base p).length:ℝ)+delta d+2*Real.sqrt ((1/4:ℝ)^n)

end

end InfoLossLAR.WorstCase.RectangularSource.Public

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity PaddedDecoder FineCodec NativeDualQuotient IntegerBasis

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open RegevLWE.GaussConv

noncomputable section

variable {n m M : ℕ} [NeZero M]

def fineSource (B : Matrix (Fin n) (Fin n) ℤ) (c : Config) (ticks : List Unit) (r z : Fin n → ℤ) : Source :=
  (((header c,ticks),(encMat encI B,serializeVector (List.ofFn r))),List.ofFn z)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FineCodec PaddedDecoder

open IntegerBasis

open NativeDualQuotient (Residual)

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2NativeAffineEncoding Integration9_9.TM2PlatformSerialization

open TM2Boolean TM2Boolean.PolyProgramCircuit RegevLWE.GaussConv SharedPoolCoherence

noncomputable section

variable {n m : ℕ}

def frameCode (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt k l stage ticks : List Unit) (R : ℚ) (prec : ℕ)
    (pool : Fin m → Fin n → ℤ) (cut : ℝ) (res : Residual B) (p : Retained (dual (inputLattice B hB)) (2^bt.length) cut) :=
  fineSource B (queryConfig bt k l R prec pool) ticks res.val (shortCoordinate B hB cut p)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates CoherentComputeUncompute QuantumXorOracle

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit SharedPoolCoherence GridReadout.Axis NativeQFTPlanCompile

open IntegerBasis RegevLWE.GaussConv GaussianPoissonSeries CoherentProjection CoherentDecoder

noncomputable section

abbrev StageI {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (b : ℕ) (c : ℝ) := Retained (StageL B hB) (2^b) c

abbrev taper {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (b : ℕ) (r cut : ℝ) (hr : 0<r)
    [Fintype (StageI B hB b cut)] :=
  normalized (finiteRestrict (fineEmbedding (StageL B hB) (2^b) cut)
    (gaussianHilbertState (fineLattice (StageL B hB) (2^b)) ((1/(Real.sqrt 2*r))/Real.sqrt 2) (by positivity) 0))

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity IntegerBasis PaddedDecoder CoherentComputeUncompute

open FineCodec

open Integration9_9.TM2NativeAffineEmitter Integration9_9.TM2PlatformSerialization

open TM2Boolean TM2Boolean.PolyProgramCircuit QuantumXorOracle ControlledNativeGates

noncomputable section

variable {n m : ℕ}

def stagedWord (s : List Unit) (q : Source) := NativePaddedWords.current (s,pack q)

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

open QAlgorithms QAlgorithms.Complexity FiniteGateTransport ControlledNativeGates ControlledNativeCode

open FineCodec PaddedDecoder TM2Boolean.PolyProgramCircuit NativeQFTPlanCompile

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9.TM2PlatformSerialization

noncomputable section

def codeList {n : ℕ} (c : Layered n) : List GateCode := c.flatten.map encodeInstr

end

end InfoLossLAR.WorstCase.RegevSearch.PhysicalFourier

end

section

namespace InfoLossLAR.WorstCase.RectangularSource.Cell

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open RegevSearch.PhysicalFourier RegevSearch.PhysicalGrid RegevSearch.FineCodec RegevSearch

open NativeDualQuotient IntegerBasis RectangularSource.Settings RectangularSource.Public

noncomputable section

section

variable (nt₀ copies acc oracle count width : List Unit) (B : Matrix (Fin nt₀.length) (Fin nt₀.length) ℤ)
  (R r : ℚ) (tape advice : Str)

abbrev encoded := receipt (RationalInverse.Native.inputRows B) R r copies acc oracle count width tape advice

include nt₀

end

end

end InfoLossLAR.WorstCase.RectangularSource.Cell

end

section

open scoped Classical BigOperators

namespace InfoLossLAR.WorstCase.RectangularSource.FineWires

open QAlgorithms QAlgorithms.Complexity CoherentComputeUncompute

open FiniteGateTransport RegevSearch.PhysicalFourier

open OAI.MetricKMedian.Binary NativeDualQuotient RegevSearch.FineCodec

open ControlledNativeGates

noncomputable section

def rawState {I : Type} [Fintype I] (F : ℕ) (s : List Unit) (src : I→Source) (v : I→ℂ) : QState F :=
  ∑ i, v i • basis (fun k=>TM2Boolean.wordExtension (stagedWord s (src i)) k.val)

end

end InfoLossLAR.WorstCase.RectangularSource.FineWires

end

section

namespace InfoLossLAR.WorstCase.RectangularSource.RawFront

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open CoherentComputeUncompute NativeDualQuotient RegevSearch.FineCodec FiniteGateTransport RegevSearch.PhysicalFourier

open Public Settings

noncomputable section

abbrev Spec := (List Unit× List Unit) × (List Unit×List Unit) × List Unit

end

end InfoLossLAR.WorstCase.RectangularSource.RawFront

end

section

open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RectangularSource.RawFront

open QAlgorithms QAlgorithms.Complexity OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open GaussianPoissonSeries FiniteGateTransport RegevSearch RegevSearch.PhysicalGrid RegevSearch.PhysicalFourier

open SharedPoolCoherence CoherentComputeUncompute CoherentProjection NativeDualQuotient RegevLWE.GaussConv IntegerBasis

open ControlledNativeCode ControlledNativeGates Settings Public

noncomputable section

def fits {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt : List Unit) (R : ℚ) (hR : 0<R)
    (pr : ℕ) (pool : Fin m→Fin n→ℤ) (cut : ℝ) (hcut : cut ≤ (famσ n:ℝ)/(2*(R:ℝ))) (data : Spec) : Prop :=
  let ((t,k),(l,s),_):=data
  k.length ≤ l.length ∧
  (∀ (res : Residual B) (i : StageI B hB bt.length cut), (FineCodec.pack (frameCode B hB bt k l s t R pr pool cut res i)).length ≤ s.length) ∧
  (∀ i : StageI B hB bt.length cut, (encVec encI (promisedShort B hB R hR cut hcut i).answer).length ≤ k.length) ∧
  (∀ i : StageI B hB bt.length cut, (encS (word pr pool (promisedShort B hB R hR cut hcut i))).length ≤ l.length)

def preparedState {n m : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (hB : B.det≠0) (bt : List Unit) (R r : ℚ) (hr : 0<r)
    (pr : ℕ) (pool : Fin m→Fin n→ℤ) (cut : ℝ) (data : Spec) (ε : ℝ)
    [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)]
    (wf : List Unit) (codes : List GateCode) : Prop :=
  let t:=data.1.1
  let k:=data.1.2
  let l:=data.2.1.1
  let s:=data.2.1.2
  let N:=data.2.2.length
  let u:=taper B hB bt.length (r:ℝ) cut (by exact_mod_cast hr)
  let src (z : Residual B × StageI B hB bt.length cut) := frameCode B hB bt k l s t R pr pool cut z.1 z.2
  ∃ G : Layered (wf.length+N), codeList G=codes ∧
    ∃ j : Hilbert (Residual B), ‖j‖=1 ∧ ∃ side : QState N, stateNorm side=1 ∧
    stateNorm (runLayered G (basis (0:Bits (wf.length+N))) -
      tensorState (FineWires.rawState wf.length s src (fun z => j z.1*u z.2)) side) ≤ ε

def frontContract (describe : Cell.Input→Spec) (emit : Cell.Input×List Unit→List GateCode) : Prop :=
  ∀ (nt copies acc oracle count width : List Unit) (B : Matrix (Fin nt.length) (Fin nt.length) ℤ)
    (hB : B.det≠0) (hn : 0<nt.length) (R r : ℚ) (hR : 0<R) (hr : 0<r) (cut : ℝ) (hc : 0<cut)
    (hscale : (nt.length:ℝ)*(physics r)^2 ≤ cut^2) (hcap : cut ≤ (nt.length+1:ℕ)*(r.den+1:ℕ))
    (hcut : cut ≤ (famσ nt.length:ℝ)/(2*(R:ℝ))) (tape advice : Str) (pool : Fin count.length→Fin nt.length→ℤ)
    (table : ∀ i, encVec encI (pool i) <+: (tape.drop (i.val*width.length)).take width.length),
    let v:=Cell.encoded nt copies acc oracle count width B R r tape advice
    let p:=atBasis B r nt.length acc
    let bt:=gridTape p.1
    ∀ [Fintype (Residual B)] [Fintype (StageI B hB bt.length cut)],
      fits B hB bt R hR oracle.length pool cut hcut (describe v) ∧
      ∀ wf : List Unit, (describe v).2.1.2.length ≤ wf.length →
        preparedState B hB bt R r hr oracle.length pool cut (describe v) (gap p nt.length nt.length) wf (emit (v,wf))

end

end InfoLossLAR.WorstCase.RectangularSource.RawFront

end



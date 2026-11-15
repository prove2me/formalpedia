-- Prove2me | Definitions.Def_InfoLossLAR_BDD_Coordinates
-- name    : InfoLossLAR_BDD_Coordinates
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:07:59.24008+00:00
-- url     : https://prove2.me/theorems/20d77fea-c25b-475b-a21a-36a8835c8619
-- title:
--   Exact original-basis coordinates and ideal modular-BDD residual objects
-- statement:
--   For the same nonsingular original integer basis, these exact definitions provide rational query pairings, the real dual basis, integral dual coordinates, canonical modular secret lifts, half-open nearest-integer coordinate rounding, one residual query/nearest point/reconstruction, and the ideal all-correct trajectories. The genuine lattice-membership and coordinate identity proofs needed to construct these objects are included as complete checked proofs. No BDD decoder is assumed or constructed. Full-error contraction, exact rounded recovery and stopping are separate theorem submissions; none is hidden as an algorithmic contract or axiom in this package.
-- source:
--   Official Lean declaration graph and syntax/info-tree oracle extract the minimal type-and-value dependency closure for the four existing BDD geometry theorems. Every kept command body is an exact source byte slice. The already published IntegerBasis Core is reused. No new mathematics; unrelated native sampler attributes and performance settings are omitted; empty namespaces preserve only unused open commands. The resulting 56 kernel declaration types and 56 values are individually definitionally equal to the original environment; all recursive axiom dependencies are standard three only. Extracted source SHA-256 b9e596d7f6b6d4536b7966e729cea038af2eda7adc06c5087c1556538386280f.

import Mathlib
import Definitions.Def_InfoLossLAR_IntegerBasis_Core
import Definitions.Def_RegevLWE_GaussConv_Lattice

set_option autoImplicit false

namespace AFT.GaussianSource
end AFT.GaussianSource

namespace AFT.RationalNumerics
end AFT.RationalNumerics

namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic

namespace OAI.MetricKMedian.Binary.Automatic
end OAI.MetricKMedian.Binary.Automatic

namespace Integration9_9.TM2NativeFiniteSeries
end Integration9_9.TM2NativeFiniteSeries

namespace Integration9_9.TM2NativeGaussian
end Integration9_9.TM2NativeGaussian

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding
end InfoLossLAR.WorstCase.GaussianRandomizedRounding

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

/-- Actual signed floor computed by the native rational ceiling/floor
machines; no real arithmetic occurs in the running program. -/
def anchor (center : ℚ) : ℚ :=
  if center<0 then -(⌈-center⌉₊ : ℚ) else (⌊center⌋₊ : ℚ)

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native



set_option autoImplicit false

namespace InfoLossLAR.WorstCase.GaussianLatticeTransport

open RegevLWE.GaussConv

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The literal image lattice under a continuous linear equivalence, expressed
as a pullback by the inverse so that existing lattice instances apply. -/
def imageLattice (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension)) :=
  ZLattice.comap ℝ lattice transform.symm.toLinearMap

@[simp] theorem mem_imageLattice (lattice : Submodule ℤ (Space (dimension := dimension)))
    (transform : Space (dimension := dimension) ≃L[ℝ] Space (dimension := dimension))
    (value : Space (dimension := dimension)) :
    value ∈ imageLattice lattice transform ↔ transform.symm value ∈ lattice := Iff.rfl

end

end InfoLossLAR.WorstCase.GaussianLatticeTransport



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection

open RegevLWE.GaussConv GaussianLatticeTransport

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev ScalingSpace := EuclideanSpace ℝ (Fin dimension)

/-- Literal positive dilation of Euclidean space. -/
def dilation (factor : ℝ) (hfactor : 0<factor) :
    ScalingSpace (dimension:=dimension) ≃L[ℝ] ScalingSpace (dimension:=dimension) :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 factor hfactor.ne')

theorem dilation_symm_apply (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    (dilation factor hfactor).symm value=factor⁻¹ • value := rfl

/-- The image is the actual scaled lattice, not merely a lattice with an
asserted smoothing bound. -/
theorem mem_dilated_lattice (lattice : Submodule ℤ (ScalingSpace (dimension:=dimension)))
    (factor : ℝ) (hfactor : 0<factor) (value : ScalingSpace (dimension:=dimension)) :
    value ∈ GaussianLatticeTransport.imageLattice lattice (dilation factor hfactor) ↔
      ∃ original ∈ lattice,factor • original=value := by
  rw [mem_imageLattice,dilation_symm_apply]
  constructor
  · intro membership
    refine ⟨factor⁻¹ • value,membership,?_⟩
    rw [smul_smul,mul_inv_cancel₀ hfactor.ne',one_smul]
  · rintro ⟨original,membership,rfl⟩
    simpa only [smul_smul,inv_mul_cancel₀ hfactor.ne',one_smul] using membership

end

end InfoLossLAR.WorstCase.GaussianProjection



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

open AFT GaussianSource RegevLWE.GaussConv GaussianRandomizedRounding

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

abbrev Space := EuclideanSpace ℝ (Fin dimension)

/-- The actual integral pairing supplied by dual-lattice membership. -/
def pairing (lattice : Submodule ℤ (Space (dimension:=dimension))) (nearest : dual lattice) : lattice →ₗ[ℤ] ℤ :=
  LinearMap.BilinForm.dualSubmoduleToDual (innerₗ (Space (dimension:=dimension))) lattice nearest

theorem pairing_spec (lattice : Submodule ℤ (Space (dimension:=dimension))) (nearest : dual lattice) (value : lattice) :
    (pairing lattice nearest value : ℝ)=inner ℝ (nearest : Space (dimension:=dimension)) (value : Space (dimension:=dimension)) := by
  exact LinearMap.BilinForm.dualSubmoduleParing_spec (innerₗ (Space (dimension:=dimension))) nearest value

def secretCoordinates {Index : Type*} [Fintype Index] (q : ℕ)
    (lattice : Submodule ℤ (Space (dimension:=dimension))) (basis : Module.Basis Index ℤ lattice) (nearest : dual lattice) : Index → ZMod q :=
  fun index => (pairing lattice nearest (basis index) : ZMod q)

def modulusLattice (q : ℕ) [NeZero q] (lattice : Submodule ℤ (Space (dimension:=dimension))) :
    Submodule ℤ (Space (dimension:=dimension)) :=
  GaussianLatticeTransport.imageLattice lattice (dilation (q : ℝ) (Nat.cast_pos.mpr (NeZero.pos q)))

end

end InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

/-- The original input columns are also the integral basis of this exact
submodule. No independently selected lattice basis is introduced. -/
def integerBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℤ (inputLattice basis hdet) := (realBasis basis hdet).restrictScalars ℤ

/-- Exact rational BDD queries are interpreted as ordinary real vectors. -/
def rationalPoint (query : Fin dimension → ℚ) : Space (dimension:=dimension) :=
  WithLp.toLp 2 (fun row => (query row : ℝ))

/-- Finite rational arithmetic computes the queried lattice projection. -/
def projection (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (value : Fin dimension → ℤ) : ℚ :=
  ∑ row,query row*((basis.mulVec value) row : ℚ)

end

end InfoLossLAR.WorstCase.IntegerBasis



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem inner_nondegenerate : (innerₗ (Space (dimension:=dimension))).Nondegenerate := by
  constructor
  · intro value hzero
    exact inner_self_eq_zero.mp (hzero value)
  · intro value hzero
    exact inner_self_eq_zero.mp (hzero value)

/-- The dual basis is defined from the original input columns and the
actual Euclidean inner product. -/
def dualRealBasis (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    Module.Basis (Fin dimension) ℝ (Space (dimension:=dimension)) :=
  LinearMap.BilinForm.dualBasis (innerₗ (Space (dimension:=dimension))) inner_nondegenerate (realBasis basis hdet)

theorem dual_lattice_eq_span (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    dual (inputLattice basis hdet)=Submodule.span ℤ (Set.range (dualRealBasis basis hdet)) := by
  exact LinearMap.BilinForm.dualSubmodule_span_of_basis (innerₗ (Space (dimension:=dimension))) inner_nondegenerate (realBasis basis hdet)

/-- Integral coordinates in the actual dual input basis. -/
def dualCoordinates (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) :
    (Fin dimension → ℤ) →ₗ[ℤ] Space (dimension:=dimension) :=
  Fintype.linearCombination ℤ (dualRealBasis basis hdet)

theorem dualCoordinates_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) : dualCoordinates basis hdet value=∑ index,value index • dualRealBasis basis hdet index := rfl

theorem dualCoordinates_mem (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (value : Fin dimension → ℤ) : dualCoordinates basis hdet value ∈ dual (inputLattice basis hdet) := by
  rw [dual_lattice_eq_span,dualCoordinates_apply]
  apply Submodule.sum_mem
  intro index _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨index,rfl⟩)

/-- Every actual dual-lattice point has the integral coordinates returned
by the fixed-secret LWE reduction. -/
theorem dualCoordinates_pairing (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (nearest : dual (inputLattice basis hdet)) :
    dualCoordinates basis hdet (fun index => pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index))=
      (nearest : Space (dimension:=dimension)) := by
  have h := (dualRealBasis basis hdet).sum_repr (nearest : Space (dimension:=dimension))
  rw [dualCoordinates_apply]
  calc
    _ = ∑ index,((dualRealBasis basis hdet).repr (nearest : Space (dimension:=dimension)) index) • dualRealBasis basis hdet index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [←Int.cast_smul_eq_zsmul ℝ,pairing_spec]
      congr 1
      have hreal : (integerBasis basis hdet index : Space (dimension:=dimension))=realBasis basis hdet index :=
        Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index
      rw [hreal]
      exact (LinearMap.BilinForm.dualBasis_repr_apply inner_nondegenerate (realBasis basis hdet) (nearest : Space (dimension:=dimension)) index).symm
    _ = _ := h

/-- Canonical mathematical representative of a decoded LWE secret in the
actual dual input lattice. -/
def secretLift (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) (secret : Fin dimension → ZMod q) : Space (dimension:=dimension) :=
  dualCoordinates basis hdet (fun index => ((secret index).val : ℤ))

/-- A recovered LWE secret specifies the actual nearest dual point modulo
q times the dual input lattice. This is a proved modular output contract;
recovering the unique full BDD point still requires the subsequent lifting
algorithm and distance checks. -/
theorem secretLift_modulus (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    (nearest : Space (dimension:=dimension))-
      secretLift basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest) ∈
        modulusLattice q (dual (inputLattice basis hdet)) := by
  let coefficients := fun index => pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index)
  let residues := fun index => (((coefficients index : ZMod q).val) : ℤ)
  let quotient := fun index => (coefficients index-residues index)/(q : ℤ)
  have hdiv (index : Fin dimension) : (q : ℤ) ∣ coefficients index-residues index := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    simp only [residues,Int.cast_sub,Int.cast_natCast,ZMod.natCast_zmod_val,sub_self]
  have hcoeff : (q : ℤ) • quotient=coefficients-residues := by
    funext index
    change (q : ℤ)*((coefficients index-residues index)/(q : ℤ))=coefficients index-residues index
    exact Int.mul_ediv_cancel' (hdiv index)
  apply (mem_dilated_lattice (dual (inputLattice basis hdet)) (q : ℝ)
    (by exact_mod_cast NeZero.pos q) _).mpr
  refine ⟨dualCoordinates basis hdet quotient,dualCoordinates_mem basis hdet quotient,?_⟩
  calc
    (q : ℝ) • dualCoordinates basis hdet quotient=(q : ℤ) • dualCoordinates basis hdet quotient := by
      simpa only [Int.cast_natCast] using Int.cast_smul_eq_zsmul ℝ (q : ℤ) (dualCoordinates basis hdet quotient)
    _ = dualCoordinates basis hdet ((q : ℤ) • quotient) := (map_smul (dualCoordinates basis hdet) (q : ℤ) quotient).symm
    _ = dualCoordinates basis hdet (coefficients-residues) := congrArg (dualCoordinates basis hdet) hcoeff
    _ = dualCoordinates basis hdet coefficients-dualCoordinates basis hdet residues := map_sub _ _ _
    _ = _ := by
      rw [show dualCoordinates basis hdet coefficients=(nearest : Space (dimension:=dimension)) from dualCoordinates_pairing basis hdet nearest]
      rfl

end

end InfoLossLAR.WorstCase.IntegerBasis



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

/-- The public residual query after decoding one mod-q secret. Its formula
uses only the query and the decoded canonical representative. -/
def residualQuery (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) (query : Space (dimension:=dimension)) (secret : Fin dimension → ZMod q) : Space (dimension:=dimension) :=
  (q : ℝ)⁻¹ • (query-secretLift basis hdet q secret)

/-- A correct modular answer leaves a genuine dual-lattice residual point.
The hidden nearest point is used only to state the success invariant. -/
theorem residualNearest_mem (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    (q : ℝ)⁻¹ • ((nearest : Space (dimension:=dimension))-
      secretLift basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)) ∈
        dual (inputLattice basis hdet) := by
  have hq : (q : ℝ)≠0 := by exact_mod_cast NeZero.ne q
  obtain ⟨point,hpoint,hequal⟩ :=
    (mem_dilated_lattice (dual (inputLattice basis hdet)) (q : ℝ) (by exact_mod_cast NeZero.pos q) _).mp
      (secretLift_modulus basis hdet q nearest)
  rw [←hequal,smul_smul,inv_mul_cancel₀ hq,one_smul]
  exact hpoint

/-- This residual point belongs to the actual dual lattice; no oracle
return value is inserted as a lattice-membership assumption. -/
def residualNearest (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) : dual (inputLattice basis hdet) :=
  ⟨(q : ℝ)⁻¹ • ((nearest : Space (dimension:=dimension))-
    secretLift basis hdet q (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet) nearest)),
      residualNearest_mem basis hdet q nearest⟩

/-- Public reconstruction from one decoded residue and a recursively
recovered residual point. -/
def reconstructPoint (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (q : ℕ) (secret : Fin dimension → ZMod q) (point : Space (dimension:=dimension)) : Space (dimension:=dimension) :=
  (q : ℝ) • point+secretLift basis hdet q secret

end

end InfoLossLAR.WorstCase.IntegerBasis



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

/-- Exact query pairing with one original input column, computed as a
finite rational matrix/vector projection. -/
def queryCoordinate (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (index : Fin dimension) : ℚ :=
  projection basis query (Pi.single index 1)

/-- Deterministic nearest-integer rounding, with the half-open tie convention. -/
def nearestInteger (center : ℚ) : ℤ := (GaussianRandomizedRounding.Native.anchor (center+1/2)).num

def roundedCoordinates (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) : Fin dimension → ℤ := fun index => nearestInteger (queryCoordinate basis query index)

/-- The final rounded candidate always lies in the actual dual lattice. -/
def roundedPoint (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) : dual (inputLattice basis hdet) :=
  ⟨dualCoordinates basis hdet (roundedCoordinates basis query),dualCoordinates_mem basis hdet _⟩

end

end InfoLossLAR.WorstCase.IntegerBasis



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

noncomputable section

variable {dimension : ℕ}

/-- The ideal unique-nearest trajectory used to verify the public modular
BDD recursion; no algorithm is allowed access to this hidden point. -/
def nearestTrajectory (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (q : ℕ) [NeZero q] : ℕ → dual (inputLattice basis hdet) → dual (inputLattice basis hdet)
  | 0,nearest => nearest
  | count+1,nearest => residualNearest basis hdet q (nearestTrajectory basis hdet q count nearest)

/-- Ideal query trajectory when every modular answer is correct. The
actual public query update is exactly residualQuery at each such answer. -/
def queryTrajectory (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det ≠ 0)
    (q : ℕ) [NeZero q] (nearest : dual (inputLattice basis hdet)) :
    ℕ → Space (dimension:=dimension) → Space (dimension:=dimension)
  | 0,query => query
  | count+1,query => residualQuery basis hdet q (queryTrajectory basis hdet q nearest count query)
      (secretCoordinates q (inputLattice basis hdet) (integerBasis basis hdet)
        (nearestTrajectory basis hdet q count nearest))

end

end InfoLossLAR.WorstCase.IntegerBasis



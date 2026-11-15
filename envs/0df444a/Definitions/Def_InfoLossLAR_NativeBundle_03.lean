-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_03
-- name    : InfoLossLAR_NativeBundle_03
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T11:01:46.889043+00:00
-- url     : https://prove2.me/theorems/748d8b2b-ddd8-42d0-a911-174fc1109a0e
-- title:
--   Finite binary sampling and stored coefficient interfaces
-- statement:
--   This package defines binary finite-distribution sampling, array and counter operations, bit-tape access, affine load assembly, and the stored scalar and dependent tensor interfaces required for finite coefficient evaluation.
--
--   For nonnegative rational probabilities $p_0,\ldots,p_{m-1}$ with total mass one, the finite sampler starts with dyadic ticket counts
--   $$a_i=\lfloor 2^b p_i\rfloor,$$
--   assigns the remaining tickets to the first entry, and selects a bucket from a fair $b$-bit tape. The implementation keeps its integers and rational arithmetic in the stored binary representation.
--
--   The package provides executable data and the definitional interfaces used by later sampling and coefficient theorems. Its native work fields do not alone assert a platform machine-time bound.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0, native lean source modules: lean/AFT/Geometry.lean, lean/AFT/IntegerAffineAssembly.lean, lean/AFT/BinaryAffineAssembly.lean, lean/AFT/CountedCenteredSampling.lean, lean/AFT/CountedWindowQuery.lean, lean/AFT/CountedRootMarginal.lean, lean/AFT/CountedActivationProgram.lean, lean/AFT/CountedPrimarySources.lean, lean/AFT/CountedPrimaryProgram.lean, lean/AFT/BinaryIntervalProbability.lean, lean/AFT/BinarySliceProbability.lean, lean/AFT/RationalPaletteSampler.lean, lean/AFT/BinaryAveragedSlice.lean, lean/AFT/BinaryTicketBucket.lean, lean/AFT/BinaryTicketTable.lean, lean/AFT/BinaryFiniteDraw.lean, lean/AFT/BinaryNormalizeArray.lean, lean/AFT/BinaryPositiveNormalize.lean, lean/AFT/BinaryPositiveDraw.lean, lean/AFT/BinaryPositiveFinDraw.lean, lean/AFT/BinaryFiniteSeries.lean, lean/AFT/BinarySeriesPolynomials.lean, lean/AFT/BinarySamplingPolynomials.lean, lean/AFT/BinaryUniformDraw.lean, lean/AFT/BinaryPermutationChoice.lean, lean/AFT/BinaryPermutationRows.lean, lean/AFT/FiniteSetNumberingTransport.lean, lean/AFT/PublicPoolScanProgram.lean, lean/AFT/CountedPublicPoolScan.lean, lean/AFT/UnaryPolynomialCounters.lean, lean/AFT/BinaryBlockAddresses.lean, lean/AFT/BinaryLegCutoff.lean, lean/AFT/BinaryBoundaryHalf.lean, lean/AFT/BinaryProtectedFeatureCost.lean, lean/AFT/BinaryProtectedScale.lean, lean/AFT/BinaryChartCoordinates.lean, lean/AFT/BinaryChartIteration.lean, lean/AFT/BinaryChartProjection.lean, lean/AFT/BinaryChartProjectionCost.lean, lean/AFT/BinaryChartInputs.lean, lean/AFT/BinaryChartInputsCost.lean, lean/AFT/BinaryMarkedChartCost.lean, lean/AFT/BinaryChartPolynomials.lean, lean/AFT/BinaryChartSupports.lean, lean/AFT/BinaryGaussianControl.lean, lean/AFT/BinaryExponentialProgram.lean, lean/AFT/BinaryGaussianInputs.lean, lean/AFT/BinaryGaussianProgram.lean, lean/AFT/BinaryGaussianPolynomials.lean, lean/AFT/BinaryLegalChart.lean, lean/AFT/BinaryMatrixArray.lean, lean/AFT/BinaryParameterProgram.lean, lean/AFT/BinaryParameterResources.lean, lean/AFT/BinaryPermutationPolynomials.lean, lean/AFT/BinaryPermutationTape.lean, lean/AFT/PhysicalLoadProgram.lean, lean/AFT/BinaryPhysicalBaseline.lean, lean/AFT/BinaryProtectedParameters.lean, lean/AFT/BinaryProtectedAtomCost.lean, lean/AFT/BinaryProtectedPaletteCost.lean, lean/AFT/BinaryProtectedMetadata.lean, lean/AFT/BinaryProtectedMetadataCost.lean, lean/AFT/BinaryProtectedWeight.lean, lean/AFT/BinaryProtectedChartDraw.lean, lean/AFT/BinarySafeProtectedChart.lean, lean/AFT/BinaryProtectedPolynomials.lean, lean/AFT/BinaryPublicBaseline.lean, lean/AFT/BinaryRejectionLoop.lean, lean/AFT/BinarySignedShiftSum.lean, lean/AFT/StoredScalarEvaluation.lean, lean/AFT/BinaryStoredScalar.lean, lean/AFT/BinaryWindowControl.lean, lean/AFT/BinaryWindowGaussian.lean, lean/AFT/DependentTensorChannel.lean, lean/AFT/DependentOldCentering.lean, lean/AFT/CanonicalPointBasis.lean, lean/AFT/Construction.lean, lean/AFT/CountableFiniteProduct.lean, lean/AFT/CountedRootSelections.lean, lean/AFT/MixedFiniteSeed.lean, lean/AFT/MixedCanonicalFibers.lean, lean/AFT/MixedReferenceCanonicalFibers.lean, lean/AFT/PendingPrimaryExpansion.lean, lean/AFT/ReferenceCoefficientPolynomial.lean, lean/AFT/ReferenceSingletonComponent.lean. Migrated source units selected by the Lean declaration and syntax oracles; exact source body hashes and original module paths recorded in Integration9_9/provenance/full_project_extraction/native_definition_bundles/manifest.json. Bundle SHA256 a471813d5493709b283cd6bf777932747f188d7fb7a98e474a8d074d25b4a953.

import Definitions.Def_InfoLossLAR_NativeBundle_01
import Definitions.Def_InfoLossLAR_NativeBundle_02
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalControl
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalLiterals
import Definitions.Def_InfoLossLAR_Native_AFT_BinaryRationalOperations
import Definitions.Def_InfoLossLAR_Native_AFT_BinarySignedAddition
import Definitions.Def_InfoLossLAR_Native_AFT_FiniteConcentration
import Definitions.Def_InfoLossLAR_Native_AFT_Histogram
import Definitions.Def_InfoLossLAR_Native_AFT_Hoeffding
import Definitions.Def_InfoLossLAR_Native_AFT_RationalHeight
import Definitions.Def_InfoLossLAR_Native_AFT_TransportBound
import Mathlib
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Matrix.LDL
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Fin.Tuple.Reflection
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Rat.Floor
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Hom.Set
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

section




/-!
# Canonical endpoint and carry identities

The modular output below is the coordinatewise reduction of the actual integer
rounding preimage. No quotient-isomorphism or carry-correctness hypothesis is
assumed. We prove the exact carry criterion for the fixed path rounding map.
-/

namespace AFT

/-- Coordinatewise reduction of an integral transport output. -/
def reduceCoordinates (n q : ℕ) (x : (Fin n → ℤ) × ℤ) :
    (Fin n → ZMod q) × ZMod q := (fun i => (x.1 i : ZMod q), (x.2 : ZMod q))

/-- Equality of modular outputs is exactly divisibility of their integer difference. -/
theorem reduceCoordinates_eq_iff (n q : ℕ) (x y : (Fin n → ℤ) × ℤ) :
    reduceCoordinates n q x = reduceCoordinates n q y ↔
      ∃ k : (Fin n → ℤ) × ℤ, x - y = (q : ℤ) • k := by
  constructor
  · intro h
    have he : ∀ i, (q : ℤ) ∣ x.1 i - y.1 i := by
      intro i
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (y.1 i) (x.1 i) q).1
      exact (congrArg (fun v : (Fin n → ZMod q) × ZMod q => v.1 i) h).symm
    choose e he using he
    have ha : (q : ℤ) ∣ x.2 - y.2 :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub y.2 x.2 q).1 (congrArg Prod.snd h).symm
    obtain ⟨a, ha⟩ := ha
    refine ⟨(e, a), Prod.ext ?_ ?_⟩
    · funext i
      exact he i
    · exact ha
  · rintro ⟨k, hk⟩
    apply Prod.ext
    · funext i
      apply Eq.symm
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub (y.1 i) (x.1 i) q).2
      exact ⟨k.1 i, congrArg (fun v : (Fin n → ℤ) × ℤ => v.1 i) hk⟩
    · apply Eq.symm
      apply (ZMod.intCast_eq_intCast_iff_dvd_sub y.2 x.2 q).2
      exact ⟨k.2, congrArg Prod.snd hk⟩

/-- Canonical integer endpoint representative, entrywise in `[0,q)`. -/
def canonicalEndpoint (n q : ℕ) (load : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => load i % (q : ℤ)

/-- Canonical carry; integer division agrees with floor division for positive `q`. -/
def canonicalCarry (n q : ℕ) (load : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun i => load i / (q : ℤ)

/-- Exact integer division-with-remainder identity, including negative loads. -/
theorem canonical_endpoint_carry (n q : ℕ) (load : Fin (n + 1) → ℤ) :
    load - canonicalEndpoint n q load = (q : ℤ) • canonicalCarry n q load := by
  funext i
  change load i - load i % (q : ℤ) = (q : ℤ) * (load i / (q : ℤ))
  have h := Int.emod_add_mul_ediv (load i) (q : ℤ)
  omega



/-- Removing the canonical carry preserves membership in the rounding image lattice. -/
theorem canonicalEndpoint_mem_lattice (n q : ℕ) (load : Fin (n + 1) → ℤ)
    (hload : (q : ℤ) ∣ totalCharge load) :
    (q : ℤ) ∣ totalCharge (canonicalEndpoint n q load) := by
  have h := congrArg totalCharge (canonical_endpoint_carry n q load)
  rw [totalCharge_sub, totalCharge_smul] at h
  have hd : (q : ℤ) ∣ totalCharge load - totalCharge (canonicalEndpoint n q load) :=
    ⟨totalCharge (canonicalCarry n q load), h⟩
  exact (dvd_sub_right hload).1 hd

/-- Integral canonical pullback through the fixed rounding map. -/
noncomputable def canonicalPullback (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (load : Fin (n + 1) → ℤ) (hload : (q : ℤ) ∣ totalCharge load) :
    (Fin n → ℤ) × ℤ :=
  (roundingCoordinates n q (by exact_mod_cast hq) c hc).symm
    ⟨canonicalEndpoint n q load, canonicalEndpoint_mem_lattice n q load hload⟩

@[simp] theorem roundingLoad_canonicalPullback (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (load : Fin (n + 1) → ℤ) (hload : (q : ℤ) ∣ totalCharge load) :
    roundingLoad n c (canonicalPullback n q hq c hc load hload) =
      canonicalEndpoint n q load := by
  change ((roundingCoordinates n q (by exact_mod_cast hq) c hc)
    ((roundingCoordinates n q (by exact_mod_cast hq) c hc).symm _)
      : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Additivity of the actual rounding map. -/
theorem roundingLoad_sub (n : ℕ) (c : Fin (n + 1) → ℤ)
    (x y : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (x - y) = roundingLoad n c x - roundingLoad n c y := by
  simp only [roundingLoad, Prod.fst_sub, Prod.snd_sub, sub_smul]
  have hp : pathLoad n (x.1 - y.1) = pathLoad n x.1 - pathLoad n y.1 :=
    (pathIncidence n).map_sub x.1 y.1
  rw [hp]
  abel

theorem roundingLoad_smul (n : ℕ) (c : Fin (n + 1) → ℤ)
    (a : ℤ) (x : (Fin n → ℤ) × ℤ) :
    roundingLoad n c (a • x) = a • roundingLoad n c x := by
  simp only [roundingLoad, Prod.smul_fst, Prod.smul_snd, pathLoad_smul, smul_add,
    smul_smul, smul_eq_mul]

/-- Exact canonical carry criterion in V7: the reduced integral output equals
its endpoint's canonical pullback exactly when the canonical carry is in the
rounding image lattice. The statement does not assume a probability estimate. -/
theorem canonical_carry_criterion (n q : ℕ) (hq : q ≠ 0)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    let load := roundingLoad n c x
    let hload := (rounding_image_lattice n q c hc load).1 ⟨x, rfl⟩
    reduceCoordinates n q x =
      reduceCoordinates n q (canonicalPullback n q hq c hc load hload) ↔
        (q : ℤ) ∣ totalCharge (canonicalCarry n q load) := by
  dsimp only
  let y := canonicalPullback n q hq c hc (roundingLoad n c x)
    ((rounding_image_lattice n q c hc _).1 ⟨x, rfl⟩)
  have hy : roundingLoad n c y = canonicalEndpoint n q (roundingLoad n c x) :=
    roundingLoad_canonicalPullback n q hq c hc _ _
  have hdiff : roundingLoad n c (x - y) =
      (q : ℤ) • canonicalCarry n q (roundingLoad n c x) := by
    rw [roundingLoad_sub, hy]
    exact canonical_endpoint_carry n q _
  change reduceCoordinates n q x = reduceCoordinates n q y ↔ _
  rw [reduceCoordinates_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    rw [hk, roundingLoad_smul] at hdiff
    have hkload : roundingLoad n c k = canonicalCarry n q (roundingLoad n c x) := by
      funext i
      have hi := congrFun hdiff i
      exact mul_left_cancel₀ (by exact_mod_cast hq : (q : ℤ) ≠ 0) hi
    exact (rounding_image_lattice n q c hc _).1 ⟨k, hkload⟩
  · intro h
    obtain ⟨k, hk⟩ := (rounding_image_lattice n q c hc _).2 h
    refine ⟨k, roundingLoad_injective n q (by exact_mod_cast hq) c hc ?_⟩
    rw [roundingLoad_smul, hk, hdiff]

end AFT

namespace AFT

open scoped BigOperators

/-- Canonical lift of a modular coordinate vector, in the coordinate order
(edges, injection coordinate) used throughout the formalization. -/
def liftCoordinates (n q : ℕ) (x : (Fin n → ZMod q) × ZMod q) :
    (Fin n → ℤ) × ℤ := (fun i => (x.1 i).val, x.2.val)

@[simp] theorem reduce_liftCoordinates (n q : ℕ) [NeZero q]
    (x : (Fin n → ZMod q) × ZMod q) :
    reduceCoordinates n q (liftCoordinates n q x) = x := by
  ext i <;> simp [reduceCoordinates, liftCoordinates]

/-- The concrete one-dimensional LAR label on any integer lift. -/
def integerLabel (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ℤ) × ℤ) : ZMod q :=
  (totalCharge (canonicalCarry n q (roundingLoad n c x)) : ZMod q)

/-- The label is independent of the chosen integer lift. -/
theorem integerLabel_congr (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x y : (Fin n → ℤ) × ℤ)
    (h : reduceCoordinates n q x = reduceCoordinates n q y) :
    integerLabel n q c x = integerLabel n q c y := by
  obtain ⟨k, hk⟩ := (reduceCoordinates_eq_iff n q x y).1 h
  have hr : roundingLoad n c x = roundingLoad n c y + (q : ℤ) • roundingLoad n c k := by
    have ht := congrArg (roundingLoad n c) hk
    rw [roundingLoad_sub, roundingLoad_smul] at ht
    exact sub_eq_iff_eq_add.mp ht |>.trans (add_comm _ _)
  have hcarry : canonicalCarry n q (roundingLoad n c x) =
      canonicalCarry n q (roundingLoad n c y) + roundingLoad n c k := by
    funext i
    rw [hr]
    exact Int.add_mul_ediv_left _ _ (by exact_mod_cast NeZero.ne q)
  unfold integerLabel
  rw [hcarry, totalCharge_add, Int.cast_add]
  have hd := (rounding_image_lattice n q c hc (roundingLoad n c k)).1 ⟨k, rfl⟩
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hd, add_zero]

/-- LAR label on the residue vector, computed using its canonical lift. -/
def fiberLabel (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x : (Fin n → ZMod q) × ZMod q) : ZMod q :=
  integerLabel n q c (liftCoordinates n q x)

@[simp] theorem fiberLabel_reduceCoordinates (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) :
    fiberLabel n q c (reduceCoordinates n q x) = integerLabel n q c x := by
  apply integerLabel_congr n q c hc
  exact reduce_liftCoordinates n q _

/-- Actual zero fiber, defined by the canonical carry label. -/
def ZeroFiber (n q : ℕ) (c : Fin (n + 1) → ℤ) :=
  {x : (Fin n → ZMod q) × ZMod q // fiberLabel n q c x = 0}

/-- The zero-sum endpoint hyperplane over `ZMod q`. -/
def EndpointHyperplane (n q : ℕ) :=
  {r : Fin (n + 1) → ZMod q // ∑ i, r i = 0}

/-- Canonical integer lift of an endpoint. -/
def endpointLift (n q : ℕ) (r : EndpointHyperplane n q) : Fin (n + 1) → ℤ :=
  fun i => (r.val i).val

theorem endpointLift_mem_lattice (n q : ℕ) [NeZero q]
    (r : EndpointHyperplane n q) : (q : ℤ) ∣ totalCharge (endpointLift n q r) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  simpa [totalCharge, endpointLift] using r.property

@[simp] theorem canonicalCarry_endpointLift (n q : ℕ) [NeZero q]
    (r : EndpointHyperplane n q) : canonicalCarry n q (endpointLift n q r) = 0 := by
  funext i
  change ((r.val i).val : ℤ) / (q : ℤ) = 0
  apply Int.ediv_eq_zero_of_lt
  · exact_mod_cast Nat.zero_le _
  · exact_mod_cast ZMod.val_lt (r.val i)

/-- Integral preimage of a canonical endpoint lift. -/
noncomputable def endpointIntegralPreimage (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) : (Fin n → ℤ) × ℤ :=
  (roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc).symm
    ⟨endpointLift n q r, endpointLift_mem_lattice n q r⟩

@[simp] theorem roundingLoad_endpointIntegralPreimage (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) :
    roundingLoad n c (endpointIntegralPreimage n q c hc r) = endpointLift n q r := by
  change ((roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc)
    ((roundingCoordinates n q (by exact_mod_cast NeZero.ne q) c hc).symm _)
      : Fin (n + 1) → ℤ) = _
  rw [LinearEquiv.apply_symm_apply]

/-- Canonical endpoint pullback into the actual zero fiber. -/
noncomputable def zeroFiberPullback (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) : ZeroFiber n q c :=
  ⟨reduceCoordinates n q (endpointIntegralPreimage n q c hc r), by
    rw [fiberLabel_reduceCoordinates n q c hc]
    simp [integerLabel, totalCharge]⟩

/-- Endpoint residue of a modular output, with its zero-sum property proved from
the integral rounding image lattice. -/
def endpointProjection (n q : ℕ)
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) : EndpointHyperplane n q :=
  ⟨fun i => (roundingLoad n c (liftCoordinates n q x) i : ZMod q), by
    have hd := (rounding_image_lattice n q c hc
      (roundingLoad n c (liftCoordinates n q x))).1 ⟨_, rfl⟩
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 hd
    simpa [totalCharge] using hz⟩

/-- Rounding commutes with changing integer representatives modulo `q`. -/
theorem roundingLoad_reduce_congr (n q : ℕ) (c : Fin (n + 1) → ℤ)
    (x y : (Fin n → ℤ) × ℤ)
    (h : reduceCoordinates n q x = reduceCoordinates n q y) (i : Fin (n + 1)) :
    (roundingLoad n c x i : ZMod q) = (roundingLoad n c y i : ZMod q) := by
  obtain ⟨k, hk⟩ := (reduceCoordinates_eq_iff n q x y).1 h
  have hr := congrArg (roundingLoad n c) hk
  rw [roundingLoad_sub, roundingLoad_smul] at hr
  apply Eq.symm
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ q).2
  exact ⟨roundingLoad n c k i, congrFun hr i⟩

@[simp] theorem endpointProjection_reduceCoordinates (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ℤ) × ℤ) (i : Fin (n + 1)) :
    (endpointProjection n q c hc (reduceCoordinates n q x)).val i =
      (roundingLoad n c x i : ZMod q) :=
  roundingLoad_reduce_congr n q c _ x (reduce_liftCoordinates n q _) i

/-- The endpoint projection recovers the input endpoint after canonical pullback. -/
theorem endpointProjection_zeroFiberPullback (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (r : EndpointHyperplane n q) :
    endpointProjection n q c hc (zeroFiberPullback n q c hc r).val = r := by
  apply Subtype.ext
  funext i
  simp [zeroFiberPullback, endpointLift]

/-- Lifting the actual endpoint residue gives precisely the canonical remainder. -/
theorem endpointLift_projection (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : (Fin n → ZMod q) × ZMod q) :
    endpointLift n q (endpointProjection n q c hc x) =
      canonicalEndpoint n q (roundingLoad n c (liftCoordinates n q x)) := by
  funext i
  exact ZMod.val_intCast _

/-- Every element of the actual zero fiber is recovered by the canonical endpoint
pullback. This uses the proved carry criterion, rather than assuming the bijection. -/
theorem zeroFiberPullback_endpointProjection (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ))
    (x : ZeroFiber n q c) :
    zeroFiberPullback n q c hc (endpointProjection n q c hc x.val) = x := by
  apply Subtype.ext
  let z := liftCoordinates n q x.val
  have hcarry : (q : ℤ) ∣ totalCharge (canonicalCarry n q (roundingLoad n c z)) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1 x.property
  have hcriterion := (canonical_carry_criterion n q (NeZero.ne q) c hc z).2 hcarry
  have heq : endpointIntegralPreimage n q c hc (endpointProjection n q c hc x.val) =
      canonicalPullback n q (NeZero.ne q) c hc (roundingLoad n c z)
        ((rounding_image_lattice n q c hc _).1 ⟨z, rfl⟩) := by
    apply roundingLoad_injective n q (by exact_mod_cast NeZero.ne q) c hc
    rw [roundingLoad_endpointIntegralPreimage, roundingLoad_canonicalPullback,
      endpointLift_projection]
  change reduceCoordinates n q (endpointIntegralPreimage n q c hc
    (endpointProjection n q c hc x.val)) = x.val
  rw [heq, ← hcriterion]
  exact reduce_liftCoordinates n q x.val

/-- V7's canonical endpoint parametrization, proved as an actual equivalence
between the zero-sum residue hyperplane and the carry-label zero fiber. -/
noncomputable def canonicalEndpointEquiv (n q : ℕ) [NeZero q]
    (c : Fin (n + 1) → ℤ) (hc : totalCharge c = (q : ℤ)) :
    EndpointHyperplane n q ≃ ZeroFiber n q c where
  toFun := zeroFiberPullback n q c hc
  invFun := fun x => endpointProjection n q c hc x.val
  left_inv := endpointProjection_zeroFiberPullback n q c hc
  right_inv := zeroFiberPullback_endpointProjection n q c hc

end AFT

namespace AFT





end AFT

end

section




























namespace AFT
end AFT
namespace AFT.AffinePair
end AFT.AffinePair
namespace AFT.AffinePair.postcompose
end AFT.AffinePair.postcompose
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.chartIntegerLoad
end AFT.BoundaryCalibration.chartIntegerLoad
namespace AFT.BoundaryCalibration.protectedInputs
end AFT.BoundaryCalibration.protectedInputs
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualChartLegEquiv
end AFT.V7Calibration.actualChartLegEquiv
namespace AFT.V7Calibration.actualChartLegLinear
end AFT.V7Calibration.actualChartLegLinear
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualIntegerBlockLoad
end AFT.V7Calibration.actualIntegerBlockLoad
namespace AFT.V7Calibration.actualIntegerBlockLoad.match_1
end AFT.V7Calibration.actualIntegerBlockLoad.match_1
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPhysicalAffinePair
end AFT.V7Calibration.actualPhysicalAffinePair
namespace AFT.V7Calibration.actualPhysicalEdgeLinear
end AFT.V7Calibration.actualPhysicalEdgeLinear
namespace AFT.V7Calibration.actualPhysicalEdgeMatrix
end AFT.V7Calibration.actualPhysicalEdgeMatrix
namespace AFT.V7Calibration.actualPhysicalInitialCoordinates
end AFT.V7Calibration.actualPhysicalInitialCoordinates
namespace AFT.V7Calibration.actualPhysicalReducedTransport
end AFT.V7Calibration.actualPhysicalReducedTransport
namespace AFT.V7Calibration.actualPhysicalTransport
end AFT.V7Calibration.actualPhysicalTransport
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualQueueMask
end AFT.V7Calibration.actualQueueMask
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.extensionCoordinates
end AFT.V7Calibration.extensionCoordinates
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.legTriangularEquiv
end AFT.V7Calibration.legTriangularEquiv
namespace AFT.V7Calibration.legTriangularLinear
end AFT.V7Calibration.legTriangularLinear
namespace AFT.V7Calibration.physicalBlockEdges
end AFT.V7Calibration.physicalBlockEdges
namespace AFT.V7Calibration.physicalBlockIncidence
end AFT.V7Calibration.physicalBlockIncidence
namespace AFT.V7Calibration.physicalBlockIncidence.match_1
end AFT.V7Calibration.physicalBlockIncidence.match_1
namespace AFT.V7Calibration.physicalBlockRoot
end AFT.V7Calibration.physicalBlockRoot
namespace AFT.V7Calibration.physicalChartLinear
end AFT.V7Calibration.physicalChartLinear
namespace AFT.V7Calibration.physicalEdgeCoordinates
end AFT.V7Calibration.physicalEdgeCoordinates
namespace AFT.V7Calibration.physicalEdgePairEquiv
end AFT.V7Calibration.physicalEdgePairEquiv
namespace AFT.V7Calibration.physicalVertexSlotEquiv
end AFT.V7Calibration.physicalVertexSlotEquiv
namespace AFT.integerCoordinateMatrix
end AFT.integerCoordinateMatrix
namespace AFT.reduceIntegerLinearEquiv
end AFT.reduceIntegerLinearEquiv



/-! # Materializing the final affine output from integer vertex loads

The output consists of a matrix (stored by columns) and an offset.  The
first coordinate is the charge coordinate, followed by the path edges.
Padding is folded into the offset before the vertex permutation.
-/
namespace AFT
open scoped BigOperators

structure IntegerAffineData (count : ℕ) where
  columns : Vector (Vector ℤ count × ℤ) (count+1)
  offset : Vector ℤ count × ℤ
  work : ℕ



 



 

 

 

 

noncomputable section
set_option backward.isDefEq.respectTransparency false



end
end AFT

end

section






















/-! The emitted affine matrix and offset are arrays of signed Boolean lists.
All column permutation, padding products, coordinate inversion and array
materialization are charged to the bit algorithm. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 

 

 def binaryAffineColumn (count : ℕ) (modulus : List Bool)
     (injection : Vector IntegerBits (count+1))
     (matrix : Vector (Vector IntegerBits (count+1)) (count+1))
     (permutation : Vector (Fin (count+1)) (count+1)) (column : Fin (count+1)) :
     CountedValue (Vector IntegerBits count × IntegerBits) :=
   let load := binaryPermutedColumn count matrix permutation column
   let result := binaryRoundingInverse count modulus injection load.value
   ⟨(result.edges,result.charge),load.work+result.work+2⟩

 structure BinaryAffineData (count : ℕ) where
   columns : Vector (Vector IntegerBits count × IntegerBits) (count+1)
   offset : Vector IntegerBits count × IntegerBits
   work : ℕ

 

 

 

 

 

end AFT.BinaryArithmetic

end

section
















/-! # Cached rational scalar windows and an actual counted fair-bit draw -/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

structure CountedGaussianWeights (size : ℕ) where
  value : Vector ℚ size
  work : ℕ









structure CountedGaussianInteger where
  value : ℤ
  work : ℕ





noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000







end
end AFT.RationalNumerics

end

section




















/-! # Counted cached queries for the actual unshifted Gaussian windows

Every raw weight and the normalization sum are materialized once. Ticket
rounding stores its complete floor table before computing the deficit.
-/
namespace AFT.RationalNumerics
open GaussianSource FiniteConvolutionProgram
open scoped BigOperators

/-- This uses precisely `windowApproxPrecision`, including its guard bits. -/
def countedWindowWeights (squaredWidth : ℚ) (cutoff bits : ℕ) :
    CountedGaussianWeights (2*cutoff+1) :=
  let raw := Vector.ofFn (fun i : Fin (2*cutoff+1) =>
    GaussianArithmetic.gaussian squaredWidth (windowIndexEquiv cutoff i) (windowApproxPrecision cutoff bits))
  let normalizer := ∑ i,(raw.get i).value
  ⟨Vector.ofFn (fun i => (raw.get i).value/normalizer),
    (∑ i,(raw.get i).work)+2*(2*cutoff+1)⟩

theorem countedWindowWeights_value (squaredWidth : ℚ) (cutoff bits : ℕ) (i : Fin (2*cutoff+1)) :
    (countedWindowWeights squaredWidth cutoff bits).value.get i=windowGaussianWeights squaredWidth cutoff bits i := by
  simp only [countedWindowWeights,Vector.get_ofFn,GaussianArithmetic.gaussian_value,
    windowGaussianWeights,windowApproxWeight]
  congr 1

structure CountedWindowTickets (size : ℕ) where
  value : Vector ℕ size
  work : ℕ

def countedWindowTickets (squaredWidth : ℚ) (cutoff bits : ℕ) : CountedWindowTickets (2*cutoff+1) :=
  let weights := countedWindowWeights squaredWidth cutoff (bits+1)
  let tickets := PermutationProgram.powerTwo (windowTicketBits cutoff bits)
  let floors := Vector.ofFn (fun i : Fin (2*cutoff+1) => ⌊(tickets.value : ℚ)*weights.value.get i⌋₊)
  let total := ∑ i,floors.get i
  let deficit := tickets.value-total
  ⟨Vector.ofFn (fun i => floors.get i+if i=0 then deficit else 0),
    weights.work+tickets.work+5*(2*cutoff+1)+1⟩

theorem countedWindowTickets_value (squaredWidth : ℚ) (cutoff bits : ℕ) (i : Fin (2*cutoff+1)) :
    (countedWindowTickets squaredWidth cutoff bits).value.get i=windowTicketCounts squaredWidth cutoff bits i := by
  simp only [countedWindowTickets,Vector.get_ofFn,countedWindowWeights_value,PermutationProgram.powerTwo_value]
  rfl

def countedWindowTicketWeight (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) : GaussianArithmetic :=
  let counts := countedWindowTickets squaredWidth cutoff bits
  let denominator := GaussianArithmetic.power 2 (windowTicketBits cutoff bits)
  ⟨(counts.value.get ((windowIndexEquiv cutoff).symm point) : ℚ)/denominator.value,
    counts.work+denominator.work+2⟩

theorem countedWindowTicketWeight_value (squaredWidth : ℚ) (cutoff bits : ℕ) (point : Window cutoff) :
    (countedWindowTicketWeight squaredWidth cutoff bits point).value=
      V7Calibration.windowTicketWeightProgram squaredWidth cutoff bits point := by
  simp only [countedWindowTicketWeight,countedWindowTickets_value,GaussianArithmetic.power_value]
  rfl



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000







end
end AFT.RationalNumerics

end

section













































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActivationApprox
end AFT.V7Calibration.actualActivationApprox
namespace AFT.V7Calibration.actualActivationInverseApprox
end AFT.V7Calibration.actualActivationInverseApprox
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualAnchorWidthProgram
end AFT.V7Calibration.actualAnchorWidthProgram
namespace AFT.V7Calibration.actualAuxiliarySquaredWidth
end AFT.V7Calibration.actualAuxiliarySquaredWidth
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBasePrimaryProgramHeight
end AFT.V7Calibration.actualBasePrimaryProgramHeight
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodyMeanProgramHeight
end AFT.V7Calibration.actualBodyMeanProgramHeight
namespace AFT.V7Calibration.actualBoundaryCoefficientProgramHeight
end AFT.V7Calibration.actualBoundaryCoefficientProgramHeight
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFairSliceProgramHeight
end AFT.V7Calibration.actualFairSliceProgramHeight
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualLegPopulationProgram
end AFT.V7Calibration.actualLegPopulationProgram
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualNormalizedSignProgramHeight
end AFT.V7Calibration.actualNormalizedSignProgramHeight
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPrimaryProgramHeight
end AFT.V7Calibration.actualPrimaryProgramHeight
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualRankInverseProgramHeight
end AFT.V7Calibration.actualRankInverseProgramHeight
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeMarginProgram
end AFT.V7Calibration.actualSafeMarginProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! # Actual root-marginal queries with cached ticket and convolution arrays -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- The scalar table is evaluated once before either dynamic program. -/
def countedRootTicketMarginal (n count : ℕ) (point : Window (3*n^2-1)) : GaussianArithmetic :=
  let tickets := countedWindowTickets (actualRootSquaredWidth n) (3*n^2-1) n
  let scalarDen := GaussianArithmetic.power 2 (actualRootTicketBits n n)
  let remaining := run (2*(3*n^2-1)) tickets.value.get (count-1)
  let full := run (2*(3*n^2-1)) tickets.value.get count
  let remainingDen := GaussianArithmetic.power 2 (actualRootTicketBits n n*(count-1))
  let fullDen := GaussianArithmetic.power 2 (actualRootTicketBits n n*count)
  let scalar := (tickets.value.get ((windowIndexEquiv _).symm point) : ℚ)/scalarDen.value
  let remainProbability := ((integerLookup remaining.data ((3*n^2-1)*(count-1)) (-(point : ℤ)) : ℕ) : ℚ)/remainingDen.value
  let fullProbability := ((integerLookup full.data ((3*n^2-1)*count) 0 : ℕ) : ℚ)/fullDen.value
  ⟨scalar*remainProbability/fullProbability,
    tickets.work+scalarDen.work+remaining.work+full.work+remainingDen.work+fullDen.work+20⟩

theorem countedRootTicketMarginal_value (n count : ℕ) (point : Window (3*n^2-1)) :
    (countedRootTicketMarginal n count point).value=actualRootTicketMarginal n count point := by
  have he : (countedWindowTickets (actualRootSquaredWidth n) (3*n^2-1) n).value.get=
      actualRootTicketCounts n n := by
    funext index
    rw [countedWindowTickets_value]
    rfl
  simp only [countedRootTicketMarginal,he,GaussianArithmetic.power_value,
    actualRootTicketMarginal,actualRootTicketProbability,actualRootTicketConvolution,actualRootIntegerConvolution]



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000





end
end AFT.V7Calibration

end

section


















/-! # Actual finite cutoff and activation evaluators with operation counts -/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- The fixed eighth and ninth powers use bounded repeated multiplication;
the integer comparison table is evaluated once. -/
def countedLegCutoff (constant n : ℕ) : BetaReference.CountedNatural :=
  let threshold := (BetaReference.CountedInteger.power (constant : ℤ) 8).value*
    (BetaReference.CountedInteger.power (n : ℤ) 9).value
  let accepted := (Finset.range (constant*n^2+1)).filter (fun index : ℕ =>
    (BetaReference.CountedInteger.power (index : ℤ) 8).value<threshold)
  ⟨accepted.card,12*(constant*n^2+1)+25⟩

theorem countedLegCutoff_value (constant n : ℕ) :
    (countedLegCutoff constant n).value=actualLegCutoffProgram constant n := by
  simp only [countedLegCutoff,BetaReference.CountedInteger.power_value]
  have he (index : ℕ) : (index : ℤ)^8<(constant : ℤ)^8*(n : ℤ)^9 ↔ index^8<constant^8*n^9 := by
    exact_mod_cast (Iff.rfl : index^8<constant^8*n^9 ↔ index^8<constant^8*n^9)
  simp only [he]
  rfl











noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000







end
end AFT.V7Calibration

end

section


















/-! # Materialized actual scalar source tables for primary calibration

The public modulus, population ratios and three scalar probability arrays
are prepared before any body or pair expectation is evaluated.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

structure PrimarySourceTable (constant n : ℕ) where
  modulus : ℕ
  population : ℕ
  dimension : ℕ
  legs : ℕ
  margin : ℕ
  width : ℕ
  boundary : ℤ
  legRate : ℚ
  queueRate : ℚ
  root : Vector ℚ (2*(3*n^2-1)+1)
  leg : Vector ℚ (2*(actualLegCutoffProgram constant n-1)+1)
  queue : Vector ℚ (2*(n^2-1)+1)
  work : ℕ

def countedPrimarySources (constant n : ℕ) : PrimarySourceTable constant n :=
  let modulus := ParameterProgram.modulus n
  let cutoff := countedLegCutoff constant n
  let legs := (max 2 n)^30
  let dimension := modulus.value*(max 2 n)^20
  let population := dimension-2*legs
  let root := Vector.ofFn (fun index : Fin (2*(3*n^2-1)+1) =>
    countedRootTicketMarginal n population (windowIndexEquiv _ index))
  let leg := Vector.ofFn (fun index : Fin (2*(actualLegCutoffProgram constant n-1)+1) =>
    countedWindowTicketWeight (actualAuxiliarySquaredWidth 10 n)
      (actualLegCutoffProgram constant n-1) n (windowIndexEquiv _ index))
  let queue := Vector.ofFn (fun index : Fin (2*(n^2-1)+1) =>
    countedWindowTicketWeight (actualAuxiliarySquaredWidth 1 n) (n^2-1) n (windowIndexEquiv _ index))
  ⟨modulus.value,population,dimension,legs,20*(max 2 n)^2,(max 2 n)^32,
    (20*(max 2 n)^2 : ℕ)-((3*n^2-1)+(cutoff.value-1)+(n^2-1) : ℕ),
    (legs : ℚ)/population,(modulus.value : ℚ)/population,
    Vector.ofFn (fun i => (root.get i).value),Vector.ofFn (fun i => (leg.get i).value),
    Vector.ofFn (fun i => (queue.get i).value),
    modulus.work+2*cutoff.work+(∑ i,(root.get i).work)+(∑ i,(leg.get i).work)+(∑ i,(queue.get i).work)+1000⟩









@[simp] theorem countedPrimarySources_modulus (constant n : ℕ) :
    (countedPrimarySources constant n).modulus=(ParameterProgram.modulus n).value := rfl
@[simp] theorem countedPrimarySources_population (constant n : ℕ) :
    (countedPrimarySources constant n).population=actualRootPopulationProgram n := rfl
@[simp] theorem countedPrimarySources_dimension (constant n : ℕ) :
    (countedPrimarySources constant n).dimension=actualDimensionProgram n := rfl
@[simp] theorem countedPrimarySources_legs (constant n : ℕ) :
    (countedPrimarySources constant n).legs=actualLegPopulationProgram n := rfl
@[simp] theorem countedPrimarySources_margin (constant n : ℕ) :
    (countedPrimarySources constant n).margin=actualSafeMarginProgram n := rfl
@[simp] theorem countedPrimarySources_width (constant n : ℕ) :
    (countedPrimarySources constant n).width=actualAnchorWidthProgram n := rfl
@[simp] theorem countedPrimarySources_boundary (constant n : ℕ) :
    (countedPrimarySources constant n).boundary=actualBoundaryHalfProgram constant n := by
  simp only [countedPrimarySources,countedLegCutoff_value,actualBoundaryHalfProgram,actualSafeMarginProgram]
@[simp] theorem countedPrimarySources_root (constant n : ℕ) (point : Window (3*n^2-1)) :
    (countedPrimarySources constant n).root.get ((windowIndexEquiv _).symm point)=actualRootMarginalProgram n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedRootTicketMarginal_value,Equiv.apply_symm_apply]
  rfl
@[simp] theorem countedPrimarySources_leg (constant n : ℕ) (point : Window (actualLegCutoffProgram constant n-1)) :
    (countedPrimarySources constant n).leg.get ((windowIndexEquiv _).symm point)=
      windowTicketWeightProgram (actualAuxiliarySquaredWidth 10 n) (actualLegCutoffProgram constant n-1) n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedWindowTicketWeight_value,Equiv.apply_symm_apply]
@[simp] theorem countedPrimarySources_queue (constant n : ℕ) (point : Window (n^2-1)) :
    (countedPrimarySources constant n).queue.get ((windowIndexEquiv _).symm point)=
      windowTicketWeightProgram (actualAuxiliarySquaredWidth 1 n) (n^2-1) n point := by
  simp only [countedPrimarySources,Vector.get_ofFn,countedWindowTicketWeight_value,Equiv.apply_symm_apply]







noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000



end
end AFT.V7Calibration

end

section


















/-! # A counted evaluator for the actual calibrated primary probability

Scalar tables are cached before the complete shared-source expectations.
The integer slice length is evaluated by its proved closed formula, so a
slice query needs no enumeration of its entire color interval.
-/
namespace AFT.V7Calibration
open GaussianSource RationalNumerics FiniteConvolutionProgram
open scoped BigOperators

/-- Two integer comparisons and the reciprocal of the integer width. -/
def countedIntervalProbability (start : ℤ) (width : ℕ) (point : ℤ) : GaussianArithmetic :=
  ⟨if start≤point ∧ point<start+width then (width : ℚ)⁻¹ else 0,5⟩

/-- Both endpoint tests and the exact nonnegative interval length. -/
def countedSliceProbability (modulus boundary shift color : ℤ) : GaussianArithmetic :=
  ⟨if boundary+max shift 0≤color ∧ color < modulus-boundary+min shift 0
    then ((modulus-2*boundary-|shift|).toNat : ℚ)⁻¹ else 0,12⟩

theorem countedIntervalProbability_value (start : ℤ) (width : ℕ) (point : ℤ) :
    (countedIntervalProbability start width point).value=intervalProbabilityProgram start width point := by
  simp only [countedIntervalProbability,intervalProbabilityProgram,anchorInterval,Finset.mem_Ico]

theorem countedSliceProbability_value (modulus boundary shift color : ℤ) :
    (countedSliceProbability modulus boundary shift color).value=sliceProbabilityProgram modulus boundary shift color := by
  rfl

































noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000











end
end AFT.V7Calibration

end

section






















/-! Interval probabilities on signed binary endpoints. Comparisons,
endpoint addition, reciprocal, and zero branch are fully executable. -/
namespace AFT.BinaryArithmetic
open RationalNumerics V7Calibration RationalBits

/-- Uniform mass on [start,start+width). -/
def binaryIntervalProbability (startSign colorSign : Bool) (start width color : List Bool) : RationalResult :=
  let upper := signedAdd startSign false start width
  let lowerTest := signedLe startSign colorSign start color
  let upperTest := signedLe upper.negative colorSign upper.digits color
  if lowerTest.value && !upperTest.value then
    let denominator := RationalBits.ofNat width
    let result := RationalBits.inverse denominator.data
    ⟨result.data,upper.work+lowerTest.work+upperTest.work+denominator.work+result.work+6⟩
  else ⟨RationalBits.zero,upper.work+lowerTest.work+upperTest.work+3⟩

theorem binaryIntervalProbability_value (startSign colorSign : Bool) (start width color : List Bool) :
    (binaryIntervalProbability startSign colorSign start width color).data.decode=
      intervalProbabilityProgram (signedValue startSign start) (value width) (signedValue colorSign color) := by
  have upperValue := signedAdd_value startSign false start width
  have hc : ((signedLe startSign colorSign start color).value &&
      !(signedLe (signedAdd startSign false start width).negative colorSign
        (signedAdd startSign false start width).digits color).value)=true ↔
      signedValue startSign start≤ signedValue colorSign color ∧
      signedValue colorSign color<signedValue startSign start+(value width : ℤ) := by
    simp only [Bool.and_eq_true,Bool.not_eq_true']
    rw [signedLe_value,←Bool.not_eq_true,signedLe_value,not_le,upperValue]
    rfl
  rw [←countedIntervalProbability_value]
  by_cases h : ((signedLe startSign colorSign start color).value &&
      !(signedLe (signedAdd startSign false start width).negative colorSign
        (signedAdd startSign false start width).digits color).value)=true
  · simp only [countedIntervalProbability,binaryIntervalProbability,if_pos h,
      if_pos (hc.mp h),RationalBits.inverse_value,RationalBits.ofNat_value]
  · simp only [countedIntervalProbability,binaryIntervalProbability,if_neg h,
      if_neg (mt hc.mpr h),RationalBits.zero_value]

def binaryIntervalProbabilityWork (bits : ℕ) : ℕ :=
  200*(bits+2)+RationalBits.primitiveWorkBound bits





end AFT.BinaryArithmetic

end

section


















/-! Trimmed-slice probabilities from actual signed binary endpoints. The
interval width is computed by signed subtraction, never encoded from a
precomputed rational probability. -/
namespace AFT.BinaryArithmetic
open RationalNumerics V7Calibration RationalBits

/-- Clip a signed integer to its nonnegative part. -/
def nonnegativeDigits (sign : Bool) (digits : List Bool) : List Bool :=
  if sign then [] else digits

theorem nonnegativeDigits_value (sign : Bool) (digits : List Bool) :
    value (nonnegativeDigits sign digits)=(signedValue sign digits).toNat := by
  cases sign <;> simp [nonnegativeDigits,signedValue,value]



/-- Probability on a signed half-open interval, including an empty one. -/
def binaryEndpointProbability (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) : RationalResult :=
  let difference := signedAdd upperSign (!lowerSign) upper lower
  let width := nonnegativeDigits difference.negative difference.digits
  let result := binaryIntervalProbability lowerSign colorSign lower width color
  ⟨result.data,difference.work+result.work+3⟩

theorem binaryEndpointProbability_value (lowerSign upperSign colorSign : Bool)
    (lower upper color : List Bool) :
    (binaryEndpointProbability lowerSign upperSign colorSign lower upper color).data.decode=
      (if signedValue lowerSign lower≤ signedValue colorSign color ∧
        signedValue colorSign color<signedValue upperSign upper
       then (((signedValue upperSign upper-signedValue lowerSign lower).toNat : ℕ) : ℚ)⁻¹ else 0) := by
  have hneg : signedValue (!lowerSign) lower= -signedValue lowerSign lower := by
    cases lowerSign <;> simp [signedValue]
  have hv := signedAdd_value upperSign (!lowerSign) upper lower
  rw [hneg,←sub_eq_add_neg] at hv
  simp only [binaryEndpointProbability,binaryIntervalProbability_value,nonnegativeDigits_value,hv]
  rw [←countedIntervalProbability_value]
  simp only [countedIntervalProbability]
  have he : (signedValue lowerSign lower≤ signedValue colorSign color ∧
      signedValue colorSign color<signedValue lowerSign lower+
        ((signedValue upperSign upper-signedValue lowerSign lower).toNat : ℤ)) ↔
      (signedValue lowerSign lower≤ signedValue colorSign color ∧
        signedValue colorSign color<signedValue upperSign upper) := by omega
  simp only [he]

def binaryEndpointProbabilityWork (bits : ℕ) : ℕ :=
  20*bits+11+binaryIntervalProbabilityWork (bits+1)





structure SliceEndpoints where
  lower : SignedResult
  upper : SignedResult
  work : ℕ

/-- Both shifts are built by signed arithmetic on the supplied operands. -/
def binarySliceEndpoints (modulusSign boundarySign shiftSign : Bool)
    (modulus boundary shift : List Bool) : SliceEndpoints :=
  let difference := signedAdd modulusSign (!boundarySign) modulus boundary
  let lower := signedAdd boundarySign false boundary (if shiftSign then [] else shift)
  let upper := signedAdd difference.negative true difference.digits (if shiftSign then shift else [])
  ⟨lower,upper,difference.work+lower.work+upper.work+4⟩

theorem binarySliceEndpoints_values (modulusSign boundarySign shiftSign : Bool)
    (modulus boundary shift : List Bool) :
    let result := binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift
    signedValue result.lower.negative result.lower.digits=
      signedValue boundarySign boundary+max (signedValue shiftSign shift) 0 ∧
    signedValue result.upper.negative result.upper.digits=
      signedValue modulusSign modulus-signedValue boundarySign boundary+min (signedValue shiftSign shift) 0 := by
  have hneg : signedValue (!boundarySign) boundary= -signedValue boundarySign boundary := by
    cases boundarySign <;> simp [signedValue]
  simp only [binarySliceEndpoints,signedAdd_value,hneg]
  cases shiftSign <;> simp [signedValue,sub_eq_add_neg] <;> rfl


def binarySliceProbability (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) : RationalResult :=
  let endpoints := binarySliceEndpoints modulusSign boundarySign shiftSign modulus boundary shift
  let result := binaryEndpointProbability endpoints.lower.negative endpoints.upper.negative colorSign
    endpoints.lower.digits endpoints.upper.digits color
  ⟨result.data,endpoints.work+result.work+2⟩

theorem binarySliceProbability_value (modulusSign boundarySign shiftSign colorSign : Bool)
    (modulus boundary shift color : List Bool) :
    (binarySliceProbability modulusSign boundarySign shiftSign colorSign modulus boundary shift color).data.decode=
      sliceProbabilityProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
        (signedValue shiftSign shift) (signedValue colorSign color) := by
  have he := binarySliceEndpoints_values modulusSign boundarySign shiftSign modulus boundary shift
  simp only [binarySliceProbability,binaryEndpointProbability_value,he.1,he.2]
  rw [←countedSliceProbability_value]
  simp only [countedSliceProbability]
  have heq : signedValue modulusSign modulus-signedValue boundarySign boundary+
      min (signedValue shiftSign shift) 0-
        (signedValue boundarySign boundary+max (signedValue shiftSign shift) 0)=
      signedValue modulusSign modulus-2*signedValue boundarySign boundary-|signedValue shiftSign shift| := by
    rcases le_total (signedValue shiftSign shift) 0 with hs | hs
    · rw [min_eq_left hs,max_eq_right hs,abs_of_nonpos hs];ring
    · rw [min_eq_right hs,max_eq_left hs,abs_of_nonneg hs];ring
  rw [heq]

def binarySliceProbabilityWork (bits : ℕ) : ℕ :=
  100*(bits+2)+binaryEndpointProbabilityWork (bits+2)







end AFT.BinaryArithmetic

end

section































































namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.CanonicalMoments.twoPoolStatistic
end AFT.CanonicalMoments.twoPoolStatistic
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.chargeWordLaw
end AFT.FiniteDist.chargeWordLaw
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.matrixApply
end AFT.MixedKernel.matrixApply
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.controlPoolEquiv
end AFT.RepresentedPolynomial.controlPoolEquiv
namespace AFT.RepresentedPolynomial.controlProductRole
end AFT.RepresentedPolynomial.controlProductRole
namespace AFT.RepresentedPolynomial.controlProductRole.match_1
end AFT.RepresentedPolynomial.controlProductRole.match_1
namespace AFT.RepresentedPolynomial.finiteControlRole
end AFT.RepresentedPolynomial.finiteControlRole
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.monomialInputStatistic
end AFT.RepresentedPolynomial.monomialInputStatistic
namespace AFT.RepresentedPolynomial.monomialPairedStatistic
end AFT.RepresentedPolynomial.monomialPairedStatistic
namespace AFT.RepresentedPolynomial.monomialPlacementCount
end AFT.RepresentedPolynomial.monomialPlacementCount
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.tableBodyScope
end AFT.RepresentedPolynomial.tableBodyScope
namespace AFT.RepresentedPolynomial.tableLocalBound
end AFT.RepresentedPolynomial.tableLocalBound
namespace AFT.RepresentedPolynomial.tableLocalTerm
end AFT.RepresentedPolynomial.tableLocalTerm
namespace AFT.RepresentedPolynomial.tablePairedBodyScope
end AFT.RepresentedPolynomial.tablePairedBodyScope
namespace AFT.RepresentedPolynomial.tablePairedEnvelope
end AFT.RepresentedPolynomial.tablePairedEnvelope
namespace AFT.RepresentedPolynomial.tablePairedLocalTerm
end AFT.RepresentedPolynomial.tablePairedLocalTerm
namespace AFT.RepresentedPolynomial.twoPoolPairedKernel
end AFT.RepresentedPolynomial.twoPoolPairedKernel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.bodyPublicMatrix
end AFT.bodyPublicMatrix
namespace AFT.pairedPublicDensity
end AFT.pairedPublicDensity
namespace AFT.pairedPublicKernel
end AFT.pairedPublicKernel
namespace AFT.pairedPublicMatrix
end AFT.pairedPublicMatrix
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.publicInputMatrix
end AFT.publicInputMatrix




/-! # Executable positive normalization on any nonempty finite palette -/
namespace AFT.RationalPaletteSampler
open scoped BigOperators

/-- The match removes only the impossible empty-palette branch. The
nonempty program is the checked rational positive normalization sampler. -/
def draw : (colors : ℕ) → (hcolors : 0<colors) → (raw : Fin colors → ℚ) → (bits : ℕ) →
    (Fin (bits+colors+1) → Fin 2) → Fin colors
  | 0,h,_,_,_ => False.elim (Nat.not_lt_zero 0 h)
  | _colors+1,_,raw,bits,word => RationalNumerics.positiveNormalizeDraw raw bits word







noncomputable section
open FiniteDist
open scoped Classical
set_option backward.isDefEq.respectTransparency false







end
end AFT.RationalPaletteSampler

end

section
















































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActivationApprox
end AFT.V7Calibration.actualActivationApprox
namespace AFT.V7Calibration.actualActivationInverseApprox
end AFT.V7Calibration.actualActivationInverseApprox
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualAnchorWidthProgram
end AFT.V7Calibration.actualAnchorWidthProgram
namespace AFT.V7Calibration.actualAuxiliarySquaredWidth
end AFT.V7Calibration.actualAuxiliarySquaredWidth
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodySampleDraw
end AFT.V7Calibration.actualBodySampleDraw
namespace AFT.V7Calibration.actualBodySamplePhysicalEquiv
end AFT.V7Calibration.actualBodySamplePhysicalEquiv
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualNormalizedSignProgramHeight
end AFT.V7Calibration.actualNormalizedSignProgramHeight
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPublicBaselineProgram
end AFT.V7Calibration.actualPublicBaselineProgram
namespace AFT.V7Calibration.actualPublicOffsetDraw
end AFT.V7Calibration.actualPublicOffsetDraw
namespace AFT.V7Calibration.actualPublicOffsetEquiv
end AFT.V7Calibration.actualPublicOffsetEquiv
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualRankInverseProgramHeight
end AFT.V7Calibration.actualRankInverseProgramHeight
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeMarginProgram
end AFT.V7Calibration.actualSafeMarginProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorIndexEquiv
end AFT.V7Calibration.anchorIndexEquiv
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.bodyShiftIntegerProgram
end AFT.V7Calibration.bodyShiftIntegerProgram
namespace AFT.V7Calibration.conditionalBaselineStart
end AFT.V7Calibration.conditionalBaselineStart
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! Actual averaging over the finite anchor interval, with explicit counter
indices and signed binary slice arithmetic. -/
namespace AFT.BinaryArithmetic
open V7Calibration RationalNumerics RationalBits
open scoped BigOperators

 def binaryAnchorSliceTerm (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) : RationalResult :=
  let offset := canonicalCounter index.val
  let center := signedAdd startSign false start offset.digits
  let shifted := signedAdd center.negative (!sourceSign) center.digits source
  let probability := binarySliceProbability modulusSign boundarySign shifted.negative colorSign
    modulus boundary shifted.digits color
  let widthBits := RationalBits.ofCounter width
  let inverse := RationalBits.inverse widthBits.data
  let result := RationalBits.multiply inverse.data probability.data
  ⟨result.data,offset.work+center.work+shifted.work+probability.work+widthBits.work+inverse.work+result.work+8⟩

 theorem binaryAnchorSliceTerm_value (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) (index : Fin width) :
    (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width index).data.decode=
    (width : ℚ)⁻¹*sliceProbabilityProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
      (signedValue startSign start+index.val-signedValue sourceSign source) (signedValue colorSign color) := by
  have hneg : signedValue (!sourceSign) source= -signedValue sourceSign source := by cases sourceSign <;> simp [signedValue]
  simp only [binaryAnchorSliceTerm,RationalBits.multiply_value,RationalBits.inverse_value,RationalBits.ofCounter_value,
    binarySliceProbability_value]
  rw [signedAdd_value,signedAdd_value,hneg]
  simp only [signedValue,Bool.false_eq_true,ite_false,canonicalCounter_value,sub_eq_add_neg]

 def binaryAveragedSlice (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) : RationalResult :=
  sumFin width (binaryAnchorSliceTerm modulusSign boundarySign startSign sourceSign colorSign
    modulus boundary start source color width)

 theorem averagedSliceProgram_indexed (modulus boundary start source : ℤ) (width : ℕ) (color : ℤ) :
    averagedSliceProgram modulus boundary start source width color=
      ∑ index : Fin width,(width : ℚ)⁻¹*sliceProbabilityProgram modulus boundary (start+index.val-source) color := by
  unfold averagedSliceProgram
  apply Finset.sum_congr rfl
  intro index _
  have hi : start ≤ start+index.val ∧ start+index.val < start+width := by
    have hindex := index.isLt
    omega
  simp only [intervalProbabilityProgram,if_pos hi]

 theorem binaryAveragedSlice_value (modulusSign boundarySign startSign sourceSign colorSign : Bool)
    (modulus boundary start source color : List Bool) (width : ℕ) :
    (binaryAveragedSlice modulusSign boundarySign startSign sourceSign colorSign
      modulus boundary start source color width).data.decode=
      averagedSliceProgram (signedValue modulusSign modulus) (signedValue boundarySign boundary)
        (signedValue startSign start) (signedValue sourceSign source) width (signedValue colorSign color) := by
  simp only [binaryAveragedSlice,sumFin_value,binaryAnchorSliceTerm_value,averagedSliceProgram_indexed]

 def binaryAnchorSliceTermWork (bits : ℕ) : ℕ :=
  110*(bits+1)^2+40*(bits+1)+16+binarySliceProbabilityWork (bits+2)+
    RationalBits.primitiveWorkBound bits+RationalBits.primitiveWorkBound (2*bits+6)+8

 

 

 def binaryAveragedSliceWork (bits : ℕ) : ℕ :=
  bits*(binaryAnchorSliceTermWork bits+RationalBits.primitiveWorkBound ((bits+1)*(2*bits+7))+2)+2

 

 

end AFT.BinaryArithmetic

end

section







/-! # Binary accumulation and bucket selection

Tickets and table counts remain binary throughout, including subtraction
on a rejected bucket. Only the polynomially bounded output index is unary.
-/
namespace AFT.BinaryArithmetic
open BetaReference

def binaryBucket : List (List Bool) → List Bool → CountedNatural
  | [],_ => ⟨0,2⟩
  | head::tail,ticket =>
      let comparison := subtract false ticket head
      if comparison.borrow then ⟨0,comparison.work+3⟩ else
        let next := binaryBucket tail comparison.digits
        ⟨next.value.succ,comparison.work+next.work+3⟩

theorem binaryBucket_value (counts : List (List Bool)) (ticket : List Bool) :
    (binaryBucket counts ticket).value=FiniteTicketSampler.bucket (counts.map value) (value ticket) := by
  induction counts generalizing ticket with
  | nil => rfl
  | cons head tail ih =>
      have hb := subtract_borrow ticket head
      simp only [binaryBucket,List.map_cons,FiniteTicketSampler.bucket]
      split <;> rename_i hc
      · rw [if_pos (hb.mp hc)]
      · have hh : value head≤ value ticket := Nat.le_of_not_gt (fun hl => hc (hb.mpr hl))
        rw [if_neg (by omega),ih,subtract_value ticket head hh]
        dsimp only
        omega



def sumDigits : List (List Bool) → Result
  | [] => ⟨[],2⟩
  | head::tail =>
      let previous := sumDigits tail
      let next := add false head previous.digits
      ⟨next.digits,previous.work+next.work+2⟩

theorem sumDigits_value (counts : List (List Bool)) : value (sumDigits counts).digits=(counts.map value).sum := by
  induction counts with
  | nil => rfl
  | cons head tail ih => simp only [sumDigits,add_value,ih,Bool.toNat_false,Nat.add_zero,List.map_cons,List.sum_cons]



def sumDigitsWork (count bits : ℕ) : ℕ := count*(10*(count+1)*(bits+1)+4)+2



end AFT.BinaryArithmetic

end

section









/-! # Actual binary ticket-table preparation

Each weight is rounded once. The remaining tickets are computed by actual
binary subtraction and added to the first table entry, exactly as in the
support-preserving rational quantization program.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

structure DigitTableResult where
  data : List (List Bool)
  work : ℕ

def floorTable (weights : List RationalBits) (bits : ℕ) : DigitTableResult :=
  match weights with
  | [] => ⟨[],2⟩
  | head::tail =>
      let current := head.dyadicFloor bits
      let rest := floorTable tail bits
      ⟨current.digits::rest.data,current.work+rest.work+3⟩

theorem floorTable_value (weights : List RationalBits) (bits : ℕ) :
    (floorTable weights bits).data.map value=weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊) := by
  induction weights with
  | nil => rfl
  | cons head tail ih => simp only [floorTable,List.map_cons,RationalBits.dyadicFloor_value,ih]







def supplementFirst (extra : ℕ) : List ℕ → List ℕ
  | [] => []
  | head::tail => (head+extra)::tail

def ticketTable (weights : List RationalBits) (bits : ℕ) : DigitTableResult :=
  let floored := floorTable weights bits
  let total := sumDigits floored.data
  let tickets := powerTwoDigits bits
  let deficit := subtract false tickets.digits total.digits
  match floored.data with
  | [] => ⟨[],floored.work+total.work+tickets.work+deficit.work+3⟩
  | head::tail =>
      let first := add false head deficit.digits
      ⟨first.digits::tail,floored.work+total.work+tickets.work+deficit.work+first.work+4⟩

theorem ticketTable_value (weights : List RationalBits) (bits : ℕ)
    (hbound : (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum≤ 2^bits) :
    (ticketTable weights bits).data.map value=
      supplementFirst (2^bits-(weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum)
        (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)) := by
  have ht := floorTable_value weights bits
  have hv : value (sumDigits (floorTable weights bits).data).digits=
      (weights.map (fun input => ⌊(2 : ℚ)^bits*input.decode⌋₊)).sum := by rw [sumDigits_value,ht]
  have hd := subtract_value (powerTwoDigits bits).digits (sumDigits (floorTable weights bits).data).digits
    (by rw [powerTwoDigits_value,hv];exact hbound)
  rw [powerTwoDigits_value,hv] at hd
  unfold ticketTable
  dsimp only
  split <;> rename_i he
  · rw [he] at ht
    simp only [List.map_nil] at ht
    rw [← ht]
    rfl
  · rw [he] at ht
    rw [← ht]
    simp only [List.map_cons,supplementFirst,add_value,Bool.toNat_false,Nat.add_zero]
    congr 2
    simpa only [← ht, List.map_cons] using hd



def ticketTableDigitBound (count height bits : ℕ) : ℕ := (count+1)*(bits+height+2)+1



def ticketTableWork (count height bits : ℕ) : ℕ :=
  count*(RationalBits.dyadicFloorWork height bits+3)+sumDigitsWork count (bits+height+1)+
    2*bits+20*ticketTableDigitBound count height bits+20



end AFT.BinaryArithmetic

end

section






















/-! # Finite rational sampling by actual binary operations

The stored probability array is rounded once, the leftover tickets are assigned
to its first entry, and bucket selection reads the supplied fair-bit tape.
Even an exponentially large ticket stays a list of bits throughout execution.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics BetaReference
open scoped BigOperators

 theorem supplementFirst_ofFn {count : ℕ} (weights : Fin (count+1) → ℕ) (extra : ℕ) :
    supplementFirst extra (List.ofFn weights)=
      List.ofFn (fun index => weights index+if index=0 then extra else 0) := by
  rw [List.ofFn_succ,List.ofFn_succ]
  simp only [supplementFirst,ite_true,Fin.succ_ne_zero,ite_false,Nat.add_zero]



/-- Array materialization, all binary arithmetic, and all tape reads are charged. -/
def binaryRationalDraw {count : ℕ} (weights : Vector RationalBits (count+1))
    (bits : ℕ) (word : Fin bits → Fin 2) : CountedNatural :=
  let table := ticketTable (List.ofFn weights.get) bits
  let ticket := readBitTape bits word
  let selected := binaryBucket table.data ticket.digits
  ⟨selected.value,table.work+ticket.work+selected.work+2*(count+1)+2⟩

theorem binaryRationalDraw_cast {count : ℕ} (weights : Vector RationalBits (count+1))
    (bits other : ℕ) (heq : bits=other) (word : Fin other → Fin 2) :
    binaryRationalDraw weights bits (fun index => word (Fin.cast heq index))=
      binaryRationalDraw weights other word := by
  subst other
  rfl

theorem binaryRationalDraw_value {count : ℕ} (weights : Vector RationalBits (count+1))
    (hnonneg : ∀ index,0≤ (weights.get index).decode)
    (hsum : ∑ index,(weights.get index).decode=1)
    (bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryRationalDraw weights bits word).value=
      (RationalFiniteQuantization.draw (fun index => (weights.get index).decode)
        hnonneg hsum bits word).val := by
  have hb := RationalFiniteQuantization.floorTotal_le (fun index => (weights.get index).decode)
    hnonneg hsum (2^bits)
  simp only [RationalFiniteQuantization.floorTotal,RationalFiniteQuantization.floorCount,
    Nat.cast_pow,Nat.cast_ofNat] at hb
  have ht := ticketTable_value (List.ofFn weights.get) bits (by
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hb)
  simp only [List.map_ofFn] at ht
  rw [supplementFirst_ofFn] at ht
  simp only [binaryRationalDraw,binaryBucket_value,readBitTape_value,ht,
    RationalFiniteQuantization.draw,FiniteTicketSampler.drawBitTable,FiniteTicketSampler.drawFin,
    Fin.val_cast,RationalFiniteQuantization.counts,RationalFiniteQuantization.floorCount,
    RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,
    List.sum_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext index
  simp only [RationalFiniteQuantization.counts,RationalFiniteQuantization.floorCount,
    RationalFiniteQuantization.deficit,RationalFiniteQuantization.floorTotal,
    Function.comp_apply,Nat.cast_pow,Nat.cast_ofNat]

def binaryRationalDrawWork (count height bits : ℕ) : ℕ :=
  ticketTableWork count height bits+3*bits+
    count*(10*ticketTableDigitBound count height bits+5)+2*count+6



end AFT.BinaryArithmetic

end

section


















/-! # Actual binary normalization of a stored finite rational array

The normalizer is accumulated once, then reused by every entry. Array reads
use the explicit sequential lookup program. No unbounded rational operation
or array lookup is charged as one step.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

def sumArray {count : ℕ} (input : Vector RationalBits count) : RationalResult :=
  sumFin count (fun index => let found := readVector zero input index;⟨found.value,found.work⟩)

theorem sumArray_value {count : ℕ} (input : Vector RationalBits count) :
    (sumArray input).data.decode=∑ index,(input.get index).decode := by
  simp only [sumArray,sumFin_value,readVector_value]



def sumArrayWork (count bits : ℕ) : ℕ :=
  count*(3*count+3+primitiveWorkBound ((count+1)*(bits+1))+2)+2



def normalizeArray {count : ℕ} (input : Vector RationalBits count) : ArrayResult count :=
  let total := sumArray input
  let output := buildArray count (fun index =>
    let numerator := readVector zero input index
    let result := quotient numerator.value total.data
    ⟨result.data,numerator.work+result.work+2⟩)
  ⟨output.data,total.work+output.work+2⟩

theorem normalizeArray_value {count : ℕ} (input : Vector RationalBits count) (index : Fin count) :
    ((normalizeArray input).data.get index).decode=
      (input.get index).decode/(∑ point,(input.get point).decode) := by
  simp only [normalizeArray,buildArray_get,quotient_value,readVector_value,sumArray_value]



def normalizeArrayWork (count bits : ℕ) : ℕ :=
  sumArrayWork count bits+count*(3*count+3+2*primitiveWorkBound (bits+count*(bits+1))+6)+4



end AFT.BinaryArithmetic.RationalBits

end

section



















namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics




/-! # Positive normalization with actual binary arithmetic

Clipping inspects the sign bit. The exceptional zero-normalizer branch tests
the canonical numerator's list constructor. Both branches materialize their
output, and every sequential array read and rational operation is charged.
-/
set_option maxRecDepth 2048

namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

theorem numerator_empty_iff (input : RationalBits) : input.numerator=[] ↔ input.decode=0 := by
  have hn := input.numerator_normal
  have hv : value input.numerator=0 ↔ input.decode=0 := by
    rw [← signedValue_natAbs input.negative input.numerator,Int.natAbs_eq_zero,← decode_num,Rat.num_eq_zero]
  constructor
  · intro hh
    apply hv.mp
    rw [hh]
    rfl
  · intro hh
    have hz := hv.mpr hh
    rw [hz] at hn
    exact List.length_eq_zero_iff.mp (by simpa using hn)

def positiveArray {count : ℕ} (input : Vector RationalBits count) : ArrayResult count :=
  buildArray count (fun index =>
    let found := readVector zero input index
    let result := maxZero found.value
    ⟨result.data,found.work+result.work+2⟩)

theorem positiveArray_value {count : ℕ} (input : Vector RationalBits count) (index : Fin count) :
    ((positiveArray input).data.get index).decode=max 0 (input.get index).decode := by
  simp only [positiveArray,buildArray_get,maxZero_value,readVector_value,max_comm]





def binaryPositiveNormalize {count : ℕ} (input : Vector RationalBits (count+1)) : ArrayResult (count+1) :=
  let clipped := positiveArray input
  let total := sumArray clipped.data
  let output := if total.data.numerator.isEmpty then
      buildArray (count+1) (fun index => ⟨if index.val=0 then one else zero,3⟩)
    else normalizeArray clipped.data
  ⟨output.data,clipped.work+total.work+output.work+4⟩

theorem binaryPositiveNormalize_value {count : ℕ} (input : Vector RationalBits (count+1))
    (index : Fin (count+1)) :
    ((binaryPositiveNormalize input).data.get index).decode=
      positiveWeightProgram (fun i => (input.get i).decode) index := by
  have ht : (sumArray (positiveArray input).data).data.decode=
      positiveNormalizerProgram (fun i => (input.get i).decode) := by
    simp only [sumArray_value,positiveArray_value,positiveNormalizerProgram,positivePartProgram]
  have hz : (sumArray (positiveArray input).data).data.numerator.isEmpty=true ↔
      positiveNormalizerProgram (fun i => (input.get i).decode)=0 := by
    rw [List.isEmpty_iff,numerator_empty_iff,ht]
  unfold binaryPositiveNormalize positiveWeightProgram
  dsimp only
  split <;> rename_i hc
  · rw [if_pos (hz.mp hc)]
    simp only [buildArray_get]
    by_cases hi : index=0
    · subst index
      simp only [Fin.val_zero,ite_true,one_value]
    · have hv : index.val≠0 := fun hh => hi (Fin.ext hh)
      simp only [hi,hv,ite_false,zero_value]
  · rw [if_neg (fun hh => hc (hz.mpr hh)),normalizeArray_value]
    simp only [positiveArray_value,positivePartProgram,positiveNormalizerProgram]



def binaryPositiveNormalizeWork (count height : ℕ) : ℕ :=
  count*(3*count+9)+sumArrayWork count height+normalizeArrayWork count height+5*count+10



end AFT.BinaryArithmetic.RationalBits

end

section






















/-! # Positive finite sampling, including guard-counter construction -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics BetaReference RationalBits
open scoped BigOperators

def binaryPositiveDraw {count : ℕ} (raw : Vector RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) : CountedNatural :=
  let normalized := binaryPositiveNormalize raw
  let guard := addCounter bits (count+1)
  let shiftedWord : Fin (guard.count+1) → Fin 2 :=
    fun index => word (Fin.cast (by rw [addCounter_value]) index)
  let selected := binaryRationalDraw normalized.data guard.count.succ shiftedWord
  ⟨selected.value,normalized.work+guard.work+selected.work+3⟩

theorem binaryPositiveDraw_value {count : ℕ} (raw : Vector RationalBits (count+1)) (bits : ℕ)
    (word : Fin (bits+(count+1)+1) → Fin 2) :
    (binaryPositiveDraw raw bits word).value=
      (positiveNormalizeDraw (fun index => (raw.get index).decode) bits word).val := by
  have hv : (fun index => ((binaryPositiveNormalize raw).data.get index).decode)=
      positiveWeightProgram (fun index => (raw.get index).decode) :=
    funext (binaryPositiveNormalize_value raw)
  have hn : ∀ index,0≤ ((binaryPositiveNormalize raw).data.get index).decode := by
    intro index
    rw [binaryPositiveNormalize_value]
    exact positiveWeightProgram_nonneg _ index
  have hs : ∑ index,((binaryPositiveNormalize raw).data.get index).decode=1 := by
    simpa only [binaryPositiveNormalize_value] using positiveWeightProgram_sum (fun index => (raw.get index).decode)
  change (binaryRationalDraw _ _ _).value=_
  rw [binaryRationalDraw_cast]
  rw [binaryRationalDraw_value _ hn hs]
  unfold positiveNormalizeDraw
  simp only [RationalFiniteQuantization.draw,FiniteTicketSampler.drawBitTable,
    FiniteTicketSampler.drawFin,Fin.val_cast]
  rw [hv]

def binaryPositiveDrawWork (count height bits : ℕ) : ℕ :=
  binaryPositiveNormalizeWork count height+2*bits+
    binaryRationalDrawWork count (height+count*(height+1)) (bits+count+1)+4



end AFT.BinaryArithmetic

end

section



















namespace AFT
end AFT
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.explicitMarkedChartDensity
end AFT.BoundaryCalibration.explicitMarkedChartDensity




/-! Positive sampling on any nonempty stored array. -/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalBits BoundaryCalibration BetaReference

def binaryPositiveFinDraw {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) : CountedNatural := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred => exact binaryPositiveDraw raw bits word

theorem binaryPositiveFinDraw_lt {count : ℕ} [NeZero count] (raw : Vector RationalBits count)
    (bits : ℕ) (word : Fin (bits+count+1) → Fin 2) :
    (binaryPositiveFinDraw raw bits word).value < count := by
  cases count with
  | zero => exact False.elim ((NeZero.ne 0) rfl)
  | succ pred =>
    change (binaryPositiveDraw raw bits word).value < _
    rw [binaryPositiveDraw_value]
    exact Fin.isLt _







end AFT.BinaryArithmetic

end

section







/-! Actual binary rational evaluation of the finite Taylor, arctangent,
and Machin-style pi series, including every dynamic denominator. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def arctanTerm (input : RationalBits) (index : ℕ) : RationalResult :=
  let doubled := doubleCounter index
  let degree := doubled.count.succ
  let sign := power minusOne index
  let argument := power input degree
  let numerator := multiply sign.data argument.data
  let denominator := ofCounter degree
  let result := quotient numerator.data denominator.data
  ⟨result.data,sign.work+argument.work+numerator.work+denominator.work+result.work+doubled.work+5⟩

def taylorTerm (input : RationalBits) (index : ℕ) : RationalResult :=
  let numerator := power input index
  let denominator := factorial index
  let result := quotient numerator.data denominator.data
  ⟨result.data,numerator.work+denominator.work+result.work+3⟩

def arctan (input : RationalBits) (terms : ℕ) : RationalResult := sumRange (arctanTerm input) terms
def taylor (input : RationalBits) (terms : ℕ) : RationalResult := sumRange (taylorTerm input) terms

theorem arctanTerm_value (input : RationalBits) (index : ℕ) :
    (arctanTerm input index).data.decode=(-1 : ℚ)^index*input.decode^(2*index+1)/(2*index+1 : ℕ) := by
  simp only [arctanTerm,doubleCounter_value,quotient_value,multiply_value,power_value,ofCounter_value,minusOne_value]

theorem taylorTerm_value (input : RationalBits) (index : ℕ) :
    (taylorTerm input index).data.decode=input.decode^index/(index.factorial : ℚ) := by
  simp only [taylorTerm,quotient_value,power_value,factorial_value]

theorem arctan_value (input : RationalBits) (terms : ℕ) :
    (arctan input terms).data.decode=arctanSum input.decode terms := by
  simp only [arctan,sumRange_value,arctanTerm_value,arctanSum]

theorem taylor_value (input : RationalBits) (terms : ℕ) :
    (taylor input terms).data.decode=expSum input.decode terms := by
  simp only [taylor,sumRange_value,taylorTerm_value,expSum]

def seriesTermBits (bits terms : ℕ) : ℕ := (2*terms+2)^2*(bits+1)
def seriesStepWork (bits terms : ℕ) : ℕ :=
  primitiveWorkBound (seriesTermBits bits terms)+60*(2*terms+2)^2+10

def seriesTermWork (bits terms : ℕ) : ℕ := 10*(terms+1)*seriesStepWork bits terms

def seriesWork (bits terms : ℕ) : ℕ :=
  terms*(seriesTermWork bits terms+primitiveWorkBound ((terms+1)*(seriesTermBits bits terms+1))+2)+2















def pi (bits : ℕ) : RationalResult :=
  let count := addCounter bits 3
  let first := arctan half count.count
  let second := arctan third count.count
  let sum := add first.data second.data
  let result := multiply four sum.data
  ⟨result.data,first.work+second.work+sum.work+result.work+count.work+4⟩

theorem pi_value (bits : ℕ) : (pi bits).data.decode=piApprox bits := by
  simp only [pi,addCounter_value,multiply_value,add_value,arctan_value,half_value,third_value,four_value,piApprox]

def piWork (bits : ℕ) : ℕ := 2*seriesWork 2 (bits+3)+2*primitiveWorkBound (piHeight bits)+(2*bits+1)+4



end AFT.BinaryArithmetic.RationalBits

end

section





/-! Literal polynomial budgets for the executable binary finite-series
algorithms. These polynomials describe the proved runtime counters. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.RationalNumerics

noncomputable def primitiveWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ := 10000000*(bits+2)^3
noncomputable def seriesTermBitsPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ := (2*terms+2)^2*(bits+1)
noncomputable def seriesStepWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  primitiveWorkPolynomial (seriesTermBitsPolynomial bits terms)+60*(2*terms+2)^2+10
noncomputable def seriesTermWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  10*(terms+1)*seriesStepWorkPolynomial bits terms
noncomputable def seriesWorkPolynomial (bits terms : Polynomial ℕ) : Polynomial ℕ :=
  terms*(seriesTermWorkPolynomial bits terms+
    primitiveWorkPolynomial ((terms+1)*(seriesTermBitsPolynomial bits terms+1))+2)+2
noncomputable def piHeightPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  2*((bits+3)*(6*(bits+3)+4))+3
noncomputable def piWorkPolynomial (bits : Polynomial ℕ) : Polynomial ℕ :=
  2*seriesWorkPolynomial 2 (bits+3)+2*primitiveWorkPolynomial (piHeightPolynomial bits)+(2*bits+1)+4

@[simp] theorem primitiveWorkPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (primitiveWorkPolynomial bits).eval n=primitiveWorkBound (bits.eval n) := by
  simp only [primitiveWorkPolynomial,primitiveWorkBound,eval_mul,eval_add,eval_pow,eval_ofNat]
@[simp] theorem seriesTermBitsPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesTermBitsPolynomial bits terms).eval n=seriesTermBits (bits.eval n) (terms.eval n) := by
  simp only [seriesTermBitsPolynomial,seriesTermBits,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one]
@[simp] theorem seriesStepWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesStepWorkPolynomial bits terms).eval n=seriesStepWork (bits.eval n) (terms.eval n) := by
  simp only [seriesStepWorkPolynomial,seriesStepWork,eval_mul,eval_add,eval_pow,eval_ofNat,
    primitiveWorkPolynomial_eval,seriesTermBitsPolynomial_eval]
@[simp] theorem seriesTermWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesTermWorkPolynomial bits terms).eval n=seriesTermWork (bits.eval n) (terms.eval n) := by
  simp only [seriesTermWorkPolynomial,seriesTermWork,eval_mul,eval_add,eval_ofNat,eval_one,
    seriesStepWorkPolynomial_eval]
@[simp] theorem seriesWorkPolynomial_eval (bits terms : Polynomial ℕ) (n : ℕ) :
    (seriesWorkPolynomial bits terms).eval n=seriesWork (bits.eval n) (terms.eval n) := by
  simp only [seriesWorkPolynomial,seriesWork,eval_mul,eval_add,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,seriesTermWorkPolynomial_eval,seriesTermBitsPolynomial_eval]
@[simp] theorem piHeightPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (piHeightPolynomial bits).eval n=piHeight (bits.eval n) := by
  simp only [piHeightPolynomial,piHeight,eval_mul,eval_add,eval_ofNat]
@[simp] theorem piWorkPolynomial_eval (bits : Polynomial ℕ) (n : ℕ) :
    (piWorkPolynomial bits).eval n=piWork (bits.eval n) := by
  simp only [piWorkPolynomial,piWork,eval_mul,eval_add,eval_ofNat,eval_one,seriesWorkPolynomial_eval,
    primitiveWorkPolynomial_eval,piHeightPolynomial_eval]











end AFT.BinaryArithmetic.RationalBits

end

section




















/-! # Literal polynomial bounds for binary finite sampling -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits

noncomputable def dyadicFloorWorkPolynomial (height bits : Polynomial ℕ) : Polynomial ℕ :=
  1000*(bits+height+2)^2+primitiveWorkPolynomial (bits+height)+6*bits+16
noncomputable def sumDigitsWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(10*(count+1)*(bits+1)+4)+2
noncomputable def ticketTableDigitPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  (count+1)*(bits+height+2)+1
noncomputable def ticketTableWorkPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(dyadicFloorWorkPolynomial height bits+3)+sumDigitsWorkPolynomial count (bits+height+1)+
    2*bits+20*ticketTableDigitPolynomial count height bits+20
noncomputable def binaryRationalDrawPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  ticketTableWorkPolynomial count height bits+3*bits+
    count*(10*ticketTableDigitPolynomial count height bits+5)+2*count+6
noncomputable def sumArrayWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+3+primitiveWorkPolynomial ((count+1)*(height+1))+2)+2
noncomputable def normalizeArrayWorkPolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  sumArrayWorkPolynomial count height+
    count*(3*count+3+2*primitiveWorkPolynomial (height+count*(height+1))+6)+4
noncomputable def binaryPositiveNormalizePolynomial (count height : Polynomial ℕ) : Polynomial ℕ :=
  count*(3*count+9)+sumArrayWorkPolynomial count height+normalizeArrayWorkPolynomial count height+5*count+10
noncomputable def binaryPositiveDrawPolynomial (count height bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryPositiveNormalizePolynomial count height+2*bits+
    binaryRationalDrawPolynomial count (height+count*(height+1)) (bits+count+1)+4

@[simp] theorem dyadicFloorWorkPolynomial_eval (height bits : Polynomial ℕ) (n : ℕ) :
    (dyadicFloorWorkPolynomial height bits).eval n=dyadicFloorWork (height.eval n) (bits.eval n) := by
  simp only [dyadicFloorWorkPolynomial,dyadicFloorWork,eval_add,eval_mul,eval_pow,eval_ofNat,primitiveWorkPolynomial_eval]
@[simp] theorem sumDigitsWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (sumDigitsWorkPolynomial count bits).eval n=sumDigitsWork (count.eval n) (bits.eval n) := by
  simp only [sumDigitsWorkPolynomial,sumDigitsWork,eval_add,eval_mul,eval_ofNat,eval_one]
@[simp] theorem ticketTableDigitPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (ticketTableDigitPolynomial count height bits).eval n=ticketTableDigitBound (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [ticketTableDigitPolynomial,ticketTableDigitBound,eval_add,eval_mul,eval_ofNat,eval_one]
@[simp] theorem ticketTableWorkPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (ticketTableWorkPolynomial count height bits).eval n=ticketTableWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [ticketTableWorkPolynomial,ticketTableWork,eval_add,eval_mul,eval_ofNat,eval_one,
    dyadicFloorWorkPolynomial_eval,sumDigitsWorkPolynomial_eval,ticketTableDigitPolynomial_eval]
@[simp] theorem binaryRationalDrawPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (binaryRationalDrawPolynomial count height bits).eval n=binaryRationalDrawWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [binaryRationalDrawPolynomial,binaryRationalDrawWork,eval_add,eval_mul,eval_ofNat,
    ticketTableWorkPolynomial_eval,ticketTableDigitPolynomial_eval]
@[simp] theorem sumArrayWorkPolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (sumArrayWorkPolynomial count height).eval n=sumArrayWork (count.eval n) (height.eval n) := by
  simp only [sumArrayWorkPolynomial,sumArrayWork,eval_add,eval_mul,eval_ofNat,eval_one,primitiveWorkPolynomial_eval]
@[simp] theorem normalizeArrayWorkPolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (normalizeArrayWorkPolynomial count height).eval n=normalizeArrayWork (count.eval n) (height.eval n) := by
  simp only [normalizeArrayWorkPolynomial,normalizeArrayWork,eval_add,eval_mul,eval_ofNat,eval_one,
    sumArrayWorkPolynomial_eval,primitiveWorkPolynomial_eval]
@[simp] theorem binaryPositiveNormalizePolynomial_eval (count height : Polynomial ℕ) (n : ℕ) :
    (binaryPositiveNormalizePolynomial count height).eval n=binaryPositiveNormalizeWork (count.eval n) (height.eval n) := by
  simp only [binaryPositiveNormalizePolynomial,binaryPositiveNormalizeWork,eval_add,eval_mul,eval_ofNat,
    sumArrayWorkPolynomial_eval,normalizeArrayWorkPolynomial_eval]
@[simp] theorem binaryPositiveDrawPolynomial_eval (count height bits : Polynomial ℕ) (n : ℕ) :
    (binaryPositiveDrawPolynomial count height bits).eval n=binaryPositiveDrawWork (count.eval n) (height.eval n) (bits.eval n) := by
  simp only [binaryPositiveDrawPolynomial,binaryPositiveDrawWork,eval_add,eval_mul,eval_ofNat,eval_one,
    binaryPositiveNormalizePolynomial_eval,binaryRationalDrawPolynomial_eval]









end AFT.BinaryArithmetic

end

section




















/-! An interval-index sampler with a binary-computed uniform probability. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics RationalBits Polynomial

def binaryUniformDraw (count : ℕ) (hc : 0 < count) (bits : ℕ)
    (word : Fin (bits+count+1) → Fin 2) : CountedValue (Fin count) :=
  letI : NeZero count := ⟨Nat.ne_zero_of_lt hc⟩
  let encoded := ofCounter count
  let probability := inverse encoded.data
  let weights := Vector.replicate count probability.data
  let selected := binaryPositiveFinDraw weights bits word
  ⟨⟨selected.value,binaryPositiveFinDraw_lt weights bits word⟩,
    encoded.work+probability.work+count+selected.work+4⟩



def binaryUniformDrawWork (count bits : ℕ) : ℕ :=
  60*(count+1)^2+primitiveWorkBound count+count+binaryPositiveDrawWork count count bits+4



noncomputable def binaryUniformDrawPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(count+1)^2+primitiveWorkPolynomial count+count+binaryPositiveDrawPolynomial count count bits+4

@[simp] theorem binaryUniformDrawPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryUniformDrawPolynomial count bits).eval n=binaryUniformDrawWork (count.eval n) (bits.eval n) := by
  simp [binaryUniformDrawPolynomial,binaryUniformDrawWork]



end AFT.BinaryArithmetic

end

section




















/-! The actual finite-bit choice used at a permutation insertion stage. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.RationalNumerics RationalBits
open scoped BigOperators

def binaryPermutationChoice (size bits : ℕ) (word : Fin bits → Fin 2) : CountedValue (Fin (size+1)) :=
  let encoded := ofCounter size.succ
  let probability := inverse encoded.data
  let weights := Vector.replicate size.succ probability.data
  let selected := binaryRationalDraw weights bits word
  have hv : (fun index => (weights.get index).decode)=PermutationProgram.choiceWeight size := by
    funext index
    simp only [weights,probability,encoded,Vector.get_replicate,inverse_value,ofCounter_value,
      PermutationProgram.choiceWeight,Nat.succ_eq_add_one]
  have hn : ∀ index,0 ≤ (weights.get index).decode := by
    intro index
    change 0 ≤ (fun index => (weights.get index).decode) index
    rw [hv]
    exact PermutationProgram.choiceWeight_nonneg size index
  have hs : (∑ index,(weights.get index).decode)=1 := by
    rw [hv];exact PermutationProgram.choiceWeight_sum size
  have hlt : selected.value < size+1 := by
    rw [binaryRationalDraw_value weights hn hs bits word]
    exact Fin.isLt _
  ⟨⟨selected.value,hlt⟩,encoded.work+probability.work+size.succ+selected.work+4⟩

theorem binaryPermutationChoice_value (size bits : ℕ) (word : Fin bits → Fin 2) :
    (binaryPermutationChoice size bits word).value=PermutationProgram.choiceDraw size bits word := by
  let weights := Vector.replicate size.succ (inverse (ofCounter size.succ).data).data
  have hv : (fun index => (weights.get index).decode)=PermutationProgram.choiceWeight size := by
    funext index
    simp only [weights,Vector.get_replicate,inverse_value,ofCounter_value,
      PermutationProgram.choiceWeight,Nat.succ_eq_add_one]
  have hn : ∀ index,0 ≤ (weights.get index).decode := by
    intro index
    change 0 ≤ (fun index => (weights.get index).decode) index
    rw [hv]
    exact PermutationProgram.choiceWeight_nonneg size index
  have hs : (∑ index,(weights.get index).decode)=1 := by
    rw [hv];exact PermutationProgram.choiceWeight_sum size
  apply Fin.ext
  change (binaryRationalDraw weights bits word).value=_
  rw [binaryRationalDraw_value weights hn hs bits word]
  simp only [hv,PermutationProgram.choiceDraw]

def binaryPermutationChoiceWork (size bits : ℕ) : ℕ :=
  60*(size+2)^2+primitiveWorkBound (size+1)+(size+1)+binaryRationalDrawWork (size+1) (size+1) bits+4





end AFT.BinaryArithmetic

end

section






















/-! Stored permutation rows from the actual insertion sampler. Each old image
is explicitly read, compared, and written; no permutation oracle is used. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

def insertionImage {count : ℕ} (picked : Fin (count+1)) (image : Fin count) : CountedValue (Fin (count+1)) :=
  let equal := equalCounter image.val.succ picked.val
  ⟨if equal.value then 0 else image.succ,equal.work+2⟩

theorem insertionImage_value {count : ℕ} (picked : Fin (count+1)) (image : Fin count) :
    (insertionImage picked image).value=Equiv.swap 0 picked image.succ := by
  have he : (equalCounter image.val.succ picked.val).value=true ↔ image.succ=picked := by
    rw [equalCounter_value]
    exact ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
  simp only [insertionImage,he,Equiv.swap_apply_def,Fin.succ_ne_zero,↓reduceIte]



def binaryPermutationRows (bits : ℕ) : (count : ℕ) → (Fin count → Fin bits → Fin 2) →
    CountedValue (Vector (Fin count) count)
  | 0,_ => ⟨Vector.ofFn Fin.elim0,2⟩
  | count+1,word =>
      let previous := binaryPermutationRows bits count (Fin.tail word)
      let selected := binaryPermutationChoice count bits (word 0)
      let result := storeData (count+1) (fun index => Fin.cases ⟨selected.value,1⟩ (fun old =>
        let read := readVector old previous.value old
        let image := insertionImage selected.value read.value
        ⟨image.value,read.work+image.work+2⟩) index)
      ⟨result.value,previous.work+selected.work+result.work+3⟩

theorem binaryPermutationRows_value (bits count : ℕ) (word : Fin count → Fin bits → Fin 2)
    (index : Fin count) :
    (binaryPermutationRows bits count word).value.get index=PermutationProgram.rows bits count word index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      refine Fin.cases ?_ (fun old => ?_) index
      · simp only [binaryPermutationRows,storeData_get,Fin.cases_zero,PermutationProgram.rows,
          Equiv.Perm.decomposeFin_symm_apply_zero,binaryPermutationChoice_value]
      · simp only [binaryPermutationRows,storeData_get,Fin.cases_succ,insertionImage_value,
          readVector_value,ih,PermutationProgram.rows,Equiv.Perm.decomposeFin_symm_apply_succ,
          binaryPermutationChoice_value]

def binaryPermutationRowsWork (count bits : ℕ) : ℕ :=
  count*(binaryPermutationChoiceWork count bits+(count+1)*(9*count+17)+5)+2





end AFT.BinaryArithmetic

end

section







/-! # The sorted coordinate numbering commutes with explicit coordinate codes -/
namespace AFT











@[simp] theorem finiteSetMatching_numbering {State : Type*} {size : ℕ}
    (index : State ≃ Fin size) (first second : Finset State)
    (hcard : first.card ≤ second.card) (position : Fin first.card) :
    finiteSetMatching index first second hcard (finiteSetNumbering index first position) =
      finiteSetNumbering index second (Fin.castLE hcard position) := by
  simp [finiteSetMatching]



/-- A linear scan in arithmetic order computes the same numbering as the
semantic finite-set sorting operation. -/
def finiteSetScan {size : ℕ} (set : Finset (Fin size)) : List (Fin size) :=
  (List.finRange size).filter (fun point => point ∈ set)

theorem finiteSetScan_eq_sort {size : ℕ} (set : Finset (Fin size)) :
    finiteSetScan set = set.sort := by
  apply ((List.sortedLT_finRange size).pairwise.filter _).sortedLT.eq_of_mem_iff set.sortedLT_sort
  simp

@[simp] theorem finiteSetScan_length {size : ℕ} (set : Finset (Fin size)) :
    (finiteSetScan set).length = set.card := by
  rw [finiteSetScan_eq_sort, Finset.length_sort]



end AFT

end

section








namespace AFT
end AFT
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.bodies
end AFT.Parameters.bodies
namespace AFT.PublicPoolProgram
end AFT.PublicPoolProgram
namespace AFT.PublicPoolProgram.pairWord
end AFT.PublicPoolProgram.pairWord
namespace AFT.PublicPoolProgram.population
end AFT.PublicPoolProgram.population


/-! # Scanning public pool lists, with explicit query and loop counters -/
namespace AFT.PublicPoolProgram





structure IndexQuery (population : ℕ) where
  value : Fin population
  work : ℕ

structure ScanResult (population : ℕ) where
  controls : List (Fin population)
  available : List (Fin population)
  work : ℕ













end AFT.PublicPoolProgram

end

section








/-! # Literal finite-range generation and public pool query costs -/
namespace AFT.PublicPoolProgram

structure RangeResult (population : ℕ) where
  values : List (Fin population)
  work : ℕ



















structure ListRead (Value : Type*) where
  value : Option Value
  work : ℕ







structure ValueQuery (Value : Type*) where
  value : Value
  work : ℕ





end AFT.PublicPoolProgram

end

section


















/-! # Explicit arithmetic on polynomially bounded unary counters

These routines are used only for metadata whose numerical magnitude is itself
polynomial in the dimension. Exponential ticket counts never use this encoding.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

def powerCounter (base : ℕ) : ℕ → UnaryCounterResult
  | 0 => ⟨1,2⟩
  | exponent+1 =>
      let previous := powerCounter base exponent
      let next := multiplyCounter base previous.count
      ⟨next.count,previous.work+next.work+2⟩

theorem powerCounter_value (base exponent : ℕ) : (powerCounter base exponent).count=base^exponent := by
  induction exponent with
  | zero => rfl
  | succ exponent ih => simp only [powerCounter,multiplyCounter_value,ih,pow_succ];ring

def powerCounterWork (base exponent : ℕ) : ℕ := (exponent+1)*(6*(base+1)^(exponent+2)+4)

theorem powerCounter_work (base exponent : ℕ) :
    (powerCounter base exponent).work≤ powerCounterWork base exponent := by
  induction exponent with
  | zero => simp only [powerCounter,powerCounterWork];omega
  | succ exponent ih =>
      have hp : (base+1)^(exponent+2)≤(base+1)^(exponent+1+2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hb : base≤(base+1)^(exponent+1+2) := by
        calc
          _ ≤ base+1 := by omega
          _ = (base+1)^1 := by simp
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have hm : base*base^exponent≤(base+1)^(exponent+1+2) := by
        calc
          _ = base^(exponent+1) := by rw [pow_succ];ring
          _ ≤ (base+1)^(exponent+1) := Nat.pow_le_pow_left (by omega) _
          _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
      have hi : (powerCounter base exponent).work≤(exponent+1)*(6*(base+1)^(exponent+1+2)+4) :=
        ih.trans (Nat.mul_le_mul_left _ (by omega))
      simp only [powerCounter,multiplyCounter_work,powerCounter_value,powerCounterWork]
      nlinarith



def lessCounter : ℕ → ℕ → CountedValue Bool
  | _,0 => ⟨false,2⟩
  | 0,_+1 => ⟨true,2⟩
  | first+1,second+1 => let previous := lessCounter first second;⟨previous.value,previous.work+3⟩

theorem lessCounter_value (first second : ℕ) : (lessCounter first second).value=true ↔ first<second := by
  induction first generalizing second with
  | zero => cases second <;> simp [lessCounter]
  | succ first ih => cases second <;> simp [lessCounter,ih]

theorem lessCounter_work (first second : ℕ) : (lessCounter first second).work≤3*(first+second)+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [lessCounter] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [lessCounter];omega
      | succ second => have hh := ih second;simp only [lessCounter];omega





def subtractCounter : ℕ → ℕ → UnaryCounterResult
  | first,0 => ⟨first,2⟩
  | 0,_+1 => ⟨0,2⟩
  | first+1,second+1 => let previous := subtractCounter first second;⟨previous.count,previous.work+2⟩

theorem subtractCounter_value (first second : ℕ) : (subtractCounter first second).count=first-second := by
  induction first generalizing second with
  | zero => cases second <;> simp [subtractCounter]
  | succ first ih => cases second <;> simp [subtractCounter,ih]

theorem subtractCounter_work_left (first second : ℕ) : (subtractCounter first second).work≤2*first+2 := by
  induction first generalizing second with
  | zero => cases second <;> simp only [subtractCounter] <;> omega
  | succ first ih =>
      cases second with
      | zero => simp only [subtractCounter];omega
      | succ second => have hh := ih second;simp only [subtractCounter];omega

end AFT.BinaryArithmetic

end

section























namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.binaryPoolScan
end AFT.BinaryArithmetic.binaryPoolScan
namespace AFT.BinaryArithmetic.binaryPoolScan.match_1
end AFT.BinaryArithmetic.binaryPoolScan.match_1
namespace AFT.BinaryArithmetic.binaryRunPoolScan
end AFT.BinaryArithmetic.binaryRunPoolScan




/-! Runtime block decoding and edge/root addressing use bounded unary
comparisons, long division and explicitly charged counter arithmetic. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def binaryVertexCode (legs rest : ℕ) (index : Fin (legs*3+rest)) :
     CountedValue (Sigma (blockSlotsProgram legs rest)) :=
   let boundary := multiplyCounter legs 3
   let selected := lessCounter index.val boundary.count
   if h : selected.value=true then
     let qr := divideCounter index.val 3
     ⟨⟨.inl ⟨qr.quotient,by
         have hi := (lessCounter_value _ _).mp h
         simp only [boundary,multiplyCounter_value] at hi
         rw [(divideCounter_value _ _ (by omega)).1]
         exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hi⟩,
       ⟨qr.remainder,by
         change qr.remainder < 3
         rw [(divideCounter_value _ _ (by omega)).2]
         exact Nat.mod_lt _ (by omega)⟩⟩,
       boundary.work+selected.work+qr.work+4⟩
   else
     let body := differenceCounter index.val boundary.count
     ⟨⟨.inr ⟨body.count,by
         rw [differenceCounter_value]
         have hi : ¬index.val<boundary.count := fun hi => h ((lessCounter_value _ _).mpr hi)
         have hb : boundary.count=legs*3 := multiplyCounter_value legs 3
         omega⟩,(0 : Fin 1)⟩,boundary.work+selected.work+body.work+4⟩

 

 

 def binaryRootAddress (legs rest : ℕ) : (Fin legs⊕Fin rest)→ CountedValue (Fin (legs+rest))
   | .inl leg => ⟨⟨leg.val,by omega⟩,1⟩
   | .inr body =>
       let address := addCounter legs body.val
       ⟨⟨address.count,by rw [addCounter_value];omega⟩,address.work+2⟩

 

 

 

 

 

end AFT.BinaryArithmetic

end

section






















/-! # Actual leg cutoff with counted integer metadata computation

The fixed powers and bounded search use unary counters. Their magnitudes have
explicit polynomial bounds, so this avoids any unit-cost large-integer test.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram V7Calibration Polynomial
open scoped BigOperators











def binaryLegCutoffWork (constant n : ℕ) : ℕ :=
  n*(2*n+3)+constant*(2*n^2+3)+powerCounterWork constant 8+powerCounterWork n 9+
    constant^8*(2*n^9+3)+
    (constant*n^2+1)*(powerCounterWork (constant*n^2+1) 8+3*((constant*n^2+1)^8+constant^8*n^9)+7)+12



noncomputable def powerCounterPolynomial (base : Polynomial ℕ) (exponent : ℕ) : Polynomial ℕ :=
  C (exponent+1)*(6*(base+1)^(exponent+2)+4)
noncomputable def binaryLegCutoffPolynomial (constant : ℕ) : Polynomial ℕ :=
  X*(2*X+3)+C constant*(2*X^2+3)+powerCounterPolynomial (C constant) 8+powerCounterPolynomial X 9+
    C constant^8*(2*X^9+3)+
    (C constant*X^2+1)*(powerCounterPolynomial (C constant*X^2+1) 8+
      3*((C constant*X^2+1)^8+C constant^8*X^9)+7)+12

@[simp] theorem powerCounterPolynomial_eval (base : Polynomial ℕ) (exponent n : ℕ) :
    (powerCounterPolynomial base exponent).eval n=powerCounterWork (base.eval n) exponent := by
  simp only [powerCounterPolynomial,powerCounterWork,eval_mul,eval_add,eval_pow,eval_C,eval_ofNat,eval_one]
@[simp] theorem binaryLegCutoffPolynomial_eval (constant n : ℕ) :
    (binaryLegCutoffPolynomial constant).eval n=binaryLegCutoffWork constant n := by
  simp only [binaryLegCutoffPolynomial,binaryLegCutoffWork,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_ofNat,
    eval_one,powerCounterPolynomial_eval]

end AFT.BinaryArithmetic

end

section

























/-! The true boundary half-width as signed binary digits, including every
integer parameter operation and the actual leg-cutoff search. -/
namespace AFT.BinaryArithmetic
open AFT.V7Calibration Polynomial











def boundaryCounterBound (constant n : ℕ) : ℕ := (constant+24)*(n+2)^2





def binaryBoundaryHalfWork (constant n : ℕ) : ℕ :=
  binaryLegCutoffWork constant n+2000*(boundaryCounterBound constant n+1)^2+100



noncomputable def boundaryCounterPolynomial (constant : ℕ) : Polynomial ℕ :=
  C (constant+24)*(X+2)^2
noncomputable def binaryBoundaryHalfPolynomial (constant : ℕ) : Polynomial ℕ :=
  binaryLegCutoffPolynomial constant+2000*(boundaryCounterPolynomial constant+1)^2+100

@[simp] theorem boundaryCounterPolynomial_eval (constant n : ℕ) :
    (boundaryCounterPolynomial constant).eval n=boundaryCounterBound constant n := by
  simp [boundaryCounterPolynomial,boundaryCounterBound]
@[simp] theorem binaryBoundaryHalfPolynomial_eval (constant n : ℕ) :
    (binaryBoundaryHalfPolynomial constant).eval n=binaryBoundaryHalfWork constant n := by
  simp [binaryBoundaryHalfPolynomial,binaryBoundaryHalfWork]

end AFT.BinaryArithmetic

end

section



















/-! Polynomial bit and unary-control costs of actual protected features.
All address values are polynomially bounded in the actual chart instance. -/
namespace AFT.BinaryArithmetic

 def modularDifferenceWork (address cutoff modulus : ℕ) : ℕ :=
   500*(cutoff+modulus+2)^2+2*modulus+2*address+6+
     500*(address+2*modulus+2)^2

 

 def protectedFeatureWork (cutoff modulus input chart : ℕ) : ℕ :=
   3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
   (modulus*(2*modulus+3)+1)+500*(chart+modulus*modulus+2)^2+
   500*(modulus*modulus+modulus+2)^2+
   modularDifferenceWork input cutoff modulus+modularDifferenceWork (2*cutoff+1) cutoff modulus+
   (modulus*modulus*(2*modulus+3)+1)+(modulus*(2*modulus+3)+1)+
   (2*chart+1)+(2*(chart+modulus*modulus*modulus)+1)+
   500*(chart+modulus*modulus*modulus+modulus*modulus+modulus+2)^2+13

 

end AFT.BinaryArithmetic

end

section



















/-! The nonzero scale coordinate decoded by two real binary divisions. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 def protectedScaleAddress (modulus chart : ℕ) : UnaryCounterResult :=
   let square := multiplyCounter modulus modulus
   let outer := divideCounter chart square.count
   let inner := divideCounter outer.remainder modulus
   ⟨inner.quotient,square.work+outer.work+inner.work+3⟩

 theorem protectedScaleAddress_value (modulus chart : ℕ) (hm : 0 < modulus) :
     (protectedScaleAddress modulus chart).count=(chart%(modulus*modulus))/modulus := by
   dsimp only [protectedScaleAddress]
   rw [(divideCounter_value _ _ hm).1,multiplyCounter_value,
     (divideCounter_value _ _ (Nat.mul_pos hm hm)).2]

 theorem protectedScaleAddress_lt (modulus chart : ℕ) (hm : 0 < modulus) :
     (protectedScaleAddress modulus chart).count< modulus := by
   rw [protectedScaleAddress_value modulus chart hm]
   exact (Nat.div_lt_iff_lt_mul hm).mpr (Nat.mod_lt _ (Nat.mul_pos hm hm))

 def protectedScale (modulus : ℕ) [NeZero modulus] (chart : Fin (modulus*(modulus*modulus))) : CountedValue (Fin modulus) :=
   let result := protectedScaleAddress modulus chart.val
   ⟨⟨result.count,protectedScaleAddress_lt modulus chart.val (Nat.pos_of_ne_zero (NeZero.ne _))⟩,result.work⟩

 

 def protectedScaleWork (modulus chart : ℕ) : ℕ :=
   modulus*(2*modulus+3)+1+500*(chart+modulus*modulus+2)^2+
     500*(modulus*modulus+modulus+2)^2+3

 

end AFT.BinaryArithmetic

end

section





















/-! Decoding a sampled chart index by actual binary long division. The
runtime data are three bounded counters; field casts appear only in the
semantic theorem. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration

structure ChartCounterResult where
  offset : ℕ
  scale : ℕ
  shear : ℕ
  work : ℕ

def binaryChartCoordinates (modulus chart : ℕ) : ChartCounterResult :=
  let square := multiplyCounter modulus modulus
  let outer := divideCounter chart square.count
  let inner := divideCounter outer.remainder modulus
  ⟨outer.quotient,inner.quotient,inner.remainder,square.work+outer.work+inner.work+3⟩

theorem binaryChartCoordinates_values (modulus chart : ℕ) (hm : 0 < modulus) :
    (binaryChartCoordinates modulus chart).offset=chart/(modulus*modulus) ∧
    (binaryChartCoordinates modulus chart).scale=(chart%(modulus*modulus))/modulus ∧
    (binaryChartCoordinates modulus chart).shear=(chart%(modulus*modulus))%modulus := by
  simp only [binaryChartCoordinates,multiplyCounter_value,
    (divideCounter_value _ _ (Nat.mul_pos hm hm)).1,(divideCounter_value _ _ (Nat.mul_pos hm hm)).2,
    (divideCounter_value _ _ hm).1,(divideCounter_value _ _ hm).2,and_self]

theorem binaryChartCoordinates_bounds (modulus chart : ℕ) (hm : 0 < modulus)
    (hi : chart < modulus*(modulus*modulus)) :
    (binaryChartCoordinates modulus chart).offset < modulus ∧
    (binaryChartCoordinates modulus chart).scale < modulus ∧
    (binaryChartCoordinates modulus chart).shear < modulus := by
  rcases binaryChartCoordinates_values modulus chart hm with ⟨ho,hs,ht⟩
  rw [ho,hs,ht]
  exact ⟨(Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hm)).mpr hi,
    (Nat.div_lt_iff_lt_mul hm).mpr (Nat.mod_lt _ (Nat.mul_pos hm hm)),Nat.mod_lt _ hm⟩





end AFT.BinaryArithmetic

end

section




















namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RationalNumerics.cachedLinearIteration
end AFT.RationalNumerics.cachedLinearIteration
namespace AFT.RationalNumerics.cachedLinearIteration.match_1
end AFT.RationalNumerics.cachedLinearIteration.match_1
namespace AFT.RationalNumerics.cachedMatrix
end AFT.RationalNumerics.cachedMatrix
namespace AFT.RationalNumerics.cachedMatrixApply
end AFT.RationalNumerics.cachedMatrixApply
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualAnchorError
end AFT.V7Calibration.actualAnchorError
namespace AFT.V7Calibration.actualAnchorErrorProgram
end AFT.V7Calibration.actualAnchorErrorProgram
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualCachedInverseProgram
end AFT.V7Calibration.actualCachedInverseProgram
namespace AFT.V7Calibration.actualErrorApprox
end AFT.V7Calibration.actualErrorApprox
namespace AFT.V7Calibration.actualInverseIterationProgram
end AFT.V7Calibration.actualInverseIterationProgram
namespace AFT.V7Calibration.actualInverseIterationProgram.match_1
end AFT.V7Calibration.actualInverseIterationProgram.match_1
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualPreconditionedMatrixProgram
end AFT.V7Calibration.actualPreconditionedMatrixProgram
namespace AFT.V7Calibration.actualRankApprox
end AFT.V7Calibration.actualRankApprox
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean



/-! Materialized Neumann iteration on canonical binary rationals. Every
matrix and vector access is an explicit sequential lookup. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram
open scoped BigOperators

def matrixEntry {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (output input : Fin count) : CountedValue RationalBits :=
  let fallback := Vector.replicate count zero
  let row := readVector fallback matrix output
  let entry := readVector zero row.value input
  ⟨entry.value,row.work+entry.work+count+2⟩

theorem matrixEntry_value {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (output input : Fin count) : (matrixEntry matrix output input).value=(matrix.get output).get input := by
  simp only [matrixEntry,readVector_value]



def matrixProductTerm {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output input : Fin count) : RationalResult :=
  let coefficient := matrixEntry matrix output input
  let argument := readVector zero profile input
  let result := multiply coefficient.value argument.value
  ⟨result.data,coefficient.work+argument.work+result.work+2⟩



def matrixRow {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) (output : Fin count) : RationalResult :=
  sumFin count (matrixProductTerm matrix profile output)

def matrixApply {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (profile : Vector RationalBits count) : ArrayResult count :=
  buildArray count (matrixRow matrix profile)





def matrixRowWork (count bits : ℕ) : ℕ :=
  count*(10*count+13+primitiveWorkBound bits+primitiveWorkBound ((count+1)*(2*bits+1))+2)+2

def matrixApplyWork (count bits : ℕ) : ℕ := count*(matrixRowWork count bits+2)+2





def iterationEntry {count : ℕ} (rhs applied : Vector RationalBits count) (output : Fin count) : RationalResult :=
  let right := readVector zero rhs output
  let image := readVector zero applied output
  let negative := negate image.value
  let result := add right.value negative.data
  ⟨result.data,right.work+image.work+negative.work+result.work+3⟩



def iteration {count : ℕ} (matrix : Vector (Vector RationalBits count) count)
    (rhs : Vector RationalBits count) : ℕ → ArrayResult count
  | 0 => ⟨Vector.replicate count zero,2*count+2⟩
  | steps+1 =>
    let previous := iteration matrix rhs steps
    let applied := matrixApply matrix previous.data
    let result := buildArray count (iterationEntry rhs applied.data)
    ⟨result.data,previous.work+applied.work+result.work+3⟩



def iterationBits (count bits limit : ℕ) : ℕ :=
  bits+limit*((3*(count^2+count)+1)*bits+count+1)

def iterationWorkStep (count bits limit : ℕ) : ℕ :=
  matrixApplyWork count (iterationBits count bits limit)+
    count*(6*count+13+2*primitiveWorkBound ((count+1)*(2*iterationBits count bits limit+1)))+5



end AFT.BinaryArithmetic.RationalBits

end

section




















/-! Literal Boolean-mask chart projection evaluated with binary arithmetic.
The program does not call a finite-set membership or cardinality primitive. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration
open scoped BigOperators

def difference (first second : RationalBits) : RationalResult :=
  let negative := negate second
  let result := add first negative.data
  ⟨result.data,negative.work+result.work+2⟩



def chartExpectation (charts : ℕ) (term : Fin charts → RationalResult) : RationalResult :=
  let total := sumFin charts term
  let denominator := ofCounter charts
  let result := quotient total.data denominator.data
  ⟨result.data,total.work+denominator.work+result.work+3⟩



def chartConditionalTerm {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts)
    (color : Fin colors) (point : Fin charts) : RationalResult :=
  let mapped := readVector 0 feature point
  let equal := equalCounter mapped.value.val color.val
  if equal.value then
    let term := readVector zero profile point
    ⟨term.value,mapped.work+equal.work+term.work+2⟩
  else ⟨zero,mapped.work+equal.work+2⟩



def chartConditional {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (profile : Vector RationalBits charts) (color : Fin colors) : RationalResult :=
  let average := chartExpectation charts (chartConditionalTerm feature profile color)
  let coefficient := ofCounter colors
  let result := multiply coefficient.data average.data
  ⟨result.data,average.work+coefficient.work+result.work+3⟩



def chartAllowedTerm {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (color : Fin colors) : RationalResult :=
  let active := readVector false allowed color
  if active.value then
    let term := chartConditional feature profile color
    ⟨term.data,active.work+term.work+2⟩
  else ⟨zero,active.work+2⟩



def chartFeature {charts colors : ℕ} [NeZero colors]
    (feature : Vector (Fin colors) charts) (allowed : Vector Bool colors)
    (profile : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let mapped := readVector 0 feature point
  let active := readVector false allowed mapped.value
  if active.value then
    let current := chartConditional feature profile mapped.value
    let total := sumFin colors (chartAllowedTerm feature allowed profile)
    let counter := maskCount allowed
    let denominator := ofCounter counter.count
    let average := quotient total.data denominator.data
    let result := difference current.data average.data
    ⟨result.data,mapped.work+active.work+current.work+total.work+counter.work+denominator.work+average.work+result.work+6⟩
  else ⟨zero,mapped.work+active.work+2⟩



def chartProjectionTerm {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) (index : Fin features) : RationalResult :=
  let row := readVector (Vector.replicate charts 0) feature index
  let mask := readVector (Vector.replicate colors false) allowed index
  let result := chartFeature row.value mask.value profile point
  ⟨result.data,row.work+mask.work+result.work+charts+colors+3⟩

def chartProjection {charts colors features : ℕ} [NeZero colors]
    (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
    (profile : Vector RationalBits charts) (point : Fin charts) : RationalResult :=
  let average := chartExpectation charts (fun index =>
    let term := readVector zero profile index
    ⟨term.value,term.work⟩)
  let total := sumFin features (chartProjectionTerm feature allowed profile point)
  let result := add average.data total.data
  ⟨result.data,average.work+total.work+result.work+3⟩



end AFT.BinaryArithmetic.RationalBits

end

section


















/-! Polynomial costs of the literal binary chart projection, including
sequential metadata reads and Boolean-mask cardinality scans. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration

def finiteSumWork (count bits termWork : ℕ) : ℕ :=
  count*(termWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2

def expectationWork (charts bits termWork : ℕ) : ℕ :=
  finiteSumWork charts bits termWork+60*(charts+1)^2+
    2*primitiveWorkBound ((charts+1)*(bits+1)+charts+1)+5

def conditionalWork (charts colors bits : ℕ) : ℕ :=
  expectationWork charts bits (6*charts+6*colors+10)+60*(colors+1)^2+
    primitiveWorkBound (chartConditionalHeight charts colors bits+1)+3

def featureWork (charts colors bits : ℕ) : ℕ :=
  let H := chartConditionalHeight charts colors bits
  conditionalWork charts colors bits+
    finiteSumWork colors H (conditionalWork charts colors bits+3*colors+5)+
    colors*(3*colors+6)+60*(colors+1)^2+3*charts+3*colors+
    2*primitiveWorkBound (colors*(H+1)+colors+1)+
    2*primitiveWorkBound (chartFeatureHeight charts colors bits)+30

def projectionWork (charts colors features bits : ℕ) : ℕ :=
  expectationWork charts bits (3*charts+3)+
    finiteSumWork features (chartFeatureHeight charts colors bits)
      (featureWork charts colors bits+6*features+charts+colors+9)+
    primitiveWorkBound (chartProjectionHeight charts colors features bits)+3











end AFT.BinaryArithmetic.RationalBits

end

section




















/-! Binary materialization of the protected deletion matrix and marked spike.
Masks are stored Boolean vectors; every read and cardinality scan is explicit. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def chartSpike {charts : ℕ} (fiber : Vector Bool charts) (point : Fin charts) : RationalResult :=
   let active := readVector false fiber point
   if active.value then
     let cardinality := maskCount fiber
     let numerator := ofCounter charts
     let denominator := ofCounter cardinality.count
     let result := quotient numerator.data denominator.data
     ⟨result.data,active.work+cardinality.work+numerator.work+denominator.work+result.work+5⟩
   else ⟨zero,active.work+2⟩

 

 def chartDeletedBasis {charts : ℕ} (safe : Vector Bool charts) (input point : Fin charts) : RationalResult :=
   let allowed := readVector false safe point
   let same := equalCounter point.val input.val
   if allowed.value then ⟨zero,allowed.work+2⟩
   else if same.value then ⟨one,allowed.work+same.work+3⟩
   else ⟨zero,allowed.work+same.work+3⟩

 

 def chartDeletionEntry {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) (output input : Fin charts) : RationalResult :=
   let basis := buildArray charts (chartDeletedBasis safe input)
   let projected := chartProjection feature allowed basis.data output
   let result := negate projected.data
   ⟨result.data,basis.work+projected.work+result.work+3⟩

 

 structure ChartMatrixResult (charts : ℕ) where
   data : Vector (Vector RationalBits charts) charts
   work : ℕ

 def chartDeletionMatrix {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (safe : Vector Bool charts) : ChartMatrixResult charts :=
   let rows := Vector.ofFn (fun output => buildArray charts (chartDeletionEntry feature allowed safe output))
   ⟨rows.map (fun row => row.data),(∑ output,(rows.get output).work)+2*charts+2⟩

 

 

 

 

 

end AFT.BinaryArithmetic.RationalBits

end

section


















/-! Explicit bit-operation budgets for materializing chart inputs. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def spikeWork (charts : ℕ) : ℕ :=
   3*charts+charts*(3*charts+6)+120*(charts+1)^2+2*primitiveWorkBound charts+12

 def deletionEntryWork (charts colors features : ℕ) : ℕ :=
   charts*(9*charts+10)+projectionWork charts colors features 0+primitiveWorkBound 0+5

 def deletionMatrixWork (charts colors features : ℕ) : ℕ :=
   charts*(charts*(deletionEntryWork charts colors features+2)+4)+2

 def defectWork (charts colors features atomBits : ℕ) : ℕ :=
   finiteSumWork features (chartFeatureHeight charts colors (2*charts))
     (featureWork charts colors (2*charts)+12*features+charts+colors+13)+
   primitiveWorkBound (atomBits+features*(chartFeatureHeight charts colors (2*charts)+1))+2

 

 

 

 

 

 

end AFT.BinaryArithmetic.RationalBits

end

section


















namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.RationalBits
end AFT.BinaryArithmetic.RationalBits
namespace AFT.BinaryArithmetic.RationalBits.chartDefect
end AFT.BinaryArithmetic.RationalBits.chartDefect
namespace AFT.BinaryArithmetic.RationalBits.chartInterior
end AFT.BinaryArithmetic.RationalBits.chartInterior
namespace AFT.BinaryArithmetic.RationalBits.chartWeightEntry
end AFT.BinaryArithmetic.RationalBits.chartWeightEntry
namespace AFT.BinaryArithmetic.RationalBits.markedChartWeight
end AFT.BinaryArithmetic.RationalBits.markedChartWeight



/-! Polynomial binary work of the complete finite marked-chart repair. -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics AFT.BoundaryCalibration

 def chartEntryBits (charts atomBits iterateBits : ℕ) : ℕ :=
   2*iterateBits+2*atomBits+3*charts+10

 def chartWeightEntryWork (charts atomBits iterateBits : ℕ) : ℕ :=
   12*charts+40+10*primitiveWorkBound (chartEntryBits charts atomBits iterateBits)+60*(charts+1)^2

 def markedChartWork (charts colors features atomBits steps : ℕ) : ℕ :=
   charts*(spikeWork charts+2)+2+deletionMatrixWork charts colors features+
     charts*(defectWork charts colors features atomBits+2)+2+
     2*(steps*iterationWorkStep charts (chartStoredHeight charts colors features atomBits) steps+2*charts+2)+
     charts*(chartWeightEntryWork charts atomBits (chartIterateHeight charts colors features atomBits steps)+2)+
     2*charts+9

 

 

 

end AFT.BinaryArithmetic.RationalBits

end

section




















/-! Literal polynomial bounds for the complete binary chart repair. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.BoundaryCalibration AFT.RationalNumerics

noncomputable def chartExpectationHeightPolynomial (charts bits : Polynomial ℕ) : Polynomial ℕ :=
  charts*(bits+1)+charts

noncomputable def chartConditionalHeightPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  colors+chartExpectationHeightPolynomial charts bits

noncomputable def chartFeatureHeightPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  chartConditionalHeightPolynomial charts colors bits+colors*(chartConditionalHeightPolynomial charts colors bits+1)+colors+1

noncomputable def chartProjectionHeightPolynomial (charts colors features bits : Polynomial ℕ) : Polynomial ℕ :=
  chartExpectationHeightPolynomial charts bits+features*(chartFeatureHeightPolynomial charts colors bits+1)+1

noncomputable def chartStoredHeightPolynomial (charts colors features atomBits : Polynomial ℕ) : Polynomial ℕ :=
  chartProjectionHeightPolynomial charts colors features 0+atomBits+features*(chartFeatureHeightPolynomial charts colors (2*charts)+1)

noncomputable def chartIterateHeightPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  steps*((3*(charts^2+charts)+1)*chartStoredHeightPolynomial charts colors features atomBits+charts+1)

noncomputable def finiteSumWorkPolynomial (count bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  count*(termWork+primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2

noncomputable def expectationWorkPolynomial (charts bits termWork : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial charts bits termWork+60*(charts+1)^2+
    2*primitiveWorkPolynomial ((charts+1)*(bits+1)+charts+1)+5

noncomputable def conditionalWorkPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  expectationWorkPolynomial charts bits (6*charts+6*colors+10)+60*(colors+1)^2+
    primitiveWorkPolynomial (chartConditionalHeightPolynomial charts colors bits+1)+3

noncomputable def featureWorkPolynomial (charts colors bits : Polynomial ℕ) : Polynomial ℕ :=
  let H := chartConditionalHeightPolynomial charts colors bits
  conditionalWorkPolynomial charts colors bits+
    finiteSumWorkPolynomial colors H (conditionalWorkPolynomial charts colors bits+3*colors+5)+
    colors*(3*colors+6)+60*(colors+1)^2+3*charts+3*colors+
    2*primitiveWorkPolynomial (colors*(H+1)+colors+1)+
    2*primitiveWorkPolynomial (chartFeatureHeightPolynomial charts colors bits)+30

noncomputable def projectionWorkPolynomial (charts colors features bits : Polynomial ℕ) : Polynomial ℕ :=
  expectationWorkPolynomial charts bits (3*charts+3)+
    finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors bits)
      (featureWorkPolynomial charts colors bits+6*features+charts+colors+9)+
    primitiveWorkPolynomial (chartProjectionHeightPolynomial charts colors features bits)+3

noncomputable def spikeWorkPolynomial (charts : Polynomial ℕ) : Polynomial ℕ :=
  3*charts+charts*(3*charts+6)+120*(charts+1)^2+2*primitiveWorkPolynomial charts+12

noncomputable def deletionEntryWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  charts*(9*charts+10)+projectionWorkPolynomial charts colors features 0+primitiveWorkPolynomial 0+5

noncomputable def deletionMatrixWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  charts*(charts*(deletionEntryWorkPolynomial charts colors features+2)+4)+2

noncomputable def defectWorkPolynomial (charts colors features atomBits : Polynomial ℕ) : Polynomial ℕ :=
  finiteSumWorkPolynomial features (chartFeatureHeightPolynomial charts colors (2*charts))
     (featureWorkPolynomial charts colors (2*charts)+12*features+charts+colors+13)+
   primitiveWorkPolynomial (atomBits+features*(chartFeatureHeightPolynomial charts colors (2*charts)+1))+2

noncomputable def iterationBitsPolynomial (count bits limit : Polynomial ℕ) : Polynomial ℕ :=
  bits+limit*((3*(count^2+count)+1)*bits+count+1)

noncomputable def matrixRowWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(10*count+13+primitiveWorkPolynomial bits+primitiveWorkPolynomial ((count+1)*(2*bits+1))+2)+2

noncomputable def matrixApplyWorkPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(matrixRowWorkPolynomial count bits+2)+2

noncomputable def iterationWorkStepPolynomial (count bits limit : Polynomial ℕ) : Polynomial ℕ :=
  matrixApplyWorkPolynomial count (iterationBitsPolynomial count bits limit)+
    count*(6*count+13+2*primitiveWorkPolynomial ((count+1)*(2*iterationBitsPolynomial count bits limit+1)))+5

noncomputable def chartEntryBitsPolynomial (charts atomBits iterateBits : Polynomial ℕ) : Polynomial ℕ :=
  2*iterateBits+2*atomBits+3*charts+10

noncomputable def chartWeightEntryWorkPolynomial (charts atomBits iterateBits : Polynomial ℕ) : Polynomial ℕ :=
  12*charts+40+10*primitiveWorkPolynomial (chartEntryBitsPolynomial charts atomBits iterateBits)+60*(charts+1)^2

noncomputable def markedChartWorkPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  charts*(spikeWorkPolynomial charts+2)+2+deletionMatrixWorkPolynomial charts colors features+
     charts*(defectWorkPolynomial charts colors features atomBits+2)+2+
     2*(steps*iterationWorkStepPolynomial charts (chartStoredHeightPolynomial charts colors features atomBits) steps+2*charts+2)+
     charts*(chartWeightEntryWorkPolynomial charts atomBits (chartIterateHeightPolynomial charts colors features atomBits steps)+2)+
     2*charts+9

@[simp] theorem chartExpectationHeightPolynomial_eval (charts bits : Polynomial ℕ) (n : ℕ) :
    (chartExpectationHeightPolynomial charts bits).eval n=chartExpectationHeight (charts.eval n) (bits.eval n) := by
  simp [chartExpectationHeightPolynomial,chartExpectationHeight]

@[simp] theorem chartConditionalHeightPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (chartConditionalHeightPolynomial charts colors bits).eval n=chartConditionalHeight (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [chartConditionalHeightPolynomial,chartConditionalHeight]

@[simp] theorem chartFeatureHeightPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (chartFeatureHeightPolynomial charts colors bits).eval n=chartFeatureHeight (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [chartFeatureHeightPolynomial,chartFeatureHeight]

@[simp] theorem chartProjectionHeightPolynomial_eval (charts colors features bits : Polynomial ℕ) (n : ℕ) :
    (chartProjectionHeightPolynomial charts colors features bits).eval n=chartProjectionHeight (charts.eval n) (colors.eval n) (features.eval n) (bits.eval n) := by
  simp [chartProjectionHeightPolynomial,chartProjectionHeight]

@[simp] theorem chartStoredHeightPolynomial_eval (charts colors features atomBits : Polynomial ℕ) (n : ℕ) :
    (chartStoredHeightPolynomial charts colors features atomBits).eval n=chartStoredHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) := by
  simp [chartStoredHeightPolynomial,chartStoredHeight]

@[simp] theorem chartIterateHeightPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (chartIterateHeightPolynomial charts colors features atomBits steps).eval n=chartIterateHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [chartIterateHeightPolynomial,chartIterateHeight]

@[simp] theorem finiteSumWorkPolynomial_eval (count bits termWork : Polynomial ℕ) (n : ℕ) :
    (finiteSumWorkPolynomial count bits termWork).eval n=finiteSumWork (count.eval n) (bits.eval n) (termWork.eval n) := by
  simp [finiteSumWorkPolynomial,finiteSumWork]

@[simp] theorem expectationWorkPolynomial_eval (charts bits termWork : Polynomial ℕ) (n : ℕ) :
    (expectationWorkPolynomial charts bits termWork).eval n=expectationWork (charts.eval n) (bits.eval n) (termWork.eval n) := by
  simp [expectationWorkPolynomial,expectationWork]

@[simp] theorem conditionalWorkPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (conditionalWorkPolynomial charts colors bits).eval n=conditionalWork (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [conditionalWorkPolynomial,conditionalWork]

@[simp] theorem featureWorkPolynomial_eval (charts colors bits : Polynomial ℕ) (n : ℕ) :
    (featureWorkPolynomial charts colors bits).eval n=featureWork (charts.eval n) (colors.eval n) (bits.eval n) := by
  simp [featureWorkPolynomial,featureWork]

@[simp] theorem projectionWorkPolynomial_eval (charts colors features bits : Polynomial ℕ) (n : ℕ) :
    (projectionWorkPolynomial charts colors features bits).eval n=projectionWork (charts.eval n) (colors.eval n) (features.eval n) (bits.eval n) := by
  simp [projectionWorkPolynomial,projectionWork]

@[simp] theorem spikeWorkPolynomial_eval (charts : Polynomial ℕ) (n : ℕ) :
    (spikeWorkPolynomial charts).eval n=spikeWork (charts.eval n) := by
  simp [spikeWorkPolynomial,spikeWork]

@[simp] theorem deletionEntryWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (deletionEntryWorkPolynomial charts colors features).eval n=deletionEntryWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [deletionEntryWorkPolynomial,deletionEntryWork]

@[simp] theorem deletionMatrixWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (deletionMatrixWorkPolynomial charts colors features).eval n=deletionMatrixWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [deletionMatrixWorkPolynomial,deletionMatrixWork]

@[simp] theorem defectWorkPolynomial_eval (charts colors features atomBits : Polynomial ℕ) (n : ℕ) :
    (defectWorkPolynomial charts colors features atomBits).eval n=defectWork (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) := by
  simp [defectWorkPolynomial,defectWork]

@[simp] theorem iterationBitsPolynomial_eval (count bits limit : Polynomial ℕ) (n : ℕ) :
    (iterationBitsPolynomial count bits limit).eval n=iterationBits (count.eval n) (bits.eval n) (limit.eval n) := by
  simp [iterationBitsPolynomial,iterationBits]

@[simp] theorem matrixRowWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (matrixRowWorkPolynomial count bits).eval n=matrixRowWork (count.eval n) (bits.eval n) := by
  simp [matrixRowWorkPolynomial,matrixRowWork]

@[simp] theorem matrixApplyWorkPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (matrixApplyWorkPolynomial count bits).eval n=matrixApplyWork (count.eval n) (bits.eval n) := by
  simp [matrixApplyWorkPolynomial,matrixApplyWork]

@[simp] theorem iterationWorkStepPolynomial_eval (count bits limit : Polynomial ℕ) (n : ℕ) :
    (iterationWorkStepPolynomial count bits limit).eval n=iterationWorkStep (count.eval n) (bits.eval n) (limit.eval n) := by
  simp [iterationWorkStepPolynomial,iterationWorkStep]

@[simp] theorem chartEntryBitsPolynomial_eval (charts atomBits iterateBits : Polynomial ℕ) (n : ℕ) :
    (chartEntryBitsPolynomial charts atomBits iterateBits).eval n=chartEntryBits (charts.eval n) (atomBits.eval n) (iterateBits.eval n) := by
  simp [chartEntryBitsPolynomial,chartEntryBits]

@[simp] theorem chartWeightEntryWorkPolynomial_eval (charts atomBits iterateBits : Polynomial ℕ) (n : ℕ) :
    (chartWeightEntryWorkPolynomial charts atomBits iterateBits).eval n=chartWeightEntryWork (charts.eval n) (atomBits.eval n) (iterateBits.eval n) := by
  simp [chartWeightEntryWorkPolynomial,chartWeightEntryWork]

@[simp] theorem markedChartWorkPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (markedChartWorkPolynomial charts colors features atomBits steps).eval n=markedChartWork (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [markedChartWorkPolynomial,markedChartWork]





end AFT.BinaryArithmetic.RationalBits

end

section





















/-! Safe and marked-fiber masks built by real sequential array scans. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration

 def chartAllowedAt {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (point : Fin charts) (index : Fin features) : CountedValue Bool :=
   let frow := readVector (Vector.replicate charts 0) feature index
   let arow := readVector (Vector.replicate colors false) allowed index
   let color := readVector 0 frow.value point
   let result := readVector false arow.value color.value
   ⟨result.value,frow.work+arow.work+color.work+result.work+charts+colors+4⟩

 

 

 def safeChart {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (point : Fin charts) : CountedValue Bool :=
   let all := countedFinAll features (chartAllowedAt feature allowed point)
   let s := readVector 0 scale point
   let isZero := equalCounter s.value.val 0
   ⟨!isZero.value && all.value,all.work+s.work+isZero.work+features*features+2*features+4⟩

 

 def chartAllowedExceptAt {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (marked : Fin features) (point : Fin charts) (index : Fin features) : CountedValue Bool :=
   let same := equalCounter index.val marked.val
   let result := chartAllowedAt feature allowed point index
   ⟨same.value || result.value,same.work+result.work+2⟩

 

 def fiberChart {charts colors features : ℕ} [NeZero colors]
     (feature : Vector (Vector (Fin colors) charts) features) (allowed : Vector (Vector Bool colors) features)
     (scale : Vector (Fin colors) charts) (marked : Fin features) (mark : Fin colors) (point : Fin charts) : CountedValue Bool :=
   let all := countedFinAll features (chartAllowedExceptAt feature allowed marked point)
   let s := readVector 0 scale point
   let isZero := equalCounter s.value.val 0
   let row := readVector (Vector.replicate charts 0) feature marked
   let color := readVector 0 row.value point
   let same := equalCounter color.value.val mark.val
   ⟨same.value && !isZero.value && all.value,
     all.work+s.work+isZero.work+row.work+color.work+same.work+features*features+2*features+charts+7⟩

 

 def supportWork (charts colors features : ℕ) : ℕ :=
   features*(12*features+4*charts+4*colors+22)+features*features+5*features+7*charts+9*colors+32

 

 

end AFT.BinaryArithmetic

end

section









/-! # Actual control parameters for the Gaussian series

Scale and precision are computed by binary ceiling and explicit conversion
into bounded unary loop counters. No decoded rational is inspected at run
time. The semantic ceiling occurs only in the correctness and cost bounds.
-/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

structure ExponentialControl where
  clipped : RationalBits
  scaleDigits : List Bool
  scale : ℕ
  work : ℕ

def prepareExponential (argument : RationalBits) : ExponentialControl :=
  let clipped := argument.maxZero
  let ceiling := clipped.data.ceilNatural
  let counter := readCounter ceiling.digits
  let doubled := doubleCounter counter.count
  ⟨clipped.data,true::ceiling.digits,doubled.count.succ,
    clipped.work+ceiling.work+counter.work+doubled.work+5⟩

theorem prepareExponential_clipped (argument : RationalBits) :
    (prepareExponential argument).clipped.decode=max argument.decode 0 := by
  simp only [prepareExponential,RationalBits.maxZero_value]

theorem prepareExponential_digits (argument : RationalBits) :
    value (prepareExponential argument).scaleDigits=expScale argument.decode := by
  simp only [prepareExponential,value,Bool.toNat_true,RationalBits.ceilNatural_value,
    RationalBits.maxZero_value,expScale]
  omega

theorem prepareExponential_scale (argument : RationalBits) :
    (prepareExponential argument).scale=expScale argument.decode := by
  simp only [prepareExponential,doubleCounter_value,readCounter_value,RationalBits.ceilNatural_value,
    RationalBits.maxZero_value,expScale]



/-- The integer guard for the finite pi series, with all counter work. -/
def prepareGaussianPrecision (ratio : RationalBits) (bits : ℕ) : UnaryCounterResult :=
  let ceiling := ratio.ceilNatural
  let guard := readCounter ceiling.digits
  let total := addCounter bits guard.count
  ⟨total.count.succ,ceiling.work+guard.work+total.work+4⟩

theorem prepareGaussianPrecision_value (ratio : RationalBits) (bits : ℕ) :
    (prepareGaussianPrecision ratio bits).count=bits+⌈ratio.decode⌉₊+1 := by
  simp only [prepareGaussianPrecision,addCounter_value,readCounter_value,RationalBits.ceilNatural_value]



end AFT.BinaryArithmetic

end

section







/-! # The actual binary range-reduced exponential evaluator

All data arithmetic calls canonical binary rational programs. Control
parameters use binary ceiling and explicit unary-counter operations.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def exponential (argument : RationalBits) (bits : ℕ) : RationalResult :=
  let control := prepareExponential argument
  let scale := ofNat control.scaleDigits
  let reduced := quotient control.clipped scale.data
  let count := addCounter bits control.scale
  let polynomial := taylor reduced.data count.count.succ
  let inv := inverse polynomial.data
  let result := power inv.data control.scale
  ⟨result.data,control.work+scale.work+reduced.work+count.work+
    polynomial.work+inv.work+result.work+8⟩

theorem exponential_value (argument : RationalBits) (bits : ℕ) :
    (exponential argument bits).data.decode=expNegApprox argument.decode bits := by
  simp only [exponential,power_value,inverse_value,taylor_value,quotient_value,ofNat_value,
    prepareExponential_digits,prepareExponential_clipped,addCounter_value,prepareExponential_scale,
    expNegApprox,expNegScaled]

def exponentialSeriesHeight (height scale bits : ℕ) : ℕ :=
  (bits+scale+1)*((bits+scale+1)*(height+scale)+(bits+scale+1)^2+1)

def exponentialWork (height scale bits : ℕ) : ℕ :=
  900*(height+2)^2+9*scale+8*(height+2)+2*bits+100+
    2*primitiveWorkBound (height+scale)+seriesWork (height+scale) (bits+scale+1)+
    primitiveWorkBound (exponentialSeriesHeight height scale bits)+
    scale*(primitiveWorkBound (exponentialSeriesHeight height scale bits*(scale+1))+2)

attribute [local irreducible] prepareExponential ofNat quotient taylor inverse power maxZero



end AFT.BinaryArithmetic.RationalBits

end

section







/-! # Actual Gaussian input construction

The dimension and window coordinate are bounded unary counters. Explicit
counter arithmetic and the ripple encoder produce their rational binary
representations; an arbitrary rational encoder is never called.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def ofUnaryInteger : ℤ → RationalResult
  | .ofNat count =>
      let result := ofCounter count
      ⟨result.data,result.work+1⟩
  | .negSucc count =>
      let magnitude := ofCounter count.succ
      let result := negate magnitude.data
      ⟨result.data,magnitude.work+result.work+3⟩

theorem ofUnaryInteger_value (integer : ℤ) : (ofUnaryInteger integer).data.decode=(integer : ℚ) := by
  cases integer with
  | ofNat count => simp only [ofUnaryInteger,ofCounter_value,Int.ofNat_eq_natCast,Int.cast_natCast]
  | negSucc count => simp only [ofUnaryInteger,negate_value,ofCounter_value,Int.cast_negSucc,Nat.cast_succ]









end AFT.BinaryArithmetic.RationalBits

end

section





/-! # The binary evaluator of the actual rational Gaussian approximation

The finite pi and exponential series, adaptive precision, range reduction,
and every rational primitive execute on the stored binary representation.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics

def gaussianFromRatio (ratio : RationalBits) (bits : ℕ) : RationalResult :=
  let precision := prepareGaussianPrecision ratio bits
  let piValue := pi precision.count
  let argument := multiply piValue.data ratio
  let result := exponential argument.data bits.succ
  ⟨result.data,precision.work+piValue.work+argument.work+result.work+5⟩

theorem gaussianFromRatio_value (ratio : RationalBits) (bits : ℕ) :
    (gaussianFromRatio ratio bits).data.decode=
      expNegApprox (piApprox (bits+⌈ratio.decode⌉₊+1)*ratio.decode) (bits+1) := by
  simp only [gaussianFromRatio,exponential_value,multiply_value,pi_value,prepareGaussianPrecision_value]

def gaussian (squaredWidth point : RationalBits) (bits : ℕ) : RationalResult :=
  let square := multiply point point
  let ratio := quotient square.data squaredWidth
  let result := gaussianFromRatio ratio.data bits
  ⟨result.data,square.work+ratio.work+result.work+4⟩

theorem gaussian_value (squaredWidth point : RationalBits) (integerPoint : ℤ) (bits : ℕ)
    (hp : point.decode=(integerPoint : ℚ)) :
    (gaussian squaredWidth point bits).data.decode=gaussianApprox squaredWidth.decode integerPoint bits := by
  simp only [gaussian,gaussianFromRatio_value,quotient_value,multiply_value,hp,gaussianApprox,gaussianGuard,
    gaussianRatio,pow_two]

def gaussianRatioWork (height guard scale bits : ℕ) : ℕ :=
  900*(height+2)^2+6*guard+4*(height+1)+2*bits+12+
    piWork (bits+guard+1)+primitiveWorkBound (piHeight (bits+guard+1)+height)+
    exponentialWork (piHeight (bits+guard+1)+height) scale (bits+1)



def gaussianWork (widthHeight pointHeight guard scale bits : ℕ) : ℕ :=
  primitiveWorkBound pointHeight+2*primitiveWorkBound (2*pointHeight+widthHeight)+
    gaussianRatioWork (2*pointHeight+widthHeight) guard scale bits+6



end AFT.BinaryArithmetic.RationalBits

end

section







/-! Explicit natural-coefficient polynomial bounds for the actual binary
Gaussian evaluator, including its precision and scale control. -/
namespace AFT.BinaryArithmetic.RationalBits
open Polynomial AFT.RationalNumerics

noncomputable def exponentialSeriesHeightPolynomial (height scale bits : Polynomial ℕ) : Polynomial ℕ :=
  (bits+scale+1)*((bits+scale+1)*(height+scale)+(bits+scale+1)^2+1)
noncomputable def exponentialWorkPolynomial (height scale bits : Polynomial ℕ) : Polynomial ℕ :=
  900*(height+2)^2+9*scale+8*(height+2)+2*bits+100+
    2*primitiveWorkPolynomial (height+scale)+seriesWorkPolynomial (height+scale) (bits+scale+1)+
    primitiveWorkPolynomial (exponentialSeriesHeightPolynomial height scale bits)+
    scale*(primitiveWorkPolynomial (exponentialSeriesHeightPolynomial height scale bits*(scale+1))+2)
noncomputable def gaussianRatioWorkPolynomial (height guard scale bits : Polynomial ℕ) : Polynomial ℕ :=
  900*(height+2)^2+6*guard+4*(height+1)+2*bits+12+
    piWorkPolynomial (bits+guard+1)+primitiveWorkPolynomial (piHeightPolynomial (bits+guard+1)+height)+
    exponentialWorkPolynomial (piHeightPolynomial (bits+guard+1)+height) scale (bits+1)
noncomputable def gaussianWorkPolynomial (widthHeight pointHeight guard scale bits : Polynomial ℕ) : Polynomial ℕ :=
  primitiveWorkPolynomial pointHeight+2*primitiveWorkPolynomial (2*pointHeight+widthHeight)+
    gaussianRatioWorkPolynomial (2*pointHeight+widthHeight) guard scale bits+6

@[simp] theorem exponentialSeriesHeightPolynomial_eval (height scale bits : Polynomial ℕ) (n : ℕ) :
    (exponentialSeriesHeightPolynomial height scale bits).eval n=
      exponentialSeriesHeight (height.eval n) (scale.eval n) (bits.eval n) := by
  simp only [exponentialSeriesHeightPolynomial,exponentialSeriesHeight,eval_mul,eval_add,eval_pow,eval_one]
@[simp] theorem exponentialWorkPolynomial_eval (height scale bits : Polynomial ℕ) (n : ℕ) :
    (exponentialWorkPolynomial height scale bits).eval n=
      exponentialWork (height.eval n) (scale.eval n) (bits.eval n) := by
  simp only [exponentialWorkPolynomial,exponentialWork,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,seriesWorkPolynomial_eval,exponentialSeriesHeightPolynomial_eval]
@[simp] theorem gaussianRatioWorkPolynomial_eval (height guard scale bits : Polynomial ℕ) (n : ℕ) :
    (gaussianRatioWorkPolynomial height guard scale bits).eval n=
      gaussianRatioWork (height.eval n) (guard.eval n) (scale.eval n) (bits.eval n) := by
  simp only [gaussianRatioWorkPolynomial,gaussianRatioWork,eval_mul,eval_add,eval_pow,eval_ofNat,eval_one,
    primitiveWorkPolynomial_eval,piWorkPolynomial_eval,piHeightPolynomial_eval,exponentialWorkPolynomial_eval]
@[simp] theorem gaussianWorkPolynomial_eval (widthHeight pointHeight guard scale bits : Polynomial ℕ) (n : ℕ) :
    (gaussianWorkPolynomial widthHeight pointHeight guard scale bits).eval n=
      gaussianWork (widthHeight.eval n) (pointHeight.eval n) (guard.eval n) (scale.eval n) (bits.eval n) := by
  simp only [gaussianWorkPolynomial,gaussianWork,eval_mul,eval_add,eval_ofNat,
    primitiveWorkPolynomial_eval,gaussianRatioWorkPolynomial_eval]







end AFT.BinaryArithmetic.RationalBits

end

section




















/-! A real sequential Boolean scan for the legal-chart fallback. No finite-set
membership or minimum search is delegated to a constant-time oracle. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration AFT.BetaReference

def firstTrue : List Bool → CountedValue (Option ℕ)
  | [] => ⟨none,1⟩
  | true::_ => ⟨some 0,2⟩
  | false::tail =>
    let remaining := firstTrue tail
    ⟨remaining.value.map Nat.succ,remaining.work+3⟩

theorem firstTrue_value (input : List Bool) :
    (firstTrue input).value=input.findIdx? id := by
  induction input with
  | nil => rfl
  | cons head tail ih => cases head <;> simp [firstTrue,List.findIdx?_cons,ih]



theorem firstTrue_lt {input : List Bool} {index : ℕ}
    (h : (firstTrue input).value=some index) : index < input.length :=
  (List.findIdx?_eq_some_iff_findIdx_eq.mp ((firstTrue_value input).symm.trans h)).1

def legalChartScan {charts : ℕ} (mask : Vector Bool charts)
    (point : Fin charts) : CountedNatural :=
  let current := readVector false mask point
  if current.value then ⟨point.val,current.work+1⟩ else
    let found := firstTrue mask.toList
    ⟨found.value.getD 0,current.work+found.work+charts+3⟩

theorem legalChartScan_lt {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) : (legalChartScan mask point).value < charts := by
  unfold legalChartScan
  try dsimp only
  split_ifs
  · exact point.isLt
  · dsimp only
    cases hf : (firstTrue mask.toList).value with
    | none => exact NeZero.pos charts
    | some index => simpa only [Option.getD_some,Vector.length_toList] using firstTrue_lt hf

def binaryLegalChartIndex {charts : ℕ} [NeZero charts] (mask : Vector Bool charts)
    (point : Fin charts) : CountedValue (Fin charts) :=
  let selected := legalChartScan mask point
  ⟨⟨selected.value,legalChartScan_lt mask point⟩,selected.work⟩





end AFT.BinaryArithmetic

end

section


















/-! # Materialized binary rational matrix arrays -/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics
open scoped BigOperators

structure MatrixResult (count : ℕ) where
  data : Vector (Vector RationalBits count) count
  work : ℕ

def buildRows (count : ℕ) (row : Fin count → ArrayResult count) : MatrixResult count :=
  let computed := Vector.ofFn row
  ⟨computed.map (fun result => result.data),(∑ index,(computed.get index).work)+2*count+2⟩

theorem buildRows_get (count : ℕ) (row : Fin count → ArrayResult count) (index : Fin count) :
    (buildRows count row).data.get index=(row index).data := by simp [buildRows]



def buildMatrix (count : ℕ) (entry : Fin count → Fin count → RationalResult) : MatrixResult count :=
  buildRows count (fun row => buildArray count (entry row))

theorem buildMatrix_get (count : ℕ) (entry : Fin count → Fin count → RationalResult) (row column : Fin count) :
    ((buildMatrix count entry).data.get row).get column=(entry row column).data := by
  simp only [buildMatrix,buildRows_get,buildArray_get]









end AFT.BinaryArithmetic.RationalBits

end

section
























/-! Public parameter generation using explicit unary loop control and binary
long division. Trial-division candidates have polynomial numerical magnitude;
large Gaussian ticket integers never enter these unary counters. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram V7Calibration Polynomial
set_option backward.isDefEq.respectTransparency false







theorem lessCounter_decide (first second : ℕ) :
    (lessCounter first second).value=decide (first<second) := by
  apply Bool.eq_iff_iff.mpr
  simp only [lessCounter_value,decide_eq_true_eq]

def binaryTrialDivisors (candidate : ℕ) : ℕ → ParameterProgram.CountedDecision
  | 0 => ⟨true,2⟩
  | length+1 =>
    let previous := binaryTrialDivisors candidate length
    let remainder := divideCounter candidate (length+2)
    ⟨previous.value && decide (remainder.remainder≠0),previous.work+remainder.work+5⟩

theorem binaryTrialDivisors_value (candidate length : ℕ) :
    (binaryTrialDivisors candidate length).value=(ParameterProgram.trialDivisors candidate length).value := by
  induction length with
  | zero => rfl
  | succ length ih =>
    simp only [binaryTrialDivisors,ParameterProgram.trialDivisors,ih,
      (divideCounter_value candidate (length+2) (by omega)).2]

theorem binaryTrialDivisors_work (candidate length : ℕ) :
    (binaryTrialDivisors candidate length).work≤2+length*(500*(candidate+length+4)^2+5) := by
  induction length with
  | zero => simp [binaryTrialDivisors]
  | succ length ih =>
    have hd := divideCounter_work candidate (length+2) (by omega)
    have hm : 500*(candidate+length+4)^2+5≤500*(candidate+(length+1)+4)^2+5 := by gcongr;omega
    have hi := ih.trans (Nat.add_le_add_left (Nat.mul_le_mul_left length hm) 2)
    have hd' : (divideCounter candidate (length+2)).work≤500*(candidate+(length+1)+4)^2 := by
      exact hd.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left (by omega) 2))
    simp only [binaryTrialDivisors]
    nlinarith

def binaryPrimeTest (candidate : ℕ) : ParameterProgram.CountedDecision :=
  let small := lessCounter candidate 2
  if small.value then ⟨false,small.work+2⟩ else
    let length := subtractCounter candidate 2
    let result := binaryTrialDivisors candidate length.count
    ⟨result.value,small.work+length.work+result.work+3⟩

theorem binaryPrimeTest_value (candidate : ℕ) :
    (binaryPrimeTest candidate).value=(ParameterProgram.primeTest candidate).value := by
  simp only [binaryPrimeTest,lessCounter_decide,decide_eq_true_eq,subtractCounter_value,
    binaryTrialDivisors_value,ParameterProgram.primeTest]
  split_ifs <;> rfl

def binaryPrimeWork (candidate : ℕ) : ℕ :=
  3*(candidate+2)+2+2*candidate+2+(2+candidate*(500*(candidate+candidate+4)^2+5))+3

theorem binaryPrimeTest_work (candidate : ℕ) : (binaryPrimeTest candidate).work≤binaryPrimeWork candidate := by
  have hs := lessCounter_work candidate 2
  have hd := subtractCounter_work_left candidate 2
  have ht := binaryTrialDivisors_work candidate (candidate-2)
  have ht' : (binaryTrialDivisors candidate (candidate-2)).work≤2+candidate*(500*(candidate+candidate+4)^2+5) := by
    apply ht.trans
    gcongr <;> omega
  simp only [binaryPrimeTest]
  split_ifs <;> simp only [subtractCounter_value]
  all_goals unfold binaryPrimeWork;omega



















end AFT.BinaryArithmetic

end

section


















/-! Literal polynomial bounds for the complete public modulus and root
population, including prime search and every binary division. -/
namespace AFT.BinaryArithmetic
open V7Calibration Polynomial
set_option backward.isDefEq.respectTransparency false

noncomputable def binaryPrimeWorkPolynomial (candidate : Polynomial ℕ) : Polynomial ℕ :=
  3*(candidate+2)+2+2*candidate+2+(2+candidate*(500*(candidate+candidate+4)^2+5))+3















end AFT.BinaryArithmetic

end

section














































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic
namespace AFT.BinaryArithmetic.binaryPoolScan
end AFT.BinaryArithmetic.binaryPoolScan
namespace AFT.BinaryArithmetic.binaryPoolScan.match_1
end AFT.BinaryArithmetic.binaryPoolScan.match_1
namespace AFT.BinaryArithmetic.binaryRunPoolScan
end AFT.BinaryArithmetic.binaryRunPoolScan
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PermutationProgram
end AFT.PermutationProgram
namespace AFT.PermutationProgram.bodyCount
end AFT.PermutationProgram.bodyCount
namespace AFT.PermutationProgram.bodyDraw
end AFT.PermutationProgram.bodyDraw
namespace AFT.PermutationProgram.vertexCount
end AFT.PermutationProgram.vertexCount
namespace AFT.PermutationProgram.vertexDraw
end AFT.PermutationProgram.vertexDraw
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! Explicit polynomial costs for the actual stored public permutations. -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits

noncomputable def binaryPermutationChoicePolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  60*(count+2)^2+primitiveWorkPolynomial (count+1)+(count+1)+
    binaryRationalDrawPolynomial (count+1) (count+1) bits+4
noncomputable def binaryPermutationRowsPolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(binaryPermutationChoicePolynomial count bits+(count+1)*(9*count+17)+5)+2

@[simp] theorem binaryPermutationChoicePolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationChoicePolynomial count bits).eval n=
      binaryPermutationChoiceWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationChoicePolynomial,binaryPermutationChoiceWork]
@[simp] theorem binaryPermutationRowsPolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationRowsPolynomial count bits).eval n=
      binaryPermutationRowsWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationRowsPolynomial,binaryPermutationRowsWork]









end AFT.BinaryArithmetic

end

section




















/-! Stored tape regrouping and actual public permutation draws. Index products
and sums are evaluated by counter programs before each sequential tape read. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

def binaryTapeCell {count bits : ℕ} (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) : CountedValue (Fin 2) :=
  let block := multiplyCounter bits row.val
  let offset := addCounter column.val block.count
  have hindex : offset.count < count*bits := by
    rw [addCounter_value,multiplyCounter_value]
    exact (finProdFinEquiv (row,column)).isLt
  let result := readVector 0 tape ⟨offset.count,hindex⟩
  ⟨result.value,block.work+offset.work+result.work+3⟩

theorem binaryTapeCell_value {count bits : ℕ} (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) :
    (binaryTapeCell tape row column).value=tape.get (finProdFinEquiv (row,column)) := by
  simp only [binaryTapeCell,readVector_value,addCounter_value,multiplyCounter_value]
  rfl

def binaryTapeCellWork (count bits : ℕ) : ℕ := bits*(2*count+3)+2*bits+3*(count*bits)+8



def binaryGroupTape (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    CountedValue (Vector (Vector (Fin 2) bits) count) :=
  storeData count (fun row => storeData bits (binaryTapeCell tape row))

theorem binaryGroupTape_value (count bits : ℕ) (tape : Vector (Fin 2) (count*bits))
    (row : Fin count) (column : Fin bits) :
    ((binaryGroupTape count bits tape).value.get row).get column=
      AFT.FiniteConditionProgram.groupBits count bits tape.get row column := by
  simp only [binaryGroupTape,storeData_get,binaryTapeCell_value,AFT.FiniteConditionProgram.groupBits,Equiv.coe_fn_mk]

def binaryGroupTapeWork (count bits : ℕ) : ℕ := count*(bits*(binaryTapeCellWork count bits+2)+4)+2



def binaryPermutationFromTape (count bits : ℕ) (tape : Vector (Fin 2) (count*bits)) :
    CountedValue (Vector (Fin count) count) :=
  let grouped := binaryGroupTape count bits tape
  let rows := binaryPermutationRows bits count (fun row => (grouped.value.get row).get)
  ⟨rows.value,grouped.work+rows.work+2⟩

theorem binaryPermutationFromTape_value (count bits : ℕ) (tape : Vector (Fin 2) (count*bits))
    (index : Fin count) :
    (binaryPermutationFromTape count bits tape).value.get index=
      AFT.PermutationProgram.draw count bits tape.get index := by
  simp only [binaryPermutationFromTape,binaryPermutationRows_value]
  have he : (fun row => ((binaryGroupTape count bits tape).value.get row).get)=
      AFT.FiniteConditionProgram.groupBits count bits tape.get := by
    funext row column
    exact binaryGroupTape_value count bits tape row column
  rw [he]
  rfl

def binaryPermutationFromTapeWork (count bits : ℕ) : ℕ :=
  binaryGroupTapeWork count bits+binaryPermutationRowsWork count bits+2



noncomputable def binaryPermutationFromTapePolynomial (count bits : Polynomial ℕ) : Polynomial ℕ :=
  count*(bits*(bits*(2*count+3)+2*bits+3*(count*bits)+10)+4)+2+
    binaryPermutationRowsPolynomial count bits+2
@[simp] theorem binaryPermutationFromTapePolynomial_eval (count bits : Polynomial ℕ) (n : ℕ) :
    (binaryPermutationFromTapePolynomial count bits).eval n=
      binaryPermutationFromTapeWork (count.eval n) (bits.eval n) := by
  simp [binaryPermutationFromTapePolynomial,binaryPermutationFromTapeWork,binaryGroupTapeWork,binaryTapeCellWork]

end AFT.BinaryArithmetic

end

section
























namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.chartIntegerLoad
end AFT.BoundaryCalibration.chartIntegerLoad
namespace AFT.BoundaryCalibration.protectedInputs
end AFT.BoundaryCalibration.protectedInputs
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualChartLegEquiv
end AFT.V7Calibration.actualChartLegEquiv
namespace AFT.V7Calibration.actualChartLegLinear
end AFT.V7Calibration.actualChartLegLinear
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualIntegerBlockLoad
end AFT.V7Calibration.actualIntegerBlockLoad
namespace AFT.V7Calibration.actualIntegerBlockLoad.match_1
end AFT.V7Calibration.actualIntegerBlockLoad.match_1
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPhysicalEdgeLinear
end AFT.V7Calibration.actualPhysicalEdgeLinear
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualQueueMask
end AFT.V7Calibration.actualQueueMask
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.legTriangularEquiv
end AFT.V7Calibration.legTriangularEquiv
namespace AFT.V7Calibration.legTriangularLinear
end AFT.V7Calibration.legTriangularLinear
namespace AFT.V7Calibration.physicalBlockEdges
end AFT.V7Calibration.physicalBlockEdges
namespace AFT.V7Calibration.physicalBlockIncidence
end AFT.V7Calibration.physicalBlockIncidence
namespace AFT.V7Calibration.physicalBlockIncidence.match_1
end AFT.V7Calibration.physicalBlockIncidence.match_1
namespace AFT.V7Calibration.physicalBlockRoot
end AFT.V7Calibration.physicalBlockRoot
namespace AFT.V7Calibration.physicalChartLinear
end AFT.V7Calibration.physicalChartLinear
namespace AFT.V7Calibration.physicalEdgeCoordinates
end AFT.V7Calibration.physicalEdgeCoordinates
namespace AFT.V7Calibration.physicalEdgePairEquiv
end AFT.V7Calibration.physicalEdgePairEquiv
namespace AFT.V7Calibration.physicalVertexSlotEquiv
end AFT.V7Calibration.physicalVertexSlotEquiv



/-! # Integer programs for the physical edge loads and initial offset -/
namespace AFT
open scoped BigOperators

 

 def physicalVertexNumberingProgram (legs rest count : ℕ) (hcount : legs*3+rest=count+1) :
    (Sigma (blockSlotsProgram legs rest))≃Fin (count+1) :=
  (blockVertexNumbering legs rest).trans (finCongr hcount)



 





namespace V7Calibration
open GaussianSource BoundaryCalibration
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 

 

 

 

 

end
end V7Calibration
end AFT

end

section

























/-! Physical initial loads and the shared queue injection are generated from
stored chart/baseline/center data using their actual arithmetic block addresses. -/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

 def IntegerBits.one : IntegerBits := ⟨false,[true]⟩
 @[simp] theorem IntegerBits.one_value : IntegerBits.one.decode=1 := rfl

 def binaryPhysicalVertex (legs rest count : ℕ) (hvertex : legs*3+rest=count+1)
     (vertex : Fin (count+1)) : CountedValue (Sigma (blockSlotsProgram legs rest)) :=
   binaryVertexCode legs rest (Fin.cast hvertex.symm vertex)

 

 

 

 

 

 

 

 

 

 

 

 


 

 

 

 

 

 

 

 

end AFT.BinaryArithmetic

end

section





















/-! Explicit loop dimensions, marked address and rational spike coefficient. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalRejectionProgram

 structure ProtectedDimensions where
   charts : ℕ
   features : ℕ
   work : ℕ

 def protectedDimensions (cutoff modulus : ℕ) : ProtectedDimensions :=
   let doubled := doubleCounter cutoff
   let features := multiplyCounter doubled.count.succ doubled.count.succ
   let square := multiplyCounter modulus modulus
   let charts := multiplyCounter modulus square.count
   ⟨charts.count,features.count,doubled.work+features.work+square.work+charts.work+5⟩

 theorem protectedDimensions_values (cutoff modulus : ℕ) :
     (protectedDimensions cutoff modulus).charts=modulus*(modulus*modulus) ∧
       (protectedDimensions cutoff modulus).features=(2*cutoff+1)*(2*cutoff+1) := by
   simp [protectedDimensions,doubleCounter_value,multiplyCounter_value,Nat.succ_eq_add_one]

 def protectedDimensionsWork (cutoff modulus : ℕ) : ℕ :=
   3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     modulus*(2*modulus+3)+1+modulus*(2*(modulus*modulus)+3)+1+5

 

 def protectedMarkAddress (cutoff : ℕ) : UnaryCounterResult :=
   let doubled := doubleCounter cutoff
   let product := multiplyCounter doubled.count.succ cutoff
   let total := addCounter cutoff product.count
   ⟨total.count,doubled.work+product.work+total.work+4⟩

 theorem protectedMarkAddress_value (cutoff : ℕ) :
     (protectedMarkAddress cutoff).count=cutoff+(2*cutoff+1)*cutoff := by
   simp only [protectedMarkAddress,addCounter_value,multiplyCounter_value,doubleCounter_value]

 theorem protectedMarkAddress_lt (cutoff : ℕ) :
     (protectedMarkAddress cutoff).count<(2*cutoff+1)*(2*cutoff+1) := by
   rw [protectedMarkAddress_value];nlinarith

 def protectedMark (cutoff : ℕ) : CountedValue (Fin ((2*cutoff+1)*(2*cutoff+1))) :=
   let result := protectedMarkAddress cutoff
   ⟨⟨result.count,protectedMarkAddress_lt cutoff⟩,result.work⟩

 


 

 

 

end AFT.BinaryArithmetic

end

section



















/-! The actual rational atom coefficient, with binary work and height. -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics

 def protectedAtomHeight (cutoff : ℕ) : ℕ := 100*((2*cutoff+1)*(2*cutoff+1))
 def protectedAtomWork (cutoff : ℕ) : ℕ :=
   3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     100*(2*((2*cutoff+1)*(2*cutoff+1))+3)+1+
     60*(protectedAtomHeight cutoff+1)^2+2*RationalBits.primitiveWorkBound (protectedAtomHeight cutoff)+7

 

 

end AFT.BinaryArithmetic

end

section



















/-! Bit costs of the actual palette predicate, including signed endpoints. -/
namespace AFT.BinaryArithmetic

 def protectedPaletteWork (cutoff modulus input color boundaryBits baselineBits : ℕ) : ℕ :=
   3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
     50*(2*cutoff+2)^2+50*(cutoff+1)^2+50*(modulus+1)^2+50*(color+1)^2+
     200*(boundaryBits+baselineBits+3*cutoff+modulus+color+10)+200

 

end AFT.BinaryArithmetic

end

section

























/-! Complete public chart metadata on stored bits. Dimensions are calculated
by the explicit counter program before materializing arrays; proof casts
only identify its addresses with the specification. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration

 structure BinaryPublicChartMetadata (charts colors features : ℕ) where
   feature : Vector (Vector (Fin colors) charts) features
   allowed : Vector (Vector Bool colors) features
   scale : Vector (Fin colors) charts
   safe : Vector Bool charts
   fiber : Vector Bool charts
   legal : Vector Bool charts

 def protectedMetadataCore (cutoff modulus charts features : ℕ) [NeZero modulus]
     (hcharts : charts=modulus*(modulus*modulus)) (hfeatures : features=(2*cutoff+1)*(2*cutoff+1))
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     CountedValue (BinaryPublicChartMetadata charts modulus features) :=
   let feature := storeData features (fun index => storeData charts (fun point =>
     protectedFeature cutoff modulus (index.cast hfeatures) (point.cast hcharts)))
   let allowed := storeData features (fun index => storeData modulus (fun color =>
     protectedPalette cutoff modulus boundarySign baselineSign boundary baseline index.val color.val))
   let scale := storeData charts (fun point => protectedScale modulus (point.cast hcharts))
   let marked := protectedMark cutoff
   let markedIndex := marked.value.cast hfeatures.symm
   let safe := storeData charts (safeChart feature.value allowed.value scale.value)
   let fiber := storeData charts (fiberChart feature.value allowed.value scale.value markedIndex mark)
   ⟨⟨feature.value,allowed.value,scale.value,safe.value,fiber.value,safe.value.zipWith Bool.or fiber.value⟩,
     feature.work+allowed.work+scale.work+marked.work+safe.work+fiber.work+4*charts+8⟩

 

 

 

 

 def protectedMetadata (cutoff modulus : ℕ) [NeZero modulus]
     (boundarySign baselineSign : Bool) (boundary baseline : List Bool) (mark : Fin modulus) :
     CountedValue (BinaryPublicChartMetadata (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1))) :=
   let dimensions := protectedDimensions cutoff modulus
   let result := protectedMetadataCore cutoff modulus dimensions.charts dimensions.features
     (protectedDimensions_values cutoff modulus).1 (protectedDimensions_values cutoff modulus).2
     boundarySign baselineSign boundary baseline mark
   ⟨cast (by rw [(protectedDimensions_values cutoff modulus).1,(protectedDimensions_values cutoff modulus).2]) result.value,
     dimensions.work+result.work+2⟩

 


end AFT.BinaryArithmetic

end

section



















/-! Cost of all materialized public chart metadata, without field or lookup
oracles. Every bound is a polynomial in the displayed dimensions and lengths. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram

 

 

 

 def protectedMetadataCoreWork (cutoff modulus charts features boundaryBits baselineBits : ℕ) : ℕ :=
   features*(charts*(protectedFeatureWork cutoff modulus features charts+2)+4)+2+
     features*(modulus*(protectedPaletteWork cutoff modulus features modulus boundaryBits baselineBits+2)+4)+2+
     charts*(protectedScaleWork modulus charts+2)+2+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+
     2*(charts*(supportWork charts modulus features+2)+2)+4*charts+8

 

 def protectedMetadataWork (cutoff modulus boundaryBits baselineBits : ℕ) : ℕ :=
   protectedDimensionsWork cutoff modulus+
     protectedMetadataCoreWork cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) boundaryBits baselineBits+2

 

end AFT.BinaryArithmetic

end

section





















namespace AFT
end AFT
namespace AFT.BinaryArithmetic
end AFT.BinaryArithmetic





/-! The original actual protected-chart weights, evaluated solely on bits. -/
namespace AFT.BinaryArithmetic
open AFT.BoundaryCalibration AFT.RationalNumerics RationalBits

 

 

 def protectedChartWeightHeight (cutoff modulus steps : ℕ) : ℕ :=
   chartWeightHeight (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeight cutoff) steps

 

 def protectedChartWeightWork (cutoff modulus boundaryBits baselineBits steps : ℕ) : ℕ :=
   protectedMetadataWork cutoff modulus boundaryBits baselineBits+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+protectedAtomWork cutoff+
     markedChartWork (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeight cutoff) steps+4

 

end AFT.BinaryArithmetic

end

section





















/-! The protected chart sampler, evaluated by actual binary arithmetic. -/
namespace AFT.BinaryArithmetic
open AFT.RationalNumerics AFT.RationalRejectionProgram AFT.BoundaryCalibration





def binaryProtectedChartDrawWork (cutoff modulus boundaryBits baselineBits steps bits : ℕ) : ℕ :=
  protectedChartWeightWork cutoff modulus boundaryBits baselineBits steps+
    binaryPositiveDrawWork (modulus*(modulus*modulus)) (protectedChartWeightHeight cutoff modulus steps) bits+2



end AFT.BinaryArithmetic

end

section





















/-! The full support-preserving protected sampler, with real legal-mask scans. -/
namespace AFT.BinaryArithmetic
open AFT.RationalRejectionProgram AFT.BoundaryCalibration





def binarySafeProtectedChartWork (cutoff modulus boundaryBits baselineBits steps bits : ℕ) : ℕ :=
  binaryProtectedChartDrawWork cutoff modulus boundaryBits baselineBits steps bits+
    protectedMetadataWork cutoff modulus boundaryBits baselineBits+7*(modulus*(modulus*modulus))+11



end AFT.BinaryArithmetic

end

section























/-! Literal natural-coefficient polynomial costs for all protected metadata,
binary repair, finite sampling, and legal fallback. -/
namespace AFT.BinaryArithmetic
open Polynomial RationalBits AFT.BoundaryCalibration

noncomputable def modularDifferenceWorkPolynomial (address cutoff modulus : Polynomial ℕ) : Polynomial ℕ :=
  500*(cutoff+modulus+2)^2+2*modulus+2*address+6+
     500*(address+2*modulus+2)^2

@[simp] theorem modularDifferenceWorkPolynomial_eval (address cutoff modulus : Polynomial ℕ) (n : ℕ) :
    (modularDifferenceWorkPolynomial address cutoff modulus).eval n=modularDifferenceWork (address.eval n) (cutoff.eval n) (modulus.eval n) := by
  simp [modularDifferenceWorkPolynomial,modularDifferenceWork]

noncomputable def protectedFeatureWorkPolynomial (cutoff modulus input chart : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
   (modulus*(2*modulus+3)+1)+500*(chart+modulus*modulus+2)^2+
   500*(modulus*modulus+modulus+2)^2+
   modularDifferenceWorkPolynomial input cutoff modulus+modularDifferenceWorkPolynomial (2*cutoff+1) cutoff modulus+
   (modulus*modulus*(2*modulus+3)+1)+(modulus*(2*modulus+3)+1)+
   (2*chart+1)+(2*(chart+modulus*modulus*modulus)+1)+
   500*(chart+modulus*modulus*modulus+modulus*modulus+modulus+2)^2+13

@[simp] theorem protectedFeatureWorkPolynomial_eval (cutoff modulus input chart : Polynomial ℕ) (n : ℕ) :
    (protectedFeatureWorkPolynomial cutoff modulus input chart).eval n=protectedFeatureWork (cutoff.eval n) (modulus.eval n) (input.eval n) (chart.eval n) := by
  simp [protectedFeatureWorkPolynomial,protectedFeatureWork]

noncomputable def protectedPaletteWorkPolynomial (cutoff modulus input color boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+500*(input+(2*cutoff+1)+2)^2+
     50*(2*cutoff+2)^2+50*(cutoff+1)^2+50*(modulus+1)^2+50*(color+1)^2+
     200*(boundaryBits+baselineBits+3*cutoff+modulus+color+10)+200

@[simp] theorem protectedPaletteWorkPolynomial_eval (cutoff modulus input color boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedPaletteWorkPolynomial cutoff modulus input color boundaryBits baselineBits).eval n=protectedPaletteWork (cutoff.eval n) (modulus.eval n) (input.eval n) (color.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedPaletteWorkPolynomial,protectedPaletteWork]

noncomputable def protectedScaleWorkPolynomial (modulus chart : Polynomial ℕ) : Polynomial ℕ :=
  modulus*(2*modulus+3)+1+500*(chart+modulus*modulus+2)^2+
     500*(modulus*modulus+modulus+2)^2+3

@[simp] theorem protectedScaleWorkPolynomial_eval (modulus chart : Polynomial ℕ) (n : ℕ) :
    (protectedScaleWorkPolynomial modulus chart).eval n=protectedScaleWork (modulus.eval n) (chart.eval n) := by
  simp [protectedScaleWorkPolynomial,protectedScaleWork]

noncomputable def supportWorkPolynomial (charts colors features : Polynomial ℕ) : Polynomial ℕ :=
  features*(12*features+4*charts+4*colors+22)+features*features+5*features+7*charts+9*colors+32

@[simp] theorem supportWorkPolynomial_eval (charts colors features : Polynomial ℕ) (n : ℕ) :
    (supportWorkPolynomial charts colors features).eval n=supportWork (charts.eval n) (colors.eval n) (features.eval n) := by
  simp [supportWorkPolynomial,supportWork]

noncomputable def protectedDimensionsWorkPolynomial (cutoff modulus : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     modulus*(2*modulus+3)+1+modulus*(2*(modulus*modulus)+3)+1+5

@[simp] theorem protectedDimensionsWorkPolynomial_eval (cutoff modulus : Polynomial ℕ) (n : ℕ) :
    (protectedDimensionsWorkPolynomial cutoff modulus).eval n=protectedDimensionsWork (cutoff.eval n) (modulus.eval n) := by
  simp [protectedDimensionsWorkPolynomial,protectedDimensionsWork]

noncomputable def protectedMetadataCoreWorkPolynomial (cutoff modulus charts features boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  features*(charts*(protectedFeatureWorkPolynomial cutoff modulus features charts+2)+4)+2+
     features*(modulus*(protectedPaletteWorkPolynomial cutoff modulus features modulus boundaryBits baselineBits+2)+4)+2+
     charts*(protectedScaleWorkPolynomial modulus charts+2)+2+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+
     2*(charts*(supportWorkPolynomial charts modulus features+2)+2)+4*charts+8

@[simp] theorem protectedMetadataCoreWorkPolynomial_eval (cutoff modulus charts features boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedMetadataCoreWorkPolynomial cutoff modulus charts features boundaryBits baselineBits).eval n=protectedMetadataCoreWork (cutoff.eval n) (modulus.eval n) (charts.eval n) (features.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedMetadataCoreWorkPolynomial,protectedMetadataCoreWork]

noncomputable def protectedMetadataWorkPolynomial (cutoff modulus boundaryBits baselineBits : Polynomial ℕ) : Polynomial ℕ :=
  protectedDimensionsWorkPolynomial cutoff modulus+
     protectedMetadataCoreWorkPolynomial cutoff modulus (modulus*(modulus*modulus)) ((2*cutoff+1)*(2*cutoff+1)) boundaryBits baselineBits+2

@[simp] theorem protectedMetadataWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits : Polynomial ℕ) (n : ℕ) :
    (protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits).eval n=protectedMetadataWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) := by
  simp [protectedMetadataWorkPolynomial,protectedMetadataWork]

noncomputable def protectedAtomHeightPolynomial (cutoff : Polynomial ℕ) : Polynomial ℕ :=
  100*((2*cutoff+1)*(2*cutoff+1))

@[simp] theorem protectedAtomHeightPolynomial_eval (cutoff : Polynomial ℕ) (n : ℕ) :
    (protectedAtomHeightPolynomial cutoff).eval n=protectedAtomHeight (cutoff.eval n) := by
  simp [protectedAtomHeightPolynomial,protectedAtomHeight]

noncomputable def protectedAtomWorkPolynomial (cutoff : Polynomial ℕ) : Polynomial ℕ :=
  3*cutoff+1+(2*cutoff+1)*(2*(2*cutoff+1)+3)+1+
     100*(2*((2*cutoff+1)*(2*cutoff+1))+3)+1+
     60*(protectedAtomHeightPolynomial cutoff+1)^2+2*primitiveWorkPolynomial (protectedAtomHeightPolynomial cutoff)+7

@[simp] theorem protectedAtomWorkPolynomial_eval (cutoff : Polynomial ℕ) (n : ℕ) :
    (protectedAtomWorkPolynomial cutoff).eval n=protectedAtomWork (cutoff.eval n) := by
  simp [protectedAtomWorkPolynomial,protectedAtomWork]

noncomputable def chartWeightHeightPolynomial (charts colors features atomBits steps : Polynomial ℕ) : Polynomial ℕ :=
  2*chartIterateHeightPolynomial charts colors features atomBits steps+2*atomBits+3*charts+3

@[simp] theorem chartWeightHeightPolynomial_eval (charts colors features atomBits steps : Polynomial ℕ) (n : ℕ) :
    (chartWeightHeightPolynomial charts colors features atomBits steps).eval n=chartWeightHeight (charts.eval n) (colors.eval n) (features.eval n) (atomBits.eval n) (steps.eval n) := by
  simp [chartWeightHeightPolynomial,chartWeightHeight]

noncomputable def protectedChartWeightHeightPolynomial (cutoff modulus steps : Polynomial ℕ) : Polynomial ℕ :=
  chartWeightHeightPolynomial (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeightPolynomial cutoff) steps

@[simp] theorem protectedChartWeightHeightPolynomial_eval (cutoff modulus steps : Polynomial ℕ) (n : ℕ) :
    (protectedChartWeightHeightPolynomial cutoff modulus steps).eval n=protectedChartWeightHeight (cutoff.eval n) (modulus.eval n) (steps.eval n) := by
  simp [protectedChartWeightHeightPolynomial,protectedChartWeightHeight]

noncomputable def protectedChartWeightWorkPolynomial (cutoff modulus boundaryBits baselineBits steps : Polynomial ℕ) : Polynomial ℕ :=
  protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits+
     (3*cutoff+1+(2*cutoff+1)*(2*cutoff+3)+1+2*cutoff+1+4)+protectedAtomWorkPolynomial cutoff+
     markedChartWorkPolynomial (modulus*(modulus*modulus)) modulus ((2*cutoff+1)*(2*cutoff+1)) (protectedAtomHeightPolynomial cutoff) steps+4

@[simp] theorem protectedChartWeightWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps : Polynomial ℕ) (n : ℕ) :
    (protectedChartWeightWorkPolynomial cutoff modulus boundaryBits baselineBits steps).eval n=protectedChartWeightWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) := by
  simp [protectedChartWeightWorkPolynomial,protectedChartWeightWork]

noncomputable def binaryProtectedChartDrawWorkPolynomial (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) : Polynomial ℕ :=
  protectedChartWeightWorkPolynomial cutoff modulus boundaryBits baselineBits steps+
    binaryPositiveDrawPolynomial (modulus*(modulus*modulus)) (protectedChartWeightHeightPolynomial cutoff modulus steps) bits+2

@[simp] theorem binaryProtectedChartDrawWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) (n : ℕ) :
    (binaryProtectedChartDrawWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits).eval n=binaryProtectedChartDrawWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) (bits.eval n) := by
  simp [binaryProtectedChartDrawWorkPolynomial,binaryProtectedChartDrawWork]

noncomputable def binarySafeProtectedChartWorkPolynomial (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) : Polynomial ℕ :=
  binaryProtectedChartDrawWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits+
    protectedMetadataWorkPolynomial cutoff modulus boundaryBits baselineBits+7*(modulus*(modulus*modulus))+11

@[simp] theorem binarySafeProtectedChartWorkPolynomial_eval (cutoff modulus boundaryBits baselineBits steps bits : Polynomial ℕ) (n : ℕ) :
    (binarySafeProtectedChartWorkPolynomial cutoff modulus boundaryBits baselineBits steps bits).eval n=binarySafeProtectedChartWork (cutoff.eval n) (modulus.eval n) (boundaryBits.eval n) (baselineBits.eval n) (steps.eval n) (bits.eval n) := by
  simp [binarySafeProtectedChartWorkPolynomial,binarySafeProtectedChartWork]

end AFT.BinaryArithmetic

end

section
















































































namespace AFT
end AFT
namespace AFT.BetaReference
end AFT.BetaReference
namespace AFT.BetaReference.density_succ
end AFT.BetaReference.density_succ
namespace AFT.BetaReference.event_mono
end AFT.BetaReference.event_mono
namespace AFT.BetaReference.gridLaw
end AFT.BetaReference.gridLaw
namespace AFT.BetaReference.gridTailLaw
end AFT.BetaReference.gridTailLaw
namespace AFT.BetaReference.momentCoefficient
end AFT.BetaReference.momentCoefficient
namespace AFT.BetaReference.referenceHistogram
end AFT.BetaReference.referenceHistogram
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.TVBound
end AFT.FiniteDist.TVBound
namespace AFT.FiniteDist.conditionalSource
end AFT.FiniteDist.conditionalSource
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.gaussianKernel
end AFT.GaussianSource.gaussianKernel
namespace AFT.GaussianSource.harmonicWidth
end AFT.GaussianSource.harmonicWidth
namespace AFT.GaussianSource.kernelPower
end AFT.GaussianSource.kernelPower
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.powerWidth
end AFT.GaussianSource.powerWidth
namespace AFT.GaussianSource.powerWidth.match_1
end AFT.GaussianSource.powerWidth.match_1
namespace AFT.GaussianSource.ratioError
end AFT.GaussianSource.ratioError
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.GaussianSource.shiftedWeight
end AFT.GaussianSource.shiftedWeight
namespace AFT.GaussianSource.sumWidth
end AFT.GaussianSource.sumWidth
namespace AFT.GaussianSource.theta
end AFT.GaussianSource.theta
namespace AFT.GaussianSource.thetaFourier
end AFT.GaussianSource.thetaFourier
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Negligible
end AFT.Negligible
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RationalNumerics
end AFT.RationalNumerics
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.quadraticExponent
end AFT.RootSlice.quadraticExponent
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActivationApprox
end AFT.V7Calibration.actualActivationApprox
namespace AFT.V7Calibration.actualActivationInverseApprox
end AFT.V7Calibration.actualActivationInverseApprox
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualAnchorMatrix
end AFT.V7Calibration.actualAnchorMatrix
namespace AFT.V7Calibration.actualAnchorWidthProgram
end AFT.V7Calibration.actualAnchorWidthProgram
namespace AFT.V7Calibration.actualAuxiliarySquaredWidth
end AFT.V7Calibration.actualAuxiliarySquaredWidth
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualBodySampleDraw
end AFT.V7Calibration.actualBodySampleDraw
namespace AFT.V7Calibration.actualBodySamplePhysicalEquiv
end AFT.V7Calibration.actualBodySamplePhysicalEquiv
namespace AFT.V7Calibration.actualBoundaryProfile
end AFT.V7Calibration.actualBoundaryProfile
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualInteriorProfile
end AFT.V7Calibration.actualInteriorProfile
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualNormalizedSign
end AFT.V7Calibration.actualNormalizedSign
namespace AFT.V7Calibration.actualNormalizedSignProgram
end AFT.V7Calibration.actualNormalizedSignProgram
namespace AFT.V7Calibration.actualNormalizedSignProgramHeight
end AFT.V7Calibration.actualNormalizedSignProgramHeight
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPairSourceApproxLaw
end AFT.V7Calibration.actualPairSourceApproxLaw
namespace AFT.V7Calibration.actualPairSourceProgram
end AFT.V7Calibration.actualPairSourceProgram
namespace AFT.V7Calibration.actualPositiveReferenceLaw
end AFT.V7Calibration.actualPositiveReferenceLaw
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualPublicBaselineProgram
end AFT.V7Calibration.actualPublicBaselineProgram
namespace AFT.V7Calibration.actualPublicOffsetDraw
end AFT.V7Calibration.actualPublicOffsetDraw
namespace AFT.V7Calibration.actualPublicOffsetEquiv
end AFT.V7Calibration.actualPublicOffsetEquiv
namespace AFT.V7Calibration.actualRankDenominator
end AFT.V7Calibration.actualRankDenominator
namespace AFT.V7Calibration.actualRankDenominatorProgram
end AFT.V7Calibration.actualRankDenominatorProgram
namespace AFT.V7Calibration.actualRankInverseProgram
end AFT.V7Calibration.actualRankInverseProgram
namespace AFT.V7Calibration.actualRankInverseProgramHeight
end AFT.V7Calibration.actualRankInverseProgramHeight
namespace AFT.V7Calibration.actualReferenceMarkedProfile
end AFT.V7Calibration.actualReferenceMarkedProfile
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualResponseProgram
end AFT.V7Calibration.actualResponseProgram
namespace AFT.V7Calibration.actualSafeMarginProgram
end AFT.V7Calibration.actualSafeMarginProgram
namespace AFT.V7Calibration.actualSignedSliceMean
end AFT.V7Calibration.actualSignedSliceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorIndexEquiv
end AFT.V7Calibration.anchorIndexEquiv
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.betaGridMesh
end AFT.V7Calibration.betaGridMesh
namespace AFT.V7Calibration.betaGridStart
end AFT.V7Calibration.betaGridStart
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.bodyShiftIntegerProgram
end AFT.V7Calibration.bodyShiftIntegerProgram
namespace AFT.V7Calibration.conditionalBaselineStart
end AFT.V7Calibration.conditionalBaselineStart
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap



/-! Public baseline formation retaining all signed source digits. -/
namespace AFT.BinaryArithmetic
open AFT.V7Calibration

def binaryBaselineStart (modulus width color : ℕ) (coin : Bool) : SignedResult :=
  let twiceColor := doubleCounter color
  let last := differenceCounter modulus 1
  let lower := lessCounter twiceColor.count last.count
  let upper := lessCounter last.count twiceColor.count
  let twiceWidth := doubleCounter width
  let positive := canonicalCounter width
  let negative := canonicalCounter twiceWidth.count
  let shifted := signedAdd true false negative.digits [true]
  let pickLower := lower.value || (!upper.value && coin)
  ⟨if pickLower then shifted.negative else false,
    if pickLower then shifted.digits else positive.digits,
    twiceColor.work+last.work+lower.work+upper.work+twiceWidth.work+
      positive.work+negative.work+shifted.work+10⟩

theorem binaryBaselineStart_value (modulus width color : ℕ) (coin : Bool) :
    signedValue (binaryBaselineStart modulus width color coin).negative
      (binaryBaselineStart modulus width color coin).digits=
      publicAnchorStartProgram modulus width color coin+(color : ℤ)-((modulus : ℤ)-1) := by
  have hn : signedValue (signedAdd true false (canonicalCounter (2*width)).digits [true]).negative
      (signedAdd true false (canonicalCounter (2*width)).digits [true]).digits=1-2*(width : ℤ) := by
    rw [signedAdd_value]
    simp [signedValue,canonicalCounter_value,value]
    ring
  have hp : signedValue false (canonicalCounter width).digits=(width : ℤ) := by
    simp [signedValue,canonicalCounter_value]
  by_cases hlow : 2*color < modulus-1
  · have hl : (lessCounter (2*color) (modulus-1)).value=true := (lessCounter_value _ _).mpr hlow
    simp only [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,Bool.true_or,
      ↓reduceIte,hn,publicAnchorStartProgram,if_pos hlow]
    omega
  · have hl : (lessCounter (2*color) (modulus-1)).value=false := by
      apply Bool.eq_false_iff.mpr
      exact fun h => hlow ((lessCounter_value _ _).mp h)
    by_cases hupp : modulus-1 < 2*color
    · have hu : (lessCounter (modulus-1) (2*color)).value=true := (lessCounter_value _ _).mpr hupp
      simp [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,hu,hp,
        publicAnchorStartProgram,hlow,hupp]
      ring
    · have hu : (lessCounter (modulus-1) (2*color)).value=false := by
        apply Bool.eq_false_iff.mpr
        exact fun h => hupp ((lessCounter_value _ _).mp h)
      cases coin <;> simp [binaryBaselineStart,doubleCounter_value,differenceCounter_value,hl,hu,
        hp,hn,publicAnchorStartProgram,hlow,hupp] <;> omega





def binaryBaselineStartWork (modulus width color : ℕ) : ℕ :=
  1000*(modulus+width+color+2)^2











end AFT.BinaryArithmetic

end

section




















/-! # Capped rejection using the actual binary acceptance implementation

The proposal and numerical score are each evaluated once per attempted
sample. This layer propagates their proved bit costs; it does not assume
constant-time rational arithmetic for the acceptance decision.
-/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalRejectionProgram
variable {State Tape : Type*}

def binaryPositiveRatio (raw envelope : RationalBits) : RationalResult :=
  let positive := raw.maxZero
  let result := positive.data.quotient envelope
  ⟨result.data,positive.work+result.work+2⟩







def binaryRejectionDraw (sample : Tape → CountedValue State) (score : State → CountedValue RationalBits)
    (envelope : RationalBits) (bits : ℕ) (fallback : CountedValue State) :
    (attempts : ℕ) → (Fin attempts → Tape×(Fin bits → Fin 2)) → CountedValue State
  | 0,_ => fallback
  | attempts+1,tape =>
      let candidate := sample (tape 0).1
      let raw := score candidate.value
      let ratio := binaryPositiveRatio raw.value envelope
      let accepted := binaryAcceptance ratio.data bits (tape 0).2
      let used := candidate.work+raw.work+ratio.work+accepted.work+3
      if accepted.value=0 then ⟨candidate.value,used⟩ else
        let remaining := binaryRejectionDraw sample score envelope bits fallback attempts (Fin.tail tape)
        ⟨remaining.value,used+remaining.work⟩



def binaryRejectionStepWork (proposalWork scoreWork scoreBits envelopeBits bits : ℕ) : ℕ :=
  proposalWork+scoreWork+2*RationalBits.primitiveWorkBound (scoreBits+envelopeBits)+
    binaryAcceptanceWork (scoreBits+envelopeBits) bits+9



end AFT.BinaryArithmetic

end

section






















/-! Integer translation of a finite rational array, using explicit binary
comparisons and an indexed finite sum. The source callback is executed only
at a matching integer; there is no integer-to-palette oracle. -/
namespace AFT.BinaryArithmetic
open RationalNumerics RationalBits RationalRejectionProgram Polynomial
open scoped BigOperators

 def signedEqual (firstSign secondSign : Bool) (first second : List Bool) : CountedValue Bool :=
  let forward := signedLe firstSign secondSign first second
  let backward := signedLe secondSign firstSign second first
  ⟨forward.value && backward.value,forward.work+backward.work+3⟩

 theorem signedEqual_value (firstSign secondSign : Bool) (first second : List Bool) :
    (signedEqual firstSign secondSign first second).value=true ↔
      signedValue firstSign first=signedValue secondSign second := by
  simp only [signedEqual,Bool.and_eq_true,signedLe_value]
  exact le_antisymm_iff.symm

 

 

 

 

 def binaryShiftTermWork (count shiftBits outputBits entryWork : ℕ) : ℕ :=
   50*(count+1)^2+100*(count+shiftBits+outputBits+2)+entryWork+100

 

 

 

 

 def binaryShiftSumWork (count bits shiftBits outputBits entryWork : ℕ) : ℕ :=
   count*(binaryShiftTermWork count shiftBits outputBits entryWork+primitiveWorkBound ((count+1)*(bits+1))+2)+2

 

 noncomputable def binaryShiftSumPolynomial (count bits shiftBits outputBits entryWork : Polynomial ℕ) : Polynomial ℕ :=
   count*(50*(count+1)^2+100*(count+shiftBits+outputBits+2)+entryWork+100+
     primitiveWorkPolynomial ((count+1)*(bits+1))+2)+2

 @[simp] theorem binaryShiftSumPolynomial_eval (count bits shiftBits outputBits entryWork : Polynomial ℕ) (n : ℕ) :
    (binaryShiftSumPolynomial count bits shiftBits outputBits entryWork).eval n=
      binaryShiftSumWork (count.eval n) (bits.eval n) (shiftBits.eval n) (outputBits.eval n) (entryWork.eval n) := by
  simp [binaryShiftSumPolynomial,binaryShiftSumWork,binaryShiftTermWork]

 

 

 

 

 

 

end AFT.BinaryArithmetic

end

section


















/-! # Scalar evaluation with stored encoded literals

All literals in executable syntax are already numeric representations.
There is no run-time rational-to-binary oracle: compiling the fixed scalar
syntax is separate from evaluating it. Dynamic integers can instead be
supplied by an explicit integer program through the leaf interface.
-/
namespace AFT.RationalNumerics
open RationalRejectionProgram

structure RationalOperations (Value : Type*) where
  add : Value → Value → CountedValue Value
  multiply : Value → Value → CountedValue Value
  negate : Value → CountedValue Value
  inverse : Value → CountedValue Value

structure RationalOperations.Correct {Value : Type*}
    (ops : RationalOperations Value) (decode : Value → ℚ) : Prop where
  add : ∀ first second,decode (ops.add first second).value=decode first+decode second
  multiply : ∀ first second,decode (ops.multiply first second).value=decode first*decode second
  negate : ∀ value,decode (ops.negate value).value=-(decode value)
  inverse : ∀ value,decode (ops.inverse value).value=(decode value)⁻¹

inductive StoredScalarProgram (Scalar Value : Type*) where
  | literal : Value → StoredScalarProgram Scalar Value
  | atom : Scalar → StoredScalarProgram Scalar Value
  | add : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | multiply : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | negate : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value
  | inverse : StoredScalarProgram Scalar Value → StoredScalarProgram Scalar Value

namespace StoredScalarProgram
variable {Scalar Value : Type*}

/-- Read-only stored literals need one syntax dispatch. Numeric operations
are charged by their actual implementations. -/
def run (ops : RationalOperations Value) (leaf : Scalar → CountedValue Value) :
    StoredScalarProgram Scalar Value → CountedValue Value
  | .literal value => ⟨value,1⟩
  | .atom code => let result := leaf code;⟨result.value,result.work+1⟩
  | .add first second =>
      let left := first.run ops leaf
      let right := second.run ops leaf
      let result := ops.add left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .multiply first second =>
      let left := first.run ops leaf
      let right := second.run ops leaf
      let result := ops.multiply left.value right.value
      ⟨result.value,left.work+right.work+result.work+1⟩
  | .negate term =>
      let input := term.run ops leaf
      let result := ops.negate input.value
      ⟨result.value,input.work+result.work+1⟩
  | .inverse term =>
      let input := term.run ops leaf
      let result := ops.inverse input.value
      ⟨result.value,input.work+result.work+1⟩

/-- Erasure into rational semantics is used only by proofs. -/
def meaning (decode : Value → ℚ) : StoredScalarProgram Scalar Value → ScalarProgram Scalar
  | .literal value => .rational (decode value)
  | .atom code => .atom code
  | .add first second => .add (first.meaning decode) (second.meaning decode)
  | .multiply first second => .multiply (first.meaning decode) (second.meaning decode)
  | .negate term => .negate (term.meaning decode)
  | .inverse term => .inverse (term.meaning decode)

theorem run_value (ops : RationalOperations Value) (decode : Value → ℚ)
    (hops : ops.Correct decode) (leaf : Scalar → CountedValue Value)
    (program : StoredScalarProgram Scalar Value) :
    decode (program.run ops leaf).value=(program.meaning decode).run (fun code => decode (leaf code).value) := by
  induction program <;> simp_all only [run,meaning,ScalarProgram.run,hops.add,hops.multiply,hops.negate,hops.inverse]



/-- Compilation is outside the execution loop. An application must supply
stored codes for its literals, or generate dynamic values through `leaf`. -/
def compile (encode : ℚ → Value) : ScalarProgram Scalar → StoredScalarProgram Scalar Value
  | .rational value => .literal (encode value)
  | .atom code => .atom code
  | .add first second => .add (compile encode first) (compile encode second)
  | .multiply first second => .multiply (compile encode first) (compile encode second)
  | .negate term => .negate (compile encode term)
  | .inverse term => .inverse (compile encode term)

theorem compile_meaning (encode : ℚ → Value) (decode : Value → ℚ)
    (hcode : ∀ value,decode (encode value)=value) (program : ScalarProgram Scalar) :
    (compile encode program).meaning decode=program := by
  induction program <;> simp_all only [compile,meaning]

end StoredScalarProgram
end AFT.RationalNumerics

end

section






















/-! Actual binary implementation of every scalar arithmetic node. There is
no rational primitive or unproved primitive-cost premise in this evaluator. -/
namespace AFT.RationalNumerics
open RationalRejectionProgram BinaryArithmetic

/-- Runtime calls only the Boolean-list algorithms, including actual gcd
normalization after addition and multiplication. -/
def binaryOperations : RationalOperations RationalBits where
  add first second :=
    let result := RationalBits.add first second
    ⟨result.data,result.work⟩
  multiply first second :=
    let result := RationalBits.multiply first second
    ⟨result.data,result.work⟩
  negate input :=
    let result := RationalBits.negate input
    ⟨result.data,result.work⟩
  inverse input :=
    let result := RationalBits.inverse input
    ⟨result.data,result.work⟩

theorem binaryOperations_correct : binaryOperations.Correct RationalBits.decode where
  add := RationalBits.add_value
  multiply := RationalBits.multiply_value
  negate := RationalBits.negate_value
  inverse := RationalBits.inverse_value

namespace StoredScalarProgram
variable {Scalar : Type*}

def binaryRun (leaf : Scalar → CountedValue RationalBits)
    (program : StoredScalarProgram Scalar RationalBits) : CountedValue RationalBits :=
  program.run binaryOperations leaf

theorem binaryRun_value (leaf : Scalar → CountedValue RationalBits)
    (program : StoredScalarProgram Scalar RationalBits) :
    (program.binaryRun leaf).value.decode=
      (program.meaning RationalBits.decode).run (fun code => (leaf code).value.decode) :=
  program.run_value binaryOperations RationalBits.decode binaryOperations_correct leaf



end StoredScalarProgram



end AFT.RationalNumerics

end

section






















/-! # Bounded unary window metadata

Dimension and array indices are polynomially bounded unary counters. Window
shape and signed coordinates are formed by explicit successor/case routines.
-/
namespace AFT.BinaryArithmetic
open RationalRejectionProgram

def integerDifference : ℕ → ℕ → CountedValue ℤ
  | first,0 => ⟨.ofNat first,2⟩
  | 0,second+1 => ⟨.negSucc second,2⟩
  | first+1,second+1 =>
      let previous := integerDifference first second
      ⟨previous.value,previous.work+2⟩

theorem integerDifference_value (first second : ℕ) :
    (integerDifference first second).value=(first : ℤ)-(second : ℤ) := by
  induction first generalizing second with
  | zero =>
      cases second with
      | zero => rfl
      | succ second => change Int.negSucc second=0-((second+1 : ℕ) : ℤ);omega
  | succ first ih =>
      cases second with
      | zero => simp [integerDifference]
      | succ second => simp only [integerDifference,ih,Nat.cast_add,Nat.cast_one];ring



structure WindowShape where
  cutoff : ℕ
  count : ℕ
  work : ℕ









end AFT.BinaryArithmetic

end

section






















namespace AFT
end AFT
namespace AFT.RationalNumerics
end AFT.RationalNumerics







/-! # Binary Gaussian evaluation on arbitrary bounded windows

The width is stored binary input. Coordinates, precision counters, every
Gaussian evaluation, and array normalization are executed explicitly.
-/
namespace AFT.BinaryArithmetic.RationalBits
open AFT.RationalNumerics GaussianSource FiniteConvolutionProgram Polynomial
open scoped BigOperators



def binaryWindowPoint (width : RationalBits) (cutoff precision index : ℕ) : RationalResult :=
  let point := integerDifference index cutoff
  let encoded := ofUnaryInteger point.value
  let result := gaussian width encoded.data precision
  ⟨result.data,point.work+encoded.work+result.work+3⟩

theorem binaryWindowPoint_value (width : RationalBits) (cutoff precision index : ℕ) :
    (binaryWindowPoint width cutoff precision index).data.decode=
      gaussianApprox width.decode ((index : ℤ)-(cutoff : ℤ)) precision := by
  simp only [binaryWindowPoint,gaussian_value _ _ _ _ (ofUnaryInteger_value _),integerDifference_value]

def binaryWindowPointWork (budget : ℕ) : ℕ :=
  60*(budget+1)^2+gaussianWork budget budget budget (11*budget) (4*budget)+10*budget+12



def binaryWindowRaw (width : RationalBits) (cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let doubled := doubleCounter cutoff
  let count := doubled.count.succ
  let precision := addCounter bits count
  let raw := buildArray count (fun index => binaryWindowPoint width cutoff precision.count.succ index.val)
  ⟨Vector.cast (by dsimp only [count,doubled];rw [doubleCounter_value]) raw.data,doubled.work+precision.work+raw.work+4⟩

theorem binaryWindowRaw_value (width : RationalBits) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((binaryWindowRaw width cutoff bits).data.get index).decode=
      windowApproxRaw width.decode cutoff bits (windowIndexEquiv cutoff index) := by
  simp only [binaryWindowRaw,Vector.get_cast,buildArray_get,binaryWindowPoint_value,Fin.val_cast,
    addCounter_value,doubleCounter_value]
  rfl

def binaryWindowRawWork (budget : ℕ) : ℕ :=
  (2*budget+1)*(binaryWindowPointWork budget+2)+5*budget+10





def binaryWindowWeights (width : RationalBits) (cutoff bits : ℕ) : ArrayResult (2*cutoff+1) :=
  let raw := binaryWindowRaw width cutoff bits
  let normalized := normalizeArray raw.data
  ⟨normalized.data,raw.work+normalized.work+2⟩

theorem binaryWindowWeights_value (width : RationalBits) (cutoff bits : ℕ) (index : Fin (2*cutoff+1)) :
    ((binaryWindowWeights width cutoff bits).data.get index).decode=windowGaussianWeights width.decode cutoff bits index := by
  simp only [binaryWindowWeights,normalizeArray_value,binaryWindowRaw_value,windowGaussianWeights,windowApproxWeight]
  congr 1

def binaryWindowWork (budget : ℕ) : ℕ :=
  binaryWindowRawWork budget+normalizeArrayWork (2*budget+1) (100000000*budget^5)+2





noncomputable def binaryWindowPointPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  60*(budget+1)^2+gaussianWorkPolynomial budget budget budget (11*budget) (4*budget)+10*budget+12
noncomputable def binaryWindowRawPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  (2*budget+1)*(binaryWindowPointPolynomial budget+2)+5*budget+10
noncomputable def binaryWindowPolynomial (budget : Polynomial ℕ) : Polynomial ℕ :=
  binaryWindowRawPolynomial budget+normalizeArrayWorkPolynomial (2*budget+1) (100000000*budget^5)+2

@[simp] theorem binaryWindowPointPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowPointPolynomial budget).eval n=binaryWindowPointWork (budget.eval n) := by
  simp only [binaryWindowPointPolynomial,binaryWindowPointWork,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat,
    gaussianWorkPolynomial_eval]
@[simp] theorem binaryWindowRawPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowRawPolynomial budget).eval n=binaryWindowRawWork (budget.eval n) := by
  simp only [binaryWindowRawPolynomial,binaryWindowRawWork,eval_add,eval_mul,eval_one,eval_ofNat,
    binaryWindowPointPolynomial_eval]
@[simp] theorem binaryWindowPolynomial_eval (budget : Polynomial ℕ) (n : ℕ) :
    (binaryWindowPolynomial budget).eval n=binaryWindowWork (budget.eval n) := by
  simp only [binaryWindowPolynomial,binaryWindowWork,eval_add,eval_mul,eval_pow,eval_one,eval_ofNat,
    binaryWindowRawPolynomial_eval,normalizeArrayWorkPolynomial_eval]

end AFT.BinaryArithmetic.RationalBits

end

section





/-! # Tensor contraction with different finite alphabets in each coordinate -/

namespace AFT
open scoped BigOperators Classical
noncomputable section

namespace FiniteDist
/-- A finite product law with genuinely dependent coordinate alphabets. -/
def dependentIndependent {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (law : ∀ i, FiniteDist (Color i)) : FiniteDist ((i : Index) → Color i) where
  weight word := ∏ i, (law i).weight (word i)
  nonneg word := Finset.prod_nonneg fun i _ => (law i).nonneg (word i)
  sum_one := by
    rw [← Fintype.prod_sum]
    simp only [sum_one, Finset.prod_const_one]

@[simp] theorem dependentIndependent_weight {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (law : ∀ i, FiniteDist (Color i)) (word : ∀ i, Color i) :
    (dependentIndependent law).weight word = ∏ i, (law i).weight (word i) := rfl
end FiniteDist

namespace DependentTensorChannel
set_option backward.isDefEq.respectTransparency false

 theorem expectation_cons (count : ℕ) {Color : Fin (count + 1) → Type*}
    [∀ i, Fintype (Color i)] (law : ∀ i, FiniteDist (Color i))
    (value : ((i : Fin (count + 1)) → Color i) → ℝ) :
    (FiniteDist.dependentIndependent law).expectation value =
      (law 0).expectation (fun first =>
        (FiniteDist.dependentIndependent (fun index => law index.succ)).expectation
          (fun rest => value (Fin.cons first rest))) := by
  unfold FiniteDist.expectation FiniteDist.dependentIndependent
  rw [← Equiv.sum_comp (Fin.consEquiv Color), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  change (∏ index, (law index).weight ((Fin.cons first rest : ∀ i, Color i) index)) * value (Fin.cons first rest) = _
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

/-- Successive contraction of dependent local channels. -/
def applyFin : (count : ℕ) → {Input Output : Fin count → Type*} →
    (∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ)) →
    (((i : Fin count) → Input i) → ℝ) → ((i : Fin count) → Output i) → ℝ
  | 0, _, _, _, kernel, _ => kernel (fun i => Fin.elim0 i)
  | count + 1, _, _, channel, kernel, output =>
      channel 0 (fun first => applyFin count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0)

@[simp] theorem applyFin_cons (count : ℕ) {Input Output : Fin (count + 1) → Type*}
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Fin (count + 1)) → Input i) → ℝ)
    (first : Output 0) (rest : ∀ i : Fin count, Output i.succ) :
    applyFin (count + 1) channel kernel (Fin.cons first rest) =
      channel 0 (fun input => applyFin count (fun index => channel index.succ)
        (fun tail => kernel (Fin.cons input tail)) rest) first := by
  simp only [applyFin, Fin.cons_zero, Fin.cons_succ]

 theorem expectation_mono {Sample : Type*} [Fintype Sample]
    (law : FiniteDist Sample) {first second : Sample → ℝ} (h : ∀ point, first point ≤ second point) :
    law.expectation first ≤ law.expectation second :=
  Finset.sum_le_sum fun point _ => mul_le_mul_of_nonneg_left (h point) (law.nonneg point)

/-- The Hilbert norm of the complete tensor channel is the product of its
local bounds. This applies to every joint kernel, including nonseparable
kernels with arbitrary dependencies among the distinguished coordinates. -/
theorem energy_fin_le (count : ℕ)
    (Input Output : Fin count → Type*) [∀ i, Fintype (Input i)] [∀ i, Fintype (Output i)]
    (input : ∀ i, FiniteDist (Input i)) (output : ∀ i, FiniteDist (Output i))
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (bound : Fin count → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : ((i : Fin count) → Input i) → ℝ) :
    (FiniteDist.dependentIndependent output).l2Sq (applyFin count channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel := by
  induction count with
  | zero =>
    have hconstant : kernel = fun _ => kernel (fun i => Fin.elim0 i) := by
      funext word
      congr 1
      funext index
      exact Fin.elim0 index
    rw [hconstant]
    simp only [applyFin, FiniteDist.l2Sq, FiniteDist.expectation_const, Fin.prod_univ_zero, one_mul]
    exact le_rfl
  | succ count ih =>
    let tailInput := FiniteDist.dependentIndependent (fun index : Fin count => input index.succ)
    let tailOutput := FiniteDist.dependentIndependent (fun index : Fin count => output index.succ)
    let tailValue := fun first rest => applyFin count (fun index => channel index.succ)
      (fun tail => kernel (Fin.cons first tail)) rest
    have htail (first : Input 0) : tailOutput.l2Sq (tailValue first) ≤
        (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest)) :=
      ih (fun index => Input index.succ) (fun index => Output index.succ) (fun index => input index.succ) (fun index => output index.succ)
        (fun index => channel index.succ) (fun index => bound index.succ)
        (fun index => hchannel index.succ) _
    have hsplit : (FiniteDist.dependentIndependent output).l2Sq (applyFin (count + 1) channel kernel) =
        tailOutput.expectation (fun rest => (output 0).l2Sq (channel 0 (fun first => tailValue first rest))) := by
      unfold FiniteDist.l2Sq
      rw [expectation_cons]
      simp only [applyFin_cons]
      exact FiniteDist.expectation_comm _ _ _
    rw [hsplit]
    calc
      _ ≤ tailOutput.expectation (fun rest => bound 0 ^ 2 * (input 0).l2Sq (fun first => tailValue first rest)) :=
        expectation_mono tailOutput (fun rest => hchannel 0 _)
      _ = bound 0 ^ 2 * (input 0).expectation (fun first => tailOutput.l2Sq (tailValue first)) := by
        rw [FiniteDist.expectation_const_mul]
        congr 1
        exact FiniteDist.expectation_comm _ _ _
      _ ≤ bound 0 ^ 2 * (input 0).expectation (fun first =>
          (∏ index : Fin count, bound index.succ ^ 2) * tailInput.l2Sq (fun rest => kernel (Fin.cons first rest))) :=
        mul_le_mul_of_nonneg_left (expectation_mono (input 0) htail) (sq_nonneg _)
      _ = _ := by
        rw [FiniteDist.expectation_const_mul, Fin.prod_univ_succ]
        rw [mul_assoc]
        congr 2
        unfold FiniteDist.l2Sq
        exact (expectation_cons count input (fun word => kernel word ^ 2)).symm


/-- The recursive tensor is the literal full joint signed response. -/
theorem applyFin_formula (count : ℕ) {Input Output : Fin count → Type*}
    [∀ i, Fintype (Input i)]
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Fin count) → Input i) → ℝ) (output : ∀ i, Output i) :
    applyFin count channel kernel output =
      ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index) := by
  induction count with
  | zero =>
    simp only [applyFin, Fin.prod_univ_zero, mul_one, Fintype.sum_unique]
    congr 1
  | succ count ih =>
    rw [show applyFin (count + 1) channel kernel output = channel 0
      (fun first => applyFin count (fun index => channel index.succ)
        (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ)) (output 0) from rfl]
    rw [TensorChannel.channel_sum_single]
    simp only [ih, Finset.sum_mul]
    rw [← Equiv.sum_comp (Fin.consEquiv Input), Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro first _
    apply Finset.sum_congr rfl
    intro rest _
    change (kernel (Fin.cons first rest) * ∏ x, channel x.succ (Pi.single (rest x) 1) (output x.succ)) *
      channel 0 (Pi.single first 1) (output 0) = _
    simp only [Fin.prod_univ_succ, Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ]
    ring

variable {Index : Type*} [Fintype Index] [DecidableEq Index]
    {Input Output : Index → Type*} [∀ i, Fintype (Input i)] [∀ i, Fintype (Output i)]

/-- Simultaneous local linear channels acting on a genuinely joint input. -/
def apply (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Index) → Input i) → ℝ) (output : ∀ i, Output i) : ℝ :=
  ∑ point, kernel point * ∏ index, channel index (Pi.single (point index) 1) (output index)

omit [∀ i, Fintype (Output i)] in
 theorem apply_reindex {Index' : Type*} [Fintype Index'] [DecidableEq Index']
    (e : Index' ≃ Index) (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ))
    (kernel : ((i : Index) → Input i) → ℝ) (output : ∀ i, Output i) :
    (∑ point : (i : Index') → Input (e i), kernel ((Equiv.piCongrLeft Input e) point) *
      ∏ i, channel (e i) (Pi.single (point i) 1) (output (e i))) = apply channel kernel output := by
  unfold apply
  rw [← (Equiv.piCongrLeft Input e).sum_comp]
  apply Finset.sum_congr rfl
  intro point _
  congr 1
  rw [← e.prod_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

 theorem energy_reindex {Index' : Type*} [Fintype Index'] [DecidableEq Index']
    {Color : Index → Type*} [∀ i, Fintype (Color i)]
    (e : Index' ≃ Index) (law : ∀ i, FiniteDist (Color i))
    (kernel : ((i : Index) → Color i) → ℝ) :
    (FiniteDist.dependentIndependent (fun i => law (e i))).l2Sq
        (fun point => kernel ((Equiv.piCongrLeft Color e) point)) =
      (FiniteDist.dependentIndependent law).l2Sq kernel := by
  unfold FiniteDist.l2Sq FiniteDist.expectation
  rw [← (Equiv.piCongrLeft Color e).sum_comp]
  apply Finset.sum_congr rfl
  intro point _
  simp only [FiniteDist.dependentIndependent_weight]
  congr 1
  rw [← e.prod_comp]
  simp only [Equiv.piCongrLeft_apply_apply]

/-- The dependent tensor contraction has exactly the product of the local
Hilbert bounds, without a dimension factor or separability assumption. -/
theorem energy_le (input : ∀ i, FiniteDist (Input i)) (output : ∀ i, FiniteDist (Output i))
    (channel : ∀ i, (Input i → ℝ) →ₗ[ℝ] (Output i → ℝ)) (bound : Index → ℝ)
    (hchannel : ∀ index kernel, (output index).l2Sq (channel index kernel) ≤
      bound index ^ 2 * (input index).l2Sq kernel)
    (kernel : ((i : Index) → Input i) → ℝ) :
    (FiniteDist.dependentIndependent output).l2Sq (apply channel kernel) ≤
      (∏ index, bound index ^ 2) * (FiniteDist.dependentIndependent input).l2Sq kernel := by
  let e : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hh := energy_fin_le (Fintype.card Index) (fun i => Input (e i)) (fun i => Output (e i))
    (fun i => input (e i)) (fun i => output (e i)) (fun i => channel (e i))
    (fun i => bound (e i)) (fun i => hchannel (e i))
    (fun word => kernel ((Equiv.piCongrLeft Input e) word))
  have heq : applyFin (Fintype.card Index) (fun i => channel (e i))
        (fun word => kernel ((Equiv.piCongrLeft Input e) word)) =
      fun word => apply channel kernel ((Equiv.piCongrLeft Output e) word) := by
    funext word
    rw [applyFin_formula]
    simpa only [Equiv.piCongrLeft_apply_apply] using
      apply_reindex e channel kernel ((Equiv.piCongrLeft Output e) word)
  rw [heq, energy_reindex, energy_reindex] at hh
  rw [e.prod_comp (fun i => bound i ^ 2)] at hh
  exact hh

end DependentTensorChannel
end
end AFT

end

section

























































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FiniteDist.boundaryRecord
end AFT.FiniteDist.boundaryRecord
namespace AFT.FiniteDist.dependentPairsEquiv
end AFT.FiniteDist.dependentPairsEquiv
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPairResidualInput
end AFT.GaussianSource.actualPairResidualInput
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.actualRootLaw
end AFT.GaussianSource.actualRootLaw
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.extraSample
end AFT.GaussianSource.extraSample
namespace AFT.GaussianSource.optionalShift
end AFT.GaussianSource.optionalShift
namespace AFT.GaussianSource.optionalShift.match_1
end AFT.GaussianSource.optionalShift.match_1
namespace AFT.GaussianSource.pairCore
end AFT.GaussianSource.pairCore
namespace AFT.GaussianSource.pairCoreDepth
end AFT.GaussianSource.pairCoreDepth
namespace AFT.GaussianSource.pairNeumannConstant
end AFT.GaussianSource.pairNeumannConstant
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.GaussianSource.rootMarginal
end AFT.GaussianSource.rootMarginal
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.jointLegalProjection
end AFT.MixedKernel.jointLegalProjection
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.backgroundLogarithm
end AFT.RepresentedPolynomial.backgroundLogarithm
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.boundaryPolynomial
end AFT.RepresentedPolynomial.boundaryPolynomial
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.inversePrimarySeed
end AFT.RepresentedPolynomial.inversePrimarySeed
namespace AFT.RepresentedPolynomial.jointChannelPolynomial
end AFT.RepresentedPolynomial.jointChannelPolynomial
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.profilePolynomialMap
end AFT.RepresentedPolynomial.profilePolynomialMap
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.RootSlice.reference
end AFT.RootSlice.reference
namespace AFT.SafeConvolution
end AFT.SafeConvolution
namespace AFT.SafeConvolution.RowBound
end AFT.SafeConvolution.RowBound
namespace AFT.SafeConvolution.SupBound
end AFT.SafeConvolution.SupBound
namespace AFT.SafeConvolution.SupportedInBox
end AFT.SafeConvolution.SupportedInBox
namespace AFT.SafeConvolution.uniformCanonical
end AFT.SafeConvolution.uniformCanonical
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointDifference
end AFT.V7Calibration.activeEndpointDifference
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCanonicalPairResidualInput
end AFT.V7Calibration.actualCanonicalPairResidualInput
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualEndpointHigherTable
end AFT.V7Calibration.actualEndpointHigherTable
namespace AFT.V7Calibration.actualEndpointSeed
end AFT.V7Calibration.actualEndpointSeed
namespace AFT.V7Calibration.actualEndpointVector
end AFT.V7Calibration.actualEndpointVector
namespace AFT.V7Calibration.actualEndpointVector.match_1
end AFT.V7Calibration.actualEndpointVector.match_1
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveBodyPairDensity
end AFT.V7Calibration.actualInactiveBodyPairDensity
namespace AFT.V7Calibration.actualInactiveBodyPairInput
end AFT.V7Calibration.actualInactiveBodyPairInput
namespace AFT.V7Calibration.actualInactiveBodyPairMass
end AFT.V7Calibration.actualInactiveBodyPairMass
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedFringeInput
end AFT.V7Calibration.actualMarkedFringeInput
namespace AFT.V7Calibration.actualMarkedInput
end AFT.V7Calibration.actualMarkedInput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualMarkedSafeDensity
end AFT.V7Calibration.actualMarkedSafeDensity
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.actualPairCompletionInput
end AFT.V7Calibration.actualPairCompletionInput
namespace AFT.V7Calibration.actualPairReferenceInput
end AFT.V7Calibration.actualPairReferenceInput
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.actual_body_population_expectation
end AFT.V7Calibration.actual_body_population_expectation
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.attachedBodyAtSource
end AFT.V7Calibration.attachedBodyAtSource
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blockBackgroundError
end AFT.V7Calibration.blockBackgroundError
namespace AFT.V7Calibration.blockBackgroundLinear
end AFT.V7Calibration.blockBackgroundLinear
namespace AFT.V7Calibration.blockBackgroundLinear.match_1
end AFT.V7Calibration.blockBackgroundLinear.match_1
namespace AFT.V7Calibration.blockBodyMeanProfile
end AFT.V7Calibration.blockBodyMeanProfile
namespace AFT.V7Calibration.blockBodyMeanProfile.match_1
end AFT.V7Calibration.blockBodyMeanProfile.match_1
namespace AFT.V7Calibration.blockBodyMeanTable
end AFT.V7Calibration.blockBodyMeanTable
namespace AFT.V7Calibration.blockBodyMeanTable.match_1
end AFT.V7Calibration.blockBodyMeanTable.match_1
namespace AFT.V7Calibration.blockPhysicalPolynomial
end AFT.V7Calibration.blockPhysicalPolynomial
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.endpointCoefficient
end AFT.V7Calibration.endpointCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
namespace AFT.V7Calibration.globalLinearProfile
end AFT.V7Calibration.globalLinearProfile
namespace AFT.V7Calibration.globalLinearTable
end AFT.V7Calibration.globalLinearTable
namespace AFT.V7Calibration.globalMeanChangeTable
end AFT.V7Calibration.globalMeanChangeTable
namespace AFT.V7Calibration.globalMeanTable
end AFT.V7Calibration.globalMeanTable
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactivePairShift
end AFT.V7Calibration.inactivePairShift
namespace AFT.V7Calibration.inactivePairSources
end AFT.V7Calibration.inactivePairSources
namespace AFT.V7Calibration.inactivePairStarts
end AFT.V7Calibration.inactivePairStarts
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localAttachedMeanInputTable
end AFT.V7Calibration.localAttachedMeanInputTable
namespace AFT.V7Calibration.localBackgroundLinear
end AFT.V7Calibration.localBackgroundLinear
namespace AFT.V7Calibration.localBodyMixture
end AFT.V7Calibration.localBodyMixture
namespace AFT.V7Calibration.localCovarianceInputTable
end AFT.V7Calibration.localCovarianceInputTable
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.localPrimaryMeanInputTable
end AFT.V7Calibration.localPrimaryMeanInputTable
namespace AFT.V7Calibration.primaryPairSeed
end AFT.V7Calibration.primaryPairSeed
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap




/-! # Old-coordinate centering inside genuinely dependent joint tensors -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Index Output : Type*} [Fintype Index] [DecidableEq Index]
  {Old : Index → Type*} [∀ i, Fintype (Old i)]

/-- The polynomial tensor sum uses its literal basis masses. In particular,
no factorization of the joint kernel is imposed. -/
def dependentPolynomial (forms : ∀ i, Old i → Table Output)
    (kernel : ((i : Index) → Old i) → ℝ) : Table Output :=
  ∑ word, MvPolynomial.C (kernel word) * ∏ i, forms i (word i)











end
end AFT.RepresentedPolynomial

namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Root Old Output : Type*} [Fintype Old]







end
end AFT.RepresentedPolynomial

end

section














/-! # A finite canonical point basis, including reference laws with zeros -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

/-- Centered point indicators have no probability denominator.  They are
therefore valid also on the zero atoms of the safe body-center law. -/
def canonicalPointBasis (reference : Slot → FiniteDist Color) (point word : Slot → Color) : ℝ :=
  ∏ slot,((if word slot=point slot then 1 else 0)-(reference slot).weight (point slot))





end
end AFT.MixedKernel

end

section








/-!
# Concrete endpoint-to-zero-fiber theorem for V7's rounding matrix

Unlike the generic probability lemma, the pullback here is the proved
equivalence for the actual path rounding matrix, and the target is genuinely
uniform on its carry-label zero fiber. The endpoint error and bad-carry
probability remain explicit hypotheses: Section 9 must supply those estimates.
-/

set_option backward.isDefEq.respectTransparency false

namespace AFT

open scoped Classical BigOperators

noncomputable instance endpointHyperplaneFintype (n q : ℕ) [NeZero q] :
    Fintype (EndpointHyperplane n q) := by unfold EndpointHyperplane; infer_instance

instance endpointHyperplaneNonempty (n q : ℕ) : Nonempty (EndpointHyperplane n q) :=
  ⟨⟨0, by simp⟩⟩

noncomputable instance zeroFiberFintype (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) : Fintype (ZeroFiber n q column) := by
  unfold ZeroFiber
  infer_instance

instance zeroFiberNonempty (n q : ℕ) (column : Fin (n + 1) → ℤ) :
    Nonempty (ZeroFiber n q column) := by
  refine ⟨⟨0, ?_⟩⟩
  simp [fiberLabel, integerLabel, liftCoordinates, roundingLoad, canonicalCarry, totalCharge]
  change (∑ i : Fin (n + 1), ((pathLoad n 0 i / (q : ℤ) : ℤ) : ZMod q)) = 0
  simp

/-- Uniform on the actual zero fiber, embedded in the ambient residue space. -/
noncomputable def uniformZeroFiber (n q : ℕ) [NeZero q]
    (column : Fin (n + 1) → ℤ) : FiniteDist ((Fin n → ZMod q) × ZMod q) :=
  (FiniteDist.uniform (ZeroFiber n q column)).map Subtype.val







end AFT

end

section





/-! # Exact finite products of countable nonnegative summable masses -/
namespace AFT
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem countableFiniteProduct_summable_sum {State : Type*} (count : ℕ)
    (mass : Fin count → State → ℝ)
    (hnonneg : ∀ i state,0 ≤ mass i state) (hsum : ∀ i,Summable (mass i)) :
    Summable (fun word : Fin count → State => ∏ i,mass i (word i)) ∧
      (∑' word : Fin count → State,∏ i,mass i (word i))=∏ i,∑' state,mass i state := by
  induction count with
  | zero =>
    letI : Fintype (Fin 0 → State) := Fintype.ofFinite _
    exact ⟨(hasSum_fintype _).summable,by simp⟩
  | succ count ih =>
    obtain ⟨htail,hvalue⟩ := ih (fun i => mass i.succ) (fun i => hnonneg i.succ) (fun i => hsum i.succ)
    have hp := (hsum 0).mul_of_nonneg htail (hnonneg 0)
      (fun word => Finset.prod_nonneg (fun i _ => hnonneg i.succ (word i)))
    let equiv : State × (Fin count → State) ≃ (Fin (count+1) → State) := Fin.consEquiv (fun _ => State)
    have hword (point : State × (Fin count → State)) :
        (∏ i,mass i (equiv point i))=mass 0 point.1*∏ i : Fin count,mass i.succ (point.2 i) := by
      simp only [Fin.prod_univ_succ,equiv,Fin.consEquiv,Equiv.coe_fn_mk,Fin.cons_zero,Fin.cons_succ]
    constructor
    · apply equiv.summable_iff.mp
      change Summable (fun point : State × (Fin count → State) => ∏ i,mass i (equiv point i))
      simpa only [hword] using hp
    · rw [← equiv.tsum_eq]
      simp only [hword]
      rw [← (hsum 0).tsum_mul_tsum htail hp,hvalue,Fin.prod_univ_succ]

end
end AFT

end

section









/-! # Fixed-order root-set enumeration, without an exponential powerset

The include/exclude recursion stops as soon as the requested cardinality
is zero. Its stored work and output lengths have polynomial bounds for
fixed order. The actual response uses orders at most twice its cutoff.
-/
namespace AFT.RationalNumerics
open scoped BigOperators

structure CountedSubsequences (α : Type*) where
  value : List (List α)
  work : ℕ

/-- Both recursive lists are materialized once; the counter includes the
append traversal and allocation of the new leading elements. -/
def countedSubsequences {α : Type*} : ℕ → List α → CountedSubsequences α
  | 0,_ => ⟨[[]],1⟩
  | _+1,[] => ⟨[],1⟩
  | order+1,head::tail =>
      let without := countedSubsequences (order+1) tail
      let withHead := countedSubsequences order tail
      ⟨without.value++withHead.value.map (head::·),
        without.work+withHead.work+without.value.length+2*withHead.value.length+4⟩

theorem countedSubsequences_value {α : Type*} (order : ℕ) (source : List α) :
    (countedSubsequences order source).value=source.sublistsLen order := by
  induction source generalizing order with
  | nil => cases order <;> simp [countedSubsequences]
  | cons head tail ih =>
    cases order with
    | zero => simp [countedSubsequences]
    | succ order => simp only [countedSubsequences,ih,List.sublistsLen_succ_cons]





/-- Each small root set is generated from a bounded-cardinality sublist. -/
def boundedRootList (population bound : ℕ) : List (Finset (Fin population)) :=
  (List.range (bound+1)).flatMap (fun order =>
    ((countedSubsequences order (List.finRange population)).value).map List.toFinset)

























end AFT.RationalNumerics

end

section
































namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.CoordinateTransport
end AFT.MixedKernel.CoordinateTransport
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualCovarianceTable
end AFT.V7Calibration.actualCovarianceTable
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairDensity
end AFT.V7Calibration.inactiveCanonicalPairDensity
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactiveEndpointMarginalDensity
end AFT.V7Calibration.inactiveEndpointMarginalDensity
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap


/-! # Literal two-pool input seeds indexed by arbitrary finite coordinate sets -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Primary Body Color : Type*} [Fintype Primary] [Fintype Body] [Fintype Color]
  [DecidableEq Primary] [DecidableEq Body]

def mixedFiniteEquiv : Primary ⊕ Body ≃ Fin (Fintype.card Primary+Fintype.card Body) :=
  (Equiv.sumCongr (Fintype.equivFin Primary) (Fintype.equivFin Body)).trans finSumFinEquiv

def mixedFiniteSeed (kernel : (Primary ⊕ Body → Color) → ℝ) : InputSeed Color where
  primaryOrder := Fintype.card Primary
  bodyOrder := Fintype.card Body
  kernel := fun word => kernel (word ∘ mixedFiniteEquiv)









end
end AFT.RepresentedPolynomial

end

section












namespace AFT
end AFT
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.CanonicalMoments.refresh
end AFT.CanonicalMoments.refresh
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity




/-! # Canonical projection preserves sharp one-fixed fibers without an atom penalty -/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def atomMajorant (p : FiniteDist Color) (source value : Color) : ℝ :=
  (if source=value then (p.weight value)⁻¹ else 0)+1







theorem atomMajorant_source (p : FiniteDist Color) (hp : ∀ color,0<p.weight color) (value : Color) :
    (∑ source,p.weight source*atomMajorant p source value)=2 := by
  simp only [atomMajorant,mul_add,mul_one,Finset.sum_add_distrib,mul_ite,mul_zero,
    Finset.sum_ite_eq',Finset.mem_univ,if_true,p.sum_one,mul_inv_cancel₀ (hp value).ne']
  norm_num

theorem atomMajorant_value (p : FiniteDist Color) (hp : ∀ color,0<p.weight color) (source : Color) :
    (∑ value,p.weight value*atomMajorant p source value)=2 := by
  have he (value) : p.weight value*atomMajorant p source value =
      (if source=value then (1:ℝ) else 0)+p.weight value := by
    unfold atomMajorant
    rw [mul_add]
    split_ifs
    · rw [mul_inv_cancel₀ (hp value).ne',mul_one]
    · ring
  simp only [he,Finset.sum_add_distrib,p.sum_one]
  norm_num

def projectionMajorant (p : Slot → FiniteDist Color) (selected : Finset Slot)
    (source value : Slot → Color) : ℝ := ∏ slot ∈ selected,atomMajorant (p slot) (source slot) (value slot)



theorem expectation_partial_product (p : Slot → FiniteDist Color) (selected : Finset Slot)
    (values : Slot → Color → ℝ) :
    (∑ word,(FiniteDist.independent p).weight word*∏ slot ∈ selected,values slot (word slot)) =
      ∏ slot ∈ selected,∑ color,(p slot).weight color*values slot color := by
  have he (word : Slot → Color) : (∏ slot ∈ selected,values slot (word slot)) =
      ∏ slot,if slot ∈ selected then values slot (word slot) else 1 := (Fintype.prod_ite_mem _ _).symm
  simp_rw [he]
  change (∑ word : Slot → Color,(∏ slot,(p slot).weight (word slot))*
      ∏ slot,if slot ∈ selected then values slot (word slot) else 1) = _
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun slot color => (p slot).weight color*(if slot ∈ selected then values slot color else 1))]
  have ht (slot) : (∑ color,(p slot).weight color*(if slot ∈ selected then values slot color else 1)) =
      if slot ∈ selected then ∑ color,(p slot).weight color*values slot color else 1 := by
    split_ifs <;> simp only [mul_one,FiniteDist.sum_one]
  simp_rw [ht]
  exact Fintype.prod_ite_mem _ _

theorem projectionMajorant_source (p : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot) (value : Slot → Color) :
    (∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value)=2^selected.card := by
  unfold projectionMajorant
  rw [expectation_partial_product p selected (fun slot source => atomMajorant (p slot) source (value slot))]
  simp only [atomMajorant_source _ (hp _),Finset.prod_const]














end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color] [Nonempty Color]
local instance mixedCanonicalFibersSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _













end
end AFT.LocalTensors

end

section








/-! # Centering at one reference and measuring fibers at another

These are the actual coefficients with atoms `δ - r`, divided by `p`.
Only the upper comparison `r ≤ R p` is used; no lower comparison or inverse
minimum atom enters the full, singleton, or supremum bounds.
-/
namespace AFT.MixedKernel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]

def referenceAtom (p r : FiniteDist Color) (source value : Color) : ℝ :=
  (if source=value then (p.weight value)⁻¹ else 0)-r.weight value/p.weight value

def referenceProjection (p r : Slot → FiniteDist Color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (value : Slot → Color) : ℝ :=
  ∑ source,(FiniteDist.independent p).weight source*f source*
    ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)

theorem referenceAtom_eq (p r : FiniteDist Color) (source value : Color) :
    referenceAtom p r source value = ((if source=value then 1 else 0)-r.weight value)/p.weight value := by
  unfold referenceAtom
  split_ifs <;> simp [sub_div,neg_div]

theorem referenceAtom_mean (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color) (source : Color) :
    (∑ value,p.weight value*referenceAtom p r source value)=0 := by
  have he (value : Color) : p.weight value*referenceAtom p r source value =
      (if source=value then 1 else 0)-r.weight value := by
    rw [referenceAtom_eq]
    field_simp [(hp value).ne']
  simp_rw [he]
  simp only [Finset.sum_sub_distrib,r.sum_one]
  simp

theorem referenceAtom_abs_le (p r : FiniteDist Color) (hp : ∀ color,0<p.weight color)
    (bound : ℝ) (hb : 1 ≤ bound) (hr : ∀ color,r.weight color ≤ bound*p.weight color)
    (source value : Color) : |referenceAtom p r source value| ≤ bound*atomMajorant p source value := by
  have hd : 0 ≤ r.weight value/p.weight value := div_nonneg (r.nonneg value) (hp value).le
  have hu : r.weight value/p.weight value ≤ bound := (div_le_iff₀ (hp value)).mpr (hr value)
  unfold referenceAtom atomMajorant
  split_ifs
  · have hi : 0 ≤ (p.weight value)⁻¹ := inv_nonneg.mpr (hp value).le
    apply (abs_sub _ _).trans
    rw [abs_of_nonneg hi,abs_of_nonneg hd]
    nlinarith
  · simpa only [zero_sub,abs_neg,abs_of_nonneg hd,zero_add,mul_one] using hu

theorem referenceProjection_square_majorant (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) (value : Slot → Color) :
    referenceProjection p r selected f value^2 ≤ bound^(2*selected.card)*(2:ℝ)^selected.card*
      ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2 := by
  let kernel (source : Slot → Color) := ∏ slot ∈ selected,referenceAtom (p slot) (r slot) (source slot) (value slot)
  have hk (source) : |kernel source| ≤ bound^selected.card*projectionMajorant p selected source value := by
    dsimp only [kernel]
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      (fun slot _ => referenceAtom_abs_le _ _ (hp slot) bound hb (hr slot) _ _)).trans_eq
      (by rw [Finset.prod_mul_distrib,Finset.prod_const]; rfl)
  have hc : (∑ source,(FiniteDist.independent p).weight source*f source*kernel source)^2 ≤
      (∑ source,(FiniteDist.independent p).weight source*|kernel source|)*
      ∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
    · intro source _; exact mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)
    · intro source _; exact mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _)
    · intro source _; ring_nf; rw [sq_abs]
  have hm : (∑ source,(FiniteDist.independent p).weight source*|kernel source|) ≤
      bound^selected.card*(2:ℝ)^selected.card := by
    rw [← projectionMajorant_source p hp selected value,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_left (hk source) (FiniteDist.nonneg _ _)).trans_eq (by ring)
  have hs : (∑ source,(FiniteDist.independent p).weight source*|kernel source| *f source^2) ≤
      bound^selected.card*∑ source,(FiniteDist.independent p).weight source*
        projectionMajorant p selected source value*f source^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro source _
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hk source)
      (FiniteDist.nonneg _ _)) (sq_nonneg _)).trans_eq (by ring)
  apply hc.trans
  apply (mul_le_mul hm hs
    (Finset.sum_nonneg fun source _ => mul_nonneg (mul_nonneg (FiniteDist.nonneg _ _) (abs_nonneg _)) (sq_nonneg _))
    (by positivity)).trans_eq
  rw [pow_mul]
  ring





theorem referenceProjection_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (selected : Finset Slot)
    (f : (Slot → Color) → ℝ) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent p).l2Sq (referenceProjection p r selected f) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq f := by
  have hb0 : 0 ≤ bound := le_trans (by norm_num) hb
  have hm (source : Slot → Color) :
      (∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value) =
      (2:ℝ)^selected.card := by
    unfold projectionMajorant
    rw [expectation_partial_product p selected (fun slot value => atomMajorant (p slot) (source slot) value)]
    simp only [atomMajorant_value _ (hp _),Finset.prod_const]
  calc
    _ ≤ ∑ value,(FiniteDist.independent p).weight value*(bound^(2*selected.card)*(2:ℝ)^selected.card*
        ∑ source,(FiniteDist.independent p).weight source*projectionMajorant p selected source value*f source^2) :=
      Finset.sum_le_sum fun value _ => mul_le_mul_of_nonneg_left
        (referenceProjection_square_majorant p r hp selected f bound hb hr value) (FiniteDist.nonneg _ _)
    _ = bound^(2*selected.card)*(2:ℝ)^selected.card*∑ source,(FiniteDist.independent p).weight source*f source^2*
        ∑ value,(FiniteDist.independent p).weight value*projectionMajorant p selected source value := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro source _
      apply Finset.sum_congr rfl
      intro value _
      ring
    _ = _ := by
      simp_rw [hm]
      rw [← Finset.sum_mul]
      simp only [FiniteDist.l2Sq,FiniteDist.expectation,mul_pow]
      rw [Nat.mul_comm 2 selected.card,pow_mul]
      ring

end
end AFT.MixedKernel

namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance mixedReferenceCanonicalFibersSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

/-- The literal selected coefficient centered at `r`, expressed as a density
relative to `p` on precisely the selected slots. -/
def referenceRestrictedComponent (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) (word : selected → Color) : ℝ :=
  ∑ input,mass input*∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (input slot) (word slot)

theorem referenceRestrictedComponent_canonical (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    Hoeffding.Canonical (fun slot : selected => p slot) Finset.univ
      (referenceRestrictedComponent p r mass selected) := by
  constructor
  · intro first second heq
    have heq : first=second := funext (fun slot => heq slot (Finset.mem_univ slot))
    rw [heq]
  · intro fixed _ values
    simp only [referenceRestrictedComponent,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro source _
    have hprod (color : Color) :
        (∏ slot : selected,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (Function.update values fixed color slot)) =
          MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
            ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ fixed),Function.update_self]
      congr 1
      apply Finset.prod_congr rfl
      intro slot hs
      rw [Function.update_of_ne (Finset.mem_erase.mp hs).1]
    simp_rw [hprod]
    have hterm (color : Color) : (p fixed).weight color*(mass source*
        (MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color*
          ∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))) =
        (mass source*∏ slot ∈ Finset.univ.erase fixed,MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values slot))*
          ((p fixed).weight color*MixedKernel.referenceAtom (p fixed) (r fixed) (source fixed) color) := by ring
    simp_rw [hterm]
    rw [← Finset.mul_sum,MixedKernel.referenceAtom_mean _ _ (hp fixed),mul_zero]

theorem referenceRestrictedComponent_eq (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (word : Slot → Color) :
    referenceRestrictedComponent p r mass selected (fun slot => word slot) =
      MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source) word := by
  unfold referenceRestrictedComponent MixedKernel.referenceProjection
  apply Finset.sum_congr rfl
  intro source _
  have hpos : (FiniteDist.independent p).weight source ≠ 0 :=
    ne_of_gt (Finset.prod_pos fun slot _ => hp slot (source slot))
  rw [mul_div_cancel₀ _ hpos]
  congr 1
  exact Finset.prod_coe_sort selected (fun slot => MixedKernel.referenceAtom (p slot) (r slot) (source slot) (word slot))



theorem referenceRestrictedComponent_l2Sq_le (p r : Slot → FiniteDist Color)
    (hp : ∀ slot color,0<(p slot).weight color) (mass : (Slot → Color) → ℝ)
    (selected : Finset Slot) (bound : ℝ) (hb : 1 ≤ bound)
    (hr : ∀ slot color,(r slot).weight color ≤ bound*(p slot).weight color) :
    (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) ≤
      ((2*bound)^selected.card)^2*(FiniteDist.independent p).l2Sq
        (fun source => mass source/(FiniteDist.independent p).weight source) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  have hh := independent_restriction_expectation p selected
    (fun word => referenceRestrictedComponent p r mass selected word^2)
  simp_rw [referenceRestrictedComponent_eq p r hp] at hh
  have he : (FiniteDist.independent (fun slot : selected => p slot)).l2Sq (referenceRestrictedComponent p r mass selected) =
      (FiniteDist.independent p).l2Sq (MixedKernel.referenceProjection p r selected
        (fun source => mass source/(FiniteDist.independent p).weight source)) := by
    convert hh.symm using 1
    all_goals
      unfold FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_congr (by ext; simp)
      intro word _
      rfl
  rw [he]
  exact MixedKernel.referenceProjection_l2Sq_le p r hp selected _ bound hb hr

variable [Nonempty Color]











end
end AFT.LocalTensors

end

section



















































namespace AFT
end AFT
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.attachedMass
end AFT.BlockDensity.attachedMass
namespace AFT.BoundaryCalibration
end AFT.BoundaryCalibration
namespace AFT.BoundaryCalibration.protectedGaussianLaw
end AFT.BoundaryCalibration.protectedGaussianLaw
namespace AFT.CanonicalMoments
end AFT.CanonicalMoments
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.FormalLogarithm
end AFT.FormalLogarithm
namespace AFT.FormalLogarithm.finiteLogarithm
end AFT.FormalLogarithm.finiteLogarithm
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.actualBodyChannel
end AFT.GaussianSource.actualBodyChannel
namespace AFT.GaussianSource.actualPrimaryChannel
end AFT.GaussianSource.actualPrimaryChannel
namespace AFT.GaussianSource.actualResponse
end AFT.GaussianSource.actualResponse
namespace AFT.GaussianSource.compensatorRootShift
end AFT.GaussianSource.compensatorRootShift
namespace AFT.GaussianSource.pairSample
end AFT.GaussianSource.pairSample
namespace AFT.GaussianSource.pairSourceLaw
end AFT.GaussianSource.pairSourceLaw
namespace AFT.GaussianSource.pairSourceShift
end AFT.GaussianSource.pairSourceShift
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.blockReplacement
end AFT.MixedKernel.blockReplacement
namespace AFT.MixedKernel.channelDensity
end AFT.MixedKernel.channelDensity
namespace AFT.MixedKernel.columnAverage
end AFT.MixedKernel.columnAverage
namespace AFT.MixedKernel.pairKernel
end AFT.MixedKernel.pairKernel
namespace AFT.MixedKernel.pairReference
end AFT.MixedKernel.pairReference
namespace AFT.MixedKernel.rowAverage
end AFT.MixedKernel.rowAverage
namespace AFT.MixedKernel.singletonJoin
end AFT.MixedKernel.singletonJoin
namespace AFT.MixedKernel.singletonKernel
end AFT.MixedKernel.singletonKernel
namespace AFT.MixedKernel.singletonSlice
end AFT.MixedKernel.singletonSlice
namespace AFT.MixedKernel.tripleProductKernel
end AFT.MixedKernel.tripleProductKernel
namespace AFT.Parameters
end AFT.Parameters
namespace AFT.Parameters.anchorWidth
end AFT.Parameters.anchorWidth
namespace AFT.Parameters.safeMargin
end AFT.Parameters.safeMargin
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.fourOutputCount
end AFT.PhysicalBlockTensors.fourOutputCount
namespace AFT.PhysicalBlockTensors.tripleOutputCount
end AFT.PhysicalBlockTensors.tripleOutputCount
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.InputTableCanonical
end AFT.RepresentedPolynomial.InputTableCanonical
namespace AFT.RepresentedPolynomial.bodySingletonInput
end AFT.RepresentedPolynomial.bodySingletonInput
namespace AFT.RepresentedPolynomial.groupedFiniteSeed
end AFT.RepresentedPolynomial.groupedFiniteSeed
namespace AFT.RepresentedPolynomial.inputRate
end AFT.RepresentedPolynomial.inputRate
namespace AFT.RepresentedPolynomial.inputReference
end AFT.RepresentedPolynomial.inputReference
namespace AFT.RepresentedPolynomial.logarithm
end AFT.RepresentedPolynomial.logarithm
namespace AFT.RepresentedPolynomial.primaryCoordinates
end AFT.RepresentedPolynomial.primaryCoordinates
namespace AFT.RepresentedPolynomial.primaryPairInput
end AFT.RepresentedPolynomial.primaryPairInput
namespace AFT.RepresentedPolynomial.primarySingletonInput
end AFT.RepresentedPolynomial.primarySingletonInput
namespace AFT.RepresentedPolynomial.primarySplitEquiv
end AFT.RepresentedPolynomial.primarySplitEquiv
namespace AFT.RepresentedPolynomial.primaryTripleInput
end AFT.RepresentedPolynomial.primaryTripleInput
namespace AFT.RepresentedPolynomial.seedChannel
end AFT.RepresentedPolynomial.seedChannel
namespace AFT.RepresentedPolynomial.seedExpansion
end AFT.RepresentedPolynomial.seedExpansion
namespace AFT.RepresentedPolynomial.seedExpansion.match_1
end AFT.RepresentedPolynomial.seedExpansion.match_1
namespace AFT.RepresentedPolynomial.splitPrimaryIndex
end AFT.RepresentedPolynomial.splitPrimaryIndex
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace AFT.V7Calibration.activeCanonicalPairDensity
end AFT.V7Calibration.activeCanonicalPairDensity
namespace AFT.V7Calibration.activeCanonicalPairInput
end AFT.V7Calibration.activeCanonicalPairInput
namespace AFT.V7Calibration.activeEndpointMarginalDensity
end AFT.V7Calibration.activeEndpointMarginalDensity
namespace AFT.V7Calibration.actualActivatedSource
end AFT.V7Calibration.actualActivatedSource
namespace AFT.V7Calibration.actualActiveMarginalBodyInput
end AFT.V7Calibration.actualActiveMarginalBodyInput
namespace AFT.V7Calibration.actualActiveMarginalBodyKernel
end AFT.V7Calibration.actualActiveMarginalBodyKernel
namespace AFT.V7Calibration.actualActiveTripleInput
end AFT.V7Calibration.actualActiveTripleInput
namespace AFT.V7Calibration.actualActiveTripleKernel
end AFT.V7Calibration.actualActiveTripleKernel
namespace AFT.V7Calibration.actualBasePrimary
end AFT.V7Calibration.actualBasePrimary
namespace AFT.V7Calibration.actualBodyCenter
end AFT.V7Calibration.actualBodyCenter
namespace AFT.V7Calibration.actualBodyIntegerProfile
end AFT.V7Calibration.actualBodyIntegerProfile
namespace AFT.V7Calibration.actualBodyMean
end AFT.V7Calibration.actualBodyMean
namespace AFT.V7Calibration.actualCompanionLaw
end AFT.V7Calibration.actualCompanionLaw
namespace AFT.V7Calibration.actualCovarianceSeed
end AFT.V7Calibration.actualCovarianceSeed
namespace AFT.V7Calibration.actualFixedRootTriple
end AFT.V7Calibration.actualFixedRootTriple
namespace AFT.V7Calibration.actualFixedRootTripleLaw
end AFT.V7Calibration.actualFixedRootTripleLaw
namespace AFT.V7Calibration.actualInactiveMarginalBodyInput
end AFT.V7Calibration.actualInactiveMarginalBodyInput
namespace AFT.V7Calibration.actualInactiveMarginalBodyKernel
end AFT.V7Calibration.actualInactiveMarginalBodyKernel
namespace AFT.V7Calibration.actualInactiveResidual
end AFT.V7Calibration.actualInactiveResidual
namespace AFT.V7Calibration.actualInactiveTripleInput
end AFT.V7Calibration.actualInactiveTripleInput
namespace AFT.V7Calibration.actualInactiveTripleKernel
end AFT.V7Calibration.actualInactiveTripleKernel
namespace AFT.V7Calibration.actualJointPairedNumerator
end AFT.V7Calibration.actualJointPairedNumerator
namespace AFT.V7Calibration.actualLeadingOutput
end AFT.V7Calibration.actualLeadingOutput
namespace AFT.V7Calibration.actualMarkedPair
end AFT.V7Calibration.actualMarkedPair
namespace AFT.V7Calibration.actualPrimary
end AFT.V7Calibration.actualPrimary
namespace AFT.V7Calibration.actualReferenceMean
end AFT.V7Calibration.actualReferenceMean
namespace AFT.V7Calibration.actualSliceAtSource
end AFT.V7Calibration.actualSliceAtSource
namespace AFT.V7Calibration.actualSliceMean
end AFT.V7Calibration.actualSliceMean
namespace AFT.V7Calibration.actualSourceShift
end AFT.V7Calibration.actualSourceShift
namespace AFT.V7Calibration.actualSourceShift.match_1
end AFT.V7Calibration.actualSourceShift.match_1
namespace AFT.V7Calibration.actualZeroSliceMean
end AFT.V7Calibration.actualZeroSliceMean
namespace AFT.V7Calibration.anchorMean
end AFT.V7Calibration.anchorMean
namespace AFT.V7Calibration.averagedInactiveBody
end AFT.V7Calibration.averagedInactiveBody
namespace AFT.V7Calibration.averagedInactivePair
end AFT.V7Calibration.averagedInactivePair
namespace AFT.V7Calibration.blurredAnchorKernel
end AFT.V7Calibration.blurredAnchorKernel
namespace AFT.V7Calibration.bodyCanonicalInput
end AFT.V7Calibration.bodyCanonicalInput
namespace AFT.V7Calibration.bodyCenteredOutside
end AFT.V7Calibration.bodyCenteredOutside
namespace AFT.V7Calibration.bodyInside
end AFT.V7Calibration.bodyInside
namespace AFT.V7Calibration.bodyOutside
end AFT.V7Calibration.bodyOutside
namespace AFT.V7Calibration.conditionalJointOutput
end AFT.V7Calibration.conditionalJointOutput
namespace AFT.V7Calibration.coreIntegerProfile
end AFT.V7Calibration.coreIntegerProfile
namespace AFT.V7Calibration.covarianceCoefficient
end AFT.V7Calibration.covarianceCoefficient
namespace AFT.V7Calibration.errorLaw
end AFT.V7Calibration.errorLaw
namespace AFT.V7Calibration.errorStarts
end AFT.V7Calibration.errorStarts
namespace AFT.V7Calibration.fixedChartTriple
end AFT.V7Calibration.fixedChartTriple
namespace AFT.V7Calibration.fixedPairedChartRaw
end AFT.V7Calibration.fixedPairedChartRaw
namespace AFT.V7Calibration.fixedPairedKernel
end AFT.V7Calibration.fixedPairedKernel
namespace AFT.V7Calibration.fixedPairedPrimaryDensity
end AFT.V7Calibration.fixedPairedPrimaryDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDensity
end AFT.V7Calibration.inactiveAttachedBodyDensity
namespace AFT.V7Calibration.inactiveAttachedBodyDifference
end AFT.V7Calibration.inactiveAttachedBodyDifference
namespace AFT.V7Calibration.inactiveCanonicalPairInput
end AFT.V7Calibration.inactiveCanonicalPairInput
namespace AFT.V7Calibration.inactiveEndpointDensity
end AFT.V7Calibration.inactiveEndpointDensity
namespace AFT.V7Calibration.inactiveEndpointDifference
end AFT.V7Calibration.inactiveEndpointDifference
namespace AFT.V7Calibration.inactivePairAtSource
end AFT.V7Calibration.inactivePairAtSource
namespace AFT.V7Calibration.inactiveStart
end AFT.V7Calibration.inactiveStart
namespace AFT.V7Calibration.independentJointHigherSeed
end AFT.V7Calibration.independentJointHigherSeed
namespace AFT.V7Calibration.independentJointInverse
end AFT.V7Calibration.independentJointInverse
namespace AFT.V7Calibration.independentOriginalJointSeed
end AFT.V7Calibration.independentOriginalJointSeed
namespace AFT.V7Calibration.independentPairedDensity
end AFT.V7Calibration.independentPairedDensity
namespace AFT.V7Calibration.independentPairedNumerator
end AFT.V7Calibration.independentPairedNumerator
namespace AFT.V7Calibration.independentReferenceHilbertConstant
end AFT.V7Calibration.independentReferenceHilbertConstant
namespace AFT.V7Calibration.integerAnchorProfile
end AFT.V7Calibration.integerAnchorProfile
namespace AFT.V7Calibration.integerShiftProfile
end AFT.V7Calibration.integerShiftProfile
namespace AFT.V7Calibration.localPairMixture
end AFT.V7Calibration.localPairMixture
namespace AFT.V7Calibration.primaryJointNumerator
end AFT.V7Calibration.primaryJointNumerator
namespace AFT.V7Calibration.publicAnchorFiniteProfile
end AFT.V7Calibration.publicAnchorFiniteProfile
namespace AFT.V7Calibration.publicChartEndpointMean
end AFT.V7Calibration.publicChartEndpointMean
namespace AFT.V7Calibration.publicChartRaw
end AFT.V7Calibration.publicChartRaw
namespace AFT.V7Calibration.responseOperator
end AFT.V7Calibration.responseOperator
namespace AFT.V7Calibration.signedChartTriple
end AFT.V7Calibration.signedChartTriple
namespace AFT.V7Calibration.signedDiffuseJoint
end AFT.V7Calibration.signedDiffuseJoint
namespace AFT.V7Calibration.signedSliceAtSource
end AFT.V7Calibration.signedSliceAtSource
namespace AFT.positiveKernelMap
end AFT.positiveKernelMap
namespace AFT.primaryRankEnvelope
end AFT.primaryRankEnvelope
namespace AFT.primaryTranslationEnvelope
end AFT.primaryTranslationEnvelope



/-! # The actual independent numerator, replacing only old primary coordinates -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section

structure PendingInput (Color : Type*) where
  seed : InputSeed Color
  pending : Finset (Fin seed.primaryOrder)



end
end AFT.RepresentedPolynomial

namespace AFT.V7Calibration
open GaussianSource BoundaryCalibration RepresentedPolynomial Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance pendingExpansionFinDecEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local instance] actualModulusNeZero





def pendingLinearState {Color : Type*} (state : PendingInput Color) : PendingInput Color :=
  if h : state.pending.Nonempty then ⟨state.seed,state.pending.erase (state.pending.min' h)⟩ else state





@[simp] theorem pendingLinearState_seed {Color : Type*} (state : PendingInput Color) :
    (pendingLinearState state).seed=state.seed := by
  unfold pendingLinearState
  split_ifs <;> rfl











end
end AFT.V7Calibration

end

section















/-! # The literal reference-centered coefficients reconstruct the full physical PGF -/
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
local instance referenceCoefficientSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

def referenceCoefficientForm (primary reference : FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (selected : Finset Slot) : MvPolynomial Color ℝ :=
  ∑ word : selected → Color,
    MvPolynomial.C (LocalTensors.referenceRestrictedComponent (fun _ : Slot => primary)
      (fun _ : Slot => reference) mass selected word*∏ slot,primary.weight (word slot))*
      ∏ slot,MvPolynomial.X (word slot)









end
end AFT.RepresentedPolynomial

end

section








namespace AFT
end AFT
namespace AFT.MixedKernel
end AFT.MixedKernel



/-! # The actual linear coefficient uses only a positive singleton marginal -/
namespace AFT.LocalTensors
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [Fintype Color] [DecidableEq Slot]
local instance referenceSingletonSubtypeDecEq (selected : Finset Slot) : DecidableEq selected := Classical.decEq _

theorem referenceRestrictedComponent_singleton (p r : Slot → FiniteDist Color)
    (mass : (Slot → Color) → ℝ) (slot : Slot) (values : ({slot} : Finset Slot) → Color) :
    referenceRestrictedComponent p r mass {slot} values =
      ((∑ word,if word slot=values ⟨slot,Finset.mem_singleton_self slot⟩ then mass word else 0) -
        (r slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩)*(∑ word,mass word)) /
      (p slot).weight (values ⟨slot,Finset.mem_singleton_self slot⟩) := by
  have hprod (source : Slot → Color) :
      (∏ index : ({slot} : Finset Slot),MixedKernel.referenceAtom (p index) (r index) (source index) (values index)) =
      MixedKernel.referenceAtom (p slot) (r slot) (source slot) (values ⟨slot,Finset.mem_singleton_self slot⟩) :=
    Fintype.prod_subsingleton _ (⟨slot,Finset.mem_singleton_self slot⟩ : ({slot} : Finset Slot))
  unfold referenceRestrictedComponent
  simp_rw [hprod,MixedKernel.referenceAtom_eq]
  rw [sub_div,Finset.sum_div,Finset.mul_sum,Finset.sum_div,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> ring





end
end AFT.LocalTensors

end



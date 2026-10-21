-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P24
-- name    : QAlgorithms_Papers_Independent_Next46_P24
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T13:54:58.989294+00:00
-- url     : https://prove2.me/theorems/bf931e81-1a86-45a0-a0f1-7b5984d313d4
-- title:
--   Definitions for Minimal computational-space implementation of multi-round quantum protocols
-- statement:
--   The objects the formalized statements of *Minimal computational-space implementation of multi-round quantum protocols* (arXiv:1006.1780) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Pair`: PDF pp.3-4: ordered pairs, used for wires 10 and for the training pair 21'.
--   - `Training`: PDF pp.3-4: the second channel input is ordered 2,1',0'.
--   - `InversionWires`: PDF p.3: comb coordinates and ambient final-memory coordinates, ordered 3210.
--   - `CombMatrix`: PDF p.3: operators on the four physical wires.
--   - `haar`: PDF p.3, Eq.(7): Haar probability measure normalized on the whole of SU(d).
--   - `IsInversionComb`: PDF p.3, Eq.(5): positivity and both causal constraints, with a genuine 10 prefix.
--   - `inverseChoiTarget`: PDF p.3, Eq.(6): |U dagger>> on 30 tensor |U star>> on 21, permuted into wire order 3210. These Choi vectors are unnormalized.
--   - `inversionFidelity`: PDF p.3, Eq.(6): channel Choi-state fidelity, including the factor 1/d squared.
--   - `inversionAverage`: PDF p.3, Eq.(7): average over the unknown U, with the fixed comb chosen first.
--   - `covarianceMatrix`: PDF p.3, Eq.(8): U on both wires 31 and W on both wires 20; no conjugated factors.
--   - `twirlKernel`: PDF p.3, proof of Lemma 1: simultaneous two-group conjugation.
--   - `inversionTwirl`: PDF p.3, proof of Lemma 1: concrete Haar twirl, using probability product measure.
--   - `InversionCovariant`: PDF p.3, Eq.(8): commuting with the displayed U,W representation.
--   - `Optimal`: PDF p.3: maximization over all fixed feasible combs, not just the invariant ansatz.
--   - `inversionSectorDimension`: PDF p.3, Eqs.(9)-(11): false denotes the symmetric sector, true the antisymmetric one.
--   - `inversionPairProjector`: PDF p.3, Eq.(9): (identity plus or minus swap)/2 on one ordered pair.
--   - `inversionSector`: PDF p.3, Eq.(9): paired-sector product on 31,20, transported back to order 3210.
--   - `invariantComb`: PDF p.3, Eq.(9): the invariant ansatz, with coefficient nonnegativity stated separately.
--   - `optimalComb`: PDF p.3, Eq.(11): the particular attaining comb, not a claim of global uniqueness.
--   - `optimalSupport`: PDF pp.3-4: support projector of the particular real Eq.(11) comb, identified below.
--   - `optimalRoot`: PDF p.3, Eq.(12): positive square root of C star, expressed in its two real sectors.
--   - `optimalInverseRoot`: PDF p.3, Eq.(13): inverse square root on the support; zero on the other two sectors.
--   - `inversionKernel`: PDF p.3, Eq.(11): the Haar integrand as a rank-one Choi operator in order 3210.
--   - `inversionFirstStage`: PDF p.3, the formula before Eq.(12): V1 prepares |I>>/sqrt(d) and stores wire 0.
--   - `secondIsometry`: PDF p.3, Eq.(12): V2 embedded into output wire 3 tensor the ambient four-wire space. Its image is in output tensor Supp(C star); no ambient-kernel identity is asserted.
--   - `networkAmplitude`: PDF pp.2-3, Eq.(3): actual contraction of the two fixed stages before final memory trace.
--   - `networkChoi`: PDF pp.2-3, Eq.(3): the sequential network's unnormalized Choi matrix.
--   - `measurementSeed`: PDF p.3, Eq.(13): |Uhat transpose>> on 3'0' tensor |Uhat>> on 2'1'.
--   - `memoryPOVM`: PDF p.3, Eq.(13): the positive POVM density in ambient coordinates, zero on the kernel.
--   - `trainingPOVM`: PDF p.4: training POVM density d |Uhat>><<Uhat| on the pair 2,1'. Printed un-hatted factors in this formula are changed to the estimated unitary.
--   - `secondChannel`: PDF pp.3-4, Eq.(14): coherent second channel, discarding only its final memory.
--   - `memoryBranch`: PDF p.4, Eq.(14): memory-measured branch in the Stinespring implementation.
--   - `residualState`: PDF p.4, Eq.(14): unnormalized residual stored state after contraction with <Uhat|.
--   - `feedForwardBranch`: PDF p.4, Eq.(14): training measurement followed by conditional Uhat dagger on stored 0'.
--   - `trainingPreparation`: PDF pp.3-4: physical application of the unknown U to the output of V1.
--   - `preparedState`: PDF pp.3-4: normalized post-call state |U>><<U|/d on 2,1' and the stored input on 0'. The source's post-call wire label 11' is corrected to the physical output 21'.
-- source:
--   Minimal computational-space implementation of multi-round quantum protocols, arXiv:1006.1780v1, https://arxiv.org/abs/1006.1780v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Measurement

/-!
Statements from Bisio, D'Ariano, Perinotti and Chiribella, arXiv:1006.1780v1.
Mathlib Fin, specialUnitaryGroup and the subtype matrix projection are reused directly.
All coordinate factors have dimension d. Four-wire coordinates are ordered 3210.
The only source corrections are recorded beside the corresponding declarations.
The general changing-support construction is explicitly deferred in HARD.md.
Compilation is pending the mechanical handoff.
-/

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators Matrix ComplexConjugate ComplexOrder Matrix.Norms.Elementwise
open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Next46.P24

/-- PDF pp.3-4: ordered pairs, used for wires 10 and for the training pair 21'. -/
abbrev Pair (d : ℕ) := Fin d × Fin d

/-- PDF pp.3-4: the second channel input is ordered 2,1',0'. -/
abbrev Training (d : ℕ) := Fin d × Pair d

/-- PDF p.3: comb coordinates and ambient final-memory coordinates, ordered 3210. -/
abbrev InversionWires (d : ℕ) := Fin d × Training d

/-- PDF p.3: operators on the four physical wires. -/
abbrev CombMatrix (d : ℕ) := Matrix (InversionWires d) (InversionWires d) ℂ

/-- PDF p.3: the finite matrix integrals use the entrywise continuous norm. -/
local instance combContinuousENorm (d : ℕ) : ContinuousENorm (CombMatrix d) :=
  inferInstanceAs (ContinuousENorm (InversionWires d → InversionWires d → ℂ))

/-- PDF p.4: topology for integrals of two-wire measurement densities. -/
local instance pairContinuousENorm (d : ℕ) :
    ContinuousENorm (Matrix (Pair d) (Pair d) ℂ) :=
  inferInstanceAs (ContinuousENorm (Pair d → Pair d → ℂ))

/-- PDF p.4: topology for integrals of conditional output matrices. -/
local instance wireContinuousENorm (d : ℕ) :
    ContinuousENorm (Matrix (Fin d) (Fin d) ℂ) :=
  inferInstanceAs (ContinuousENorm (Fin d → Fin d → ℂ))

/-- PDF p.3: the actual SU(d) outcome group carries its Borel sigma algebra. -/
instance suMeasurable (d : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) := borel _

/-- PDF p.3: this measurable space is the Borel space of the matrix subtype. -/
instance suBorel (d : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) := ⟨rfl⟩

/-- PDF p.3: inversion is the continuous adjoint on the special-unitary subtype. -/
instance suContinuousInv (d : ℕ) : ContinuousInv (Matrix.specialUnitaryGroup (Fin d) ℂ) where
  continuous_inv := continuous_induced_rng.mpr continuous_subtype_val.star

/-- PDF p.3: multiplication and inversion inherit the matrix-subtype topology. -/
instance suTopologicalGroup (d : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin d) ℂ) where

/-- PDF p.3: finite-dimensional SU(d) is compact, allowing whole-group Haar normalization.
The construction follows the inspected accepted compact-unitary infrastructure. -/
instance suCompact (d : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin d) ℂ) := by
  have hc : IsClosed (Matrix.specialUnitaryGroup (Fin d) ℂ :
      Set (Matrix (Fin d) (Fin d) ℂ)) :=
    isClosed_unitary.inter (isClosed_eq
      (show Continuous (fun A : Matrix (Fin d) (Fin d) ℂ => A.det) from
        continuous_id.matrix_det) continuous_const)
  have hb : Bornology.IsBounded (Matrix.specialUnitaryGroup (Fin d) ℂ :
      Set (Matrix (Fin d) (Fin d) ℂ)) :=
    (show Bornology.IsBounded (Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1) from
      Metric.isBounded_closedBall).subset (by
        intro U hU
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact entrywise_sup_norm_bound_of_unitary hU.1)
  exact isCompact_iff_compactSpace.mp (Metric.isCompact_of_isClosed_isBounded hc hb)

/-- PDF p.3, Eq.(7): Haar probability measure normalized on the whole of SU(d). -/
def haar (d : ℕ) : Measure (Matrix.specialUnitaryGroup (Fin d) ℂ) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts _)

/-- PDF p.3, Eq.(5): positivity and both causal constraints, with a genuine 10 prefix. -/
def IsInversionComb {d : ℕ} (C : CombMatrix d) : Prop :=
  C.PosSemidef ∧ ∃ B : Matrix (Pair d) (Pair d) ℂ,
    B.PosSemidef ∧ traceLeft C = Matrix.kronecker (1 : Matrix (Fin d) _ ℂ) B ∧
    traceLeft B = 1

/-- PDF p.3, Eq.(6): |U dagger>> on 30 tensor |U star>> on 21,
permuted into wire order 3210. These Choi vectors are unnormalized. -/
def inverseChoiTarget {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : InversionWires d → ℂ :=
  fun x => conj (U.val x.2.2.2 x.1) *
    conj (U.val x.2.1 x.2.2.1)

/-- PDF p.3, Eq.(6): channel Choi-state fidelity, including the factor 1/d squared. -/
def inversionFidelity {d : ℕ} (C : CombMatrix d) (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : ℝ :=
  (∑ x, ∑ y, conj (inverseChoiTarget U x) * C x y * inverseChoiTarget U y).re / (d : ℝ)^2

/-- PDF p.3, Eq.(7): average over the unknown U, with the fixed comb chosen first. -/
def inversionAverage {d : ℕ} (C : CombMatrix d) : ℝ :=
  ∫ U, inversionFidelity C U ∂haar d

/-- PDF p.3, Eq.(8): U on both wires 31 and W on both wires 20; no conjugated factors. -/
def covarianceMatrix {d : ℕ} (U W : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : CombMatrix d :=
  fun x y => U.val x.1 y.1 * W.val x.2.1 y.2.1 *
    U.val x.2.2.1 y.2.2.1 * W.val x.2.2.2 y.2.2.2

/-- PDF p.3, proof of Lemma 1: simultaneous two-group conjugation. -/
def twirlKernel {d : ℕ} (C : CombMatrix d) (z : (Matrix.specialUnitaryGroup (Fin d) ℂ) × (Matrix.specialUnitaryGroup (Fin d) ℂ)) : CombMatrix d :=
  covarianceMatrix z.1 z.2 * C * (covarianceMatrix z.1 z.2)ᴴ

/-- PDF p.3, proof of Lemma 1: concrete Haar twirl, using probability product measure. -/
def inversionTwirl {d : ℕ} (C : CombMatrix d) : CombMatrix d :=
  ∫ z, twirlKernel C z ∂(haar d).prod (haar d)

/-- PDF p.3, Eq.(8): commuting with the displayed U,W representation. -/
def InversionCovariant {d : ℕ} (C : CombMatrix d) : Prop :=
  ∀ U W : (Matrix.specialUnitaryGroup (Fin d) ℂ), C * covarianceMatrix U W = covarianceMatrix U W * C

/-- PDF p.3: maximization over all fixed feasible combs, not just the invariant ansatz. -/
def Optimal {d : ℕ} (C : CombMatrix d) : Prop :=
  IsInversionComb C ∧ ∀ D : CombMatrix d, IsInversionComb D → inversionAverage D ≤ inversionAverage C

/-- PDF p.3, Eqs.(9)-(11): false denotes the symmetric sector, true the antisymmetric one. -/
def inversionSectorDimension (d : ℕ) (antisymmetric : Bool) : ℝ :=
  if antisymmetric then (d : ℝ) * ((d : ℝ) - 1) / 2
  else (d : ℝ) * ((d : ℝ) + 1) / 2

/-- PDF p.3, Eq.(9): (identity plus or minus swap)/2 on one ordered pair. -/
def inversionPairProjector (d : ℕ) (antisymmetric : Bool) : Matrix (Pair d) (Pair d) ℂ :=
  fun x y => ((if x = y then 1 else 0) +
    (if antisymmetric then (-1 : ℂ) else 1) *
      (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)) / 2

/-- PDF p.3, Eq.(9): paired-sector product on 31,20, transported back to order 3210. -/
def inversionSector (d : ℕ) (b c : Bool) : CombMatrix d :=
  fun x y => inversionPairProjector d b (x.1,x.2.2.1) (y.1,y.2.2.1) *
    inversionPairProjector d c (x.2.1,x.2.2.2) (y.2.1,y.2.2.2)

/-- PDF p.3, Eq.(9): the invariant ansatz, with coefficient nonnegativity stated separately. -/
def invariantComb (d : ℕ) (a : Bool → Bool → ℝ) : CombMatrix d :=
  ∑ b : Bool, ∑ c : Bool, (a b c : ℂ) • inversionSector d b c

/-- PDF p.3, Eq.(11): the particular attaining comb, not a claim of global uniqueness. -/
def optimalComb (d : ℕ) : CombMatrix d :=
  ∑ b : Bool, ((inversionSectorDimension d b : ℂ)⁻¹) • inversionSector d b b

/-- PDF pp.3-4: support projector of the particular real Eq.(11) comb, identified below. -/
def optimalSupport (d : ℕ) : CombMatrix d :=
  ∑ b : Bool, inversionSector d b b

/-- PDF p.3, Eq.(12): positive square root of C star, expressed in its two real sectors. -/
def optimalRoot (d : ℕ) : CombMatrix d :=
  ∑ b : Bool, (((Real.sqrt (inversionSectorDimension d b))⁻¹ : ℝ) : ℂ) • inversionSector d b b

/-- PDF p.3, Eq.(13): inverse square root on the support; zero on the other two sectors. -/
def optimalInverseRoot (d : ℕ) : CombMatrix d :=
  ∑ b : Bool, (Real.sqrt (inversionSectorDimension d b) : ℂ) • inversionSector d b b

/-- PDF p.3, Eq.(11): the Haar integrand as a rank-one Choi operator in order 3210. -/
def inversionKernel {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : CombMatrix d :=
  fun x y => inverseChoiTarget U x * conj (inverseChoiTarget U y)

example (d : ℕ) : haar d Set.univ = 1 := Measure.haarMeasure_self

example : inversionSectorDimension 2 false = 3 ∧ inversionSectorDimension 2 true = 1 := by
  norm_num [inversionSectorDimension]

example : inversionPairProjector 1 true = 0 := by
  ext x y
  have hxy : x = y := Subsingleton.elim x y
  have hswap : x.1 = y.2 ∧ x.2 = y.1 :=
    ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  change ((if x = y then (1 : ℂ) else 0) + (-1 : ℂ) *
    (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)) / 2 = 0
  rw [if_pos hxy, if_pos hswap]
  norm_num

/-- PDF p.3, the formula before Eq.(12): V1 prepares |I>>/sqrt(d) and stores wire 0. -/
def inversionFirstStage (d : ℕ) : Matrix (Fin d × Pair d) (Fin d) ℂ :=
  fun x i => if x.1 = x.2.1 ∧ x.2.2 = i then (Real.sqrt (d : ℝ) : ℂ)⁻¹ else 0

/-- PDF p.3, Eq.(12): V2 embedded into output wire 3 tensor the ambient four-wire space.
Its image is in output tensor Supp(C star); no ambient-kernel identity is asserted. -/
def secondIsometry (d : ℕ) : Matrix (Fin d × InversionWires d) (Training d) ℂ :=
  fun x y => (Real.sqrt (d : ℝ) : ℂ) * optimalRoot d x.2 (x.1,y)

/-- PDF pp.2-3, Eq.(3): actual contraction of the two fixed stages before final memory trace. -/
def networkAmplitude (d : ℕ) (a : InversionWires d) (x : InversionWires d) : ℂ :=
  ∑ m : Pair d, secondIsometry d (x.1,a) (x.2.1,m) *
    inversionFirstStage d (x.2.2.1,m) x.2.2.2

/-- PDF pp.2-3, Eq.(3): the sequential network's unnormalized Choi matrix. -/
def networkChoi (d : ℕ) : CombMatrix d :=
  fun x y => ∑ a : InversionWires d, networkAmplitude d a x * conj (networkAmplitude d a y)

/-- PDF p.3, Eq.(13): |Uhat transpose>> on 3'0' tensor |Uhat>> on 2'1'. -/
def measurementSeed {d : ℕ} (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : InversionWires d → ℂ :=
  fun x => Uhat.val x.2.2.2 x.1 * Uhat.val x.2.1 x.2.2.1

/-- PDF p.3, Eq.(13): the positive POVM density in ambient coordinates, zero on the kernel. -/
def memoryPOVM {d : ℕ} (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : CombMatrix d :=
  optimalInverseRoot d *
    (show CombMatrix d from
      fun x y => measurementSeed Uhat x * conj (measurementSeed Uhat y)) *
    optimalInverseRoot d

/-- PDF p.4: training POVM density d |Uhat>><<Uhat| on the pair 2,1'.
Printed un-hatted factors in this formula are changed to the estimated unitary. -/
def trainingPOVM {d : ℕ} (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : Matrix (Pair d) (Pair d) ℂ :=
  fun x y => (d : ℂ) * Uhat.val x.1 x.2 * conj (Uhat.val y.1 y.2)

/-- PDF pp.3-4, Eq.(14): coherent second channel, discarding only its final memory. -/
def secondChannel {d : ℕ} (rho : Matrix (Training d) (Training d) ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  traceRight (secondIsometry d * rho * (secondIsometry d)ᴴ)

/-- PDF p.4, Eq.(14): memory-measured branch in the Stinespring implementation. -/
def memoryBranch {d : ℕ} (rho : Matrix (Training d) (Training d) ℂ) (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    Matrix (Fin d) (Fin d) ℂ :=
  traceRight ((secondIsometry d * rho * (secondIsometry d)ᴴ) *
    Matrix.kronecker (1 : Matrix (Fin d) _ ℂ) (memoryPOVM Uhat))

/-- PDF p.4, Eq.(14): unnormalized residual stored state after contraction with <Uhat|. -/
def residualState {d : ℕ} (rho : Matrix (Training d) (Training d) ℂ) (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => ∑ i : Pair d, ∑ j : Pair d,
    conj (Uhat.val i.1 i.2) * rho (i.1,(i.2,a)) (j.1,(j.2,b)) *
      Uhat.val j.1 j.2

/-- PDF p.4, Eq.(14): training measurement followed by conditional Uhat dagger on stored 0'. -/
def feedForwardBranch {d : ℕ} (rho : Matrix (Training d) (Training d) ℂ)
    (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : Matrix (Fin d) (Fin d) ℂ :=
  (d : ℂ) • ((Uhat.val)ᴴ * residualState rho Uhat * Uhat.val)

/-- PDF pp.3-4: physical application of the unknown U to the output of V1. -/
def trainingPreparation {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) : Matrix (Training d) (Fin d) ℂ :=
  fun x i => ∑ j : Fin d, U.val x.1 j * inversionFirstStage d (j,x.2) i

/-- PDF pp.3-4: normalized post-call state |U>><<U|/d on 2,1' and the stored input on 0'.
The source's post-call wire label 11' is corrected to the physical output 21'. -/
def preparedState {d : ℕ} (U : (Matrix.specialUnitaryGroup (Fin d) ℂ)) (sigma : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Training d) (Training d) ℂ :=
  fun x y => (d : ℂ)⁻¹ * U.val x.1 x.2.1 *
    conj (U.val y.1 y.2.1) * sigma x.2.2 y.2.2

example {d : ℕ} (Uhat : (Matrix.specialUnitaryGroup (Fin d) ℂ)) (rho : Matrix (Training d) (Training d) ℂ) :
    feedForwardBranch rho Uhat =
      (d : ℂ) • ((Uhat.val)ᴴ * residualState rho Uhat * Uhat.val) := rfl

end QAlgorithms.Papers.Independent.Next46.P24



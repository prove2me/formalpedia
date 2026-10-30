-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P06
-- name    : QAlgorithms_Papers_Independent_Extend50_P06
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T13:30:40.202375+00:00
-- url     : https://prove2.me/theorems/4a44cfd8-59fa-4312-9cbf-0bd20811376c
-- title:
--   Definitions for Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality
-- statement:
--   The objects the formalized statements of *Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality* (arXiv:2109.08202) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Target`: PDF pp.10–14: a unitary-valued target with the Borel measurability implicit in the Haar averages. Continuity is not assumed for a general target: bounded measurable kernels are integrable under probability Haar measure. For the homomorphic and anti-homomorphic results, measurability implies the usual continuity of finite-dimensional unitary representations.
--   - `Homomorphic`: PDF pp.14,16: multiplicativity or reversed multiplicativity on SU(d).
--   - `Antihomomorphic`
--   - `transformationChoi`: PDF p.4, Eq.(3): J(U) = |U⟩⟩⟨⟨U|, input index first.
--   - `QueryRegister`
--   - `TransformationWires`
--   - `TransformationProcess`
--   - `Mask`
--   - `overwrite`: A mask selects named wires for tracing and replacing, PDF p.9, Eq.(14).
--   - `replace`: Trace selected wires and tensor with their normalized identities. Summing all z duplicates unselected coordinates; division by the full dimension cancels that multiplicity. This is exactly the trace-and-replace of Eq.(14).
--   - `futureMask`
--   - `outputsMask`
--   - `pastMask`
--   - `allMask`
--   - `tailMask`: Wires after slot t, including F, and optionally O_t; Eq.(12).
--   - `slotProductChoi`: Product of k independent channel Choi matrices; each slot is used once.
--   - `insertSlots`: PDF p.4, Eq.(5), contracting all IO wires (entry formula includes the shared-wire transpose). There is no oracle-dependent choice in S.
--   - `unitarySlots`
--   - `StrategyClass`
--   - `TransformationAdmissible`: Definitions 2–4, PDF pp.6–9. Parallel and sequential domains use the exact linear trace constraints (10),(12); general uses Definition 4, including PSD, which supplies complete positivity also for ancillary extensions.
--   - `targetChoiFidelity`: PDF p.11, Eq.(15): channel fidelity, normalized by target dimension e².
--   - `pointFidelity`
--   - `transformationAverage`: PDF p.11, Eq.(17): normalized Haar average.
--   - `performance`: PDF pp.13–14, Eq.(24), explicitly in P,I,O,F wire order.
--   - `scores`: The set of actually attained fidelities, not an unconstrained real supremum.
--   - `transposeTarget`: Canonical targets in the computational basis, PDF pp.15,17,21.
--   - `inverseTarget`
--   - `conjugateTarget`
--   - `ParallelTester`: PDF p.10: normalized parallel testers (positive effects summing to σ⊗I). They characterize arbitrary finite-memory probes and normalized POVMs.
--   - `ParallelMeasurePrepare`: Definition 5, PDF p.10: prepare the channel R_a after the tester outcome a. Transposition is absorbed into the tester convention, as explained in the text.
--   - `Estimator`: PDF p.17, Eqs.(46),(47): a finite normalized parallel tester with fixed unitary guesses, equivalent to a unit probe and POVM by p.10.
--   - `estimateScore`
--   - `estimationScores`
--   - `OrthogonalCommutantBasis`: A basis may be orthogonal without unit Hilbert–Schmidt norm; PDF p.15.
--   - `targetTensorRepresentation`: Tensor representation on k query wires followed by one target wire.
--   - `place`: Named IP/OF or crossed OP/IF placement, PDF Eqs.(31),(41).
--   - `commutantExpansion`: Hilbert–Schmidt expansion; every denominator is nonzero for a basis member.
--   - `queryTargetPairProjector`: PDF p.32, Eq.(113): symmetric/antisymmetric projectors, index 0/1.
--   - `queryTargetBellProjector`: PDF p.33, Eq.(115): maximally entangled projector / its complement.
--   - `Triple`
--   - `permTriple`: PDF p.32, Eq.(112): permutation matrix with its inverse action explicit. The tuple a records π^{-1}(0),π^{-1}(1),π^{-1}(2).
--   - `rBasis`: PDF p.32, Eq.(114), in order R+,R-,R0,R1,R2,R3.
--   - `sBasis`: PDF p.33, Eq.(116), in order S+,S-,S0,S1,S2,S3. X=I₁⊗J(I)₂₃, V=F₁₂⊗I₃; the third physical wire is never silently swapped.
--   - `sixExpansion`: Eqs.(119),(122),(125). Zero members are omitted before division (not asserted to form a six-element basis at d=2). The imaginary member 3 has minus sign; Hilbert–Schmidt norms equal the printed projector/Pauli denominators.
--   - `PBTProtocol`: PDF p.24: deterministic PBT with k ports, a pure unit resource and a normalized k-outcome POVM on target × Alice's k registers.
--   - `PBTCovariant`: Eq.(70), PDF p.24: U on the measured resource halves equals Uᵀ on the retained resource halves.
--   - `pbtChoi`: Select one retained port, discard the others, and condition on the POVM. The redundant z_a summation is canceled by division by d.
--   - `pbtProcess`: The corrected p.24 transposition circuit: query Alice's measured halves, measure P together with queried O, and retain the unqueried auxiliary port. Printed p.24 instead says to measure auxiliaries; that gives the direct-U orientation, contrary to Eq.(70). This wire-label correction needs moderation.
--   - `queriedResource`
--   - `pbtScore`: Entanglement (channel) fidelity, not average pure-state fidelity.
--   - `pbtScores`
--   - `Certified`: A four-decimal certification is a conservative absolute error bound.
--   - `StrictAdvantage`: A comparison of attained optima in Definition 4's mathematical domain.
-- source:
--   Deterministic transformations between unitary operations: Exponential advantage with adaptive quantum circuits and the power of indefinite causality, arXiv:2109.08202v3, https://arxiv.org/abs/2109.08202v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P17
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P47

/-!
Statements from Quintino and Ebler, arXiv:2109.08202v3.
Pinned matrix, SU(d), Haar, channel-Choi and projector definitions are reused.
The remaining paper-specific definitions are local. Physical wire order is P,I,O,F, with
I and O each comprising k qudits. Choi vectors are input first and unnormalized.
-/

namespace QAlgorithms.Papers.Independent.Extend50.P06

open scoped BigOperators ComplexConjugate Matrix ComplexOrder
open MeasureTheory

noncomputable section

attribute [local instance] Classical.propDecidable

-- Exact accepted interfaces; no duplicate SU subtype or ambient-coordinate Haar law.
open QAlgorithms.Papers.Independent.Information100.P47 (Mat)
open QAlgorithms.Papers.Independent.Claimed50.P21 (SU HaarLaw)
open QAlgorithms.Papers.Independent.Dependency50.P05 (ChannelChoi)

/-- Borel matrix coordinates for the target Haar pushforward, PDF pp.11–12. -/
local instance targetMatrixMeasurable (d : ℕ) : MeasurableSpace (Mat d) := borel _

/-- PDF pp.10–14: a unitary-valued target with the Borel measurability
implicit in the Haar averages. Continuity is not assumed for a general target:
bounded measurable kernels are integrable under probability Haar measure.
For the homomorphic and anti-homomorphic results, measurability implies the
usual continuity of finite-dimensional unitary representations. -/
structure Target (d e : ℕ) where
  value : SU d → Mat e
  measurable : Measurable value
  specialUnitary : ∀ U, value U ∈ Matrix.specialUnitaryGroup (Fin e) ℂ

/-- PDF pp.14,16: multiplicativity or reversed multiplicativity on SU(d). -/
def Homomorphic {d e : ℕ} (f : Target d e) : Prop :=
  ∀ U V W : SU d, W.val = U.val * V.val → f.value W = f.value U * f.value V

def Antihomomorphic {d e : ℕ} (f : Target d e) : Prop :=
  ∀ U V W : SU d, W.val = U.val * V.val → f.value W = f.value V * f.value U

/-- PDF p.4, Eq.(3): J(U) = |U⟩⟩⟨⟨U|, input index first. -/
def transformationChoi {d : ℕ} (U : Mat d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  QAlgorithms.pureDensity (WithLp.toLp 2 (fun x : Fin d × Fin d => U x.2 x.1))

abbrev QueryRegister (k d : ℕ) := Fin k → Fin d
abbrev TransformationWires (k d e : ℕ) := Fin e × QueryRegister k d × QueryRegister k d × Fin e
abbrev TransformationProcess (k d e : ℕ) := Matrix (TransformationWires k d e) (TransformationWires k d e) ℂ
abbrev Mask (k : ℕ) := Bool × (Fin k → Bool) × (Fin k → Bool) × Bool

/-- A mask selects named wires for tracing and replacing, PDF p.9, Eq.(14). -/
def overwrite {k d e : ℕ} (m : Mask k) (x z : TransformationWires k d e) : TransformationWires k d e :=
  (if m.1 then z.1 else x.1,
   (fun j => if m.2.1 j then z.2.1 j else x.2.1 j),
   (fun j => if m.2.2.1 j then z.2.2.1 j else x.2.2.1 j),
   if m.2.2.2 then z.2.2.2 else x.2.2.2)

/-- Trace selected wires and tensor with their normalized identities. Summing
all z duplicates unselected coordinates; division by the full dimension cancels
that multiplicity. This is exactly the trace-and-replace of Eq.(14). -/
def replace {k d e : ℕ} (m : Mask k) (S : TransformationProcess k d e) : TransformationProcess k d e :=
  fun x y => if (m.1 = true → x.1 = y.1) ∧
      (∀ j, m.2.1 j = true → x.2.1 j = y.2.1 j) ∧
      (∀ j, m.2.2.1 j = true → x.2.2.1 j = y.2.2.1 j) ∧
      (m.2.2.2 = true → x.2.2.2 = y.2.2.2)
    then (∑ z : TransformationWires k d e, S (overwrite m x z) (overwrite m y z)) /
      (Fintype.card (TransformationWires k d e) : ℂ)
    else 0

def futureMask (k : ℕ) : Mask k := (false, fun _ => false, fun _ => false, true)

def outputsMask (k : ℕ) : Mask k := (false, fun _ => false, fun _ => true, true)

def pastMask (k : ℕ) : Mask k := (false, fun _ => true, fun _ => true, true)

def allMask (k : ℕ) : Mask k := (true, fun _ => true, fun _ => true, true)

/-- Wires after slot t, including F, and optionally O_t; Eq.(12). -/
def tailMask {k : ℕ} (t : Fin k) (includeOutput : Bool) : Mask k :=
  (false, fun j => decide (t < j),
   fun j => decide (t < j) || (includeOutput && decide (j = t)), true)

/-- Product of k independent channel Choi matrices; each slot is used once. -/
def slotProductChoi {k d : ℕ}
    (C : Fin k → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (QueryRegister k d × QueryRegister k d) (QueryRegister k d × QueryRegister k d) ℂ :=
  fun x y => ∏ t, C t (x.1 t,x.2 t) (y.1 t,y.2 t)

/-- PDF p.4, Eq.(5), contracting all IO wires (entry formula includes the
shared-wire transpose). There is no oracle-dependent choice in S. -/
def insertSlots {k d e : ℕ} (S : TransformationProcess k d e)
    (C : Matrix (QueryRegister k d × QueryRegister k d) (QueryRegister k d × QueryRegister k d) ℂ) :
    Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ :=
  fun x y => ∑ i, ∑ j, ∑ o, ∑ v, S (x.1,i,o,x.2) (y.1,j,v,y.2) * C (i,o) (j,v)

def unitarySlots {k d : ℕ} (U : Mat d) := slotProductChoi (k := k) (fun _ => transformationChoi U)

inductive StrategyClass where
  | parallel | sequential | general
  deriving DecidableEq

/-- Definitions 2–4, PDF pp.6–9. Parallel and sequential domains use the exact
linear trace constraints (10),(12); general uses Definition 4, including PSD,
which supplies complete positivity also for ancillary extensions. -/
def TransformationAdmissible {k d e : ℕ} (c : StrategyClass) (S : TransformationProcess k d e) : Prop :=
  S.PosSemidef ∧ match c with
  | .parallel => replace (futureMask k) S = replace (outputsMask k) S ∧
      replace (pastMask k) S = replace (allMask k) S ∧ S.trace = (e * d ^ k : ℕ)
  | .sequential => (∀ t, replace (tailMask t false) S = replace (tailMask t true) S) ∧
      replace (pastMask k) S = replace (allMask k) S ∧ S.trace = (e * d ^ k : ℕ)
  | .general => ∀ C : Fin k → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      (∀ t, ChannelChoi (C t)) → ChannelChoi (insertSlots S (slotProductChoi C))

/-- PDF p.11, Eq.(15): channel fidelity, normalized by target dimension e². -/
def targetChoiFidelity {e : ℕ} (C : Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ)
    (V : Mat e) : ℝ := (Matrix.trace (C * transformationChoi V)).re / (e : ℝ)^2

def pointFidelity {k d e : ℕ} (S : TransformationProcess k d e) (f : SU d → Mat e) (U : SU d) : ℝ :=
  targetChoiFidelity (insertSlots S (unitarySlots U.val)) (f U)

/-- PDF p.11, Eq.(17): normalized Haar average. -/
def transformationAverage {k d e : ℕ} (H : HaarLaw d) (f : SU d → Mat e) (S : TransformationProcess k d e) : ℝ :=
  ∫ U, pointFidelity S f U ∂H.law

/-- PDF pp.13–14, Eq.(24), explicitly in P,I,O,F wire order. -/
def performance {k d e : ℕ} (H : HaarLaw d) (f : SU d → Mat e) : TransformationProcess k d e :=
  ((e : ℂ)^2)⁻¹ • ∫ U : SU d, (fun (x y : TransformationWires k d e) => transformationChoi (f U) (x.1,x.2.2.2) (y.1,y.2.2.2) *
    conj (unitarySlots (k := k) U.val (x.2.1,x.2.2.1) (y.2.1,y.2.2.1))) ∂H.law

/-- The set of actually attained fidelities, not an unconstrained real supremum. -/
def scores {k d e : ℕ} (H : HaarLaw d) (f : SU d → Mat e) (c : StrategyClass) : Set ℝ :=
  {v | ∃ S : TransformationProcess k d e, TransformationAdmissible c S ∧ transformationAverage H f S = v}

/-- Canonical targets in the computational basis, PDF pp.15,17,21. -/
def transposeTarget {d : ℕ} (U : SU d) : Mat d := U.val.transpose

def inverseTarget {d : ℕ} (U : SU d) : Mat d := U.valᴴ

def conjugateTarget {d : ℕ} (U : SU d) : Mat d := U.val.map conj

/-- PDF p.10: normalized parallel testers (positive effects summing to σ⊗I).
They characterize arbitrary finite-memory probes and normalized POVMs. -/
def ParallelTester {k d n : ℕ}
    (T : Fin n → Matrix (QueryRegister k d × QueryRegister k d) (QueryRegister k d × QueryRegister k d) ℂ) : Prop :=
  (∀ a, (T a).PosSemidef) ∧ ∃ σ : Matrix (QueryRegister k d) (QueryRegister k d) ℂ,
    σ.PosSemidef ∧ σ.trace = 1 ∧ ∀ x y,
      (∑ a, T a x y) = σ x.1 y.1 * (1 : Matrix (QueryRegister k d) (QueryRegister k d) ℂ) x.2 y.2

/-- Definition 5, PDF p.10: prepare the channel R_a after the tester outcome a.
Transposition is absorbed into the tester convention, as explained in the text. -/
def ParallelMeasurePrepare {k d e : ℕ} (S : TransformationProcess k d e) : Prop :=
  ∃ n : ℕ, ∃ T : Fin n → Matrix (QueryRegister k d × QueryRegister k d) (QueryRegister k d × QueryRegister k d) ℂ,
    ∃ R : Fin n → Matrix (Fin e × Fin e) (Fin e × Fin e) ℂ,
      ParallelTester T ∧ (∀ a, ChannelChoi (R a)) ∧
      ∀ x y, S x y = ∑ a, T a (x.2.1,x.2.2.1) (y.2.1,y.2.2.1) *
        R a (x.1,x.2.2.2) (y.1,y.2.2.2)

/-- PDF p.17, Eqs.(46),(47): a finite normalized parallel tester with fixed
unitary guesses, equivalent to a unit probe and POVM by p.10. -/
structure Estimator (k d n : ℕ) where
  tester : Fin n → Matrix (QueryRegister k d × QueryRegister k d) (QueryRegister k d × QueryRegister k d) ℂ
  normalized : ParallelTester tester
  guess : Fin n → SU d

def estimateScore {k d n : ℕ} (H : HaarLaw d) (E : Estimator k d n) : ℝ :=
  ∫ U, ∑ a, (Matrix.trace (E.tester a * unitarySlots U.val)).re *
    targetChoiFidelity (transformationChoi (E.guess a).val) U.val ∂H.law

def estimationScores {k d : ℕ} (H : HaarLaw d) : Set ℝ :=
  {v | ∃ n : ℕ, ∃ E : Estimator k d n, estimateScore H E = v}

/-- A basis may be orthogonal without unit Hilbert–Schmidt norm; PDF p.15. -/
def OrthogonalCommutantBasis {d n : ℕ} {ι : Type*} [Fintype ι]
    (ρ : SU d → Matrix ι ι ℂ) (P : Fin n → Matrix ι ι ℂ) : Prop :=
  (∀ i, P i ≠ 0) ∧ (∀ i j, i ≠ j → Matrix.trace ((P i)ᴴ * P j) = 0) ∧
  ∀ A : Matrix ι ι ℂ, (∀ U, A * ρ U = ρ U * A) ↔ A ∈ Submodule.span ℂ (Set.range P)

/-- Tensor representation on k query wires followed by one target wire. -/
def targetTensorRepresentation {k d e : ℕ} (f : SU d → Mat e) (anti : Bool) (U : SU d) :
    Matrix (QueryRegister k d × Fin e) (QueryRegister k d × Fin e) ℂ :=
  fun x y => (∏ t, conj (U.val (x.1 t) (y.1 t))) *
    (if anti then (f U).transpose x.2 y.2 else f U x.2 y.2)

/-- Named IP/OF or crossed OP/IF placement, PDF Eqs.(31),(41). -/
def place {k d e : ℕ} (crossed : Bool)
    (A B : Matrix (QueryRegister k d × Fin e) (QueryRegister k d × Fin e) ℂ) : TransformationProcess k d e :=
  fun x y => if crossed then A (x.2.2.1,x.1) (y.2.2.1,y.1) * B (x.2.1,x.2.2.2) (y.2.1,y.2.2.2)
    else A (x.2.1,x.1) (y.2.1,y.1) * B (x.2.2.1,x.2.2.2) (y.2.2.1,y.2.2.2)

/-- Hilbert–Schmidt expansion; every denominator is nonzero for a basis member. -/
def commutantExpansion {k d e n : ℕ} (crossed : Bool)
    (P : Fin n → Matrix (QueryRegister k d × Fin e) (QueryRegister k d × Fin e) ℂ) : TransformationProcess k d e :=
  ((e : ℂ)^2)⁻¹ • ∑ i, (Matrix.trace ((P i)ᴴ * P i))⁻¹ • place crossed ((P i).map conj) (P i)

example : transformationChoi (1 : Mat 1) (0,0) (0,0) = 1 := by simp [transformationChoi, QAlgorithms.pureDensity]

example (k d : ℕ) (U : Mat d) : unitarySlots (k := 0) U = 1 := by
  ext x y
  have hxy : x = y := Subsingleton.elim _ _
  subst y
  simp [unitarySlots, slotProductChoi, Matrix.one_apply]

/-- PDF p.32, Eq.(113): symmetric/antisymmetric projectors, index 0/1. -/
def queryTargetPairProjector (d : ℕ) (antisymmetric : Bool) :
    Matrix (QueryRegister 1 d × Fin d) (QueryRegister 1 d × Fin d) ℂ :=
  fun x y => QAlgorithms.Papers.Independent.Claimed50.P17.pairProjector d
    (if antisymmetric then 1 else 0) (x.1 0,x.2) (y.1 0,y.2)

/-- PDF p.33, Eq.(115): maximally entangled projector / its complement. -/
def queryTargetBellProjector (d : ℕ) (complement : Bool) :
    Matrix (QueryRegister 1 d × Fin d) (QueryRegister 1 d × Fin d) ℂ :=
  let P : Matrix (QueryRegister 1 d × Fin d) (QueryRegister 1 d × Fin d) ℂ :=
    fun x y => QAlgorithms.Papers.Independent.Claimed50.P21.entangledProjector d
      (x.1 0,x.2) (y.1 0,y.2)
  if complement then 1 - P else P

abbrev Triple (d : ℕ) := QueryRegister 2 d × Fin d

/-- PDF p.32, Eq.(112): permutation matrix with its inverse action explicit.
The tuple a records π^{-1}(0),π^{-1}(1),π^{-1}(2). -/
def permTriple (d : ℕ) (a : Fin 3 → Fin 3) : Matrix (Triple d) (Triple d) ℂ :=
  fun x y => let xv : Fin 3 → Fin d := ![x.1 0,x.1 1,x.2]
             let yv : Fin 3 → Fin d := ![y.1 0,y.1 1,y.2]
             if ∀ j, xv j = yv (a j) then 1 else 0

/-- PDF p.32, Eq.(114), in order R+,R-,R0,R1,R2,R3. -/
def rBasis (d : ℕ) : Fin 6 → Matrix (Triple d) (Triple d) ℂ :=
  let a := permTriple d ![1,0,2]
  let b := permTriple d ![0,2,1]
  let c := permTriple d ![2,1,0]
  let v := permTriple d ![2,0,1]
  let w := permTriple d ![1,2,0]
  ![(6 : ℂ)⁻¹ • (1+a+b+c+v+w),
    (6 : ℂ)⁻¹ • (1-a-b-c+v+w),
    (3 : ℂ)⁻¹ • ((2 : ℂ) • 1-v-w),
    (3 : ℂ)⁻¹ • ((2 : ℂ) • b-c-a),
    ((Real.sqrt 3 : ℂ))⁻¹ • (a-c),
    (Complex.I / (Real.sqrt 3 : ℂ)) • (v-w)]

/-- PDF p.33, Eq.(116), in order S+,S-,S0,S1,S2,S3. X=I₁⊗J(I)₂₃,
V=F₁₂⊗I₃; the third physical wire is never silently swapped. -/
def sBasis (d : ℕ) : Fin 6 → Matrix (Triple d) (Triple d) ℂ :=
  let X : Matrix (Triple d) (Triple d) ℂ := fun x y =>
    if x.1 0 = y.1 0 ∧ x.1 1 = x.2 ∧ y.1 1 = y.2 then 1 else 0
  let V := permTriple d ![1,0,2]
  let A := (2 : ℂ)⁻¹ • (1+V)
  let B := (2 : ℂ)⁻¹ • (1-V)
  let q : ℂ := (d : ℂ)^2-1
  ![A * (1 - (2 / ((d : ℂ)+1)) • X) * A,
    B * (1 - (2 / ((d : ℂ)-1)) • X) * B,
    q⁻¹ • ((d : ℂ) • (X+V*X*V) - (X*V+V*X)),
    q⁻¹ • ((d : ℂ) • (X*V+V*X) - (X+V*X*V)),
    (Real.sqrt ((d : ℝ)^2-1) : ℂ)⁻¹ • (X-V*X*V),
    (Complex.I / (Real.sqrt ((d : ℝ)^2-1) : ℂ)) • (X*V-V*X)]

/-- Eqs.(119),(122),(125). Zero members are omitted before division (not
asserted to form a six-element basis at d=2). The imaginary member 3 has minus
sign; Hilbert–Schmidt norms equal the printed projector/Pauli denominators. -/
def sixExpansion (d : ℕ) (crossed : Bool)
    (B : Fin 6 → Matrix (Triple d) (Triple d) ℂ) : TransformationProcess 2 d d :=
  ((d : ℂ)^2)⁻¹ • ∑ i, if B i = 0 then 0 else
    ((if i = 5 then (-1 : ℂ) else 1) / Matrix.trace ((B i)ᴴ * B i)) •
      place crossed (B i) (B i)

/-- PDF p.24: deterministic PBT with k ports, a pure unit resource and a
normalized k-outcome POVM on target × Alice's k registers. -/
structure PBTProtocol (k d : ℕ) where
  resource : QueryRegister k d × QueryRegister k d → ℂ
  unit : ∑ x, Complex.normSq (resource x) = 1
  effect : Fin k → Matrix (Fin d × QueryRegister k d) (Fin d × QueryRegister k d) ℂ
  positive : ∀ a, (effect a).PosSemidef
  complete : ∑ a, effect a = 1

/-- Eq.(70), PDF p.24: U on the measured resource halves equals Uᵀ on the
retained resource halves. -/
def PBTCovariant {k d : ℕ} (P : PBTProtocol k d) : Prop :=
  ∀ U : SU d, ∀ a b : QueryRegister k d,
    (∑ c, (∏ t, U.val (a t) (c t)) * P.resource (c,b)) =
    ∑ c, (∏ t, U.val (c t) (b t)) * P.resource (a,c)

/-- Select one retained port, discard the others, and condition on the POVM.
The redundant z_a summation is canceled by division by d. -/
def pbtChoi {k d : ℕ} (P : PBTProtocol k d)
    (ψ : QueryRegister k d × QueryRegister k d → ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun x y => (∑ a, ∑ i, ∑ j, ∑ z : QueryRegister k d,
    P.effect a (y.1,j) (x.1,i) * ψ (i,Function.update z a x.2) *
      conj (ψ (j,Function.update z a y.2))) / (d : ℂ)

/-- The corrected p.24 transposition circuit: query Alice's measured halves,
measure P together with queried O, and retain the unqueried auxiliary port.
Printed p.24 instead says to measure auxiliaries; that gives the direct-U
orientation, contrary to Eq.(70). This wire-label correction needs moderation. -/
def pbtProcess {k d : ℕ} (P : PBTProtocol k d) : TransformationProcess k d d :=
  fun x y => (∑ a, ∑ z : QueryRegister k d,
    P.effect a (y.1,y.2.2.1) (x.1,x.2.2.1) *
      P.resource (x.2.1,Function.update z a x.2.2.2) *
      conj (P.resource (y.2.1,Function.update z a y.2.2.2))) / (d : ℂ)

def queriedResource {k d : ℕ} (P : PBTProtocol k d) (U : Mat d) :
    QueryRegister k d × QueryRegister k d → ℂ :=
  fun x => ∑ i, (∏ t, U (x.1 t) (i t)) * P.resource (i,x.2)

/-- Entanglement (channel) fidelity, not average pure-state fidelity. -/
def pbtScore {k d : ℕ} (P : PBTProtocol k d) : ℝ :=
  targetChoiFidelity (pbtChoi P P.resource) 1

def pbtScores (k d : ℕ) : Set ℝ := {v | ∃ P : PBTProtocol k d, pbtScore P = v}

/-- A four-decimal certification is a conservative absolute error bound. -/
def Certified {k d : ℕ} (H : HaarLaw d) (f : SU d → Mat d)
    (c : StrategyClass) (r : ℝ) : Prop :=
  ∃ v, IsGreatest (scores (k := k) H f c) v ∧ |v-r| ≤ 1/10000

/-- A comparison of attained optima in Definition 4's mathematical domain. -/
def StrictAdvantage {k d : ℕ} (H : HaarLaw d) (f : SU d → Mat d) : Prop :=
  ∃ a b, IsGreatest (scores (k := k) H f .sequential) a ∧
    IsGreatest (scores (k := k) H f .general) b ∧ a < b

example : queryTargetPairProjector 1 false (fun _ => 0,0) (fun _ => 0,0) = 1 := by
  norm_num [queryTargetPairProjector,
    QAlgorithms.Papers.Independent.Claimed50.P17.pairProjector]

example (d : ℕ) : queryTargetBellProjector d true = 1 - queryTargetBellProjector d false := rfl

end

end QAlgorithms.Papers.Independent.Extend50.P06



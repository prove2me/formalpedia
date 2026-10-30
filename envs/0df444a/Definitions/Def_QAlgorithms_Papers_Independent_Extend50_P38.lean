-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P38
-- name    : QAlgorithms_Papers_Independent_Extend50_P38
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T14:48:04.222289+00:00
-- url     : https://prove2.me/theorems/4a031712-c99f-4e04-91e2-c31b274d1c78
-- title:
--   Definitions for Asymptotic teleportation scheme as a universal programmable quantum processor
-- statement:
--   The objects the formalized statements of *Asymptotic teleportation scheme as a universal programmable quantum processor* (arXiv:0807.4568) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Ports`: PDF p.2: the computational configurations of N d-dimensional ports.
--   - `AC`: PDF p.2: Alice's ports together with the input (or the relabelled output).
--   - `ResourceRegister`: PDF p.2: all of Alice's and Bob's N-port resource configurations. This is distinct from the accepted single-pair register Claimed50.P17.AB.
--   - `ValidResource`: PDF p.2: a resource operator O is normalized by Tr(OO†)=d^N.
--   - `resourceVector`: PDF p.2: coordinates of (O tensor I)|phi+>^{tensor N}.
--   - `resourceDensity`: PDF p.2: the normalized pure resource density when ValidResource holds.
--   - `insertPort`: PDF p.2: insert the retained port value into the other Bob configurations.
--   - `processor`: PDF p.2: Alice measures A,C and Bob retains B_i without a correction. This is the entrywise partial trace of the Lueders measurement sum. Cyclicity on traced registers replaces the two square roots of the effect by the effect itself. The definition accepts mixed program densities as required by PDF pp.1,4.
--   - `teleport`: PDF p.2: the teleportation channel using the pure resource specified by O.
--   - `signals`: PDF p.2 Eq.(1): the phi+ signal d^{-(N-1)} P+_{A_i B} tensor I_{other A}. The coefficient is d^{-N}, since each nonzero entry of P+ is 1/d.
--   - `resourceLift`: PDF p.2 Eq.(2): O tensor I on the resource-signal space. Renew46.P20.aliceLift instead adds a leading Bob identity to an Alice/input effect.
--   - `teleportationObjective`: PDF p.2 Eq.(2): the scalar teleportationObjective, with every signal physically specified.
--   - `supportedInvSqrt`: PDF p.2: the supported inverse square root; zero on the kernel.
--   - `rawSrm`: PDF p.2: uncompleted square-root effects for the given signal family.
--   - `srmCompletion`: PDF p.2: the equal kernel completion Delta, necessary to obtain a POVM.
--   - `srm`: PDF p.2: the normalized N-outcome SRM, including Delta.
--   - `singletResource`: PDF pp.2–3: N singlets, A and B registers grouped together.
--   - `singletSignals`: PDF p.3: singlet signals; their local projections are P-_{B A_i}.
--   - `singletSrmChannel`: PDF p.3: the actual singlet-resource SRM teleportation map. Support21.P19.qubitChannel is a noiseless communication resource, not this channel.
--   - `qubitClosedF`: PDF p.3: exact closed sum; all signed numerators are real, never Nat subtraction.
--   - `qubitAverage`: PDF p.3: f is the Haar-average fidelity of the physical qubit channel.
--   - `spinBit`: PDF p.3: twice the magnetic number of |0> is -1, that of |1> is +1.
--   - `finalSpin`: PDF p.3: twice the total spin at the end of the accepted sequential coupling path. The frozen path stores each doubled spin in Fin (n+1); its step condition gives the same nonnegative paths as the source, since the kth spin cannot exceed k.
--   - `ValidMagnetic`: PDF p.3: the magnetic numbers present in a spin-r/2 representation.
--   - `coupling`: PDF p.3: real Clebsch–Gordan coefficients for coupling spin p/2 with spin 1/2. Arguments m and q are twice the old magnetic number and new total spin. This fixes one standard real phase convention; alpha-dependent global signs are immaterial.
--   - `spinVector`: PDF p.3, Appendix A: recursively coupled Phi, as the product of the coupling coefficients along alpha. The final magnetic number m is doubled.
--   - `coupledVector`: PDF p.3 Eq.(3): couple Phi on A to B, whose output coordinate is last. The source writes B first; this is only a permutation of tensor coordinates.
--   - `CoupledSpinLabel`: PDF p.3 Eq.(3): every allowed path, coupled-spin branch, and doubled magnetic number. The lower branch is absent when the Alice spin is zero.
--   - `lambdaMinus`: PDF p.3: the two signal-sum eigenvalues, parameterized by actual spin j.
--   - `lambdaPlus`: PDF p.3: lambda^+_j.
--   - `singletSpinBranch`: PDF p.6 Eq.(B1): the two actual spectral branch operators constructed from the coupled vectors. false is rhoMinus (total spin j+1/2), true is rhoPlus (total spin j-1/2). All magnetic numbers occur once, including the endpoints; the nonexistent j=0 lower branch is omitted.
--   - `overlapCoefficient`: PDF p.3 Eq.(5): weights s/(2s+1) and (s+1)/(2s+1), without square roots. At s=0 the absent lower branch has zero weight.
--   - `xi`: PDF p.3 Eq.(4): xi at port i, with the other n qubits in their sequential spin basis.
--   - `PortPrimalFeasible`: PDF p.4 Eq.(6): port-teleportation joint primal feasibility, allowing singular X. Unlike SDP.PrimalFeasible this includes both X and N positive effects with an exact sum.
--   - `primalValue`: PDF p.4 Eq.(6): primal teleportationObjective.
--   - `bobTrace`: PDF p.4: trace out the last (Bob) qudit in the dual constraint.
--   - `PortDualFeasible`: PDF p.4: port-teleportation dual feasibility; a is real and Omega is Hermitian. Unlike SDP.DualFeasible this uses an operator variable and a partial-trace constraint.
--   - `separableOperator`: PDF p.4: the explicitly separable resource |0>_A^{tensor N} tensor product_i |e_i>_B, expressed in the O parametrization; e labels orthogonal computational output states.
--   - `program`: PDF pp.1,4: a CPTP operation is applied to all Bob ports in a program density. The accepted tensor-superoperator definition includes entangled/off-diagonal inputs.
--   - `stateFidelity`: PDF p.4: two-state squared Uhlmann fidelity (distinct from channel entanglement fidelity).
--   - `programmedAverage`: PDF p.4: average over pure inputs of fidelity to the desired processed output.
-- source:
--   Asymptotic teleportation scheme as a universal programmable quantum processor, arXiv:0807.4568v2, https://arxiv.org/abs/0807.4568v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

/-!
Statements from Ishizaka–Hiroshima, arXiv:0807.4568v2. All page numbers are PDF pages.
Paper-local definitions implement the physical registers, selection channel, completed SRM,
and an explicit sequentially coupled spin basis using accepted spin paths and singlet amplitudes. No claim is made for trace-decreasing
programs or for the false general multiple-vector subtraction assertion on p.4.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P38

attribute [local instance] Classical.propDecidable Classical.decEq

-- Pinned accepted definitions; neither is re-declared in this module.
open QAlgorithms.Papers.Independent.Frontier18.P14 (singlet)
open QAlgorithms.Papers.Independent.Renew46.P01 (SpinPath)

/-- PDF p.2: the computational configurations of N d-dimensional ports. -/
abbrev Ports (d N : ℕ) := Fin N → Fin d

/-- PDF p.2: Alice's ports together with the input (or the relabelled output). -/
abbrev AC (d N : ℕ) := Ports d N × Fin d

/-- PDF p.2: all of Alice's and Bob's N-port resource configurations.
This is distinct from the accepted single-pair register Claimed50.P17.AB. -/
abbrev ResourceRegister (d N : ℕ) := Ports d N × Ports d N

/-- PDF p.2: a resource operator O is normalized by Tr(OO†)=d^N. -/
def ValidResource {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ) : Prop :=
  (O * Oᴴ).trace = (d : ℂ) ^ N

/-- PDF p.2: coordinates of (O tensor I)|phi+>^{tensor N}. -/
def resourceVector {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ) :
    EuclideanSpace ℂ (ResourceRegister d N) :=
  WithLp.toLp 2 fun z => O z.1 z.2 / (Real.sqrt ((d : ℝ) ^ N) : ℂ)

/-- PDF p.2: the normalized pure resource density when ValidResource holds. -/
def resourceDensity {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ) :
    Matrix (ResourceRegister d N) (ResourceRegister d N) ℂ := pureDensity (resourceVector O)

/-- PDF p.2: insert the retained port value into the other Bob configurations. -/
def insertPort {d N : ℕ} (i : Fin N)
    (z : {j : Fin N // j ≠ i} → Fin d) (b : Fin d) : Ports d N :=
  fun j => if h : j = i then b else z ⟨j, h⟩

/-- PDF p.2: Alice measures A,C and Bob retains B_i without a correction.
This is the entrywise partial trace of the Lueders measurement sum. Cyclicity on
traced registers replaces the two square roots of the effect by the effect itself.
The definition accepts mixed program densities as required by PDF pp.1,4. -/
def processor {d N : ℕ} (M : Fin N → Matrix (AC d N) (AC d N) ℂ)
    (R : Matrix (ResourceRegister d N) (ResourceRegister d N) ℂ) : Superop (Fin d) (Fin d) :=
  fun X => Matrix.of fun b c =>
    ∑ i, ∑ a : Ports d N, ∑ a' : Ports d N, ∑ u : Fin d, ∑ v : Fin d,
      ∑ z : {j : Fin N // j ≠ i} → Fin d,
        M i (a', v) (a, u) *
          R (a, insertPort i z b) (a', insertPort i z c) * X u v

/-- PDF p.2: the teleportation channel using the pure resource specified by O. -/
def teleport {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ)
    (M : Fin N → Matrix (AC d N) (AC d N) ℂ) : Superop (Fin d) (Fin d) :=
  processor M (resourceDensity O)

/-- PDF p.2 Eq.(1): the phi+ signal d^{-(N-1)} P+_{A_i B} tensor I_{other A}.
The coefficient is d^{-N}, since each nonzero entry of P+ is 1/d. -/
def signals (d N : ℕ) (i : Fin N) : Matrix (AC d N) (AC d N) ℂ :=
  Matrix.of fun x y =>
    if x.1 i = x.2 ∧ y.1 i = y.2 ∧ (∀ j, j ≠ i → x.1 j = y.1 j)
    then (((d : ℝ) ^ N)⁻¹ : ℂ) else 0

/-- PDF p.2 Eq.(2): O tensor I on the resource-signal space.
Renew46.P20.aliceLift instead adds a leading Bob identity to an Alice/input effect. -/
def resourceLift {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ) :
    Matrix (AC d N) (AC d N) ℂ := Matrix.kronecker O 1

/-- PDF p.2 Eq.(2): the scalar teleportationObjective, with every signal physically specified. -/
def teleportationObjective {d N : ℕ} (O : Matrix (Ports d N) (Ports d N) ℂ)
    (M : Fin N → Matrix (AC d N) (AC d N) ℂ) : ℝ :=
  (∑ i, (M i * (resourceLift O * signals d N i * (resourceLift O)ᴴ)).trace.re) /
    (d : ℝ) ^ 2

/-- PDF p.2: the supported inverse square root; zero on the kernel. -/
def supportedInvSqrt {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) : Matrix I I ℂ := cfc (fun t : ℝ => (Real.sqrt t)⁻¹) A

/-- PDF p.2: uncompleted square-root effects for the given signal family. -/
def rawSrm {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (S : Fin N → Matrix I I ℂ) (i : Fin N) : Matrix I I ℂ :=
  supportedInvSqrt (∑ j, S j) * S i * supportedInvSqrt (∑ j, S j)

/-- PDF p.2: the equal kernel completion Delta, necessary to obtain a POVM. -/
def srmCompletion {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (S : Fin N → Matrix I I ℂ) : Matrix I I ℂ :=
  ((N : ℂ)⁻¹) • (1 - ∑ i, rawSrm S i)

/-- PDF p.2: the normalized N-outcome SRM, including Delta. -/
def srm {N : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (S : Fin N → Matrix I I ℂ) (i : Fin N) : Matrix I I ℂ :=
  rawSrm S i + srmCompletion S

/-- PDF pp.2–3: N singlets, A and B registers grouped together. -/
def singletResource (N : ℕ) : Matrix (ResourceRegister 2 N) (ResourceRegister 2 N) ℂ :=
  pureDensity (WithLp.toLp 2 fun z : ResourceRegister 2 N => ∏ i, singlet (z.1 i, z.2 i))

/-- PDF p.3: singlet signals; their local projections are P-_{B A_i}. -/
def singletSignals (N : ℕ) (i : Fin N) : Matrix (AC 2 N) (AC 2 N) ℂ :=
  Matrix.of fun x y =>
    if ∀ j, j ≠ i → x.1 j = y.1 j
    then (((2 : ℝ) ^ (N - 1))⁻¹ : ℂ) *
      singlet (x.2, x.1 i) * conj (singlet (y.2, y.1 i)) else 0

/-- PDF p.3: the actual singlet-resource SRM teleportation map.
Support21.P19.qubitChannel is a noiseless communication resource, not this channel. -/
def singletSrmChannel (N : ℕ) : Superop (Fin 2) (Fin 2) :=
  processor (srm (singletSignals N)) (singletResource N)

/-- PDF p.3: exact closed sum; all signed numerators are real, never Nat subtraction. -/
def qubitClosedF (N : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (N + 1),
    (((N : ℝ) - 2 * (k : ℝ) - 1) / Real.sqrt ((k : ℝ) + 1) +
     ((N : ℝ) - 2 * (k : ℝ) + 1) / Real.sqrt ((N : ℝ) - (k : ℝ) + 1)) ^ 2 *
       (N.choose k : ℝ)) / (2 : ℝ) ^ (N + 3)

/-- PDF p.3: f is the Haar-average fidelity of the physical qubit channel. -/
def qubitAverage (N : ℕ) : ℝ := QuditFidelity.averageFidelity 2 (by decide) (singletSrmChannel N)

/-- PDF p.3: twice the magnetic number of |0> is -1, that of |1> is +1. -/
def spinBit (b : Fin 2) : ℤ := if b = 0 then -1 else 1

/-- PDF p.3: twice the total spin at the end of the accepted sequential coupling path.
The frozen path stores each doubled spin in Fin (n+1); its step condition gives the
same nonnegative paths as the source, since the kth spin cannot exceed k. -/
def finalSpin {n : ℕ} (p : SpinPath n) : ℕ := (p.val (Fin.last n)).val

/-- PDF p.3: the magnetic numbers present in a spin-r/2 representation. -/
def ValidMagnetic (r : ℕ) (m : ℤ) : Prop :=
  -(r : ℤ) ≤ m ∧ m ≤ (r : ℤ) ∧ (m + (r : ℤ)) % 2 = 0

/-- PDF p.3: real Clebsch–Gordan coefficients for coupling spin p/2 with spin 1/2.
Arguments m and q are twice the old magnetic number and new total spin.
This fixes one standard real phase convention; alpha-dependent global signs are immaterial. -/
def coupling (p : ℕ) (m : ℤ) (q : ℕ) (b : Fin 2) : ℝ :=
  if ValidMagnetic p m ∧ ValidMagnetic q (m + spinBit b) then
    if q = p + 1 then
      if b = 0 then Real.sqrt (((p : ℝ) - (m : ℝ) + 2) / (2 * ((p : ℝ) + 1)))
      else Real.sqrt (((p : ℝ) + (m : ℝ) + 2) / (2 * ((p : ℝ) + 1)))
    else if p = q + 1 then
      if b = 0 then Real.sqrt (((p : ℝ) + (m : ℝ)) / (2 * ((p : ℝ) + 1)))
      else -Real.sqrt (((p : ℝ) - (m : ℝ)) / (2 * ((p : ℝ) + 1)))
    else 0
  else 0

/-- PDF p.3, Appendix A: recursively coupled Phi, as the product of the coupling
coefficients along alpha. The final magnetic number m is doubled. -/
def spinVector {n : ℕ} (p : SpinPath n) (m : ℤ) : EuclideanSpace ℂ (Ports 2 n) :=
  WithLp.toLp 2 fun x =>
    if (∑ k, spinBit (x k)) = m then
      ∏ k : Fin n,
        (coupling (p.val k.castSucc).val
          (∑ l ∈ Finset.univ.filter (fun l : Fin n => l.val < k.val), spinBit (x l))
          (p.val k.succ).val (x k) : ℂ)
    else 0

/-- PDF p.3 Eq.(3): couple Phi on A to B, whose output coordinate is last.
The source writes B first; this is only a permutation of tensor coordinates. -/
def coupledVector {n : ℕ} (p : SpinPath n) (q : ℕ) (m : ℤ) :
    EuclideanSpace ℂ (AC 2 n) :=
  WithLp.toLp 2 fun x =>
    spinVector p (m - spinBit x.2) x.1 *
      (coupling (finalSpin p) (m - spinBit x.2) q x.2 : ℂ)

/-- PDF p.3 Eq.(3): every allowed path, coupled-spin branch, and doubled magnetic
number. The lower branch is absent when the Alice spin is zero. -/
abbrev CoupledSpinLabel (N : ℕ) :=
  {l : SpinPath N × ℕ × ℤ //
    (l.2.1 = finalSpin l.1 + 1 ∨ finalSpin l.1 = l.2.1 + 1) ∧
      ValidMagnetic l.2.1 l.2.2}

/-- PDF p.3: the two signal-sum eigenvalues, parameterized by actual spin j. -/
def lambdaMinus (N : ℕ) (j : ℝ) : ℝ := ((N : ℝ) / 2 - j) / (2 : ℝ) ^ N

/-- PDF p.3: lambda^+_j. -/
def lambdaPlus (N : ℕ) (j : ℝ) : ℝ := ((N : ℝ) / 2 + j + 1) / (2 : ℝ) ^ N

/-- PDF p.6 Eq.(B1): the two actual spectral branch operators constructed from
the coupled vectors. false is rhoMinus (total spin j+1/2), true is rhoPlus
(total spin j-1/2). All magnetic numbers occur once, including the endpoints;
the nonexistent j=0 lower branch is omitted. -/
def singletSpinBranch (N : ℕ) (lowerTotalSpin : Bool) : Matrix (AC 2 N) (AC 2 N) ℂ :=
  ∑ p : SpinPath N,
    if lowerTotalSpin = true ∧ finalSpin p = 0 then 0 else
      let q := if lowerTotalSpin then finalSpin p - 1 else finalSpin p + 1
      let eigenvalue := if lowerTotalSpin then lambdaPlus N ((finalSpin p : ℝ) / 2)
        else lambdaMinus N ((finalSpin p : ℝ) / 2)
      (eigenvalue : ℂ) • ∑ k : Fin (q + 1),
        pureDensity (coupledVector p q (2 * (k.val : ℤ) - (q : ℤ)))

/-- PDF p.3 Eq.(5): weights s/(2s+1) and (s+1)/(2s+1), without square roots.
At s=0 the absent lower branch has zero weight. -/
def overlapCoefficient (N : ℕ) (s : ℝ) : ℝ :=
  (Real.sqrt (lambdaMinus N (s - 1 / 2)))⁻¹ * s / (2 * s + 1) +
  (Real.sqrt (lambdaPlus N (s + 1 / 2)))⁻¹ * (s + 1) / (2 * s + 1)

/-- PDF p.3 Eq.(4): xi at port i, with the other n qubits in their sequential spin basis. -/
def xi {n : ℕ} (i : Fin (n + 1)) (p : SpinPath n) (m : ℤ) :
    EuclideanSpace ℂ (AC 2 (n + 1)) :=
  WithLp.toLp 2 fun x => singlet (x.2, x.1 i) *
    spinVector p m (fun k => x.1 (i.succAbove k))

/-- PDF p.4 Eq.(6): port-teleportation joint primal feasibility, allowing singular X.
Unlike SDP.PrimalFeasible this includes both X and N positive effects with an exact sum. -/
def PortPrimalFeasible {d N : ℕ} (X : Matrix (Ports d N) (Ports d N) ℂ)
    (T : Fin N → Matrix (AC d N) (AC d N) ℂ) : Prop :=
  X.PosSemidef ∧ X.trace = (d : ℂ) ^ N ∧
    (∀ i, (T i).PosSemidef) ∧ ∑ i, T i = resourceLift X

/-- PDF p.4 Eq.(6): primal teleportationObjective. -/
def primalValue {d N : ℕ} (T : Fin N → Matrix (AC d N) (AC d N) ℂ) : ℝ :=
  (∑ i, (T i * signals d N i).trace.re) / (d : ℝ) ^ 2

/-- PDF p.4: trace out the last (Bob) qudit in the dual constraint. -/
def bobTrace {d N : ℕ} (W : Matrix (AC d N) (AC d N) ℂ) :
    Matrix (Ports d N) (Ports d N) ℂ := Matrix.of fun a b => ∑ c, W (a, c) (b, c)

/-- PDF p.4: port-teleportation dual feasibility; a is real and Omega is Hermitian.
Unlike SDP.DualFeasible this uses an operator variable and a partial-trace constraint. -/
def PortDualFeasible {d N : ℕ} (W : Matrix (AC d N) (AC d N) ℂ) (a : ℝ) : Prop :=
  W.IsHermitian ∧ (∀ i, (W - signals d N i).PosSemidef) ∧
    ((a : ℂ) • (1 : Matrix (Ports d N) (Ports d N) ℂ) - bobTrace W).PosSemidef

/-- PDF p.4: the explicitly separable resource |0>_A^{tensor N} tensor product_i |e_i>_B,
expressed in the O parametrization; e labels orthogonal computational output states. -/
def separableOperator {d N : ℕ} (hd : 0 < d) (e : Fin N ↪ Fin d) :
    Matrix (Ports d N) (Ports d N) ℂ :=
  Matrix.of fun x y =>
    if (∀ i, x i = ⟨0, hd⟩) ∧ (∀ i, y i = e i)
    then (Real.sqrt ((d : ℝ) ^ N) : ℂ) else 0

/-- PDF pp.1,4: a CPTP operation is applied to all Bob ports in a program density.
The accepted tensor-superoperator definition includes entangled/off-diagonal inputs. -/
def program {d N : ℕ} (E : Superop (Fin d) (Fin d))
    (R : Matrix (ResourceRegister d N) (ResourceRegister d N) ℂ) : Matrix (ResourceRegister d N) (ResourceRegister d N) ℂ :=
  idTensorSuperop (piSuperop (fun _ : Fin N => E)) R

/-- PDF p.4: two-state squared Uhlmann fidelity (distinct from channel entanglement fidelity). -/
def stateFidelity {I : Type*} [Fintype I] [DecidableEq I]
    (R S : Matrix I I ℂ) : ℝ := rootFidelity R S ^ 2

/-- PDF p.4: average over pure inputs of fidelity to the desired processed output. -/
def programmedAverage {d N : ℕ} (hd : 0 < d) (E : Superop (Fin d) (Fin d))
    (M : Fin N → Matrix (AC d N) (AC d N) ℂ) (R : Matrix (ResourceRegister d N) (ResourceRegister d N) ℂ) : ℝ :=
  ∫ v, stateFidelity (E (pureDensity v))
    (processor M (program E R) (pureDensity v)) ∂QuditFidelity.haarPureStateLaw d hd

/-- Sanity: the retained coordinate is precisely b. PDF p.2. -/
example {d N : ℕ} (i : Fin N) (z : {j : Fin N // j ≠ i} → Fin d) (b : Fin d) :
    insertPort i z b i = b := by simp [insertPort]

/-- Sanity: the zero program produces the zero output; no hidden normalization. PDF pp.1,4. -/
example {d N : ℕ} (M : Fin N → Matrix (AC d N) (AC d N) ℂ) (X : Matrix (Fin d) (Fin d) ℂ) :
    processor M 0 X = 0 := by ext b c; simp [processor]

/-- Sanity: absent outcomes give the zero map, and positive N is required below. PDF p.2. -/
example {d : ℕ} (R : Matrix (ResourceRegister d 0) (ResourceRegister d 0) ℂ) (M : Fin 0 → Matrix (AC d 0) (AC d 0) ℂ) :
    processor M R = fun _ => 0 := by funext X; ext b c; simp [processor]

/-- Sanity: inverse square root sends the zero eigenvalue to zero. PDF p.2. -/
example : (Real.sqrt (0 : ℝ))⁻¹ = 0 := by simp

/-- Sanity: neither singlet has an equal-bit component. PDF pp.2–3. -/
example : singlet (0, 0) = 0 ∧ singlet (1, 1) = 0 := by norm_num [singlet]

/-- Sanity: the one-port singlet and triplet eigenvalues are 1 and 0. PDF p.3. -/
example : lambdaMinus 1 (1 / 2) = 0 ∧ lambdaPlus 1 (1 / 2) = 1 := by
  norm_num [lambdaMinus, lambdaPlus]

/-- Sanity: a negative magnetic number outside the representation is excluded. PDF p.3. -/
example : ¬ ValidMagnetic 0 (-1) := by norm_num [ValidMagnetic]

/-- Sanity: coupling the zero-spin vacuum to a down qubit has unit coefficient. PDF p.3. -/
example : coupling 0 0 1 0 = 1 := by norm_num [coupling, ValidMagnetic, spinBit]

end QAlgorithms.Papers.Independent.Extend50.P38



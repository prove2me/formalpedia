-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P33
-- name    : QAlgorithms_Papers_Independent_Extend50_P33
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:45:11.231864+00:00
-- url     : https://prove2.me/theorems/f3301052-1d01-4cc2-a44c-f7467a847712
-- title:
--   Definitions for Port-based teleportation in arbitrary dimension
-- statement:
--   The objects the formalized statements of *Port-based teleportation in arbitrary dimension* (arXiv:1612.09260) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `sdim`: Specht dimension of the actual regular Young ideal; PDF pp.4,8.
--   - `mult`: Natural tensor multiplicity, computed as the GL(d) Young image dimension; PDF pp.4,9,24 (Schur–Weyl multiplicity).
--   - `Extends`: One-box branching, with height already enforced by both shape types; PDF p.4. This applies also to the untruncated appendix shape types.
--   - `tensorIdentityExtension`: Tensor identity extension on the last q registers; PDF pp.7–8.
--   - `joinWord`: Coordinate concatenation for physical tensor cuts; PDF pp.7,22.
--   - `traceFinalQudits`: Partial trace over exactly the last q qudits; PDF pp.11,13,22.
--   - `transposeLast`: Partial transpose on the final qudit, in the computational basis; PDF p.6.
--   - `unnormalizedPortBell`: Unnormalized Bell operator B on port a and input r, identity elsewhere; PDF pp.3,6,14,22. It has B²=dB, rather than B²=B.
--   - `bellQ`: Trace-one Bell projector Q=B/d on the selected pair; identities elsewhere. PDF pp.27–28, Eqs.(100),(106).
--   - `portSwap`: Swap a with the final Alice port; the last (input) register is fixed. PDF pp.8,27. The identity coset is included.
--   - `effect`: A bar-a operator is expressed in the ordered coordinates obtained by swapping a with the final Alice port; PDF pp.12,28, Eq.(108).
--   - `pbtSwapSum`: η is the actual partially transposed swap sum, without d^(-N); PDF p.7, Eq.(3). Here N=k+2 and n=k+3.
--   - `etaAlpha`: The physical α component constructed from Young projectors and Bell operators, PDF p.8 Eq.(7), before taking its support.
--   - `mBlock`: Physical M_alpha, constructed as support of Eq.(7), PDF p.8.
--   - `fBlock`: Physical F_mu(alpha)=M_alpha P_mu, PDF p.8.
--   - `pbtBlockEigenvalue`: Spectral scalar computed by the trace quotient, PDF p.9 Eq.(12). Its multiplicity/character formulas are conclusions below.
--   - `classScalar`: Central transposition-class scalar. Empty classes at degrees zero and one have scalar zero; PDF pp.9,18–20.
--   - `reciprocalSet`: Positive physical successor eigenvalues whose reciprocals are minimized; PDF p.27 Eq.(101). Finite nonemptiness is part of the mathematical result.
--   - `minReciprocal`: The finite minimum, used only with d≥2 and N≥2; PDF p.27 Eq.(101).
--   - `fixedTheta`: Optimal fixed-resource auxiliary operators in bar-a coordinates; PDF p.12 Proposition7 and p.27 Eq.(101).
--   - `pbtSuccessProbability`: Objective of the exact-success probabilistic PBT SDP, PDF p.11 Eq.(19).
--   - `FixedFeasible`: Physical fixed-resource primal feasibility; PDF p.11 Eq.(20).
--   - `fixedValues`: Fixed-resource feasible success values, without an empty/unbounded real supremum convention; PDF p.11.
--   - `fixedValue`: The corrected achievable value N/d^N sum_alpha m_alpha d_alpha/max gamma; PDF pp.11,27, missing N in the printed Lemma4 corrected from Eq.(19),(102).
--   - `fixedRatioValue`: Multiplicity-ratio minimum in Theorem3; PDF pp.4,11.
--   - `pairTrace`: Pair trace in the bar-a coordinates; PDF p.11 Eq.(22), p.13 Eq.(28).
--   - `FixedDual`: The fixed-resource dual has all N constraints and uses Q=B/d; PDF pp.11,28 Eqs.(22),(106).
--   - `MaxSelector`: A maximizing successor selector (not a supplied SDP witness); PDF p.11 Eq.(23).
--   - `fixedOmega`: Actual dual matrix for any maximizing selector, PDF p.28 Eq.(106).
--   - `squareSum`: Sum of squared actual tensor multiplicities, including degree zero; PDF p.24 Eq.(84).
--   - `jointX`: Explicit jointly optimal resource matrix X, PDF pp.12,28 Eq.(26),(109).
--   - `jointTheta`: Explicit jointly optimal transformed auxiliary effects, PDF pp.12,28 Eqs.(27),(108). They are transported to physical effects below.
--   - `JointFeasible`: Joint primal feasibility, including positivity and normalization of X; PDF p.12 Eq.(25).
--   - `jointValues`: Jointly attainable SDP success values; PDF pp.12–13.
--   - `optimalProbability`: Closed success expression with N ports, PDF pp.12–13,29 Eq.(112).
--   - `jointO`: O=X^(1/2), using the nonnegative spectral square root; PDF p.12.
--   - `resourceVector`: (O tensor I)|Phi_d>^tensor N, with normalized Bell pairs; PDF p.12 Theorem8. Its norm is a conclusion, not a premise.
--   - `jointPhysical`: Physical success effects obtained from the transformed SDP effects by conjugation with O^(-1); PDF p.12 Eq.(25).
--   - `jointFailure`: Failure effect completing the physical N+1 outcome POVM; PDF pp.2,12.
--   - `jointOmega`: The actual joint dual witness d eta/(N+d²−1), PDF p.29 Eq.(117).
--   - `JointDual`: Joint dual constraints: the third traces out the input n, correcting printed Tr_a in Eq.(28) by Eqs.(119)–(121), PDF pp.13,30.
--   - `pbtSignal`: rho_a=B_a/d^N from PDF pp.3,6, distinct from SDP's Q_a.
--   - `srmRaw`: Uncompleted square-root measurement, with inverse zero on the kernel; PDF pp.5,13,14.
--   - `srm`: Completed deterministic POVM: Delta uses the uncompleted effects, resolving the self-reference in the source; PDF pp.5,13.
--   - `portOutcome`: Physical subchannel for one outcome: measure E on Alice's N ports and input, discard Alice and every Bob port except a, and identify that port with Fin d. The resource amplitudes are O(x,z)/sqrt(d^N). This contraction is independent of the measurement instrument because Alice is discarded. PDF pp.2,4–5,12–14. No output correction or transpose is applied by Bob.
--   - `ProtocolPOVM`: The N conclusive effects together with the residual failure effect form an N+1 outcome POVM; PDF pp.2,11–12.
--   - `ExactPBT`: Perfect conclusive teleportation for every input operator, hence also for inputs entangled with a reference. Each outcome subchannel is its nonnegative probability times the identity; total success is p. PDF pp.2,4,11–12. This is not an SDP certificate.
--   - `fixedOperationalValues`: Operational attainable probabilities for the fixed normalized Bell-pair resource O=I, ranging over every perfect-conclusive POVM, not only effects already supplied in the source's reduced SDP form. PDF pp.4,11.
--   - `jointOperationalValues`: Operational attainable probabilities over all pure resource states and perfect-conclusive POVMs. Every pure resource has coefficients O(x,z)/sqrt(d^N); Tr(O†O)=d^N is precisely its normalization. Singular O is allowed. PDF p.12, Theorem8.
--   - `pbtDeterministicChannel`: Actual deterministic channel: normalized Bell resource, Alice's completed square-root POVM and Bob's selected port, with all other systems discarded. PDF pp.5,13–14.
--   - `deterministicFidelity`: Entanglement fidelity of the actual channel with a normalized Bell reference, rather than a definition by the proof's trace identity (30). PDF pp.5,13–14.
--   - `cycles`: Full number of cycles, including every fixed point, PDF p.24.
--   - `extendPerm`: Inclusion S_r into S_(r+1) fixing the final letter; PDF pp.17,24.
--   - `fourierSubgroup`: Unscaled subgroup Fourier sum F_ij^mu (not F_mu(alpha)); PDF p.20 Eq.(64).
--   - `permutationSpan`: The represented permutation algebra as its actual linear span; PDF pp.22,25. Linear dependence of permutation operators is allowed.
--   - `transposedSpan`: The represented partially transposed permutation algebra, PDF p.22: its underlying vector space is the span of the actual transposed matrices.
--   - `RealizesSpechtIrrep`: Realization of the irreducible labelled by mu in an arbitrary orthonormal coordinate space. The intertwiner identifies the label; no branching, projector rank or sum rule is assumed. PDF pp.17–18.
--   - `Preds`: Every predecessor shape, without the physical height-d truncation; PDF pp.17–18, Eq.(42). At degree zero there is the empty diagram.
--   - `subgroupProjector`: The subgroup isotypic projector in any realization R, independently computed by its character sum, PDF pp.17–18.
--   - `predecessorAction`: The orthonormal Specht direct-sum action on all predecessors; PDF p.17 Eq.(42).
-- source:
--   Port-based teleportation in arbitrary dimension, arXiv:1612.09260v3, https://arxiv.org/abs/1612.09260v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurWeylDecomposition
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Gap20_P01

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P33

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted type constructors; local notation only reorders Word's arguments.
local notation "Word" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P58.Word r d)

local notation "Op" => (fun d r : ℕ =>
  QAlgorithms.Papers.Independent.Information100.P21.Op
    (QAlgorithms.Papers.Independent.Information100.P58.Word r d))

open QAlgorithms.Papers.Independent.Information100.P07 (support)
open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

/-- Specht dimension of the actual regular Young ideal; PDF pp.4,8. -/
def sdim {d r : ℕ} (a : Schur.Partition d r) : ℕ :=
  Module.finrank ℂ (Schur.spechtSpace a)

/-- Natural tensor multiplicity, computed as the GL(d) Young image dimension;
PDF pp.4,9,24 (Schur–Weyl multiplicity). -/
def mult {d r : ℕ} (a : Schur.Partition d r) : ℕ :=
  Module.finrank ℂ (Schur.schurModule a)

/-- One-box branching, with height already enforced by both shape types;
PDF p.4. This applies also to the untruncated appendix shape types. -/
def Extends {d e r : ℕ} (a : Schur.Partition d r)
    (b : Schur.Partition e (r+1)) : Prop := a.val.cells ⊆ b.val.cells

/-- Tensor identity extension on the last q registers; PDF pp.7–8. -/
def tensorIdentityExtension {d p : ℕ} (q : ℕ) (A : Op d p) : Op d (p+q) :=
  fun x y => if ∀ i : Fin (p+q), p ≤ i.val → x i = y i then
    A (fun i => x ⟨i.val,by omega⟩) (fun i => y ⟨i.val,by omega⟩) else 0

/-- Coordinate concatenation for physical tensor cuts; PDF pp.7,22. -/
def joinWord {d p q : ℕ} (x : Word d p) (z : Word d q) : Word d (p+q) :=
  fun i => if h : i.val < p then x ⟨i.val,h⟩ else z ⟨i.val-p,by omega⟩

/-- Partial trace over exactly the last q qudits; PDF pp.11,13,22. -/
def traceFinalQudits {d p : ℕ} (q : ℕ) (A : Op d (p+q)) : Op d p :=
  fun x y => ∑ z : Word d q, A (joinWord x z) (joinWord y z)

/-- Partial transpose on the final qudit, in the computational basis; PDF p.6. -/
def transposeLast {d r : ℕ} (A : Op d (r+1)) : Op d (r+1) :=
  fun x y => A (Function.update x (Fin.last r) (y (Fin.last r)))
    (Function.update y (Fin.last r) (x (Fin.last r)))

/-- Unnormalized Bell operator B on port a and input r, identity elsewhere;
PDF pp.3,6,14,22. It has B²=dB, rather than B²=B. -/
def unnormalizedPortBell (d r : ℕ) (a : Fin r) : Op d (r+1) :=
  fun x y => if x a.castSucc = x (Fin.last r) ∧
    y a.castSucc = y (Fin.last r) ∧
    (∀ i : Fin (r+1), i ≠ a.castSucc → i ≠ Fin.last r → x i = y i)
    then 1 else 0

/-- Trace-one Bell projector Q=B/d on the selected pair; identities elsewhere.
PDF pp.27–28, Eqs.(100),(106). -/
def bellQ (d r : ℕ) (a : Fin r) : Op d (r+1) := (1/(d:ℂ)) • unnormalizedPortBell d r a

/-- Swap a with the final Alice port; the last (input) register is fixed.
PDF pp.8,27. The identity coset is included. -/
def portSwap (d k : ℕ) (a : Fin (k+2)) : Op d (k+3) :=
  Schur.tensorPermutation d (k+3)
    (Equiv.swap a.castSucc (Fin.last (k+1)).castSucc)

/-- A bar-a operator is expressed in the ordered coordinates obtained by
swapping a with the final Alice port; PDF pp.12,28, Eq.(108). -/
def effect {d k : ℕ} (a : Fin (k+2)) (T : Op d (k+1)) : Op d (k+3) :=
  portSwap d k a * (bellQ d (k+2) (Fin.last (k+1)) * tensorIdentityExtension 2 T) *
    portSwap d k a

/-- η is the actual partially transposed swap sum, without d^(-N);
PDF p.7, Eq.(3). Here N=k+2 and n=k+3. -/
def pbtSwapSum (d k : ℕ) : Op d (k+3) := ∑ a : Fin (k+2), unnormalizedPortBell d (k+2) a

/-- The physical α component constructed from Young projectors and Bell
operators, PDF p.8 Eq.(7), before taking its support. -/
def etaAlpha {d k : ℕ} (a : Schur.Partition d (k+1)) : Op d (k+3) :=
  ∑ b : Fin (k+2), portSwap d k b *
    (tensorIdentityExtension 2 (Schur.isotypicProjector a) * unnormalizedPortBell d (k+2) (Fin.last (k+1))) *
    portSwap d k b

/-- Physical M_alpha, constructed as support of Eq.(7), PDF p.8. -/
def mBlock {d k : ℕ} (a : Schur.Partition d (k+1)) : Op d (k+3) :=
  support (etaAlpha a)

/-- Physical F_mu(alpha)=M_alpha P_mu, PDF p.8. -/
def fBlock {d k : ℕ} (a : Schur.Partition d (k+1))
    (b : Schur.Partition d (k+2)) : Op d (k+3) :=
  mBlock a * tensorIdentityExtension 1 (Schur.isotypicProjector b)

/-- Spectral scalar computed by the trace quotient, PDF p.9 Eq.(12).
Its multiplicity/character formulas are conclusions below. -/
def pbtBlockEigenvalue {d k : ℕ} (a : Schur.Partition d (k+1))
    (b : Schur.Partition d (k+2)) : ℝ :=
  ( (tensorIdentityExtension 1 (Schur.isotypicProjector b) * etaAlpha a).trace ).re /
    ((mult a : ℝ) * sdim b)

/-- Central transposition-class scalar. Empty classes at degrees zero and one
have scalar zero; PDF pp.9,18–20. -/
def classScalar {d r : ℕ} (a : Schur.Partition d r) : ℝ :=
  (∑ i : Fin r, ∑ j : Fin r, if i < j then
    (Schur.spechtCharacter a (Equiv.swap i j)).re else 0) / sdim a

/-- Positive physical successor eigenvalues whose reciprocals are minimized;
PDF p.27 Eq.(101). Finite nonemptiness is part of the mathematical result. -/
def reciprocalSet {d k : ℕ} (a : Schur.Partition d (k+1)) : Set ℝ :=
  {x | ∃ b : Schur.Partition d (k+2), Extends a b ∧ x = 1 / pbtBlockEigenvalue a b}

/-- The finite minimum, used only with d≥2 and N≥2; PDF p.27 Eq.(101). -/
def minReciprocal {d k : ℕ} (a : Schur.Partition d (k+1)) : ℝ :=
  sInf (reciprocalSet a)

/-- Optimal fixed-resource auxiliary operators in bar-a coordinates;
PDF p.12 Proposition7 and p.27 Eq.(101). -/
def fixedTheta (d k : ℕ) : Fin (k+2) → Op d (k+1) := fun _ =>
  ∑ a : Schur.Partition d (k+1), ((d:ℂ) * (minReciprocal a : ℂ)) •
    Schur.isotypicProjector a

/-- Objective of the exact-success probabilistic PBT SDP, PDF p.11 Eq.(19). -/
def pbtSuccessProbability {d k : ℕ} (T : Fin (k+2) → Op d (k+1)) : ℝ :=
  (∑ a, (T a).trace.re) / (d:ℝ)^(k+3)

/-- Physical fixed-resource primal feasibility; PDF p.11 Eq.(20). -/
def FixedFeasible {d k : ℕ} (T : Fin (k+2) → Op d (k+1)) : Prop :=
  (∀ a, (T a).PosSemidef) ∧ (1 - ∑ a, effect a (T a)).PosSemidef

/-- Fixed-resource feasible success values, without an empty/unbounded real
supremum convention; PDF p.11. -/
def fixedValues (d k : ℕ) : Set ℝ := {p | ∃ T : Fin (k+2) → Op d (k+1),
    FixedFeasible (d := d) (k := k) T ∧
      p = pbtSuccessProbability (d := d) (k := k) T}

/-- The corrected achievable value N/d^N sum_alpha m_alpha d_alpha/max gamma;
PDF pp.11,27, missing N in the printed Lemma4 corrected from Eq.(19),(102). -/
def fixedValue (d k : ℕ) : ℝ :=
  ((k+2:ℕ):ℝ) / (d:ℝ)^(k+2) *
    ∑ a : Schur.Partition d (k+1), (mult a:ℝ) * sdim a * minReciprocal a

/-- Multiplicity-ratio minimum in Theorem3; PDF pp.4,11. -/
def fixedRatioValue (d k : ℕ) : ℝ :=
  (1/(d:ℝ)^(k+2)) * ∑ a : Schur.Partition d (k+1), (mult a:ℝ)^2 *
    sInf {x : ℝ | ∃ b : Schur.Partition d (k+2), Extends a b ∧
      x = (sdim b:ℝ) / mult b}

/-- Pair trace in the bar-a coordinates; PDF p.11 Eq.(22), p.13 Eq.(28). -/
def pairTrace {d k : ℕ} (a : Fin (k+2)) (A : Op d (k+3)) : Op d (k+1) :=
  traceFinalQudits 2 (portSwap d k a * A * portSwap d k a)

/-- The fixed-resource dual has all N constraints and uses Q=B/d;
PDF pp.11,28 Eqs.(22),(106). -/
def FixedDual {d k : ℕ} (A : Op d (k+3)) : Prop :=
  A.PosSemidef ∧ ∀ a : Fin (k+2), (pairTrace a (bellQ d (k+2) a * A) - 1).PosSemidef

/-- A maximizing successor selector (not a supplied SDP witness); PDF p.11 Eq.(23). -/
def MaxSelector {d k : ℕ}
    (s : Schur.Partition d (k+1) → Schur.Partition d (k+2)) : Prop :=
  ∀ a, Extends a (s a) ∧ ∀ b, Extends a b → pbtBlockEigenvalue a b ≤ pbtBlockEigenvalue a (s a)

/-- Actual dual matrix for any maximizing selector, PDF p.28 Eq.(106). -/
def fixedOmega {d k : ℕ}
    (s : Schur.Partition d (k+1) → Schur.Partition d (k+2)) : Op d (k+3) :=
  ∑ a, ((d:ℂ) * (mult a:ℂ) / (mult (s a):ℂ)) • fBlock a (s a)

/-- Sum of squared actual tensor multiplicities, including degree zero;
PDF p.24 Eq.(84). -/
def squareSum (d r : ℕ) : ℝ := ∑ a : Schur.Partition d r, (mult a:ℝ)^2

/-- Explicit jointly optimal resource matrix X, PDF pp.12,28 Eq.(26),(109). -/
def jointX (d k : ℕ) : Op d (k+2) :=
  ∑ b : Schur.Partition d (k+2),
    ((d:ℂ)^(k+2) / (squareSum d (k+2):ℂ) * (mult b:ℂ) / (sdim b:ℂ)) •
      Schur.isotypicProjector b

/-- Explicit jointly optimal transformed auxiliary effects, PDF pp.12,28
Eqs.(27),(108). They are transported to physical effects below. -/
def jointTheta (d k : ℕ) : Fin (k+2) → Op d (k+1) := fun _ =>
  ∑ a : Schur.Partition d (k+1),
    ((d:ℂ)^(k+3) / (squareSum d (k+2):ℂ) * (mult a:ℂ) /
      (((k+2:ℕ):ℂ) * (sdim a:ℂ))) • Schur.isotypicProjector a

/-- Joint primal feasibility, including positivity and normalization of X;
PDF p.12 Eq.(25). -/
def JointFeasible {d k : ℕ} (X : Op d (k+2))
    (T : Fin (k+2) → Op d (k+1)) : Prop :=
  X.PosSemidef ∧ X.trace = (d:ℂ)^(k+2) ∧ (∀ a, (T a).PosSemidef) ∧
    (tensorIdentityExtension 1 X - ∑ a, effect a (T a)).PosSemidef

/-- Jointly attainable SDP success values; PDF pp.12–13. -/
def jointValues (d k : ℕ) : Set ℝ :=
  {p | ∃ X : Op d (k+2), ∃ T : Fin (k+2) → Op d (k+1),
    JointFeasible (d := d) (k := k) X T ∧
      p = pbtSuccessProbability (d := d) (k := k) T}

/-- Closed success expression with N ports, PDF pp.12–13,29 Eq.(112). -/
def optimalProbability (d N : ℕ) : ℝ := (N:ℝ) / ((N:ℝ) + (d:ℝ)^2 - 1)

/-- O=X^(1/2), using the nonnegative spectral square root; PDF p.12. -/
def jointO (d k : ℕ) : Op d (k+2) := cfc Real.sqrt (jointX d k)

/-- (O tensor I)|Phi_d>^tensor N, with normalized Bell pairs;
PDF p.12 Theorem8. Its norm is a conclusion, not a premise. -/
def resourceVector (d k : ℕ) :
    EuclideanSpace ℂ (Word d (k+2) × Word d (k+2)) :=
  WithLp.toLp 2 fun z => jointO d k z.1 z.2 / (Real.sqrt ((d:ℝ)^(k+2)) : ℂ)

/-- Physical success effects obtained from the transformed SDP effects by
conjugation with O^(-1); PDF p.12 Eq.(25). -/
def jointPhysical (d k : ℕ) (a : Fin (k+2)) : Op d (k+3) :=
  tensorIdentityExtension 1 (jointO d k)⁻¹ * effect a (jointTheta d k a) *
    tensorIdentityExtension 1 (jointO d k)⁻¹

/-- Failure effect completing the physical N+1 outcome POVM; PDF pp.2,12. -/
def jointFailure (d k : ℕ) : Op d (k+3) := 1 - ∑ a, jointPhysical d k a

/-- The actual joint dual witness d eta/(N+d²−1), PDF p.29 Eq.(117). -/
def jointOmega (d k : ℕ) : Op d (k+3) :=
  ((d:ℂ) / (((k+2:ℕ):ℂ) + (d:ℂ)^2 - 1)) • pbtSwapSum d k

/-- Joint dual constraints: the third traces out the input n, correcting
printed Tr_a in Eq.(28) by Eqs.(119)–(121), PDF pp.13,30. -/
def JointDual {d k : ℕ} (A : Op d (k+3)) (b : ℝ) : Prop :=
  FixedDual A ∧ 0 ≤ b ∧
    ((b:ℂ) • (1 : Op d (k+2)) - (1/(d:ℂ)^(k+3)) • traceFinalQudits 1 A).PosSemidef

/-- rho_a=B_a/d^N from PDF pp.3,6, distinct from SDP's Q_a. -/
def pbtSignal (d k : ℕ) (a : Fin (k+2)) : Op d (k+3) :=
  (1/(d:ℂ)^(k+2)) • unnormalizedPortBell d (k+2) a

/-- Uncompleted square-root measurement, with inverse zero on the kernel;
PDF pp.5,13,14. -/
def srmRaw (d k : ℕ) (a : Fin (k+2)) : Op d (k+3) :=
  let R := cfc (fun x : ℝ => (Real.sqrt x)⁻¹) (∑ b, pbtSignal d k b)
  R * pbtSignal d k a * R

/-- Completed deterministic POVM: Delta uses the uncompleted effects,
resolving the self-reference in the source; PDF pp.5,13. -/
def srm (d k : ℕ) (a : Fin (k+2)) : Op d (k+3) :=
  srmRaw d k a + (1/((k+2:ℕ):ℂ)) • (1 - ∑ b, srmRaw d k b)

/-- Physical subchannel for one outcome: measure E on Alice's N ports and
input, discard Alice and every Bob port except a, and identify that port with
Fin d. The resource amplitudes are O(x,z)/sqrt(d^N). This contraction is
independent of the measurement instrument because Alice is discarded.
PDF pp.2,4–5,12–14. No output correction or transpose is applied by Bob. -/
def portOutcome {d k : ℕ} (O : Op d (k+2)) (E : Op d (k+3))
    (a : Fin (k+2)) : Superop (Fin d) (Fin d) :=
  fun Z u v => (1/(d:ℂ)^(k+2)) *
    ∑ z : Word d (k+2), if z a = u then
      ∑ x : Word d (k+2), ∑ y : Word d (k+2),
        ∑ i : Fin d, ∑ j : Fin d,
          O x z * star (O y (Function.update z a v)) * Z i j *
            E (joinWord (d := d) (p := k+2) (q := 1) y (fun _ : Fin 1 => j))
              (joinWord (d := d) (p := k+2) (q := 1) x (fun _ : Fin 1 => i))
      else 0

/-- The N conclusive effects together with the residual failure effect form
an N+1 outcome POVM; PDF pp.2,11–12. -/
def ProtocolPOVM {d k : ℕ} (E : Fin (k+2) → Op d (k+3)) : Prop :=
  (∀ a, (E a).PosSemidef) ∧ (1 - ∑ a, E a).PosSemidef

/-- Perfect conclusive teleportation for every input operator, hence also
for inputs entangled with a reference. Each outcome subchannel is its
nonnegative probability times the identity; total success is p.
PDF pp.2,4,11–12. This is not an SDP certificate. -/
def ExactPBT {d k : ℕ} (O : Op d (k+2))
    (E : Fin (k+2) → Op d (k+3)) (p : ℝ) : Prop :=
  ∃ c : Fin (k+2) → ℝ, (∀ a, 0 ≤ c a) ∧ (∑ a, c a) = p ∧
    ∀ a Z, portOutcome O (E a) a Z = (c a : ℂ) • Z

/-- Operational attainable probabilities for the fixed normalized Bell-pair
resource O=I, ranging over every perfect-conclusive POVM, not only effects
already supplied in the source's reduced SDP form. PDF pp.4,11. -/
def fixedOperationalValues (d k : ℕ) : Set ℝ :=
  {p | ∃ E : Fin (k+2) → Op d (k+3), ProtocolPOVM E ∧
    ExactPBT (1 : Op d (k+2)) E p}

/-- Operational attainable probabilities over all pure resource states and
perfect-conclusive POVMs. Every pure resource has coefficients O(x,z)/sqrt(d^N);
Tr(O†O)=d^N is precisely its normalization. Singular O is allowed.
PDF p.12, Theorem8. -/
def jointOperationalValues (d k : ℕ) : Set ℝ :=
  {p | ∃ O : Op d (k+2), ∃ E : Fin (k+2) → Op d (k+3),
    (star O * O).trace = (d:ℂ)^(k+2) ∧ ProtocolPOVM E ∧ ExactPBT O E p}

/-- Actual deterministic channel: normalized Bell resource, Alice's completed
square-root POVM and Bob's selected port, with all other systems discarded.
PDF pp.5,13–14. -/
def pbtDeterministicChannel (d k : ℕ) : Superop (Fin d) (Fin d) :=
  fun Z => ∑ a : Fin (k+2), portOutcome (1 : Op d (k+2)) (srm d k a) a Z

/-- Entanglement fidelity of the actual channel with a normalized Bell
reference, rather than a definition by the proof's trace identity (30).
PDF pp.5,13–14. -/
def deterministicFidelity (d k : ℕ) (hd : 0 < d) : ℝ :=
  QuditFidelity.entanglementFidelity d hd (pbtDeterministicChannel d k)

/-- Full number of cycles, including every fixed point, PDF p.24. -/
def cycles {r : ℕ} (pi : Equiv.Perm (Fin r)) : ℕ :=
  pi.cycleType.card + (r - pi.support.card)

/-- Inclusion S_r into S_(r+1) fixing the final letter; PDF pp.17,24. -/
def extendPerm {r : ℕ} (pi : Equiv.Perm (Fin r)) : Equiv.Perm (Fin (r+1)) :=
  Equiv.permCongr finSumFinEquiv (Equiv.sumCongr pi (Equiv.refl (Fin 1)))

/-- Unscaled subgroup Fourier sum F_ij^mu (not F_mu(alpha)); PDF p.20 Eq.(64). -/
def fourierSubgroup {d k : ℕ} (b : Schur.Partition d (k+2))
    (i j : Fin (sdim b)) : Op d (k+2) :=
  ∑ pi : Equiv.Perm (Fin (k+1)),
    spechtMatrix b (extendPerm pi⁻¹) j i •
      Schur.tensorPermutation d (k+2) (extendPerm pi)

/-- The represented permutation algebra as its actual linear span;
PDF pp.22,25. Linear dependence of permutation operators is allowed. -/
def permutationSpan (d r : ℕ) : Submodule ℂ (Op d r) :=
  Submodule.span ℂ (Set.range (Schur.tensorPermutation d r))

/-- The represented partially transposed permutation algebra, PDF p.22:
its underlying vector space is the span of the actual transposed matrices. -/
def transposedSpan (d r : ℕ) : Submodule ℂ (Op d (r+1)) :=
  Submodule.span ℂ (Set.range fun pi : Equiv.Perm (Fin (r+1)) =>
    transposeLast (Schur.tensorPermutation d (r+1) pi))

/-- Realization of the irreducible labelled by mu in an arbitrary orthonormal
coordinate space. The intertwiner identifies the label; no branching, projector
rank or sum rule is assumed. PDF pp.17–18. -/
def RealizesSpechtIrrep {r D : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ) : Prop :=
  ∃ e : Schur.spechtSpace mu ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D),
    ∀ pi v, e (Schur.spechtRepresentation mu pi v) =
      act (R pi : Matrix (Fin D) (Fin D) ℂ) (e v)

/-- Every predecessor shape, without the physical height-d truncation;
PDF pp.17–18, Eq.(42). At degree zero there is the empty diagram. -/
abbrev Preds {r : ℕ} (mu : Schur.Partition (r+1) (r+1)) :=
  {a : Schur.Partition r r // Extends a mu}

/-- The subgroup isotypic projector in any realization R, independently
computed by its character sum, PDF pp.17–18. -/
def subgroupProjector {r D : ℕ}
    (R : Equiv.Perm (Fin (r+1)) →* Matrix.unitaryGroup (Fin D) ℂ)
    (a : Schur.Partition r r) : Matrix (Fin D) (Fin D) ℂ :=
  ((sdim a:ℂ)/(r.factorial:ℂ)) •
    ∑ pi : Equiv.Perm (Fin r), Schur.spechtCharacter a pi⁻¹ •
      (R (extendPerm pi) : Matrix (Fin D) (Fin D) ℂ)

/-- The orthonormal Specht direct-sum action on all predecessors; PDF p.17 Eq.(42). -/
def predecessorAction {r : ℕ} (mu : Schur.Partition (r+1) (r+1))
    (pi : Equiv.Perm (Fin r))
    (v : EuclideanSpace ℂ ((a : Preds mu) × Fin (sdim a.val))) :
    EuclideanSpace ℂ ((a : Preds mu) × Fin (sdim a.val)) :=
  WithLp.toLp 2 fun z => ∑ j : Fin (sdim z.1.val),
    spechtMatrix z.1.val pi z.2 j * v ⟨z.1,j⟩

/-- At the all-zero tensor word, the unnormalized Bell coefficient is one;
PDF p.22 Eq.(70), normalization sanity check. -/
example : unnormalizedPortBell 2 2 0 (fun _ => 0) (fun _ => 0) = 1 := by simp [unnormalizedPortBell]

/-- The normalized Bell coefficient is 1/2 at d=2, PDF p.27 Eq.(100). -/
example : bellQ 2 2 0 (fun _ => 0) (fun _ => 0) = (1/2:ℂ) := by
  simp [bellQ,unnormalizedPortBell]

/-- Identity permutations have r cycles, including fixed points; PDF p.24. -/
example (r : ℕ) : cycles (1 : Equiv.Perm (Fin r)) = r := by simp [cycles]

/-- At d=2,N=2 the joint closed value is 2/5; PDF p.29 Eq.(112). -/
example : optimalProbability 2 2 = (2/5:ℝ) := by norm_num [optimalProbability]

/-- Zero operator has zero support; PDF p.8 support convention. -/
example (d r : ℕ) : support (0 : Op d r) = 0 := by
  simp [support,
    QAlgorithms.Papers.Independent.Information100.P07.projection,
    QAlgorithms.Papers.Independent.Information100.P07.operatorRange]

/-- A zero measurement effect produces the zero outcome map on every input;
this checks the effect's placement in the physical contraction. -/
example {d k : ℕ} (O : Op d (k+2)) (a : Fin (k+2))
    (Z : Matrix (Fin d) (Fin d) ℂ) : portOutcome O 0 a Z = 0 := by
  ext u v
  simp [portOutcome]

end QAlgorithms.Papers.Independent.Extend50.P33



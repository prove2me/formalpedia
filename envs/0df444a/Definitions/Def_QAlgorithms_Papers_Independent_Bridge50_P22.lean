-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22
-- name    : QAlgorithms_Papers_Independent_Bridge50_P22
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T15:09:19.925545+00:00
-- url     : https://prove2.me/theorems/1b69b172-7f74-44d0-804d-3f2e69de31d3
-- title:
--   Definitions for Amortization does not enhance the max-Rains information of a quantum channel
-- statement:
--   The objects the formalized statements of *Amortization does not enhance the max-Rains information of a quantum channel* (arXiv:1709.04907) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `channelUse`: PDF pp.5,7,14, (29),(80): identity on both memories and N on A. Input cut is (L A):R; output cut is L:(B R). Off-diagonal memory blocks are retained. This also writes out the source's implicit regrouping.
--   - `stateMaxRains`: PDF p.6, (17),(19),(21): max-Rains relative entropy over PPT-prime. The comparison operators are positive but need not have trace one. EReal preserves support-failure infinity in the inner Dmax optimization.
--   - `channelMaxRains`: PDF pp.2,7, (2),(23): max-Rains information of the fixed channel. The reference is a copy of A, and every unit vector on S A is allowed. On CPTP channels with positive finite input/output dimensions this is finite.
--   - `amortizedMaxRains`: PDF pp.2–3,7, (3): all finite positive ancillary dimensions, all mixed states. The indices l,r encode dimensions l+1,r+1, including one and with no cutoff. Each subtracted state quantity is finite on the normalized finite-dimensional inputs and their CPTP outputs; no infinity-minus-infinity case is used.
--   - `channelEMax`: PDF pp.2,13, (2),(69): channel Emax from the accepted state Emax. All pure S A inputs are optimized, with S isomorphic to A.
--   - `amortizedEMax`: PDF pp.2–3,12–13, (3),(68): amortized Emax with unrestricted finite memories. Only normalized states occur; all state Emax values in the difference are finite.
--   - `stateConeObjectives`: PDF p.13, (71): feasible trace values on the full separable positive cone. Trace normalization of X is deliberately absent.
--   - `wSep`: PDF p.13, (71): separable-cone state value. On density matrices the feasible set is nonempty and bounded below by one. Lemma 6 below asserts that this infimum is an attained minimum.
--   - `channelConeObjectives`: PDF p.13, (76): spectral operator-norm objectives over the separable cone. The accepted choi is UNNORMALIZED: its identity-channel trace is dim A. The accepted specNorm is the Euclidean operator norm, not an entrywise norm.
--   - `sigmaSep`: PDF p.13, (76): separable-cone channel value. For CPTP N on positive finite registers the objective set is nonempty and bounded below by one. Lemma 7 asserts attainment as well as the identity.
--   - `PPTExecution`: PDF p.10, (44)–(46): the state after n actual uses of this same fixed N. The first constructor prepares from the trivial bipartite system through a PPT-preserving channel; step adds one interleaving PPT channel and one N use. Memory dimensions l+1 and r+1 are arbitrary positive finite integers. There is no zero-use constructor and no entanglement-budget assumption.
--   - `IsProtocolOutput`: PDF p.10, (47): output of a concrete adaptive PPT-P-assisted protocol. The decoder is a final PPT channel. The input to the first channel use is constructed by PPTExecution.first, rather than supplied as a free state.
--   - `IsPPTProtocol`: PDF p.10, (48)–(50): an (n,M,epsilon) protocol, with squared fidelity. The target is the normalized projector onto M^(-1/2) sum_i |i i>. The actual overlap need only be at least 1-epsilon, not equal to it.
--   - `communicationRate`: PDF pp.10–12: qubits per channel use. Only n,M>0 occur in protocols.
--   - `IsStrongConverseRate`: PDF pp.10–11: for every fixed error epsilon<1 and positive rate slack, all sufficiently large positive block lengths admit no such protocol. Integer M with log2 M >= n(R+delta) implements the source's 2^(n(R+delta)) shorthand; the arbitrary positive slack absorbs integer rounding.
--   - `strongConversePPTCapacity`: PDF p.11: infimum of strong-converse rates, retaining the dagger. An extended infimum avoids a default real value for an empty/unbounded set.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, https://arxiv.org/abs/1709.04907v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P36
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

/-!
Berta and Wilde, arXiv:1709.04907v2. All page numbers are PDF pages.
All new definitions are local to this paper. Registers are finite product bases;
nonempty factors are required wherever information quantities are evaluated.
The accepted state Emax, Dmax, PPT-prime, separable cone, spectral norm, Choi
matrix, PPT maps, Bell target and heterogeneous tensor action are reused.
Compilation is pending the separate batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology
open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)
open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)
open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)
open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

/-- PDF pp.5,7,14, (29),(80): identity on both memories and N on A.
Input cut is (L A):R; output cut is L:(B R). Off-diagonal memory blocks
are retained. This also writes out the source's implicit regrouping. -/
def channelUse {A B L R : Type} (N : Superop A B) :
    Superop ((L × A) × R) (L × (B × R)) :=
  fun rho p q => N (fun a aa => rho ((p.1,a),p.2.2) ((q.1,aa),q.2.2)) p.2.1 q.2.1

/-- PDF p.6, (17),(19),(21): max-Rains relative entropy over PPT-prime.
The comparison operators are positive but need not have trace one. EReal
preserves support-failure infinity in the inner Dmax optimization. -/
def stateMaxRains {I J : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Nonempty I] [Nonempty J]
    (rho : Mat (I × J)) : EReal :=
  sInf {v | ∃ sigma : Mat (I × J), pptPrime sigma ∧ v = maxRelative rho sigma}

/-- PDF pp.2,7, (2),(23): max-Rains information of the fixed channel.
The reference is a copy of A, and every unit vector on S A is allowed.
On CPTP channels with positive finite input/output dimensions this is finite. -/
def channelMaxRains {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) : EReal :=
  sSup {v | ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧
    v = stateMaxRains (idTensorSuperop N (pureDensity psi))}

/-- PDF pp.2–3,7, (3): all finite positive ancillary dimensions, all mixed states.
The indices l,r encode dimensions l+1,r+1, including one and with no cutoff.
Each subtracted state quantity is finite on the normalized finite-dimensional
inputs and their CPTP outputs; no infinity-minus-infinity case is used. -/
def amortizedMaxRains {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) : EReal :=
  sSup {v | ∃ l r : ℕ,
    ∃ rho : Mat ((Fin (l+1) × A) × Fin (r+1)), IsDensityMatrix rho ∧
      v = stateMaxRains (channelUse N rho) - stateMaxRains rho}

/-- PDF pp.2,13, (2),(69): channel Emax from the accepted state Emax.
All pure S A inputs are optimized, with S isomorphic to A. -/
def channelEMax {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) : EReal :=
  sSup {v | ∃ psi : EuclideanSpace ℂ (A × A), ‖psi‖ = 1 ∧
    v = eMax (idTensorSuperop N (pureDensity psi))}

/-- PDF pp.2–3,12–13, (3),(68): amortized Emax with unrestricted finite memories.
Only normalized states occur; all state Emax values in the difference are finite. -/
def amortizedEMax {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (N : Superop A B) : EReal :=
  sSup {v | ∃ l r : ℕ,
    ∃ rho : Mat ((Fin (l+1) × A) × Fin (r+1)), IsDensityMatrix rho ∧
      v = eMax (channelUse N rho) - eMax rho}

/-- PDF p.13, (71): feasible trace values on the full separable positive cone.
Trace normalization of X is deliberately absent. -/
def stateConeObjectives {I J : Type} [Fintype I] [Fintype J]
    (rho : Mat (I × J)) : Set ℝ :=
  {t | ∃ X : Mat (I × J), IsSeparablePositive X ∧ Le rho X ∧ t = tr X}

/-- PDF p.13, (71): separable-cone state value.
On density matrices the feasible set is nonempty and bounded below by one.
Lemma 6 below asserts that this infimum is an attained minimum. -/
def wSep {I J : Type} [Fintype I] [Fintype J] (rho : Mat (I × J)) : ℝ :=
  sInf (stateConeObjectives rho)

/-- PDF p.13, (76): spectral operator-norm objectives over the separable cone.
The accepted choi is UNNORMALIZED: its identity-channel trace is dim A.
The accepted specNorm is the Euclidean operator norm, not an entrywise norm. -/
def channelConeObjectives {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] (N : Superop A B) : Set ℝ :=
  {t | ∃ Y : Mat (A × B), IsSeparablePositive Y ∧ Le (choi N) Y ∧
    t = specNorm (traceRight Y)}

/-- PDF p.13, (76): separable-cone channel value.
For CPTP N on positive finite registers the objective set is nonempty and
bounded below by one. Lemma 7 asserts attainment as well as the identity. -/
def sigmaSep {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Superop A B) : ℝ := sInf (channelConeObjectives N)

/-- PDF p.10, (44)–(46): the state after n actual uses of this same fixed N.
The first constructor prepares from the trivial bipartite system through a
PPT-preserving channel; step adds one interleaving PPT channel and one N use.
Memory dimensions l+1 and r+1 are arbitrary positive finite integers.
There is no zero-use constructor and no entanglement-budget assumption. -/
inductive PPTExecution {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) :
    ℕ → (l r : ℕ) → Mat (Fin (l+1) × (B × Fin (r+1))) → Prop where
  | first (l r : ℕ)
      (prepare : Superop (Fin 1 × Fin 1) ((Fin (l+1) × A) × Fin (r+1)))
      (free : IsPPTChannel prepare) :
      PPTExecution N 1 l r (channelUse N (prepare 1))
  | step {n l r : ℕ} {sigma : Mat (Fin (l+1) × (B × Fin (r+1)))}
      (previous : PPTExecution N n l r sigma) (nextL nextR : ℕ)
      (between : Superop (Fin (l+1) × (B × Fin (r+1)))
        ((Fin (nextL+1) × A) × Fin (nextR+1)))
      (free : IsPPTChannel between) :
      PPTExecution N (n+1) nextL nextR (channelUse N (between sigma))

/-- PDF p.10, (47): output of a concrete adaptive PPT-P-assisted protocol.
The decoder is a final PPT channel. The input to the first channel use is
constructed by PPTExecution.first, rather than supplied as a free state. -/
def IsProtocolOutput {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (n M : ℕ)
    (omega : Mat (Fin M × Fin M)) : Prop :=
  0 < n ∧ 0 < M ∧ ∃ l r : ℕ,
    ∃ sigma : Mat (Fin (l+1) × (B × Fin (r+1))), PPTExecution N n l r sigma ∧
      ∃ decoder : Superop (Fin (l+1) × (B × Fin (r+1))) (Fin M × Fin M),
        IsPPTChannel decoder ∧ omega = decoder sigma

/-- PDF p.10, (48)–(50): an (n,M,epsilon) protocol, with squared fidelity.
The target is the normalized projector onto M^(-1/2) sum_i |i i>.
The actual overlap need only be at least 1-epsilon, not equal to it. -/
def IsPPTProtocol {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (n M : ℕ) (epsilon : ℝ) : Prop :=
  0 ≤ epsilon ∧ epsilon ≤ 1 ∧ ∃ omega : Mat (Fin M × Fin M),
    IsProtocolOutput N n M omega ∧ 1 - epsilon ≤ effectProb (target M) omega

/-- PDF pp.10–12: qubits per channel use. Only n,M>0 occur in protocols. -/
def communicationRate (n M : ℕ) : ℝ := Real.logb 2 (M : ℝ) / (n : ℝ)

/-- PDF pp.10–11: for every fixed error epsilon<1 and positive rate slack,
all sufficiently large positive block lengths admit no such protocol.
Integer M with log2 M >= n(R+delta) implements the source's 2^(n(R+delta))
shorthand; the arbitrary positive slack absorbs integer rounding. -/
def IsStrongConverseRate {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) (R : ℝ) : Prop :=
  ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon < 1 →
    ∀ delta : ℝ, 0 < delta → ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      ∀ M : ℕ, 0 < M → (n : ℝ) * (R + delta) ≤ Real.logb 2 (M : ℝ) →
        ¬ IsPPTProtocol N n M epsilon

/-- PDF p.11: infimum of strong-converse rates, retaining the dagger.
An extended infimum avoids a default real value for an empty/unbounded set. -/
def strongConversePPTCapacity {A B : Type} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (N : Superop A B) : EReal :=
  sInf {v | ∃ R : ℝ, IsStrongConverseRate N R ∧ v = (R : EReal)}

/-! Sanity checks for register wiring, counting, normalization and objectives. -/

example {A L R : Type} (rho : Mat ((L × A) × R)) :
    channelUse (fun X : Mat A => X) rho =
      (fun p q : L × (A × R) =>
        rho ((p.1,p.2.1),p.2.2) ((q.1,q.2.1),q.2.2)) := rfl

example {A B L R : Type} (N : Superop A B) (rho : Mat ((L × A) × R))
    (l ll : L) (b bb : B) (r rr : R) :
    channelUse N rho (l,(b,r)) (ll,(bb,rr)) =
      N (fun a aa => rho ((l,a),r) ((ll,aa),rr)) b bb := rfl

example : target 1 (0,0) (0,0) = 1 := by simp [target]

example : target 2 (0,0) (1,1) = (1/2 : ℂ) := by norm_num [target]

example : choi (fun X : Mat (Fin 2) => X) (0,0) (1,1) = 1 := by
  simp [choi]

example {I J : Type} [Fintype I] [Fintype J] (rho X : Mat (I × J))
    (hX : IsSeparablePositive X) (hdom : Le rho X) :
    tr X ∈ stateConeObjectives rho := ⟨X, hX, hdom, rfl⟩

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    (N : Superop A B) (Y : Mat (A × B)) (hY : IsSeparablePositive Y)
    (hdom : Le (choi N) Y) : specNorm (traceRight Y) ∈ channelConeObjectives N :=
  ⟨Y, hY, hdom, rfl⟩

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (N : Superop A B) (l r : ℕ) (sigma : Mat (Fin (l+1) × (B × Fin (r+1)))) :
    ¬ PPTExecution N 0 l r sigma := by
  intro h
  cases h

example : communicationRate 1 1 = 0 := by simp [communicationRate, Real.logb]

section Statements

variable {A B C D L R : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
variable [DecidableEq L] [DecidableEq R]
variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22



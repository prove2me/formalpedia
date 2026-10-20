-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P07
-- name    : QAlgorithms_Papers_Independent_Dependency50_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T13:20:38.124878+00:00
-- url     : https://prove2.me/theorems/da45aa4a-711b-4232-8faa-9c7d2104d2d7
-- title:
--   Definitions for Distilling common randomness from bipartite quantum states
-- statement:
--   The objects the formalized statements of *Distilling common randomness from bipartite quantum states* (arXiv:quant-ph/0304196) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CQData`: PDF pp.2,5: a finite classical-quantum ensemble; validity is a separate predicate.
--   - `CQData.Valid`: PDF pp.2,5: normalized probabilities and density operators, including at zero-weight labels.
--   - `ensembleMean`: PDF p.6: adapt the accepted matrix average to this paper's ensemble record.
--   - `ensembleInformation`: PDF p.6: adapt accepted bit-valued labelInformation to this paper's ensemble record.
--   - `classicalGivenQuantum`: PDF p.5: H(X|Q) in the enlarged Hilbert-space representation.
--   - `Auxiliary`: PDF p.6, (5): a stochastic channel X to a finite nonempty auxiliary alphabet.
--   - `constantAux`: PDF p.6: the constant auxiliary, feasible even at rate zero.
--   - `auxJoint`: PDF p.6, (5): joint law of U and X.
--   - `auxProb`: PDF p.6: marginal law of U.
--   - `auxState`: PDF p.6: conditional density of Q given U; zero on null events, used only with weight zero.
--   - `auxIX`: PDF pp.5--6: I(U;X).
--   - `quantumGivenAux`: PDF pp.5--6: H(Q|U), a probability ensembleMean of normalized conditional-state entropies.
--   - `auxIQ`: PDF p.6: I(U;Q), for U to X to Q.
--   - `auxCost`: PDF p.6: required communication I(U;X)-I(U;Q).
--   - `classicalGivenAux`: PDF p.10: H(X|U).
--   - `dStar`: PDF p.6, (7): optimize over every finite stochastic auxiliary, without a cardinality cap. For valid nonempty ensembles and R >= 0 the value set is nonempty and bounded by H(Q).
--   - `cStar`: PDF p.6, (6): the proposed single-letter CR curve.
--   - `productCQ`: PDF p.7: independent product ensembles.
--   - `wordProb`: PDF pp.4,7: iid classical word probabilities, including the empty product at n=0.
--   - `wordState`: PDF p.7: the conditional iid quantum state rho_(x^n).
--   - `iidCQ`: PDF p.7: the n-fold iid ensemble.
--   - `dStarBlock`: PDF p.7, (8): both objective and rate constraint are normalized per original copy.
--   - `cqDensity`: PDF p.2, (1): diagonal embedding of the classical register.
--   - `qcDensity`: PDF p.15, Example 8: the quantum-classical placement, with communication still Alice to Bob.
--   - `bipartitePower`: PDF pp.4,14: iid bipartite state regrouped across A^n:B^n.
--   - `bipartiteProduct`: PDF p.16: product state with the canonical AA':BB' regrouping.
--   - `Protocol`: PDF p.4: Alice's full record, a deterministic message, and Alice's key; Bob's message-controlled POVM is already coarsened to his key. Private coins and local operations are absorbed into the POVMs, and the Born law has no initial shared-randomness variable.
--   - `Protocol.charge`: PDF p.4: actual one-way message charge is the logarithm of the image of f.
--   - `Protocol.joint`: PDF p.4: joint distribution of the full Alice record and Bob's decoded key.
--   - `Protocol.error`: PDF p.4, (2): the error is the probability of unequal keys.
--   - `Protocol.keyProb`: PDF p.4: Alice's key marginal, without a uniformity requirement.
--   - `AchievableWith`: PDF pp.4--5: one exponential key-alphabet constant, then every accuracy and all sufficiently large positive blocklengths. A restriction specifies which initial measurements are permitted.
--   - `CRAchievable`: PDF pp.4--5: unrestricted one-way achievability, with free private randomness.
--   - `crCapacity`: PDF p.5: operational capacity, not defined by the variational answer. For density matrices on finite nonzero systems and R >= 0 its achievable set is nonempty and bounded.
--   - `crExcess`: PDF p.5, (4): CR in excess of communication.
--   - `total`: PDF pp.5,9: total distillable CR is a supremum over finite nonnegative rates.
--   - `measurementBranch`: PDF p.14: unnormalized postmeasurement Bob state. Partial-trace cyclicity makes this identical to the square-root sandwich in the source, avoiding an arbitrary instrument choice.
--   - `measuredCQ`: PDF p.14: the ensemble left by Alice's POVM. Null branches are zero and enter only with zero probability; the normalized conditional state is used on positive-probability branches.
--   - `fixedCapacity`: PDF pp.14--15: repeat one fixed POVM, then use an arbitrary cq protocol. Optimizing is operational; this definition does not insert the mutual-information expression (23).
--   - `fixedExcess`: PDF p.18: fixed-POVM excess curve, which need not be concave.
--   - `fixedTotal`: PDF p.15, (24): total fixed-POVM operational excess.
--   - `blockCapacity`: PDF p.15: use identical L-copy measurements and divide all block rates by L.
--   - `blockExcess`: PDF p.15: normalized L-copy excess curve.
--   - `blockTotal`: PDF p.15: normalized L-copy total excess.
--   - `measurementValues`: PDF p.15, (23): values of the nested measurement/auxiliary variational problem.
--   - `classicalCorrelation`: PDF p.15, (24): Henderson--Vedral C_A, with the same POVM optimization as [21].
--   - `accessibleInformation`: PDF p.16, Example 8: accessible information, optimized over measurements on the ensemble states. It is the classical mutual information of label X and measurement outcome.
--   - `qStar`: PDF p.12, background [19]: the visible pure-state compression variational curve. The nonempty equality-constrained domain is 0 <= R <= H(X); rates above H(X) cost zero qubits.
--   - `Typical`: PDF p.19: absolute-frequency typicality, including the source's <= convention.
--   - `ConditionalTypical`: PDF pp.19--20: conditional typicality with tolerance n delta, not N(u) delta.
--   - `eventMass`: PDF p.10: probability of a word event.
--   - `eventState`: PDF p.10: the event-conditioned quantum state; only positive-mass events are used unweighted.
--   - `GoodSubset`: PDF p.10, (14): all classical conclusions for the same F,u, and positive mass.
--   - `coarseProb`: PDF pp.10--11: distribution of deterministic coarse-graining g(X^n).
--   - `quantumGivenCoarse`: PDF p.10, (18): H(Q^n|g(X^n)), a weighted sum; zero-mass fibers contribute zero.
--   - `classicalGivenCoarse`: PDF p.10, (19): H(X^n|g(X^n)) for deterministic g.
--   - `threeStateVector`: PDF p.12: the three explicitly listed vectors, correcting the repeated phi_1 label.
--   - `threeStateEnsemble`: PDF p.12: equiprobable three-state ensemble E_3.
--   - `concaveHull`: PDF p.18: finite deterministic time sharing, with nonnegative component rates. The value set is nonempty and bounded for the finite-dimensional excess curves used below.
--   - `ProductInitial`: PDF p.18: the initial POVM is a tensor product of possibly different one-copy POVMs. Arbitrary stochastic classical postprocessing of the complete product record includes private coins, deterministic time sharing, and the subsequent classical encoder.
--   - `productCapacity`: PDF p.18: operational capacity with an initial tensor-product measurement.
--   - `trivialProtocol`: PDF p.4: the protocol with constant records and no communication, on any blocklength.
-- source:
--   Distilling common randomness from bipartite quantum states, arXiv:quant-ph/0304196v2, https://arxiv.org/abs/quant-ph/0304196v2

import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P04

/-!
Statements from Devetak--Winter, arXiv:quant-ph/0304196v2.
All new objects are local to this paper. Entropies and communication are in bits.
Operational protocols use disagreement probability and Shannon entropy, not fidelity.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Filter
open QAlgorithms.Papers.Independent.Information100.P27 (shannon)
open QAlgorithms.Papers.Independent.Information100.P04 (Measurement)

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Dependency50.P07

/-- PDF pp.2,5: a finite classical-quantum ensemble; validity is a separate predicate. -/
structure CQData (X Q : Type) where
  prob : X → ℝ
  state : X → Matrix Q Q ℂ

/-- PDF pp.2,5: normalized probabilities and density operators, including at zero-weight labels. -/
def CQData.Valid {X Q : Type} [Fintype X] [Fintype Q] (E : CQData X Q) : Prop :=
  (∀ x, 0 ≤ E.prob x) ∧ (∑ x, E.prob x) = 1 ∧
    ∀ x, IsDensityMatrix (E.state x)

/-- PDF p.6: adapt the accepted matrix average to this paper's ensemble record. -/
def ensembleMean {X Q : Type} [Fintype X] (E : CQData X Q) : Matrix Q Q ℂ :=
  QAlgorithms.Papers.Independent.Information100.P27.average E.prob E.state

/-- PDF p.6: adapt accepted bit-valued labelInformation to this paper's ensemble record. -/
def ensembleInformation {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P27.labelInformation E.prob E.state

/-- PDF p.5: H(X|Q) in the enlarged Hilbert-space representation. -/
def classicalGivenQuantum {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) : ℝ := shannon E.prob - ensembleInformation E

/-- PDF p.6, (5): a stochastic channel X to a finite nonempty auxiliary alphabet. -/
structure Auxiliary (X : Type) where
  size : ℕ
  positive : 0 < size
  channel : X → Fin size → ℝ
  nonnegative : ∀ x u, 0 ≤ channel x u
  normalized : ∀ x, (∑ u, channel x u) = 1

/-- PDF p.6: the constant auxiliary, feasible even at rate zero. -/
def constantAux (X : Type) : Auxiliary X where
  size := 1
  positive := by decide
  channel := fun _ _ => 1
  nonnegative := by intros; norm_num
  normalized := by intro x; simp

/-- PDF p.6, (5): joint law of U and X. -/
def auxJoint {X Q : Type} (E : CQData X Q) (V : Auxiliary X) : Fin V.size × X → ℝ :=
  fun z => E.prob z.2 * V.channel z.2 z.1

/-- PDF p.6: marginal law of U. -/
def auxProb {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X)
    (u : Fin V.size) : ℝ := ∑ x, auxJoint E V (u, x)

/-- PDF p.6: conditional density of Q given U; zero on null events, used only with weight zero. -/
def auxState {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X)
    (u : Fin V.size) : Matrix Q Q ℂ :=
  ((auxProb E V u)⁻¹ : ℂ) • ∑ x, (auxJoint E V (u, x) : ℂ) • E.state x

/-- PDF pp.5--6: I(U;X). -/
def auxIX {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X) : ℝ :=
  shannon E.prob + shannon (auxProb E V) - shannon (auxJoint E V)

/-- PDF pp.5--6: H(Q|U), a probability ensembleMean of normalized conditional-state entropies. -/
def quantumGivenAux {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (V : Auxiliary X) : ℝ :=
  ∑ u, auxProb E V u * vnEntropy (auxState E V u)

/-- PDF p.6: I(U;Q), for U to X to Q. -/
def auxIQ {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (V : Auxiliary X) : ℝ :=
  vnEntropy (ensembleMean E) - quantumGivenAux E V

/-- PDF p.6: required communication I(U;X)-I(U;Q). -/
def auxCost {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (V : Auxiliary X) : ℝ := auxIX E V - auxIQ E V

/-- PDF p.10: H(X|U). -/
def classicalGivenAux {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X) : ℝ :=
  shannon (auxJoint E V) - shannon (auxProb E V)

/-- PDF p.6, (7): optimize over every finite stochastic auxiliary, without a cardinality cap.
For valid nonempty ensembles and R >= 0 the value set is nonempty and bounded by H(Q). -/
def dStar {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (R : ℝ) : ℝ :=
  sSup {v | ∃ V : Auxiliary X, auxCost E V ≤ R ∧ v = auxIQ E V}

/-- PDF p.6, (6): the proposed single-letter CR curve. -/
def cStar {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (R : ℝ) : ℝ := R + dStar E R

/-- PDF p.7: independent product ensembles. -/
def productCQ {X Q Y T : Type} (E : CQData X Q) (F : CQData Y T) : CQData (X × Y) (Q × T) where
  prob := fun z => E.prob z.1 * F.prob z.2
  state := fun z => Matrix.kronecker (E.state z.1) (F.state z.2)

/-- PDF pp.4,7: iid classical word probabilities, including the empty product at n=0. -/
def wordProb {X : Type} (p : X → ℝ) (n : ℕ) (w : Fin n → X) : ℝ := ∏ i, p (w i)

/-- PDF p.7: the conditional iid quantum state rho_(x^n). -/
def wordState {X Q : Type} (E : CQData X Q) (n : ℕ) (w : Fin n → X) :
    Matrix (Fin n → Q) (Fin n → Q) ℂ := fun a b => ∏ i, E.state (w i) (a i) (b i)

/-- PDF p.7: the n-fold iid ensemble. -/
def iidCQ {X Q : Type} (E : CQData X Q) (n : ℕ) : CQData (Fin n → X) (Fin n → Q) where
  prob := wordProb E.prob n
  state := wordState E n

/-- PDF p.7, (8): both objective and rate constraint are normalized per original copy. -/
def dStarBlock {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (n : ℕ) (R : ℝ) : ℝ := dStar (iidCQ E n) (n * R) / n

/-- PDF p.2, (1): diagonal embedding of the classical register. -/
def cqDensity {X Q : Type} (E : CQData X Q) : Matrix (X × Q) (X × Q) ℂ :=
  fun a b => if a.1 = b.1 then (E.prob a.1 : ℂ) * E.state a.1 a.2 b.2 else 0

/-- PDF p.15, Example 8: the quantum-classical placement, with communication still Alice to Bob. -/
def qcDensity {X Q : Type} (E : CQData X Q) : Matrix (Q × X) (Q × X) ℂ :=
  fun a b => if a.2 = b.2 then (E.prob a.2 : ℂ) * E.state a.2 a.1 b.1 else 0

/-- PDF pp.4,14: iid bipartite state regrouped across A^n:B^n. -/
def bipartitePower {A B : Type} (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun a b => ∏ i, rho (a.1 i, a.2 i) (b.1 i, b.2 i)

/-- PDF p.16: product state with the canonical AA':BB' regrouping. -/
def bipartiteProduct {A B A2 B2 : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (A2 × B2) (A2 × B2) ℂ) :
    Matrix ((A × A2) × (B × B2)) ((A × A2) × (B × B2)) ℂ :=
  fun a b => rho (a.1.1, a.2.1) (b.1.1, b.2.1) * sigma (a.1.2, a.2.2) (b.1.2, b.2.2)

/-- PDF p.4: Alice's full record, a deterministic message, and Alice's key; Bob's
message-controlled POVM is already coarsened to his key. Private coins and local operations
are absorbed into the POVMs, and the Born law has no initial shared-randomness variable. -/
structure Protocol (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] (n : ℕ) where
  alice : Measurement (Fin n → A)
  messages : ℕ
  messagePositive : 0 < messages
  keys : ℕ
  keyPositive : 0 < keys
  send : Fin alice.outcomes → Fin messages
  key : Fin alice.outcomes → Fin keys
  bob : Fin messages → Fin keys → Matrix (Fin n → B) (Fin n → B) ℂ
  bobValid : ∀ m, IsPOVM (bob m)

/-- PDF p.4: actual one-way message charge is the logarithm of the image of f. -/
def Protocol.charge {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : Protocol A B n) : ℝ :=
  Real.logb 2 ((Finset.univ.image P.send).card : ℝ)

/-- PDF p.4: joint distribution of the full Alice record and Bob's decoded key. -/
def Protocol.joint {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : Protocol A B n) (rho : Matrix (A × B) (A × B) ℂ)
    (x : Fin P.alice.outcomes) (l : Fin P.keys) : ℝ :=
  effectProb (Matrix.kronecker (P.alice.effect x) (P.bob (P.send x) l)) (bipartitePower rho n)

/-- PDF p.4, (2): the error is the probability of unequal keys. -/
def Protocol.error {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : Protocol A B n) (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  ∑ x, ∑ l, if P.key x ≠ l then P.joint rho x l else 0

/-- PDF p.4: Alice's key marginal, without a uniformity requirement. -/
def Protocol.keyProb {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {n : ℕ} (P : Protocol A B n) (rho : Matrix (A × B) (A × B) ℂ) (k : Fin P.keys) : ℝ :=
  ∑ x, if P.key x = k then ∑ l, P.joint rho x l else 0

/-- PDF pp.4--5: one exponential key-alphabet constant, then every accuracy and all sufficiently
large positive blocklengths. A restriction specifies which initial measurements are permitted. -/
def AchievableWith {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (restriction : (n : ℕ) → Protocol A B n → Prop)
    (rho : Matrix (A × B) (A × B) ℂ) (C R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ c : ℝ, 0 ≤ c ∧ ∀ epsilon delta : ℝ, 0 < epsilon → 0 < delta →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n → ∃ P : Protocol A B n,
      restriction n P ∧ P.charge ≤ n * R ∧
      (P.keys : ℝ) ≤ (2 : ℝ) ^ (c * n) ∧ P.error rho ≤ epsilon ∧
      C - delta ≤ shannon (P.keyProb rho) / n

/-- PDF pp.4--5: unrestricted one-way achievability, with free private randomness. -/
def CRAchievable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (C R : ℝ) : Prop :=
  AchievableWith (fun _ _ => True) rho C R

/-- PDF p.5: operational capacity, not defined by the variational answer. For density matrices
on finite nonzero systems and R >= 0 its achievable set is nonempty and bounded. -/
def crCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : ℝ :=
  sSup {C | CRAchievable rho C R}

/-- PDF p.5, (4): CR in excess of communication. -/
def crExcess {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : ℝ := crCapacity rho R - R

/-- PDF pp.5,9: total distillable CR is a supremum over finite nonnegative rates. -/
def total {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ R : ℝ, 0 ≤ R ∧ v = crExcess rho R}

/-- PDF p.14: unnormalized postmeasurement Bob state. Partial-trace cyclicity makes this
identical to the square-root sandwich in the source, avoiding an arbitrary instrument choice. -/
def measurementBranch {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (M : Measurement A) (x : Fin M.outcomes) : Matrix B B ℂ :=
  traceLeft (Matrix.kronecker (M.effect x) (1 : Matrix B B ℂ) * rho)

/-- PDF p.14: the ensemble left by Alice's POVM. Null branches are zero and enter only with
zero probability; the normalized conditional state is used on positive-probability branches. -/
def measuredCQ {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (M : Measurement A) : CQData (Fin M.outcomes) B where
  prob := fun x => (measurementBranch rho M x).trace.re
  state := fun x => (((measurementBranch rho M x).trace.re)⁻¹ : ℂ) • measurementBranch rho M x

/-- PDF pp.14--15: repeat one fixed POVM, then use an arbitrary cq protocol. Optimizing is
operational; this definition does not insert the mutual-information expression (23). -/
def fixedCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : ℝ :=
  sSup {C | ∃ M : Measurement A, CRAchievable (cqDensity (measuredCQ rho M)) C R}

/-- PDF p.18: fixed-POVM excess curve, which need not be concave. -/
def fixedExcess {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : ℝ := fixedCapacity rho R - R

/-- PDF p.15, (24): total fixed-POVM operational excess. -/
def fixedTotal {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ R : ℝ, 0 ≤ R ∧ v = fixedExcess rho R}

/-- PDF p.15: use identical L-copy measurements and divide all block rates by L. -/
def blockCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (L : ℕ) (R : ℝ) : ℝ :=
  fixedCapacity (bipartitePower rho L) (L * R) / L

/-- PDF p.15: normalized L-copy excess curve. -/
def blockExcess {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (L : ℕ) (R : ℝ) : ℝ := blockCapacity rho L R - R

/-- PDF p.15: normalized L-copy total excess. -/
def blockTotal {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (L : ℕ) : ℝ := fixedTotal (bipartitePower rho L) / L

/-- PDF p.15, (23): values of the nested measurement/auxiliary variational problem. -/
def measurementValues {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : Set ℝ :=
  {v | ∃ M : Measurement A, ∃ V : Auxiliary (Fin M.outcomes),
    auxCost (measuredCQ rho M) V ≤ R ∧ v = auxIQ (measuredCQ rho M) V}

/-- PDF p.15, (24): Henderson--Vedral C_A, with the same POVM optimization as [21]. -/
def classicalCorrelation {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v | ∃ M : Measurement A, v = ensembleInformation (measuredCQ rho M)}

/-- PDF p.16, Example 8: accessible information, optimized over measurements on the ensemble
states. It is the classical mutual information of label X and measurement outcome. -/
def accessibleInformation {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) : ℝ :=
  sSup {v | ∃ M : Measurement Q,
    let joint : X × Fin M.outcomes → ℝ := fun z => E.prob z.1 * effectProb (M.effect z.2) (E.state z.1)
    v = shannon E.prob + shannon (fun y => ∑ x, joint (x,y)) - shannon joint}

/-- PDF p.12, background [19]: the visible pure-state compression variational curve. The
nonempty equality-constrained domain is 0 <= R <= H(X); rates above H(X) cost zero qubits. -/
def qStar {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (R : ℝ) : ℝ :=
  if shannon E.prob < R then 0 else
    sInf {v | ∃ V : Auxiliary X, auxIX E V = R ∧ v = quantumGivenAux E V}

/-- PDF p.19: absolute-frequency typicality, including the source's <= convention. -/
def Typical {X : Type} [Fintype X] (p : X → ℝ) (n : ℕ) (delta : ℝ) (w : Fin n → X) : Prop :=
  ∀ x, |((Finset.univ.filter (fun i => w i = x)).card : ℝ) - n * p x| ≤ n * delta

/-- PDF pp.19--20: conditional typicality with tolerance n delta, not N(u) delta. -/
def ConditionalTypical {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X)
    (n : ℕ) (delta : ℝ) (u : Fin n → Fin V.size) (w : Fin n → X) : Prop :=
  ∀ v x, |((Finset.univ.filter (fun i => u i = v ∧ w i = x)).card : ℝ) -
    (auxJoint E V (v,x) / auxProb E V v) * (Finset.univ.filter (fun i => u i = v)).card| ≤ n * delta

/-- PDF p.10: probability of a word event. -/
def eventMass {X Q : Type} [Fintype X] (E : CQData X Q) (n : ℕ) (F : Finset (Fin n → X)) : ℝ :=
  ∑ w ∈ F, wordProb E.prob n w

/-- PDF p.10: the event-conditioned quantum state; only positive-mass events are used unweighted. -/
def eventState {X Q : Type} [Fintype X] (E : CQData X Q) (n : ℕ)
    (F : Finset (Fin n → X)) : Matrix (Fin n → Q) (Fin n → Q) ℂ :=
  ((eventMass E n F)⁻¹ : ℂ) • ∑ w ∈ F, (wordProb E.prob n w : ℂ) • wordState E n w

/-- PDF p.10, (14): all classical conclusions for the same F,u, and positive mass. -/
def GoodSubset {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X)
    (n : ℕ) (delta : ℝ) (Eset F : Finset (Fin n → X)) (u : Fin n → Fin V.size) : Prop :=
  F ⊆ Eset ∧ 0 < eventMass E n F ∧ Typical (auxProb E V) n delta u ∧
    (∀ w ∈ F, ConditionalTypical E V n delta u w) ∧
    |Real.logb 2 (F.card : ℝ) / n - classicalGivenAux E V| ≤ delta

/-- PDF pp.10--11: distribution of deterministic coarse-graining g(X^n). -/
def coarseProb {X Q Y : Type} [Fintype X] (E : CQData X Q) (n : ℕ)
    (g : (Fin n → X) → Y) (y : Y) : ℝ :=
  eventMass E n (Finset.univ.filter (fun w => g w = y))

/-- PDF p.10, (18): H(Q^n|g(X^n)), a weighted sum; zero-mass fibers contribute zero. -/
def quantumGivenCoarse {X Q Y : Type} [Fintype X] [Fintype Q] [DecidableEq Q] [Fintype Y]
    (E : CQData X Q) (n : ℕ) (g : (Fin n → X) → Y) : ℝ :=
  ∑ y, coarseProb E n g y * vnEntropy (eventState E n (Finset.univ.filter (fun w => g w = y)))

/-- PDF p.10, (19): H(X^n|g(X^n)) for deterministic g. -/
def classicalGivenCoarse {X Q Y : Type} [Fintype X] [Fintype Y]
    (E : CQData X Q) (n : ℕ) (g : (Fin n → X) → Y) : ℝ :=
  shannon (wordProb E.prob n) - shannon (coarseProb E n g)

/-- PDF p.12: the three explicitly listed vectors, correcting the repeated phi_1 label. -/
def threeStateVector (x : Fin 3) : EuclideanSpace ℂ (Fin 3) :=
  if x = 0 then ket 0 else if x = 1 then
    ((Real.sqrt 2)⁻¹ : ℂ) • (ket 0 + ket 1) else ket 2

/-- PDF p.12: equiprobable three-state ensemble E_3. -/
def threeStateEnsemble : CQData (Fin 3) (Fin 3) where
  prob := fun _ => 1 / 3
  state := fun x => pureDensity (threeStateVector x)

/-- PDF p.18: finite deterministic time sharing, with nonnegative component rates. The value
set is nonempty and bounded for the finite-dimensional excess curves used below. -/
def concaveHull (f : ℝ → ℝ) (R : ℝ) : ℝ :=
  sSup {v | ∃ k : ℕ, ∃ weights rates : Fin k → ℝ,
    (∀ i, 0 ≤ weights i ∧ 0 ≤ rates i) ∧ (∑ i, weights i) = 1 ∧
    (∑ i, weights i * rates i) = R ∧ v = ∑ i, weights i * f (rates i)}

/-- PDF p.18: the initial POVM is a tensor product of possibly different one-copy POVMs.
Arbitrary stochastic classical postprocessing of the complete product record includes private
coins, deterministic time sharing, and the subsequent classical encoder. -/
def ProductInitial {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) (P : Protocol A B n) : Prop :=
  ∃ M : Fin n → Measurement A,
  ∃ kernel : ((i : Fin n) → Fin (M i).outcomes) → Fin P.alice.outcomes → ℝ,
    (∀ w x, 0 ≤ kernel w x) ∧ (∀ w, (∑ x, kernel w x) = 1) ∧
    ∀ x a b, P.alice.effect x a b =
      ∑ w : ((i : Fin n) → Fin (M i).outcomes),
        (kernel w x : ℂ) * ∏ i, (M i).effect (w i) (a i) (b i)

/-- PDF p.18: operational capacity with an initial tensor-product measurement. -/
def productCapacity {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (R : ℝ) : ℝ :=
  sSup {C | AchievableWith ProductInitial rho C R}

/-- PDF p.4: the protocol with constant records and no communication, on any blocklength. -/
def trivialProtocol (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (n : ℕ) : Protocol A B n where
  alice := {
    outcomes := 1
    positive := by decide
    effect := fun _ => 1
    valid := ⟨fun _ => Matrix.PosSemidef.one, by simp⟩ }
  messages := 1
  messagePositive := by decide
  keys := 1
  keyPositive := by decide
  send := fun _ => 0
  key := fun _ => 0
  bob := fun _ _ => 1
  bobValid := by intro m; exact ⟨fun _ => Matrix.PosSemidef.one, by simp⟩

/-! Sanity examples for new definitions. These check conventions, not the paper's theorems. -/

example : shannon (fun _ : Fin 1 => (1 : ℝ)) = 0 := by simp [shannon]

example {X : Type} (p : X → ℝ) (w : Fin 0 → X) : wordProb p 0 w = 1 := by
  simp [wordProb]

example {X Q : Type} (E : CQData X Q) (w : Fin 0 → X) (a b : Fin 0 → Q) :
    wordState E 0 w a b = 1 := by simp [wordState]

example {X Q : Type} [Fintype X] (E : CQData X Q) : eventMass E 1 ∅ = 0 := by
  simp [eventMass]

example {X : Type} (x : X) : (constantAux X).channel x ⟨0, (constantAux X).positive⟩ = 1 := rfl

example : threeStateVector 0 = ket (0 : Fin 3) := by simp [threeStateVector]

example {A B : Type} (rho : Matrix (A × B) (A × B) ℂ)
    (a b : (Fin 0 → A) × (Fin 0 → B)) : bipartitePower rho 0 a b = 1 := by
  simp [bipartitePower]

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    (trivialProtocol A B n).error rho = 0 := by
  unfold Protocol.error
  change (∑ x : Fin 1, ∑ l : Fin 1,
    if (0 : Fin 1) ≠ l then (trivialProtocol A B n).joint rho x l else 0) = 0
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro l hl
  have hkey : (0 : Fin 1) = l := Subsingleton.elim _ _
  simp only [hkey, ne_eq, not_true_eq_false, ite_false]

example {X Q : Type} [Fintype X] (E : CQData X Q) : ensembleMean E =
    ∑ x, (E.prob x : ℂ) • E.state x := rfl

example {X Q : Type} [Fintype X] [Fintype Q]
    (E : CQData X Q) : ensembleInformation E =
      vnEntropy (ensembleMean E) - ∑ x, E.prob x * vnEntropy (E.state x) := rfl

example {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (R : ℝ) : cStar E R = R + dStar E R := rfl

example {X Q : Type} [Fintype X] [Fintype Q] [DecidableEq Q]
    (E : CQData X Q) (V : Auxiliary X) :
    auxCost E V = auxIX E V - auxIQ E V := rfl

example {X Q : Type} [Fintype X] (E : CQData X Q) (V : Auxiliary X) (u : Fin V.size)
    (h : auxProb E V u = 0) : auxState E V u = 0 := by simp [auxState, h]

example {X Q : Type} [Fintype X] (E : CQData X Q) (n : ℕ) :
    eventState E n ∅ = 0 := by simp [eventState, eventMass]

example {X Q : Type} (E : CQData X Q) (x : X) (a b : Q) :
    cqDensity E (x,a) (x,b) = (E.prob x : ℂ) * E.state x a b := by simp [cqDensity]

example {X Q : Type} (E : CQData X Q) (x : X) (a b : Q) :
    qcDensity E (a,x) (b,x) = (E.prob x : ℂ) * E.state x a b := by simp [qcDensity]

/-! Theorem statements. No result of this paper is assumed as a hypothesis. -/

section CQStatements

variable {X Q Y T : Type} [Fintype X] [Fintype Q] [Fintype Y] [Fintype T]
  [DecidableEq X] [DecidableEq Q] [DecidableEq Y] [DecidableEq T]
  [Nonempty X] [Nonempty Q] [Nonempty Y] [Nonempty T]

end CQStatements

section QuantumStatements

variable {A B A2 B2 : Type} [Fintype A] [Fintype B] [Fintype A2] [Fintype B2]
  [DecidableEq A] [DecidableEq B] [DecidableEq A2] [DecidableEq B2]
  [Nonempty A] [Nonempty B] [Nonempty A2] [Nonempty B2]

end QuantumStatements

end QAlgorithms.Papers.Independent.Dependency50.P07



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P25
-- name    : QAlgorithms_Papers_Independent_Bridge50_P25
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:00:53.344266+00:00
-- url     : https://prove2.me/theorems/0d5f6956-dcde-4375-8fc6-d1561da17a37
-- title:
--   Definitions for Relative Entropy Bounds on Quantum, Private and Repeater Capacities
-- statement:
--   The objects the formalized statements of *Relative Entropy Bounds on Quantum, Private and Repeater Capacities* (arXiv:1604.03448) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `paperSandwichedRenyi`: PDF pp.3--4, (4): include the Umegaki endpoint at alpha=1 and support failures. This endpoint wrapper reuses frozen relative/divergence; Next46.P23.renyi is a natural-log Petz overlap, a different quantity.
--   - `entanglementRenyi`: PDF p.5, Definition II.1: infimum over all separable density matrices.
--   - `channelEMax`: PDF p.5, (9): arbitrary positive finite reference dimension and mixed input.
--   - `channelFormationSupremum`: PDF p.9: channel formation, using the accepted pure-ensemble INFIMUM. Printed: sup over ensembles. Changed: inf. Why: the named formation measure, the cited argument and EC use the convex roof, not entanglement of assistance. Independent moderation of this source correction remains required. Information100.P08.channelFormation takes a fixed input marginal; here the supremum is over all reference/input densities, as required by p.9.
--   - `maxQuotients`: PDF p.15: positive-copy Emax quotients, with no zero denominator.
--   - `regularizedEMax`: PDF p.15: computed regularization; the corollary explicitly asserts convergence.
--   - `formationQuotients`: PDF p.9, (12): positive-copy formation quotients.
--   - `regularizedFormationCost`: PDF p.9, (12): computed regularization, whose convergence is part of Theorem II.4. Dependency50.P41.channelCost is an operational simulation infimum on Fin registers. This is the computed regularized formation in (12), not that definition.
--   - `LOCCOn`: PDF pp.5--6, (10): transport the accepted finite adaptive LOCC tree to arbitrary finite local bases. Both matrix indices use the same local bijections.
--   - `sendChannelRegister`: PDF pp.6,10--12: send the middle input from Alice to Bob. The input split is (A,I):B, the output split A:(J,B). Frozen functions named transfer describe modular evolution or lattice Fourier matrices; neither sends the middle register across the party cut.
--   - `TwoWayChannelProtocol`: PDF p.6, Definition II.3: exactly m actual channel applications, with arbitrary finite changing workspaces and finite adaptive two-way LOCC between them. A zero-use tail is a local operation. At positive m the first operation is T; preparation of the initial state is separate. Consecutive local operations can compose. Dependency50.P07.Protocol is a measurement/message protocol on shared copies; it has no channel-use recursion and cannot model Definition II.3.
--   - `privateStateInPartyOrder`: PDF p.7, Definition II.6: the twisted maximally entangled key and arbitrary shield density, written in party order (Ak,As):(Bk,Bs). Only the diagonal-key blocks of a controlled twisting act on the maximally entangled key. Only the register ordering and unitary-group coercion adapt the frozen Information100.P67.privateState; its matrix formula is not redeclared.
--   - `entangledKeyTarget`: PDF p.7, Definition II.4: normalized maximally entangled key, with trivial local shield factors when s=0. The only use for quantum targets imposes s=0. Dependency50.P32.entangledTarget is a port-indexed channel Choi target. This target reuses the private-state formula with identity twist and trivial shield (s=0 in every quantum code); there is no copied entangled-target formula.
--   - `TwoWayGenerationCode`: PDF pp.6--8, Definitions II.3--II.7: an actual positive-use code. true selects private generation, false selects entanglement generation. The initial state is separable; the target and output have the same key and (equal) shield dimensions. Errors are computed below, never supplied as free scalars. Frontier30.P06.BlockCode is a feedback classical-message code, without this paper's private/entangled targets and separable preparation.
--   - `generationCodeError`: PDF pp.7--8: the code's actual half trace-norm error. Information100.P67.codeError is a classical privacy criterion; this is Definition II.7's half trace distance to an actual private-state target.
--   - `TwoWayAchievableRate`: PDF pp.7--8, Definitions II.5,II.8: the exact sequence-based achievable rates. Finite initial code lengths cause no division-by-zero default; every code has uses>0. Information100.P04.Achievable is state-distillation achievability under a different operation class; the channel protocol sequences here are essential.
--   - `twoWayGenerationCapacity`: PDF pp.7--8: extended supremum over the nonnegative achievable rates. Frozen functions named capacity describe one-shot messages or specialized channels; this is the unrestricted two-way operational supremum of II.5/II.8.
--   - `PrivateStrongConverseBound`: PDF p.8: includes the upper bound and the full error-to-one strong converse, for every code sequence and every convergent rate above the bound.
--   - `forgetExtra`: PDF p.16: trace out only the extra subsystem, retaining the A:B split.
--   - `reducedChannel`: PDF p.17: the reduced channel is computed from the given channel.
--   - `BreaksEntanglementAllReferences`: PDF p.17: EB means separable output for EVERY reference and input state. Frozen EB predicates are qubit-only, same-input/output-size, or Fin-indexed pure-input tests. This interface keeps arbitrary rectangular bases and references.
--   - `normalizedChannelChoi`: PDF pp.3,17: normalized Choi matrix, reference first. Reuse the frozen normalized maximally entangled ket rather than redeclaring omega. Other frozen Choi conventions include unnormalized and output-first matrices.
--   - `choiEBBound`: PDF p.17: infimum over EB CHANNELS, preserving the Choi input marginal. Theorem V.2 asserts attainment, rather than assuming it.
--   - `StateFunctional`: PDF p.25: dimension-indexed state functional; values on nonstates are unused.
--   - `IsDimensionChangingLOCCMonotone`: PDF pp.25--26: nonnegative, real-valued on states and monotone under all finite LOCC, including local addition/disposal and arbitrary dimension changes. No convexity or vanishing-on-separable-states axiom is imposed. Frontier30.P30.IsLOCCMonotone assumes selective average monotonicity. A.1 only requires deterministic LOCC monotonicity across arbitrary dimensions.
--   - `channelValue`: PDF p.25: associated channel supremum, which may be infinite for arbitrary E.
--   - `attachInput`: PDF p.25, (A1): attach the single-use resource, with the input and its reference at Alice and the resource's output at Bob.
--   - `ImplementsFrom`: PDF p.25, Definition A.1: the SAME sigma supplies the resource through one use of T. The implementation holds on every input density. Alice's final system is one-dimensional; no residual resource or extra channel use is available.
--   - `channelSquashed`: PDF p.8, (11): channel squashed entanglement using the accepted all-finite-extension state infimum, with arbitrary finite mixed reference input.
--   - `transpositionBound`: PDF pp.8,19: the transposition bound, using the accepted full stabilized trace-norm diamond norm on the actual output-transposed linear map.
--   - `flowerMatrix`: PDF p.18, (24): coordinate adapter for the accepted DFT flower state. Each local register is (d-dimensional shield, Boolean key); the two-party state is the trace over the actual purifying d-dimensional register.
--   - `flowerChannel`: PDF p.19: inverse NORMALIZED Choi construction, with input dimension 2d. Its action on every operator, not only diagonal states, is specified.
-- source:
--   Relative Entropy Bounds on Quantum, Private and Repeater Capacities, arXiv:1604.03448v2, https://arxiv.org/abs/1604.03448v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P21
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

/-!
Christandl--Mueller-Hermes, arXiv:1604.03448v2. Finite positive dimensions;
all logarithms are in bits. Only pinned accepted modules are imported.
The frozen matrix type, channel tensor power, normalized entangled ket, and
private-state matrix formula are reused directly. Distinct local interface names
separate this paper's conventions from unrelated accepted same-name declarations.
Paper-local definitions supply the operational conventions of Definitions II.3--II.8
and Appendix A. The formation infimum corrects the printed supremum on PDF p.9.
The three deferred repeater nodes are documented in HARD.md and GAPS.json.
Compilation is pending the separate mechanical handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P25

open QAlgorithms QAlgorithms.Entanglement Filter
open scoped Matrix ComplexConjugate ComplexOrder BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)
open QAlgorithms.Papers.Independent.Information100.P71 (channelPower)

open QAlgorithms.Papers.Independent.Dependency50.P35 (maxRelative)
open QAlgorithms.Papers.Independent.Support50.P21 (eMax)

variable {I J A B C D : Type}
variable [Fintype I] [DecidableEq I] [Nonempty I]
variable [Fintype J] [DecidableEq J] [Nonempty J]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype C] [DecidableEq C] [Nonempty C]
variable [Fintype D] [DecidableEq D] [Nonempty D]

/-- PDF pp.3--4, (4): include the Umegaki endpoint at alpha=1 and support failures.
This endpoint wrapper reuses frozen relative/divergence; Next46.P23.renyi is
a natural-log Petz overlap, a different quantity. -/
def paperSandwichedRenyi (alpha : ℝ) (rho sigma : Mat I) : EReal :=
  if alpha = 1 then QAlgorithms.Papers.Independent.Dependency50.P35.relative rho sigma
  else QAlgorithms.Papers.Independent.Dependency50.P35.divergence alpha rho sigma

/-- PDF p.5, Definition II.1: infimum over all separable density matrices. -/
def entanglementRenyi (alpha : ℝ) (rho : Mat (A × B)) : EReal :=
  sInf {v | ∃ sigma : Mat (A × B), IsSeparableDensity sigma ∧ v = paperSandwichedRenyi alpha rho sigma}

/-- PDF p.5, (9): arbitrary positive finite reference dimension and mixed input. -/
def channelEMax (T : Superop I J) : EReal :=
  sSup {v | ∃ r : ℕ, ∃ rho : Mat (Fin (r + 1) × I),
    IsDensityMatrix rho ∧ v = eMax (idTensorSuperop T rho)}

/-- PDF p.9: channel formation, using the accepted pure-ensemble INFIMUM.
Printed: sup over ensembles. Changed: inf. Why: the named formation measure,
the cited argument and EC use the convex roof, not entanglement of assistance.
Independent moderation of this source correction remains required.
Information100.P08.channelFormation takes a fixed input marginal; here the
supremum is over all reference/input densities, as required by p.9. -/
def channelFormationSupremum (T : Superop I J) : EReal :=
  sSup {v | ∃ r : ℕ, ∃ rho : Mat (Fin (r + 1) × I),
    IsDensityMatrix rho ∧ v =
      (QAlgorithms.Papers.Independent.Information100.P08.formation (idTensorSuperop T rho) : EReal)}

/-- PDF p.15: positive-copy Emax quotients, with no zero denominator. -/
def maxQuotients (T : Superop I J) (n : ℕ) : EReal :=
  ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal) * channelEMax (channelPower T (n + 1))

/-- PDF p.15: computed regularization; the corollary explicitly asserts convergence. -/
def regularizedEMax (T : Superop I J) : EReal := liminf (maxQuotients T) atTop

/-- PDF p.9, (12): positive-copy formation quotients. -/
def formationQuotients (T : Superop I J) (n : ℕ) : EReal :=
  ((1 / ((n + 1 : ℕ) : ℝ) : ℝ) : EReal) * channelFormationSupremum (channelPower T (n + 1))

/-- PDF p.9, (12): computed regularization, whose convergence is part of Theorem II.4.
Dependency50.P41.channelCost is an operational simulation infimum on Fin
registers. This is the computed regularized formation in (12), not that definition. -/
def regularizedFormationCost (T : Superop I J) : EReal := liminf (formationQuotients T) atTop

/-- PDF pp.5--6, (10): transport the accepted finite adaptive LOCC tree to
arbitrary finite local bases. Both matrix indices use the same local bijections. -/
def LOCCOn (L : Superop (A × B) (C × D)) : Prop :=
  QAlgorithms.Papers.Independent.Information100.P21.FiniteLOCC
    (fun X : Mat (Fin (Fintype.card A) × Fin (Fintype.card B)) =>
      let input : Mat (A × B) := fun i j =>
        X ((Fintype.equivFin A) i.1, (Fintype.equivFin B) i.2)
          ((Fintype.equivFin A) j.1, (Fintype.equivFin B) j.2)
      fun i j => L input
        ((Fintype.equivFin C).symm i.1, (Fintype.equivFin D).symm i.2)
        ((Fintype.equivFin C).symm j.1, (Fintype.equivFin D).symm j.2))

/-- PDF pp.6,10--12: send the middle input from Alice to Bob.
The input split is (A,I):B, the output split A:(J,B).
Frozen functions named transfer describe modular evolution or lattice Fourier
matrices; neither sends the middle register across the party cut. -/
def sendChannelRegister (T : Superop I J) : Superop ((A × I) × B) (A × (J × B)) :=
  fun rho p q => T (fun i j => rho ((p.1, i), p.2.2) ((q.1, j), q.2.2)) p.2.1 q.2.1

/-- PDF p.6, Definition II.3: exactly m actual channel applications, with
arbitrary finite changing workspaces and finite adaptive two-way LOCC between them.
A zero-use tail is a local operation. At positive m the first operation is T;
preparation of the initial state is separate. Consecutive local operations can compose.
Dependency50.P07.Protocol is a measurement/message protocol on shared copies;
it has no channel-use recursion and cannot model Definition II.3. -/
inductive TwoWayChannelProtocol (T : Superop I J) (C D : Type)
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D] :
    (m a b : ℕ) → Superop ((Fin (a + 1) × I) × Fin (b + 1)) (C × D) → Prop where
  | stop {a b : ℕ}
      (L : Superop ((Fin (a + 1) × I) × Fin (b + 1)) (C × D))
      (locc : LOCCOn L) : TwoWayChannelProtocol T C D 0 a b L
  | step {m a b aa bb : ℕ}
      (L : Superop (Fin (a + 1) × (J × Fin (b + 1)))
        ((Fin (aa + 1) × I) × Fin (bb + 1)))
      (locc : LOCCOn L)
      (P : Superop ((Fin (aa + 1) × I) × Fin (bb + 1)) (C × D))
      (rest : TwoWayChannelProtocol T C D m aa bb P) :
      TwoWayChannelProtocol T C D (m + 1) a b (fun rho => P (L (sendChannelRegister T rho)))

/-- PDF p.7, Definition II.6: the twisted maximally entangled key and arbitrary
shield density, written in party order (Ak,As):(Bk,Bs). Only the diagonal-key
blocks of a controlled twisting act on the maximally entangled key.
Only the register ordering and unitary-group coercion adapt the frozen
Information100.P67.privateState; its matrix formula is not redeclared. -/
def privateStateInPartyOrder (K s : ℕ) (sigma : Mat (Fin (s + 1) × Fin (s + 1)))
    (U : Fin K → Matrix.unitaryGroup (Fin (s + 1) × Fin (s + 1)) ℂ) :
    Mat ((Fin K × Fin (s + 1)) × (Fin K × Fin (s + 1))) :=
  fun p q => QAlgorithms.Papers.Independent.Information100.P67.privateState
    (fun i => (U i : Mat (Fin (s + 1) × Fin (s + 1)))) sigma
    (p.1.1, (p.1.2, (p.2.1, p.2.2)))
    (q.1.1, (q.1.2, (q.2.1, q.2.2)))

/-- PDF p.7, Definition II.4: normalized maximally entangled key, with trivial
local shield factors when s=0. The only use for quantum targets imposes s=0.
Dependency50.P32.entangledTarget is a port-indexed channel Choi target.
This target reuses the private-state formula with identity twist and trivial
shield (s=0 in every quantum code); there is no copied entangled-target formula. -/
def entangledKeyTarget (K s : ℕ) :
    Mat ((Fin K × Fin (s + 1)) × (Fin K × Fin (s + 1))) :=
  privateStateInPartyOrder K s (fun _ _ => 1) (fun _ => 1)

/-- PDF pp.6--8, Definitions II.3--II.7: an actual positive-use code.
true selects private generation, false selects entanglement generation.
The initial state is separable; the target and output have the same key and
(equal) shield dimensions. Errors are computed below, never supplied as free scalars.
Frontier30.P06.BlockCode is a feedback classical-message code, without
this paper's private/entangled targets and separable preparation. -/
structure TwoWayGenerationCode (T : Superop I J) (isPrivate : Bool) where
  key : ℕ
  uses : ℕ
  uses_pos : 0 < uses
  alice : ℕ
  bob : ℕ
  shield : ℕ
  initial : Mat ((Fin (alice + 1) × I) × Fin (bob + 1))
  initial_density : IsDensityMatrix initial
  initial_separable : IsSeparableDensity initial
  evolution : Superop ((Fin (alice + 1) × I) × Fin (bob + 1))
    ((Fin (2 ^ key) × Fin (shield + 1)) × (Fin (2 ^ key) × Fin (shield + 1)))
  protocol : TwoWayChannelProtocol T (Fin (2 ^ key) × Fin (shield + 1))
    (Fin (2 ^ key) × Fin (shield + 1)) uses alice bob evolution
  target : Mat ((Fin (2 ^ key) × Fin (shield + 1)) ×
    (Fin (2 ^ key) × Fin (shield + 1)))
  target_density : IsDensityMatrix target
  private_target : isPrivate = true → ∃ sigma U,
    IsDensityMatrix sigma ∧ target = privateStateInPartyOrder (2 ^ key) shield sigma U
  quantum_target : isPrivate = false → shield = 0 ∧ target = entangledKeyTarget (2 ^ key) shield

/-- PDF pp.7--8: the code's actual half trace-norm error.
Information100.P67.codeError is a classical privacy criterion; this is
Definition II.7's half trace distance to an actual private-state target. -/
def generationCodeError {T : Superop I J} {isPrivate : Bool} (c : TwoWayGenerationCode T isPrivate) : ℝ :=
  traceNorm (c.evolution c.initial - c.target) / 2

/-- PDF pp.7--8, Definitions II.5,II.8: the exact sequence-based achievable rates.
Finite initial code lengths cause no division-by-zero default; every code has uses>0.
Information100.P04.Achievable is state-distillation achievability under a
different operation class; the channel protocol sequences here are essential. -/
def TwoWayAchievableRate (T : Superop I J) (isPrivate : Bool) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ codes : ℕ → TwoWayGenerationCode T isPrivate,
    Tendsto (fun n => (codes n).uses) atTop atTop ∧
    Tendsto (fun n => ((codes n).key : ℝ) / ((codes n).uses : ℝ)) atTop (nhds R) ∧
    Tendsto (fun n => generationCodeError (codes n)) atTop (nhds 0)

/-- PDF pp.7--8: extended supremum over the nonnegative achievable rates.
Frozen functions named capacity describe one-shot messages or specialized
channels; this is the unrestricted two-way operational supremum of II.5/II.8. -/
def twoWayGenerationCapacity (T : Superop I J) (isPrivate : Bool) : EReal :=
  sSup {v | ∃ R : ℝ, TwoWayAchievableRate T isPrivate R ∧ v = (R : EReal)}

/-- PDF p.8: includes the upper bound and the full error-to-one strong converse,
for every code sequence and every convergent rate above the bound. -/
def PrivateStrongConverseBound (T : Superop I J) (bound : EReal) : Prop :=
  0 ≤ bound ∧ twoWayGenerationCapacity T true ≤ bound ∧
    ∀ (codes : ℕ → TwoWayGenerationCode T true) (R : ℝ),
      Tendsto (fun n => (codes n).uses) atTop atTop →
      Tendsto (fun n => ((codes n).key : ℝ) / ((codes n).uses : ℝ)) atTop (nhds R) →
      bound < (R : EReal) → Tendsto (fun n => generationCodeError (codes n)) atTop (nhds 1)

/-- PDF p.16: trace out only the extra subsystem, retaining the A:B split. -/
def forgetExtra (rho : Mat (A × (B × C))) : Mat (A × B) :=
  fun i j => ∑ c, rho (i.1, (i.2, c)) (j.1, (j.2, c))

/-- PDF p.17: the reduced channel is computed from the given channel. -/
def reducedChannel (T : Superop I (B × C)) : Superop I B :=
  fun X => traceRight (T X)

/-- PDF p.17: EB means separable output for EVERY reference and input state.
Frozen EB predicates are qubit-only, same-input/output-size, or Fin-indexed
pure-input tests. This interface keeps arbitrary rectangular bases and references. -/
def BreaksEntanglementAllReferences (S : Superop I J) : Prop :=
  ∀ r : ℕ, ∀ rho : Mat (Fin (r + 1) × I), IsDensityMatrix rho →
    IsSeparableDensity (idTensorSuperop S rho)

/-- PDF pp.3,17: normalized Choi matrix, reference first. Reuse the frozen
normalized maximally entangled ket rather than redeclaring omega. Other frozen
Choi conventions include unnormalized and output-first matrices. -/
def normalizedChannelChoi (T : Superop I J) : Mat (I × J) :=
  idTensorSuperop T (pureDensity (finiteMaxEntangled I))

/-- PDF p.17: infimum over EB CHANNELS, preserving the Choi input marginal.
Theorem V.2 asserts attainment, rather than assuming it. -/
def choiEBBound (T : Superop I J) : EReal :=
  sInf {v | ∃ S : Superop I J, IsChannel S ∧ BreaksEntanglementAllReferences S ∧
    v = maxRelative (normalizedChannelChoi T) (normalizedChannelChoi S)}

/-- PDF p.25: dimension-indexed state functional; values on nonstates are unused. -/
abbrev StateFunctional := ∀ (A B : Type) [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype B] [DecidableEq B] [Nonempty B], Mat (A × B) → ℝ

/-- PDF pp.25--26: nonnegative, real-valued on states and monotone under all
finite LOCC, including local addition/disposal and arbitrary dimension changes.
No convexity or vanishing-on-separable-states axiom is imposed.
Frontier30.P30.IsLOCCMonotone assumes selective average monotonicity.
A.1 only requires deterministic LOCC monotonicity across arbitrary dimensions. -/
def IsDimensionChangingLOCCMonotone (E : StateFunctional) : Prop :=
  (∀ (A B : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (rho : Mat (A × B)),
    IsDensityMatrix rho → 0 ≤ E A B rho) ∧
  (∀ (A B C D : Type) [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    (L : Superop (A × B) (C × D)) (rho : Mat (A × B)),
    LOCCOn L → IsDensityMatrix rho → E C D (L rho) ≤ E A B rho)

/-- PDF p.25: associated channel supremum, which may be infinite for arbitrary E. -/
def channelValue (E : StateFunctional) (T : Superop I J) : EReal :=
  sSup {v | ∃ r : ℕ, ∃ rho : Mat (Fin (r + 1) × I),
    IsDensityMatrix rho ∧ v = (E (Fin (r + 1)) J (idTensorSuperop T rho) : EReal)}

/-- PDF p.25, (A1): attach the single-use resource, with the input and its
reference at Alice and the resource's output at Bob. -/
def attachInput (X : Mat I) (resource : Mat (A × J)) : Mat ((I × A) × J) :=
  fun i j => X i.1.1 j.1.1 * resource (i.1.2, i.2) (j.1.2, j.2)

/-- PDF p.25, Definition A.1: the SAME sigma supplies the resource through one
use of T. The implementation holds on every input density. Alice's final system
is one-dimensional; no residual resource or extra channel use is available. -/
def ImplementsFrom (T : Superop I J) (sigma : Mat (A × I))
    (L : Superop ((I × A) × J) (Unit × J)) : Prop :=
  IsDensityMatrix sigma ∧ LOCCOn L ∧ ∀ X : Mat I, IsDensityMatrix X →
    (fun i j => L (attachInput X (idTensorSuperop T sigma)) ((), i) ((), j)) = T X

/-- PDF p.8, (11): channel squashed entanglement using the accepted
all-finite-extension state infimum, with arbitrary finite mixed reference input. -/
def channelSquashed (T : Superop I J) : EReal :=
  sSup {v | ∃ r : ℕ, ∃ rho : Mat (Fin (r + 1) × I),
    IsDensityMatrix rho ∧ v =
      (QAlgorithms.Papers.Independent.Dependency50.P19.squashed (idTensorSuperop T rho) : EReal)}

/-- PDF pp.8,19: the transposition bound, using the accepted full stabilized
trace-norm diamond norm on the actual output-transposed linear map. -/
def transpositionBound (T : Superop I J) : ℝ :=
  Real.logb 2 (QAlgorithms.Papers.Independent.Information100.P71.diamond (fun X => (T X).transpose))

/-- PDF p.18, (24): coordinate adapter for the accepted DFT flower state.
Each local register is (d-dimensional shield, Boolean key); the two-party
state is the trace over the actual purifying d-dimensional register. -/
def flowerMatrix (d : ℕ) : Mat ((Fin d × Bool) × (Fin d × Bool)) :=
  fun p q => QAlgorithms.Papers.Independent.Claimed50.P33.multipartiteFlower 2 d
    ![p.1, p.2] ![q.1, q.2]

/-- PDF p.19: inverse NORMALIZED Choi construction, with input dimension 2d.
Its action on every operator, not only diagonal states, is specified. -/
def flowerChannel (d : ℕ) : Superop (Fin d × Bool) (Fin d × Bool) :=
  fun X i j => (2 * d : ℂ) * ∑ a, ∑ b, X a b * flowerMatrix d (a,i) (b,j)

/-! Sanity examples: support endpoint, fixed reference, partial action,
normalization coefficient, zero-weight infinity and no-use protocol semantics. -/

example (T : Superop I J) (n : ℕ) :
    channelPower T n = piSuperop (fun _ : Fin n => T) := rfl

example (K s : ℕ) (sigma : Mat (Fin (s + 1) × Fin (s + 1)))
    (U : Fin K → Matrix.unitaryGroup (Fin (s + 1) × Fin (s + 1)) ℂ)
    (p q : (Fin K × Fin (s + 1)) × (Fin K × Fin (s + 1))) :
    privateStateInPartyOrder K s sigma U p q =
      QAlgorithms.Papers.Independent.Information100.P67.privateState
        (fun i => (U i : Mat (Fin (s + 1) × Fin (s + 1)))) sigma
        (p.1.1, (p.1.2, (p.2.1, p.2.2)))
        (q.1.1, (q.1.2, (q.2.1, q.2.2))) := rfl

example (rho sigma : Mat I) :
    paperSandwichedRenyi 1 rho sigma = QAlgorithms.Papers.Independent.Dependency50.P35.relative rho sigma := by
  simp [paperSandwichedRenyi]

example (rho : Mat ((A × I) × B)) (p q : A × (J × B)) (T : Superop I J) :
    sendChannelRegister T rho p q =
      T (fun i j => rho ((p.1,i),p.2.2) ((q.1,j),q.2.2)) p.2.1 q.2.1 := rfl

example (L : Superop ((Fin 1 × I) × Fin 1) (C × D)) (hL : LOCCOn L) :
    TwoWayChannelProtocol (I := I) (J := J) (fun _ => 0) C D 0 0 0 L := TwoWayChannelProtocol.stop L hL

example : pureDensity (finiteMaxEntangled (Fin 1)) (0,0) (0,0) = 1 := by
  simp [finiteMaxEntangled, pureDensity]

example : (0 : EReal) * (⊤ : EReal) = 0 := by simp

example (T : Superop I (B × C)) (X : Mat I) :
    reducedChannel T X = traceRight (T X) := rfl

example (X : Mat I) (s : Mat (A × J)) (i j : (I × A) × J) :
    attachInput X s i j = X i.1.1 j.1.1 * s (i.1.2,i.2) (j.1.2,j.2) := rfl

example (sigma : Mat (Fin 1 × Fin 1)) :
    privateStateInPartyOrder 1 0 sigma (fun _ => 1) ((0,0),(0,0)) ((0,0),(0,0)) =
      sigma (0,0) (0,0) := by
  simp [privateStateInPartyOrder,
    QAlgorithms.Papers.Independent.Information100.P67.privateState]

example (d : ℕ) : flowerChannel d 0 = 0 := by
  ext i j
  simp [flowerChannel]

example (d : ℕ) (p q : (Fin d × Bool) × (Fin d × Bool)) :
    flowerMatrix d p q = QAlgorithms.Papers.Independent.Claimed50.P33.multipartiteFlower 2 d
      ![p.1,p.2] ![q.1,q.2] := rfl

example {T : Superop I J} {isPrivate : Bool} (code : TwoWayGenerationCode T isPrivate) :
    0 < code.uses := code.uses_pos

example {T : Superop I J} {isPrivate : Bool} (code : TwoWayGenerationCode T isPrivate)
    (h : code.evolution code.initial = code.target) : generationCodeError code = 0 := by
  simp [generationCodeError, h, traceNorm, cfc_zero]

example {T : Superop I J} {R : ℝ} (h : TwoWayAchievableRate T true R) : 0 ≤ R := h.1

example {T : Superop I J} {bound : EReal} (h : PrivateStrongConverseBound T bound) :
    twoWayGenerationCapacity T true ≤ bound := h.2.1

example {T : Superop I J} {sigma : Mat (A × I)}
    {L : Superop ((I × A) × J) (Unit × J)} (h : ImplementsFrom T sigma L) :
    IsDensityMatrix sigma := h.1

/-! One headline theorem per nondeferred node. -/

end QAlgorithms.Papers.Independent.Bridge50.P25



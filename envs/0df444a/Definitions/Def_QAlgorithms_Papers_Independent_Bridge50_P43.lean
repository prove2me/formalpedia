-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P43
-- name    : QAlgorithms_Papers_Independent_Bridge50_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T16:19:19.43702+00:00
-- url     : https://prove2.me/theorems/bdda5892-d107-4b2f-8c0a-9ca1e664cce2
-- title:
--   Definitions for Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication
-- statement:
--   The objects the formalized statements of *Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication* (arXiv:1408.3373) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `NormalizedDensity`: Normalized positive operators, PDF p.10.
--   - `UnitStateVector`: Pure normalized vectors; global phases give the same density, PDF p.12.
--   - `FiniteReferenceInput`: All finite reference systems and all mixed bipartite inputs, PDF p.4. Any finite nonzero reference dimension is represented by Fin reference.
--   - `petzWithUmegaki`: Petz orders with the Umegaki value at one, PDF pp.10--11, (3.2),(3.5). The reused spectral power has value zero on the kernel, including order zero.
--   - `sandwichedWithUmegaki`: Sandwiched orders with the Umegaki value at one, PDF p.11, (3.3),(3.5). Support mismatch and orthogonality retain positive infinity on density arguments.
--   - `channelDiv`: Accepted all-finite-reference mixed-input stabilization, PDF p.4. The zero-dimensional reference has no density inputs and adds only the neutral bottom value to the outer supremum. No fixed-copy or purity reduction is assumed.
--   - `fixedMixedDiv`: The fixed-copy mixed-input optimization, PDF p.7, (2.5).
--   - `fixedPureDiv`: The fixed-copy pure-input optimization, PDF p.12, (3.16).
--   - `unnormalizedGamma`: Unnormalized |Gamma><Gamma|, PDF p.12. Its trace is dim A.
--   - `referenceCanonicalDensity`: Canonical purification density from rho on the fixed reference copy, PDF p.12.
--   - `canonicalOutput`: Moving the reference square roots outside the channel action, PDF p.12, (3.14).
--   - `coefficientGram`: rho=X*X is computed from the input vector, Appendix A, PDF p.27, (A.1)--(A.7).
--   - `CanonicalIdentity`: Both forms of the corrected fixed-input identity, PDF pp.12,27.
--   - `canonicalDiv`: Canonical-input optimization, PDF p.12, (3.17).
--   - `stateMI`: State mutual information in bits, PDF p.14, using the actual two marginals.
--   - `stateRenyiMI`: The state infimum over every normalized comparison on B, PDF p.13, (3.24)--(3.25).
--   - `stabilizedMutualInformation`: Channel mutual information is sup input then inf comparison, PDF p.9, (2.13).
--   - `channelRenyiMI`: Channel Renyi mutual information keeps the input supremum outside the state infimum, PDF p.13, (3.26)--(3.27).
--   - `canonicalMI`: Canonical fixed-reference mutual-information optimization, PDF p.13, (3.28)--(3.29).
--   - `OrderOneProperties`: Monotonicity on the order domain and the two-sided order-one limit, PDF p.14. The deleted point avoids assigning any formula with denominator alpha-1 at alpha=1.
--   - `surprisal`: Extended surprisal in bits, PDF pp.2,6. Zero probability has value positive infinity. It is used only on probabilities in [0,1], so its values are nonnegative.
--   - `positiveLengthExponent`: Normalized exponent at block length k+1; no zero denominator, PDF pp.6--8.
--   - `adaptiveTerminalState`: Final premeasurement state of the actual k+1-use execution, PDF p.15, (4.1)--(4.2).
--   - `adaptiveTestingD`: Optimized adaptive testing divergence, computed from actual strategies, PDF p.6, (2.1).
--   - `optimalAlpha`: Optimal type-I error under the finite-block type-II constraint, PDF p.4, (1.13). The zero effect is feasible for every real r, and all errors lie in [0,1].
--   - `StrategySequence`: A single sequence chooses an actual strategy at every positive block length, PDF p.7, (2.6)--(2.8). Memories may grow with the block length.
--   - `scLower`: Lower strong-converse exponent: the type-II liminf must be STRICTLY greater than r, PDF p.7, (2.6). Infima and limits are extended-valued.
--   - `scUpper`: Upper strong-converse exponent with the SAME strict type-II constraint, PDF p.7, (2.7).
--   - `payoff`: The positive fractional-linear coefficient, PDF p.8, (2.10)--(2.12). For alpha>1, a divergent comparison gives minus infinity, not a real default value.
--   - `channelExponent`: Channel variational strong-converse expression, PDF p.8, (2.12).
--   - `inputPayoff`: The mixed-input payoff with its own freely chosen finite reference, PDF p.8.
--   - `purePayoff`: The fixed-copy pure-input payoff, PDF p.8.
--   - `tensorDensity`: Tensor powers of density operators include the tensor unit at k=0, PDF p.17.
-- source:
--   Strong converse exponents for a quantum channel discrimination problem and quantum-feedback-assisted communication, arXiv:1408.3373v3, https://arxiv.org/abs/1408.3373v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P09
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P71
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

/-!
Statement drafts for Cooney--Mosonyi--Wilde, arXiv:1408.3373v3.
All citations are PDF pages, and every information quantity is in bits.
Only pinned accepted modules are imported. Paper-local definitions below do not
assume any optimization reduction, minimax identity, or adaptive entropy bound.
Three protocol-model-dependent nodes are explicitly deferred in HARD.md.
Compilation is pending the mechanical batch handoff.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology
open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P43

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P09 (Divergence relativeD petzD sandwichedD)
open QAlgorithms.Papers.Independent.Information100.P71
  (SupportIncluded supportPower AdaptiveTest adaptiveInput adaptiveAccept adaptiveBeta channelPower)
open QAlgorithms.Papers.Independent.Information100.P58 (testingD)
-- Exactly the trace-preparation map of PDF pp.5--6, on every operator.
open QAlgorithms.Papers.Independent.Information100.P69 (replacer)

/-- Normalized positive operators, PDF p.10. -/
abbrev NormalizedDensity (I : Type) [Fintype I] :=
  {X : Matrix I I ℂ // IsDensityMatrix X}

/-- Pure normalized vectors; global phases give the same density, PDF p.12. -/
abbrev UnitStateVector (I : Type) [Fintype I] :=
  {v : EuclideanSpace ℂ I // IsState v}

/-- All finite reference systems and all mixed bipartite inputs, PDF p.4.
Any finite nonzero reference dimension is represented by Fin reference. -/
structure FiniteReferenceInput (A : Type) [Fintype A] where
  reference : ℕ
  reference_pos : 0 < reference
  state : NormalizedDensity (Fin reference × A)

/-- Petz orders with the Umegaki value at one, PDF pp.10--11, (3.2),(3.5).
The reused spectral power has value zero on the kernel, including order zero. -/
def petzWithUmegaki (alpha : ℝ) : Divergence :=
  if alpha = 1 then relativeD else petzD alpha

/-- Sandwiched orders with the Umegaki value at one, PDF p.11, (3.3),(3.5).
Support mismatch and orthogonality retain positive infinity on density arguments. -/
def sandwichedWithUmegaki (alpha : ℝ) : Divergence :=
  if alpha = 1 then relativeD else sandwichedD alpha

/-- Accepted all-finite-reference mixed-input stabilization, PDF p.4.
The zero-dimensional reference has no density inputs and adds only the neutral
bottom value to the outer supremum. No fixed-copy or purity reduction is assumed. -/
abbrev channelDiv {A B : Type} [Fintype A] [Fintype B]
    (div : Divergence) (N M : Superop A B) : EReal :=
  QAlgorithms.Papers.Independent.Dependency50.P09.channelD div N M

/-- The fixed-copy mixed-input optimization, PDF p.7, (2.5). -/
def fixedMixedDiv {A B : Type} [Fintype A] [Fintype B]
    (div : Divergence) (N M : Superop A B) : EReal :=
  ⨆ psi : NormalizedDensity (A × A), div (idTensorSuperop N psi.1) (idTensorSuperop M psi.1)

/-- The fixed-copy pure-input optimization, PDF p.12, (3.16). -/
def fixedPureDiv {A B : Type} [Fintype A] [Fintype B]
    (div : Divergence) (N M : Superop A B) : EReal :=
  ⨆ psi : UnitStateVector (A × A), div (idTensorSuperop N (pureDensity psi.1))
    (idTensorSuperop M (pureDensity psi.1))

/-- Unnormalized |Gamma><Gamma|, PDF p.12. Its trace is dim A. -/
def unnormalizedGamma (A : Type) [DecidableEq A] : Matrix (A × A) (A × A) ℂ :=
  fun p q => if p.1 = p.2 ∧ q.1 = q.2 then 1 else 0

/-- Canonical purification density from rho on the fixed reference copy, PDF p.12. -/
def referenceCanonicalDensity {A : Type} [Fintype A] [DecidableEq A]
    (rho : Matrix A A ℂ) : Matrix (A × A) (A × A) ℂ :=
  let S := Matrix.kronecker (supportPower rho (1/2 : ℝ)) (1 : Matrix A A ℂ)
  S * unnormalizedGamma A * S

/-- Moving the reference square roots outside the channel action, PDF p.12, (3.14). -/
def canonicalOutput {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]
    [DecidableEq B] (rho : Matrix A A ℂ) (N : Superop A B) : Matrix (A × B) (A × B) ℂ :=
  let S := Matrix.kronecker (supportPower rho (1/2 : ℝ)) (1 : Matrix B B ℂ)
  S * idTensorSuperop N (unnormalizedGamma A) * S

/-- rho=X*X is computed from the input vector, Appendix A, PDF p.27, (A.1)--(A.7). -/
def coefficientGram {R A : Type} [Fintype R] [Fintype A]
    (psi : EuclideanSpace ℂ (R × A)) : Matrix A A ℂ :=
  let X : Matrix R A ℂ := fun r a => psi (r,a)
  Xᴴ * X

/-- Both forms of the corrected fixed-input identity, PDF pp.12,27. -/
def CanonicalIdentity {R A B : Type} [Fintype R] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (div : Divergence)
    (psi : EuclideanSpace ℂ (R × A)) (rho : Matrix A A ℂ) (N M : Superop A B) : Prop :=
  div (idTensorSuperop N (pureDensity psi)) (idTensorSuperop M (pureDensity psi)) =
    div (idTensorSuperop N (referenceCanonicalDensity rho)) (idTensorSuperop M (referenceCanonicalDensity rho)) ∧
  div (idTensorSuperop N (referenceCanonicalDensity rho)) (idTensorSuperop M (referenceCanonicalDensity rho)) =
    div (canonicalOutput rho N) (canonicalOutput rho M)

/-- Canonical-input optimization, PDF p.12, (3.17). -/
def canonicalDiv {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (div : Divergence) (N M : Superop A B) : EReal :=
  ⨆ rho : NormalizedDensity A, div (canonicalOutput rho.1 N) (canonicalOutput rho.1 M)

/-- State mutual information in bits, PDF p.14, using the actual two marginals. -/
def stateMI {R B : Type} [Fintype R] [Fintype B]
    (rho : Matrix (R × B) (R × B) ℂ) : EReal :=
  relativeD rho (Matrix.kronecker (traceRight rho) (traceLeft rho))

/-- The state infimum over every normalized comparison on B, PDF p.13, (3.24)--(3.25). -/
def stateRenyiMI {R B : Type} [Fintype R] [Fintype B]
    (div : Divergence) (rho : Matrix (R × B) (R × B) ℂ) : EReal :=
  ⨅ sigma : NormalizedDensity B, div rho (Matrix.kronecker (traceRight rho) sigma.1)

/-- Channel mutual information is sup input then inf comparison, PDF p.9, (2.13). -/
def stabilizedMutualInformation {A B : Type} [Fintype A] [Fintype B] (N : Superop A B) : EReal :=
  ⨆ psi : FiniteReferenceInput A, stateRenyiMI relativeD (idTensorSuperop N psi.state.1)

/-- Channel Renyi mutual information keeps the input supremum outside the state infimum,
PDF p.13, (3.26)--(3.27). -/
def channelRenyiMI {A B : Type} [Fintype A] [Fintype B]
    (div : Divergence) (N : Superop A B) : EReal :=
  ⨆ psi : FiniteReferenceInput A, stateRenyiMI div (idTensorSuperop N psi.state.1)

/-- Canonical fixed-reference mutual-information optimization, PDF p.13, (3.28)--(3.29). -/
def canonicalMI {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (div : Divergence) (N : Superop A B) : EReal :=
  ⨆ rho : NormalizedDensity A, stateRenyiMI div (idTensorSuperop N (referenceCanonicalDensity rho.1))

/-- Monotonicity on the order domain and the two-sided order-one limit, PDF p.14.
The deleted point avoids assigning any formula with denominator alpha-1 at alpha=1. -/
def OrderOneProperties (f : ℝ → EReal) (domain : Set ℝ) (value : EReal) : Prop :=
  MonotoneOn f domain ∧
    Tendsto f (nhdsWithin 1 (domain \ {1})) (𝓝 value)

/-- Extended surprisal in bits, PDF pp.2,6. Zero probability has value positive infinity.
It is used only on probabilities in [0,1], so its values are nonnegative. -/
def surprisal (p : ℝ) : EReal :=
  if p = 0 then ⊤ else ((-Real.logb 2 p : ℝ) : EReal)

/-- Normalized exponent at block length k+1; no zero denominator, PDF pp.6--8. -/
def positiveLengthExponent (k : ℕ) (p : ℝ) : EReal :=
  (((1 : ℝ) / (k+1 : ℕ) : ℝ) : EReal) * surprisal p

/-- Final premeasurement state of the actual k+1-use execution, PDF p.15, (4.1)--(4.2). -/
def adaptiveTerminalState {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    {k : ℕ} (P : AdaptiveTest A B (k+1)) (N : Superop A B) :
    Matrix (Fin P.memory × B) (Fin P.memory × B) ℂ :=
  idTensorSuperop N (adaptiveInput P N k)

/-- Optimized adaptive testing divergence, computed from actual strategies, PDF p.6, (2.1). -/
def adaptiveTestingD {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (k : ℕ) (epsilon : ℝ) (N M : Superop A B) : EReal :=
  surprisal (adaptiveBeta (k+1) epsilon N M)

/-- Optimal type-I error under the finite-block type-II constraint, PDF p.4, (1.13).
The zero effect is feasible for every real r, and all errors lie in [0,1]. -/
def optimalAlpha {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (k : ℕ) (r : ℝ) (N M : Superop A B) : ℝ :=
  sInf {a : ℝ | ∃ P : AdaptiveTest A B (k+1),
    adaptiveAccept P M ≤ Real.rpow 2 (-((k+1 : ℕ) : ℝ) * r) ∧
      a = 1 - adaptiveAccept P N}

/-- A single sequence chooses an actual strategy at every positive block length,
PDF p.7, (2.6)--(2.8). Memories may grow with the block length. -/
abbrev StrategySequence (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :=
  (k : ℕ) → AdaptiveTest A B (k+1)

/-- Lower strong-converse exponent: the type-II liminf must be STRICTLY greater than r,
PDF p.7, (2.6). Infima and limits are extended-valued. -/
def scLower {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : ℝ) (N M : Superop A B) : EReal :=
  sInf {e : EReal | ∃ P : StrategySequence A B,
    (r : EReal) < Filter.liminf (fun k => positiveLengthExponent k (adaptiveAccept (P k) M)) atTop ∧
    e = Filter.liminf (fun k => positiveLengthExponent k (adaptiveAccept (P k) N)) atTop}

/-- Upper strong-converse exponent with the SAME strict type-II constraint,
PDF p.7, (2.7). -/
def scUpper {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : ℝ) (N M : Superop A B) : EReal :=
  sInf {e : EReal | ∃ P : StrategySequence A B,
    (r : EReal) < Filter.liminf (fun k => positiveLengthExponent k (adaptiveAccept (P k) M)) atTop ∧
    e = Filter.limsup (fun k => positiveLengthExponent k (adaptiveAccept (P k) N)) atTop}

/-- The positive fractional-linear coefficient, PDF p.8, (2.10)--(2.12).
For alpha>1, a divergent comparison gives minus infinity, not a real default value. -/
def payoff (alpha r : ℝ) (d : EReal) : EReal :=
  (((alpha-1)/alpha : ℝ) : EReal) * ((r : EReal) - d)

/-- Channel variational strong-converse expression, PDF p.8, (2.12). -/
def channelExponent {A B : Type} [Fintype A] [Fintype B]
    (r : ℝ) (N M : Superop A B) : EReal :=
  ⨆ alpha : {a : ℝ // 1 < a}, payoff alpha.1 r (channelDiv (sandwichedWithUmegaki alpha.1) N M)

/-- The mixed-input payoff with its own freely chosen finite reference, PDF p.8. -/
def inputPayoff {A B : Type} [Fintype A] [Fintype B]
    (alpha r : ℝ) (N M : Superop A B) (psi : FiniteReferenceInput A) : EReal :=
  payoff alpha r (sandwichedWithUmegaki alpha (idTensorSuperop N psi.state.1)
    (idTensorSuperop M psi.state.1))

/-- The fixed-copy pure-input payoff, PDF p.8. -/
def purePayoff {A B : Type} [Fintype A] [Fintype B]
    (alpha r : ℝ) (N M : Superop A B) (psi : UnitStateVector (A × A)) : EReal :=
  payoff alpha r (sandwichedWithUmegaki alpha (idTensorSuperop N (pureDensity psi.1))
    (idTensorSuperop M (pureDensity psi.1)))

/-- Tensor powers of density operators include the tensor unit at k=0, PDF p.17. -/
def tensorDensity {B : Type} (sigma : Matrix B B ℂ) (k : ℕ) :
    Matrix (Fin k → B) (Fin k → B) ℂ :=
  fun x y => ∏ i, sigma (x i) (y i)

example : surprisal 0 = ⊤ := by simp [surprisal]

example : surprisal 1 = 0 := by simp [surprisal]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    petzWithUmegaki 1 rho sigma = relativeD rho sigma := by simp [petzWithUmegaki]

example {I : Type} [Fintype I] [DecidableEq I] (rho sigma : Matrix I I ℂ) :
    sandwichedWithUmegaki 1 rho sigma = relativeD rho sigma := by simp [sandwichedWithUmegaki]

example : unnormalizedGamma (Fin 2) (0,0) (1,1) = 1 := by simp [unnormalizedGamma]

example {B : Type} (sigma : Matrix B B ℂ) (x y : Fin 0 → B) :
    tensorDensity sigma 0 x y = 1 := by simp [tensorDensity]

example {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (P : AdaptiveTest A B 1) (N : Superop A B) :
    adaptiveTerminalState (k := 0) P N = idTensorSuperop N P.initial := rfl

end QAlgorithms.Papers.Independent.Bridge50.P43



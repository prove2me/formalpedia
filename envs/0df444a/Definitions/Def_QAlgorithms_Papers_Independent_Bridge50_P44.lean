-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P44
-- name    : QAlgorithms_Papers_Independent_Bridge50_P44
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T19:06:52.001453+00:00
-- url     : https://prove2.me/theorems/994235d2-e115-415c-9838-37d7b9e7d62e
-- title:
--   Definitions for Cryptographic security of quantum key distribution
-- statement:
--   The objects the formalized statements of *Cryptographic security of quantum key distribution* (arXiv:1409.3525) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `IsDiscreteLaw`: PDF pp.36,40: normalized discrete mass function; absolute convergence is explicit.
--   - `discreteTV`: PDF p.36, Definition A.1: total variation for arbitrary discrete alphabets. Uses below are on normalized, absolutely summable laws.
--   - `IsCoupling`: PDF p.40, Eqs.(26)--(27): a normalized joint law with both specified marginals.
--   - `binaryTestSuccess`: PDF pp.38--39: one-sample, equal-prior success of an arbitrary randomized rule; g(z) is its probability of guessing the first law. This differs from the frozen Information100.P53.classicalSuccess (finite-message MAP decoding).
--   - `optimalBinaryTestSuccess`: PDF p.39: optimal equal-prior one-sample success. For probability laws the feasible set contains constant rules and is bounded by one. This differs from the frozen Information100.P58.classicalOptimum (erasure-code optimization).
--   - `IsDiscretePOVM`: PDF pp.37--38: extension of the finite frozen POVM to discrete outcome families. Matrix-series convergence avoids default values of divergent sums.
--   - `ClassicalFirst`: PDF p.38: classicality on the first factor in its designated basis.
--   - `xorWord`: PDF pp.11--13: bitwise XOR, for arbitrary message length including zero.
--   - `otpReal`: PDF pp.11--13: actual joint Bob/ciphertext output under a uniform shared key and a faithfully forwarding authentic channel.
--   - `otpIdeal`: PDF pp.12--13: ideal channel delivers x; its simulator samples a uniform ciphertext given only the public length n.
--   - `verifyTag`: PDF pp.49--50: tag verification. An honest forwarding filter returns exactly the pair (x,h_k(x)); no property of the hash family is assumed.
--   - `honestAuthentication`: PDF p.50: the honest filtered tag-and-verify channel, after uniform-key sampling.
--   - `Interface`: PDF pp.14--15: named interfaces; only Alice and Bob are honest.
--   - `ACModel`: PDF pp.13--15, Eqs.(3)--(7): abstract compatible resources and converters, with named-interface attachment. This is the source's axiomatic AC layer, not an implementation of quantum protocols. Parallel distance contractivity is required in each argument, as for arbitrary compatible resource contexts.
--   - `honest`: PDF p.15: the honest converter pair attached to A and B.
--   - `Filtered`: PDF p.14: a filtered resource is the same resource together with an E-filter.
--   - `Constructs`: PDF p.15, Definition 2.1: both availability and existence of a single E-simulator. The adversarial distance is the model's resource distance, covering all contexts.
--   - `serialProtocol`: PDF pp.14,46: componentwise serial wiring of the honest converter pair.
--   - `parallelProtocol`: PDF pp.14,47: componentwise parallel wiring of the honest converter pair.
--   - `parallelFiltered`: PDF p.47: parallel filtered resources retain both honest filters.
--   - `distinguishingAdvantage`: PDF p.45: signed distinguishing advantage from actual abstract test execution laws. A nonempty test class and PMF probabilities make this supremum bounded.
--   - `ClosedTests`: PDF p.45, Eq.(30): every composite test is represented in the same class, with its entire binary output law preserved on every resource.
--   - `nuclearDistance`: PDF pp.36,44--45: half the nuclear trace norm on full coefficient arrays. State-domain theorems below guarantee finiteness. Extended nonnegative values retain infinity, including on arrays without a nuclear expansion.
--   - `uniformReference`: PDF pp.43--45: uniform d-dimensional key, independent of the given memory operator. The uniform finite matrix is reused from the accepted library.
--   - `optimizedSecrecy`: PDF pp.44--45, Appendix B: optimize over all normalized reference states. The extended infimum is defined without compactness of infinite-dimensional state space; the actual marginal supplies a feasible reference in its uses.
--   - `PositiveMemoryOperator`: PDF p.43, Eq.(28): positivity of an actual bounded operator on full l² memory, expressed by its quadratic form. This is not positivity of a finite truncation.
--   - `IsMemoryPOVM`: PDF p.43, Eq.(28): K-outcome POVMs of bounded operators on arbitrary memory. Each operator is positive and their finite sum is exactly the identity.
--   - `memoryTracePair`: PDF p.43: Re Tr(M rho), written in the full countable basis. On bounded M and trace-class rho each inner coefficient sum and the outer diagonal sum converge absolutely. The order is M_(i,j) rho_(j,i).
--   - `memoryGuess`: PDF p.43, Eq.(28): optimal finite classical-key guessing with unrestricted countable quantum memory. Normalized ensembles make the feasible values nonempty and bounded in [0,1].
-- source:
--   Cryptographic security of quantum key distribution, arXiv:1409.3525v1, https://arxiv.org/abs/1409.3525v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P76
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P24

/-!
Portmann--Renner, arXiv:1409.3525v1. Only the elementary matrix interpretation
is used for the appendix's matrix statements. The operational QKD statements
are explicitly deferred in HARD.md. The guessing and optimized-secrecy
statements use positive trace-class states on arbitrary countable memory. Abstract AC theorems below quantify over the source's
axiomatic resource models; they do not supply a concrete QKD execution model.
Accepted paper imports above are pinned libraries, used under the independent
paper workflow override. Compilation is pending the mechanical batch stage.
-/

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P44

open QAlgorithms
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Dependency50.P24 (cqState)
open QAlgorithms.Papers.Independent.Frontier18.P08 (partialTraceFirst)
open QAlgorithms.Papers.Independent.Information100.P76 (maximallyMixed)
open QAlgorithms.Papers.Independent.Frontier18.P08 (conditionalEntropyNats)

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF pp.36,40: normalized discrete mass function; absolute convergence is explicit. -/
def IsDiscreteLaw {Z : Type*} (p : Z → ℝ) : Prop :=
  (∀ z, 0 ≤ p z) ∧ Summable p ∧ (∑' z, p z) = 1

/-- PDF p.36, Definition A.1: total variation for arbitrary discrete alphabets.
Uses below are on normalized, absolutely summable laws. -/
def discreteTV {Z : Type*} (p q : Z → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑' z, |p z - q z|

/-- PDF p.40, Eqs.(26)--(27): a normalized joint law with both specified marginals. -/
def IsCoupling {Z : Type*} (p q : Z → ℝ) (j : Z × Z → ℝ) : Prop :=
  IsDiscreteLaw j ∧ (∀ z, (∑' w, j (z,w)) = p z) ∧
    (∀ w, (∑' z, j (z,w)) = q w)

/-- PDF pp.38--39: one-sample, equal-prior success of an arbitrary randomized rule;
g(z) is its probability of guessing the first law. This differs from the frozen
Information100.P53.classicalSuccess (finite-message MAP decoding). -/
def binaryTestSuccess {Z : Type*} (p q : Z → ℝ) (g : Z → Set.Icc (0 : ℝ) 1) : ℝ :=
  (1 / 2 : ℝ) * tsum (fun z => p z * (g z).val + q z * (1 - (g z).val))

/-- PDF p.39: optimal equal-prior one-sample success. For probability laws the
feasible set contains constant rules and is bounded by one. This differs from
the frozen Information100.P58.classicalOptimum (erasure-code optimization). -/
def optimalBinaryTestSuccess {Z : Type*} (p q : Z → ℝ) : ℝ :=
  sSup (Set.range (binaryTestSuccess p q))

/-- PDF pp.37--38: extension of the finite frozen POVM to discrete outcome
families. Matrix-series convergence avoids default values of divergent sums. -/
def IsDiscretePOVM {O I : Type*} [Fintype I] [DecidableEq I]
    (M : O → Matrix I I ℂ) : Prop :=
  (∀ o, (M o).PosSemidef) ∧ HasSum M 1

/-- PDF p.38: classicality on the first factor in its designated basis. -/
def ClassicalFirst {Z B : Type*} (rho : Matrix (Z × B) (Z × B) ℂ) : Prop :=
  ∀ z zprime b bprime, z ≠ zprime → rho (z,b) (zprime,bprime) = 0

/-- PDF pp.11--13: bitwise XOR, for arbitrary message length including zero. -/
def xorWord {n : ℕ} (x k : Fin n → Bool) : Fin n → Bool :=
  fun i => Bool.xor (x i) (k i)

/-- PDF pp.11--13: actual joint Bob/ciphertext output under a uniform shared key
and a faithfully forwarding authentic channel. -/
def otpReal {n : ℕ} (x : Fin n → Bool)
    (out : (Fin n → Bool) × (Fin n → Bool)) : ℝ :=
  ∑ k : Fin n → Bool,
    if out = (xorWord (xorWord x k) k, xorWord x k)
      then (Fintype.card (Fin n → Bool) : ℝ)⁻¹ else 0

/-- PDF pp.12--13: ideal channel delivers x; its simulator samples a uniform
ciphertext given only the public length n. -/
def otpIdeal {n : ℕ} (x : Fin n → Bool)
    (out : (Fin n → Bool) × (Fin n → Bool)) : ℝ :=
  if out.1 = x then (Fintype.card (Fin n → Bool) : ℝ)⁻¹ else 0

/-- PDF pp.49--50: tag verification. An honest forwarding filter returns exactly
the pair (x,h_k(x)); no property of the hash family is assumed. -/
def verifyTag {K X T : Type*} [DecidableEq T] (h : K → X → T)
    (k : K) (received : X × T) : Option X :=
  if received.2 = h k received.1 then some received.1 else none

/-- PDF p.50: the honest filtered tag-and-verify channel, after uniform-key sampling. -/
def honestAuthentication {K X T : Type*} [Fintype K] [DecidableEq X] [DecidableEq T]
    (h : K → X → T) (x : X) (out : Option X) : ℝ :=
  ∑ k, if verifyTag h k (x, h k x) = out then (Fintype.card K : ℝ)⁻¹ else 0

/-- PDF pp.14--15: named interfaces; only Alice and Bob are honest. -/
inductive Interface where
  | alice
  | bob
  | eve
  deriving DecidableEq

/-- PDF pp.13--15, Eqs.(3)--(7): abstract compatible resources and converters,
with named-interface attachment. This is the source's axiomatic AC layer, not
an implementation of quantum protocols. Parallel distance contractivity is
required in each argument, as for arbitrary compatible resource contexts. -/
structure ACModel where
  Resource : Type
  Converter : Type
  parallel : Resource → Resource → Resource
  serial : Converter → Converter → Converter
  tensor : Converter → Converter → Converter
  identity : Converter
  attach : Interface → Converter → Resource → Resource
  distance : Resource → Resource → ℝ
  serial_attach : ∀ i a b r, attach i (serial a b) r = attach i a (attach i b r)
  identity_attach : ∀ i r, attach i identity r = r
  distinct_attach : ∀ i j a b r, i ≠ j →
    attach i a (attach j b r) = attach j b (attach i a r)
  parallel_attach : ∀ i a b r s,
    attach i (tensor a b) (parallel r s) = parallel (attach i a r) (attach i b s)
  distance_nonneg : ∀ r s, 0 ≤ distance r s
  distance_self : ∀ r, distance r r = 0
  distance_symm : ∀ r s, distance r s = distance s r
  distance_triangle : ∀ r s t, distance r t ≤ distance r s + distance s t
  attach_contract : ∀ i a r s, distance (attach i a r) (attach i a s) ≤ distance r s
  parallel_contract_right : ∀ r s t, distance (parallel r t) (parallel s t) ≤ distance r s
  parallel_contract_left : ∀ r s t, distance (parallel t r) (parallel t s) ≤ distance r s

/-- PDF p.15: the honest converter pair attached to A and B. -/
def honest (M : ACModel) (p : M.Converter × M.Converter) (r : M.Resource) : M.Resource :=
  M.attach .alice p.1 (M.attach .bob p.2 r)

/-- PDF p.14: a filtered resource is the same resource together with an E-filter. -/
structure Filtered (M : ACModel) where
  resource : M.Resource
  filter : M.Converter

/-- PDF p.15, Definition 2.1: both availability and existence of a single E-simulator.
The adversarial distance is the model's resource distance, covering all contexts. -/
def Constructs (M : ACModel) (p : M.Converter × M.Converter)
    (r s : Filtered M) (epsilon : ℝ) : Prop :=
  M.distance (honest M p (M.attach .eve r.filter r.resource))
      (M.attach .eve s.filter s.resource) ≤ epsilon ∧
  ∃ simulator : M.Converter,
    M.distance (honest M p r.resource) (M.attach .eve simulator s.resource) ≤ epsilon

/-- PDF pp.14,46: componentwise serial wiring of the honest converter pair. -/
def serialProtocol (M : ACModel) (q p : M.Converter × M.Converter) :=
  (M.serial q.1 p.1, M.serial q.2 p.2)

/-- PDF pp.14,47: componentwise parallel wiring of the honest converter pair. -/
def parallelProtocol (M : ACModel) (p q : M.Converter × M.Converter) :=
  (M.tensor p.1 q.1, M.tensor p.2 q.2)

/-- PDF p.47: parallel filtered resources retain both honest filters. -/
def parallelFiltered (M : ACModel) (r s : Filtered M) : Filtered M :=
  ⟨M.parallel r.resource s.resource, M.tensor r.filter s.filter⟩

/-- PDF p.45: signed distinguishing advantage from actual abstract test execution
laws. A nonempty test class and PMF probabilities make this supremum bounded. -/
def distinguishingAdvantage {R D : Type} (run : D → R → PMF Bool) (r s : R) : ℝ :=
  sSup (Set.range (fun d => (run d r true).toReal - (run d s true).toReal))

/-- PDF p.45, Eq.(30): every composite test is represented in the same class,
with its entire binary output law preserved on every resource. -/
def ClosedTests {R D : Type} (run : D → R → PMF Bool) (f : R → R) : Prop :=
  ∀ d, ∃ composite, ∀ r, run composite r = run d (f r)

/-- PDF pp.36,44--45: half the nuclear trace norm on full coefficient arrays.
State-domain theorems below guarantee finiteness. Extended nonnegative values
retain infinity, including on arrays without a nuclear expansion. -/
def nuclearDistance {I : Type} (rho sigma : Matrix I I ℂ) : ENNReal :=
  traceSize (rho - sigma) / 2

/-- PDF pp.43--45: uniform d-dimensional key, independent of the given memory
operator. The uniform finite matrix is reused from the accepted library. -/
def uniformReference {d : ℕ} {E : Type} (sigma : Matrix E E ℂ) :
    Matrix (Fin d × E) (Fin d × E) ℂ :=
  Matrix.kronecker (maximallyMixed d) sigma

/-- PDF pp.44--45, Appendix B: optimize over all normalized reference states.
The extended infimum is defined without compactness of infinite-dimensional
state space; the actual marginal supplies a feasible reference in its uses. -/
def optimizedSecrecy {d : ℕ} {E : Type} (rho : State (Fin d × E)) : ENNReal :=
  ⨅ sigma : State E, nuclearDistance rho.coefficients (uniformReference sigma.coefficients)

/-- PDF p.43, Eq.(28): positivity of an actual bounded operator on full l² memory,
expressed by its quadratic form. This is not positivity of a finite truncation. -/
def PositiveMemoryOperator {E : Type} (A : Hilbert E →L[ℂ] Hilbert E) : Prop :=
  ∀ v, (inner ℂ v (A v)).im = 0 ∧ 0 ≤ (inner ℂ v (A v)).re

/-- PDF p.43, Eq.(28): K-outcome POVMs of bounded operators on arbitrary memory.
Each operator is positive and their finite sum is exactly the identity. -/
def IsMemoryPOVM {K E : Type} [Fintype K]
    (M : K → (Hilbert E →L[ℂ] Hilbert E)) : Prop :=
  (∀ k, PositiveMemoryOperator (M k)) ∧ ∑ k, M k = ContinuousLinearMap.id ℂ (Hilbert E)

/-- PDF p.43: Re Tr(M rho), written in the full countable basis. On bounded M
and trace-class rho each inner coefficient sum and the outer diagonal sum
converge absolutely. The order is M_(i,j) rho_(j,i). -/
def memoryTracePair {E : Type} (M : Hilbert E →L[ℂ] Hilbert E)
    (rho : Matrix E E ℂ) : ℝ :=
  (∑' i : E, ∑' j : E, (M (lp.single 2 j (1 : ℂ))) i * rho j i).re

/-- PDF p.43, Eq.(28): optimal finite classical-key guessing with unrestricted
countable quantum memory. Normalized ensembles make the feasible values
nonempty and bounded in [0,1]. -/
def memoryGuess {d : ℕ} {E : Type} (p : Fin d → ℝ) (rho : Fin d → State E) : ℝ :=
  sSup {v | ∃ M : Fin d → (Hilbert E →L[ℂ] Hilbert E), IsMemoryPOVM M ∧
    v = ∑ k, p k * memoryTracePair (M k) (rho k).coefficients}

/-! Sanity checks concern definitions only; source theorem targets remain sorry. -/

example : IsDiscreteLaw (fun _ : Unit => (1 : ℝ)) := by
  refine ⟨fun _ => zero_le_one, (hasSum_fintype _).summable, ?_⟩
  simp

example {Z : Type*} (p : Z → ℝ) : discreteTV p p = 0 := by
  simp [discreteTV]

example : IsCoupling (fun _ : Unit => (1 : ℝ)) (fun _ : Unit => 1)
    (fun _ : Unit × Unit => 1) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨fun _ => zero_le_one, (hasSum_fintype _).summable, by simp⟩
  · intro z; simp
  · intro z; simp

example (p q : Unit → ℝ) (g : Unit → Set.Icc (0 : ℝ) 1) :
    binaryTestSuccess p q g = (1 / 2 : ℝ) *
      (p () * (g ()).val + q () * (1 - (g ()).val)) := by
  simp [binaryTestSuccess]

example {I : Type*} [Fintype I] [DecidableEq I] :
    IsDiscretePOVM (fun _ : Unit => (1 : Matrix I I ℂ)) := by
  exact ⟨fun _ => Matrix.PosSemidef.one, by simpa using hasSum_fintype (fun _ : Unit => (1 : Matrix I I ℂ))⟩

example {Z B : Type*} : ClassicalFirst (0 : Matrix (Z × B) (Z × B) ℂ) := by
  intro z zprime b bprime h; rfl

example {n : ℕ} (x : Fin n → Bool) : xorWord x (fun _ => false) = x := by
  funext i; simp [xorWord]

example (x : Fin 0 → Bool) : otpIdeal x (x,x) = 1 := by
  simp [otpIdeal]

example {K X T : Type*} [DecidableEq T] (h : K → X → T) (k : K) (x : X) :
    verifyTag h k (x,h k x) = some x := by simp [verifyTag]

example {X T : Type*} [DecidableEq X] [DecidableEq T]
    (h : Unit → X → T) (x : X) : honestAuthentication h x (some x) = 1 := by
  simp [honestAuthentication, verifyTag]

example (M : ACModel) (r : M.Resource) : honest M (M.identity,M.identity) r = r := by
  simp [honest, M.identity_attach]

example (M : ACModel) (p : M.Converter × M.Converter) (r s : Filtered M) (epsilon : ℝ)
    (h : Constructs M p r s epsilon) :
    ∃ sim, M.distance (honest M p r.resource) (M.attach .eve sim s.resource) ≤ epsilon := h.2

example {R D : Type} (run : D → R → PMF Bool) : ClosedTests run id := by
  intro d; exact ⟨d, fun _ => rfl⟩

example {E : Type} (sigma : Matrix E E ℂ) (i j : E) :
    uniformReference (d := 1) sigma (0,i) (0,j) = sigma i j := by
  simp [uniformReference, maximallyMixed, Matrix.kronecker]

example {E : Type} (rho : Matrix E E ℂ) : memoryTracePair 0 rho = 0 := by
  simp [memoryTracePair]

example {E : Type} : PositiveMemoryOperator (0 : Hilbert E →L[ℂ] Hilbert E) := by
  intro v; simp

end QAlgorithms.Papers.Independent.Bridge50.P44



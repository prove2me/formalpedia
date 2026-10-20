-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P47
-- name    : QAlgorithms_Papers_Independent_Dependency50_P47
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T15:35:10.023595+00:00
-- url     : https://prove2.me/theorems/a4acdc56-34ec-427e-a02e-550528fd0e06
-- title:
--   Definitions for On Dimension Bounds for Auxiliary Quantum Systems
-- statement:
--   The objects the formalized statements of *On Dimension Bounds for Auxiliary Quantum Systems* (arXiv:1207.3911) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Law`: §2, pp.4–5: normalized finite classical law.
--   - `CChannel`: §2, p.5: classical channel, normalized at every input.
--   - `QChannel`: §2, p.5: cq channel with positive semidefinite trace-one conditional states.
--   - `cqMatrix`: §2, p.5: block-diagonal density of (f(X),F), including zero-probability blocks.
--   - `qCond`: §2, p.5: H(f(X)|F), computed on the joint cq state.
--   - `qMI`: §2, p.5: I(f(X);F).
--   - `cCond`: §2, p.5: H(f(X)|C), with the original source law retained.
--   - `cMI`: §2, p.5: I(f(X);C).
--   - `qCMI`: §2, p.5: I(f(X);F|g(X)) on one simultaneously existing joint state.
--   - `Alphabet`: §4, p.9: the finite product alphabet.
--   - `classicalHull`: §4, p.9: classical convexification, including the law coordinate.
--   - `quantumHull`: §4, p.9: quantum convexification, with all positive finite dimensions.
--   - `AssertionOne`: Theorem 3(a1), p.10: all alphabet quantifiers belong inside A1.
--   - `AssertionTwo`: Theorem 3(a2), p.10: one channel uniformly approximates every input law in absolute error.
--   - `quantumDifference`: §4, pp.10–11: quantum objective; F-X-YZ is constructed, not assumed about an arbitrary state.
--   - `classicalDifference`: §4, p.10: the classical objective with C-X-YZ.
--   - `AssertionThree`: Theorem 3(a3), p.10: existence of an attained classical optimizer dominating every finite quantum auxiliary; no potentially default-valued real supremum is used.
--   - `FlaggedBinaryChannel`: Appendix E, p.28: output (real retained flag, binary outcome). A dominating probability measure with bounded densities represents the measurable binary-input classical channel.
--   - `flaggedMI`: Appendix E, p.28: H(X) minus the integral of the posterior binary entropy. The mixture density is at most two, and posterior entropy is in [0,1], so the integrand is integrable. A zero mixture density contributes zero even at input endpoints.
--   - `OutputChannel`: Appendix D, p.26: arbitrary positive finite output sizes, permitting a common flag.
--   - `outputWeights`: Appendix D: induced joint weights.
--   - `outputClassicalDifference`: Appendix D: classical difference payoff.
--   - `outputQuantumDifference`: Appendix D: quantum difference payoff.
--   - `minimaxPayoff`: Lemma 7, p.26: the weighted payoff.
--   - `classicalGW`: §3.1, p.5: classical Gray–Wyner upper region, containing all rates above a tuple.
--   - `singleQuantumGW`: §3.1, p.6: single-quantum-auxiliary outer region, coordinatewise upward closed.
--   - `factorTrace`: §3.1, pp.5–6: partial trace onto factor i of a product-basis register.
--   - `multiQuantumGW`: §3.1, p.5: multi-auxiliary region of (3), defined entropically; the operational characterization attributed to Winter is not asserted as a new theorem here.
--   - `Sequence`: §3.2, p.6: n outcomes of a finite alphabet.
--   - `iidCorrelation`: §3.2, p.6: n-fold product weights of the complete correlation law.
--   - `sourceXY`: §3.2, p.6: the fixed source marginal p(x,y).
--   - `SimulationCode`: §3.2, p.7: one-way entanglement-assisted code. Alice's input selects a POVM with outcomes (a^n,m); Bob's input and m select a POVM with outcomes b^n. The shared density is fixed independently of both inputs. Alice need not retain a quantum output.
--   - `simulationWeights`: §3.2, pp.6–7: the induced complete law; shared entanglement does not depend on x^n,y^n.
--   - `messageWeights`: §3.2, p.7: the classical message distribution, marginalized over the input and Alice's output.
--   - `simulationError`: §3.2, pp.6–7: full unhalved l1 error of the complete induced law.
--   - `quantumRates`: §3.2, p.7: Rq uses H(M)/n, with no rate slack, and vanishing global l1 error. The n+1 indexing excludes division by zero without dropping any positive blocklength.
--   - `ClassicalSimulationCode`: §3.2, pp.6–7: a classical code with arbitrary finite input-independent shared randomness. The joint encoder includes both Alice's local output and her message.
--   - `classicalSimulationWeights`: §3.2, p.7: induced classical complete law.
--   - `classicalMessageWeights`: §3.2, p.7: message distribution of a classical code.
--   - `classicalRates`: §3.2, pp.6–7: classical simulation rate region, using message entropy and full l1 error.
--   - `axyWeights`: Equation (7), p.8: the AXY marginal of an approximate complete law.
--   - `SingleLetterWitness`: Equation (7), p.8: all cq conditions on one AXYF state, followed by a measurement channel producing B. F and the measured B are not simultaneous registers.
--   - `singleLetterRegion`: Equation (7), p.8: unrestricted finite-dimensional single-letter region.
--   - `boundedSingleLetterRegion`: Remark 1, p.8: single-letter witnesses with a uniform dimension cap.
--   - `steer`: Appendix B.2, pp.20–21: Alice's POVM steers Bob to this unnormalized density. It is Tr_A[(E tensor I)eta], so Alice's discarded quantum output is immaterial.
--   - `PreparationCode`: Definition 1, p.21: remote-state-preparation code with classical side information. The shared state is input-independent; Bob's CPTP decoder depends on (message,y^n).
--   - `preparedOutput`: Definition 1, p.21: conditional prepared output, averaged over the sent message.
--   - `productDensity`: Appendix A, p.17: the tensor product rho_(x^n).
--   - `preparationState`: Equation (19), p.21: the output includes both unaltered classical reference registers.
--   - `preparationTarget`: Equation (19), p.21: the target is the complete n-fold cq state, including X^n,Y^n.
--   - `preparationRates`: Definition 1, p.21: logarithmic message cardinality with vanishing rate slack, and vanishing global trace norm error (not entropy communication cost or per-letter error).
--   - `chshWeights`: Appendix C, pp.24–25: normalized CHSH correlation with uniform independent inputs. The winning probability is (1+bias)/2, hence 0 ≤ bias ≤ 1 is required.
--   - `IsCHSHLaw`: Appendix C, p.24: the CHSH law, packaged with its source-domain normalization. The proof fields are supplied as binders, rather than silently trusting arbitrary bias values.
--   - `averageConditionalEntropy`: Appendix A, p.17: H(F|X) for a cq channel.
--   - `deltaDouble`: Appendix A, p.17: the printed delta-double-prime.
--   - `doubleProjection`: Appendix B.3, p.23: the constructed normalized double projection, not a free poststate.
--   - `flatPurification`: Appendix B.2, p.22: normalized (I tensor P)|Phi>, with coefficients P_(b,a)/sqrt(Tr P).
--   - `preparationFilter`: Appendix B.2, p.22: success Kraus operator Q, including the source's transpose.
--   - `filterKraus`: Appendix B.3, pp.22–23: the two Kraus operators Q and sqrt(I-Q^2), not POVM effects.
--   - `filterBranch`: Appendix B.3, p.23: unnormalized success-branch state on Bob's side.
--   - `moreThanOneProbability`: Appendix B.2–B.3, pp.22,24: probability of at least two successes in m independent binary measurements with success probability t. The m=0 case is also zero.
-- source:
--   On Dimension Bounds for Auxiliary Quantum Systems, arXiv:1207.3911v4, https://arxiv.org/abs/1207.3911v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P27
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P48
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P62

/-! Beigi–Gohari, arXiv:1207.3911v4. All entropies are in bits.
Every auxiliary dimension is finite, but unrestricted unless expressly bounded.
The only nonfinite classical output is the retained flag of Appendix E. -/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P47

-- Accepted definitions: entropy in bits, finite pushforward, real-trace normalization,
-- and Hermitian idempotent projections. No theorem from these papers is used.
open QAlgorithms.Papers.Independent.Information100.P27 (shannon average)
open QAlgorithms.Papers.Independent.Information100.P39 (pushLaw)
open QAlgorithms.Papers.Independent.Information100.P48 (normalize)
open QAlgorithms.Papers.Independent.Information100.P62 (IsProjection)

/-- §2, pp.4–5: normalized finite classical law. -/
structure Law (X : Type) [Fintype X] where
  prob : X → ℝ
  nonneg : ∀ x, 0 ≤ prob x
  total : ∑ x, prob x = 1

/-- §2, p.5: classical channel, normalized at every input. -/
abbrev CChannel (X C : Type) [Fintype C] := X → Law C

/-- §2, p.5: cq channel with positive semidefinite trace-one conditional states. -/
structure QChannel (X D : Type) [Fintype D] where
  rho : X → Matrix D D ℂ
  valid : ∀ x, IsDensityMatrix (rho x)

/-- §2, p.5: block-diagonal density of (f(X),F), including zero-probability blocks. -/
def cqMatrix {X Y D : Type} [Fintype X] [DecidableEq Y]
    (p : X → ℝ) (rho : X → Matrix D D ℂ) (f : X → Y) : Matrix (Y × D) (Y × D) ℂ :=
  fun a b => if a.1 = b.1 then
    ∑ x, if f x = a.1 then (p x : ℂ) * rho x a.2 b.2 else 0 else 0

/-- §2, p.5: H(f(X)|F), computed on the joint cq state. -/
def qCond {X Y D : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D] (p : X → ℝ) (rho : X → Matrix D D ℂ) (f : X → Y) : ℝ :=
  vnEntropy (cqMatrix p rho f) - vnEntropy (average p rho)

/-- §2, p.5: I(f(X);F). -/
def qMI {X Y D : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype D] [DecidableEq D] (p : X → ℝ) (rho : X → Matrix D D ℂ) (f : X → Y) : ℝ :=
  shannon (pushLaw p f) - qCond p rho f

/-- §2, p.5: H(f(X)|C), with the original source law retained. -/
def cCond {X Y C : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype C] [DecidableEq C] (p : X → ℝ) (K : CChannel X C) (f : X → Y) : ℝ :=
  let w : X × C → ℝ := fun z => p z.1 * (K z.1).prob z.2
  shannon (pushLaw w (fun z => (f z.1, z.2))) - shannon (pushLaw w Prod.snd)

/-- §2, p.5: I(f(X);C). -/
def cMI {X Y C : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype C] [DecidableEq C] (p : X → ℝ) (K : CChannel X C) (f : X → Y) : ℝ :=
  shannon (pushLaw p f) - cCond p K f

/-- §2, p.5: I(f(X);F|g(X)) on one simultaneously existing joint state. -/
def qCMI {X Y Z D : Type} [Fintype X] [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z] [Fintype D] [DecidableEq D]
    (p : X → ℝ) (rho : X → Matrix D D ℂ) (f : X → Y) (g : X → Z) : ℝ :=
  shannon (pushLaw p (fun x => (f x, g x))) - shannon (pushLaw p g) -
    qCond p rho (fun x => (f x, g x)) + qCond p rho g

/-- §4, p.9: the finite product alphabet. -/
abbrev Alphabet (m : ℕ) (s : Fin m → ℕ) := (i : Fin m) → Fin (s i)

/-- §4, p.9: classical convexification, including the law coordinate. -/
def classicalHull (m : ℕ) (s : Fin m → ℕ) : Set ((Alphabet m s → ℝ) × (Fin m → ℝ)) :=
  {v | ∃ p : Law (Alphabet m s), ∃ k : ℕ, 0 < k ∧
    ∃ K : CChannel (Alphabet m s) (Fin k), v.1 = p.prob ∧
      ∀ i, v.2 i = cCond p.prob K (fun x => x i)}

/-- §4, p.9: quantum convexification, with all positive finite dimensions. -/
def quantumHull (m : ℕ) (s : Fin m → ℕ) : Set ((Alphabet m s → ℝ) × (Fin m → ℝ)) :=
  {v | ∃ p : Law (Alphabet m s), ∃ d : ℕ, 0 < d ∧
    ∃ Q : QChannel (Alphabet m s) (Fin d), v.1 = p.prob ∧
      ∀ i, v.2 i = qCond p.prob Q.rho (fun x => x i)}

/-- Theorem 3(a1), p.10: all alphabet quantifiers belong inside A1. -/
def AssertionOne : Prop := ∀ (m : ℕ) (s : Fin m → ℕ), (∀ i, 0 < s i) →
  quantumHull m s = classicalHull m s

/-- Theorem 3(a2), p.10: one channel uniformly approximates every input law in absolute error. -/
def AssertionTwo : Prop := ∀ (n d : ℕ), 0 < n → 0 < d →
  ∀ Q : QChannel (Fin n) (Fin d), ∀ eps : ℝ, 0 < eps →
    ∃ k : ℕ, 0 < k ∧ ∃ K : CChannel (Fin n) (Fin k),
      ∀ p : Law (Fin n), |qMI p.prob Q.rho id - cMI p.prob K id| ≤ eps

/-- §4, pp.10–11: quantum objective; F-X-YZ is constructed, not assumed about an arbitrary state. -/
def quantumDifference {n y z d : ℕ} (p : Law (Fin n × Fin y × Fin z))
    (Q : QChannel (Fin n) (Fin d)) : ℝ :=
  qMI p.prob (fun x => Q.rho x.1) (fun x => x.2.1) -
    qMI p.prob (fun x => Q.rho x.1) (fun x => x.2.2)

/-- §4, p.10: the classical objective with C-X-YZ. -/
def classicalDifference {n y z k : ℕ} (p : Law (Fin n × Fin y × Fin z))
    (K : CChannel (Fin n) (Fin k)) : ℝ :=
  cMI p.prob (fun x => K x.1) (fun x => x.2.1) -
    cMI p.prob (fun x => K x.1) (fun x => x.2.2)

/-- Theorem 3(a3), p.10: existence of an attained classical optimizer dominating every
finite quantum auxiliary; no potentially default-valued real supremum is used. -/
def AssertionThree : Prop := ∀ (n y z : ℕ), 0 < n → 0 < y → 0 < z →
  ∀ p : Law (Fin n × Fin y × Fin z), ∃ k : ℕ, 0 < k ∧
    ∃ K : CChannel (Fin n) (Fin k),
      (∀ d : ℕ, 0 < d → ∀ Q : QChannel (Fin n) (Fin d),
        quantumDifference p Q ≤ classicalDifference p K) ∧
      (∀ l : ℕ, 0 < l → ∀ L : CChannel (Fin n) (Fin l),
        classicalDifference p L ≤ classicalDifference p K)

/-- Appendix E, p.28: output (real retained flag, binary outcome). A dominating probability
measure with bounded densities represents the measurable binary-input classical channel. -/
structure FlaggedBinaryChannel where
  reference : Measure (ℝ × Fin 2)
  probability : IsProbabilityMeasure reference
  density : Fin 2 → (ℝ × Fin 2) → ℝ
  measurable : ∀ x, Measurable (density x)
  bounds : ∀ x c, 0 ≤ density x c ∧ density x c ≤ 2
  integrable : ∀ x, Integrable (density x) reference
  normalized : ∀ x, ∫ c, density x c ∂reference = 1
  flagIndependent : ∀ x (S : Set ℝ), MeasurableSet S →
    (∫ c in Prod.fst ⁻¹' S, density x c ∂reference) = (reference (Prod.fst ⁻¹' S)).toReal

/-- Appendix E, p.28: H(X) minus the integral of the posterior binary entropy.
The mixture density is at most two, and posterior entropy is in [0,1], so the
integrand is integrable. A zero mixture density contributes zero even at input endpoints. -/
def flaggedMI (K : FlaggedBinaryChannel) (p : Law (Fin 2)) : ℝ :=
  shannon p.prob - ∫ c, (∑ j, p.prob j * K.density j c) *
    binEntropy2 (p.prob 0 * K.density 0 c / (∑ j, p.prob j * K.density j c)) ∂K.reference

/-- Appendix D, p.26: arbitrary positive finite output sizes, permitting a common flag. -/
structure OutputChannel (n : ℕ) where
  y : ℕ
  z : ℕ
  yPositive : 0 < y
  zPositive : 0 < z
  channel : CChannel (Fin n) (Fin y × Fin z)

/-- Appendix D: induced joint weights. -/
def outputWeights {n : ℕ} (p : Law (Fin n)) (O : OutputChannel n)
    (v : Fin n × (Fin O.y × Fin O.z)) : ℝ := p.prob v.1 * (O.channel v.1).prob v.2

/-- Appendix D: classical difference payoff. -/
def outputClassicalDifference {n c : ℕ} (p : Law (Fin n))
    (K : CChannel (Fin n) (Fin c)) (O : OutputChannel n) : ℝ :=
  cMI (outputWeights p O) (fun v => K v.1) (fun v => v.2.1) -
    cMI (outputWeights p O) (fun v => K v.1) (fun v => v.2.2)

/-- Appendix D: quantum difference payoff. -/
def outputQuantumDifference {n d : ℕ} (p : Law (Fin n))
    (Q : QChannel (Fin n) (Fin d)) (O : OutputChannel n) : ℝ :=
  qMI (outputWeights p O) (fun v => Q.rho v.1) (fun v => v.2.1) -
    qMI (outputWeights p O) (fun v => Q.rho v.1) (fun v => v.2.2)

/-- Lemma 7, p.26: the weighted payoff. -/
def minimaxPayoff {n d M : ℕ} (p : Law (Fin n)) (Q : QChannel (Fin n) (Fin d))
    (K : Fin M → CChannel (Fin n) (Fin n)) (w : Law (Fin M)) (O : OutputChannel n) : ℝ :=
  outputQuantumDifference p Q O - ∑ j, w.prob j * outputClassicalDifference p (K j) O

example {X : Type} [Fintype X] : shannon (fun _ : X => 0) = 0 := by simp [shannon]

example {X D : Type} [Fintype X] (rho : X → Matrix D D ℂ) :
    average (fun _ => 0) rho = 0 := by simp [QAlgorithms.Papers.Independent.Information100.P27.average]

example {X Y D : Type} [Fintype X] [DecidableEq Y]
    (rho : X → Matrix D D ℂ) (f : X → Y) : cqMatrix (fun _ => 0) rho f = 0 := by
  ext a b
  simp [cqMatrix]

/-- §3.1, p.5: classical Gray–Wyner upper region, containing all rates above a tuple. -/
def classicalGW {m : ℕ} {s : Fin m → ℕ} (p : Law (Alphabet m s)) : Set (ℝ × (Fin m → ℝ)) :=
  {r | ∃ k : ℕ, 0 < k ∧ ∃ K : CChannel (Alphabet m s) (Fin k),
    cMI p.prob K id ≤ r.1 ∧ ∀ i, cCond p.prob K (fun x => x i) ≤ r.2 i}

/-- §3.1, p.6: single-quantum-auxiliary outer region, coordinatewise upward closed. -/
def singleQuantumGW {m : ℕ} {s : Fin m → ℕ} (p : Law (Alphabet m s)) : Set (ℝ × (Fin m → ℝ)) :=
  {r | ∃ d : ℕ, 0 < d ∧ ∃ Q : QChannel (Alphabet m s) (Fin d),
    qMI p.prob Q.rho id ≤ r.1 ∧ ∀ i, qCond p.prob Q.rho (fun x => x i) ≤ r.2 i}

/-- §3.1, pp.5–6: partial trace onto factor i of a product-basis register. -/
def factorTrace {m : ℕ} {d : Fin m → ℕ} (i : Fin m)
    (rho : Matrix (Alphabet m d) (Alphabet m d) ℂ) : Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  fun a b => ∑ v : Alphabet m d, if v i = a then rho v (Function.update v i b) else 0

/-- §3.1, p.5: multi-auxiliary region of (3), defined entropically; the operational
characterization attributed to Winter is not asserted as a new theorem here. -/
def multiQuantumGW {m : ℕ} {s : Fin m → ℕ} (p : Law (Alphabet m s)) : Set (ℝ × (Fin m → ℝ)) :=
  {r | ∃ d : Fin m → ℕ, (∀ i, 0 < d i) ∧
    ∃ Q : QChannel (Alphabet m s) (Alphabet m d),
      qMI p.prob Q.rho id ≤ r.1 ∧
        ∀ i, qCond p.prob (fun x => factorTrace i (Q.rho x)) (fun x => x i) ≤ r.2 i}

/-- §3.2, p.6: n outcomes of a finite alphabet. -/
abbrev Sequence (n k : ℕ) := Fin n → Fin k

/-- §3.2, p.6: n-fold product weights of the complete correlation law. -/
def iidCorrelation {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y)) (n : ℕ)
    (v : Sequence n a × Sequence n b × Sequence n x × Sequence n y) : ℝ :=
  ∏ i, p.prob (v.1 i, v.2.1 i, v.2.2.1 i, v.2.2.2 i)

/-- §3.2, p.6: the fixed source marginal p(x,y). -/
def sourceXY {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y)) (v : Fin x × Fin y) : ℝ :=
  ∑ aa : Fin a, ∑ bb : Fin b, p.prob (aa, bb, v.1, v.2)

/-- §3.2, p.7: one-way entanglement-assisted code. Alice's input selects a POVM with
outcomes (a^n,m); Bob's input and m select a POVM with outcomes b^n. The shared density
is fixed independently of both inputs. Alice need not retain a quantum output. -/
structure SimulationCode (n a b x y : ℕ) where
  ea : ℕ
  eb : ℕ
  messages : ℕ
  eaPositive : 0 < ea
  ebPositive : 0 < eb
  messagesPositive : 0 < messages
  shared : Matrix (Fin ea × Fin eb) (Fin ea × Fin eb) ℂ
  sharedValid : IsDensityMatrix shared
  alice : Sequence n x → (Sequence n a × Fin messages) → Matrix (Fin ea) (Fin ea) ℂ
  aliceValid : ∀ xx, IsPOVM (alice xx)
  bob : Fin messages → Sequence n y → Sequence n b → Matrix (Fin eb) (Fin eb) ℂ
  bobValid : ∀ mm yy, IsPOVM (bob mm yy)

/-- §3.2, pp.6–7: the induced complete law; shared entanglement does not depend on x^n,y^n. -/
def simulationWeights {n a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (C : SimulationCode n a b x y)
    (v : Sequence n a × Sequence n b × Sequence n x × Sequence n y) : ℝ :=
  (∏ i, sourceXY p (v.2.2.1 i, v.2.2.2 i)) *
    ∑ mm, effectProb ((C.alice v.2.2.1 (v.1, mm)).kronecker (C.bob mm v.2.2.2 v.2.1)) C.shared

/-- §3.2, p.7: the classical message distribution, marginalized over the input and Alice's output. -/
def messageWeights {n a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (C : SimulationCode n a b x y) (mm : Fin C.messages) : ℝ :=
  ∑ xx : Sequence n x, ∑ yy : Sequence n y,
    (∏ i, sourceXY p (xx i, yy i)) * ∑ aa : Sequence n a,
      effectProb ((C.alice xx (aa, mm)).kronecker (1 : Matrix (Fin C.eb) (Fin C.eb) ℂ)) C.shared

/-- §3.2, pp.6–7: full unhalved l1 error of the complete induced law. -/
def simulationError {n a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (C : SimulationCode n a b x y) : ℝ :=
  ∑ v, |simulationWeights p C v - iidCorrelation p n v|

/-- §3.2, p.7: Rq uses H(M)/n, with no rate slack, and vanishing global l1 error.
The n+1 indexing excludes division by zero without dropping any positive blocklength. -/
def quantumRates {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y)) : Set ℝ :=
  {R | ∃ C : (n : ℕ) → SimulationCode (n + 1) a b x y,
    (∀ n, shannon (messageWeights p (C n)) ≤ R * (n + 1)) ∧
    Tendsto (fun n => simulationError p (C n)) atTop (nhds 0)}

/-- §3.2, pp.6–7: a classical code with arbitrary finite input-independent shared randomness.
The joint encoder includes both Alice's local output and her message. -/
structure ClassicalSimulationCode (n a b x y : ℕ) where
  seeds : ℕ
  messages : ℕ
  seedsPositive : 0 < seeds
  messagesPositive : 0 < messages
  shared : Law (Fin seeds)
  alice : Sequence n x → Fin seeds → Law (Sequence n a × Fin messages)
  bob : Fin messages → Sequence n y → Fin seeds → Law (Sequence n b)

/-- §3.2, p.7: induced classical complete law. -/
def classicalSimulationWeights {n a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (C : ClassicalSimulationCode n a b x y)
    (v : Sequence n a × Sequence n b × Sequence n x × Sequence n y) : ℝ :=
  (∏ i, sourceXY p (v.2.2.1 i, v.2.2.2 i)) *
    ∑ s, ∑ mm, C.shared.prob s * (C.alice v.2.2.1 s).prob (v.1, mm) *
      (C.bob mm v.2.2.2 s).prob v.2.1

/-- §3.2, p.7: message distribution of a classical code. -/
def classicalMessageWeights {n a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (C : ClassicalSimulationCode n a b x y) (mm : Fin C.messages) : ℝ :=
  ∑ xx : Sequence n x, ∑ yy : Sequence n y, (∏ i, sourceXY p (xx i, yy i)) *
    ∑ s, ∑ aa : Sequence n a, C.shared.prob s * (C.alice xx s).prob (aa, mm)

/-- §3.2, pp.6–7: classical simulation rate region, using message entropy and full l1 error. -/
def classicalRates {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y)) : Set ℝ :=
  {R | ∃ C : (n : ℕ) → ClassicalSimulationCode (n + 1) a b x y,
    (∀ n, shannon (classicalMessageWeights p (C n)) ≤ R * (n + 1)) ∧
    Tendsto (fun n => ∑ v, |classicalSimulationWeights p (C n) v -
      iidCorrelation p (n + 1) v|) atTop (nhds 0)}

/-- Equation (7), p.8: the AXY marginal of an approximate complete law. -/
def axyWeights {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (v : Fin a × Fin x × Fin y) : ℝ := ∑ bb : Fin b, p.prob (v.1, bb, v.2.1, v.2.2)

/-- Equation (7), p.8: all cq conditions on one AXYF state, followed by a measurement
channel producing B. F and the measured B are not simultaneous registers. -/
def SingleLetterWitness {a b x y d : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (eps R : ℝ) (t : Law (Fin a × Fin b × Fin x × Fin y))
    (Q : QChannel (Fin a × Fin x × Fin y) (Fin d)) : Prop :=
  (∑ v, |t.prob v - p.prob v|) ≤ eps ∧
  qCMI (axyWeights t) Q.rho (fun v => v.2.1) (fun v => v.2.2) ≤ R ∧
  qCMI (axyWeights t) Q.rho (fun v => v.2.2) (fun v => v.2.1) = 0 ∧
  qCond (axyWeights t) Q.rho (fun v => (v.1, v.2.1)) +
    qCond (axyWeights t) Q.rho (fun v => (v.2.1, v.2.2)) -
    qCond (axyWeights t) Q.rho (fun v => v.2.1) - qCond (axyWeights t) Q.rho id = 0 ∧
  ∃ E : Fin y → Fin b → Matrix (Fin d) (Fin d) ℂ,
    (∀ yy, IsPOVM (E yy)) ∧ ∀ aa bb xx yy,
      t.prob (aa, bb, xx, yy) = axyWeights t (aa, xx, yy) *
        effectProb (E yy bb) (Q.rho (aa, xx, yy))

/-- Equation (7), p.8: unrestricted finite-dimensional single-letter region. -/
def singleLetterRegion {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y)) (eps : ℝ) : Set ℝ :=
  {R | ∃ d : ℕ, 0 < d ∧ ∃ t : Law (Fin a × Fin b × Fin x × Fin y),
    ∃ Q : QChannel (Fin a × Fin x × Fin y) (Fin d), SingleLetterWitness p eps R t Q}

/-- Remark 1, p.8: single-letter witnesses with a uniform dimension cap. -/
def boundedSingleLetterRegion {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (eps : ℝ) (D : ℕ) : Set ℝ :=
  {R | ∃ d : ℕ, 0 < d ∧ d ≤ D ∧ ∃ t : Law (Fin a × Fin b × Fin x × Fin y),
    ∃ Q : QChannel (Fin a × Fin x × Fin y) (Fin d), SingleLetterWitness p eps R t Q}

example {a b x y : ℕ} (p : Law (Fin a × Fin b × Fin x × Fin y))
    (v : Sequence 0 a × Sequence 0 b × Sequence 0 x × Sequence 0 y) :
    iidCorrelation p 0 v = 1 := by simp [iidCorrelation]

/-- Appendix B.2, pp.20–21: Alice's POVM steers Bob to this unnormalized density.
It is Tr_A[(E tensor I)eta], so Alice's discarded quantum output is immaterial. -/
def steer {ea eb : ℕ} (E : Matrix (Fin ea) (Fin ea) ℂ)
    (eta : Matrix (Fin ea × Fin eb) (Fin ea × Fin eb) ℂ) : Matrix (Fin eb) (Fin eb) ℂ :=
  fun b c => ∑ i : Fin ea, ∑ j : Fin ea, E j i * eta (i, b) (j, c)

/-- Definition 1, p.21: remote-state-preparation code with classical side information.
The shared state is input-independent; Bob's CPTP decoder depends on (message,y^n). -/
structure PreparationCode (n x y d : ℕ) where
  ea : ℕ
  eb : ℕ
  messages : ℕ
  eaPositive : 0 < ea
  ebPositive : 0 < eb
  messagesPositive : 0 < messages
  shared : Matrix (Fin ea × Fin eb) (Fin ea × Fin eb) ℂ
  sharedValid : IsDensityMatrix shared
  alice : Sequence n x → Fin messages → Matrix (Fin ea) (Fin ea) ℂ
  aliceValid : ∀ xx, IsPOVM (alice xx)
  bob : Fin messages → Sequence n y → Superop (Fin eb) (Sequence n d)
  bobValid : ∀ mm yy, IsChannel (bob mm yy)

/-- Definition 1, p.21: conditional prepared output, averaged over the sent message. -/
def preparedOutput {n x y d : ℕ} (C : PreparationCode n x y d)
    (xx : Sequence n x) (yy : Sequence n y) : Matrix (Sequence n d) (Sequence n d) ℂ :=
  ∑ mm, C.bob mm yy (steer (C.alice xx mm) C.shared)

/-- Appendix A, p.17: the tensor product rho_(x^n). -/
def productDensity {X D : Type} {n : ℕ} (rho : X → Matrix D D ℂ)
    (xx : Fin n → X) : Matrix (Fin n → D) (Fin n → D) ℂ :=
  fun a b => ∏ i, rho (xx i) (a i) (b i)

/-- Equation (19), p.21: the output includes both unaltered classical reference registers. -/
def preparationState {n x y d : ℕ} (p : Law (Fin x × Fin y)) (C : PreparationCode n x y d) :
    Matrix ((Sequence n x × Sequence n y) × Sequence n d)
      ((Sequence n x × Sequence n y) × Sequence n d) ℂ :=
  fun a b => if a.1 = b.1 then
    ((∏ i, p.prob (a.1.1 i, a.1.2 i) : ℝ) : ℂ) * preparedOutput C a.1.1 a.1.2 a.2 b.2 else 0

/-- Equation (19), p.21: the target is the complete n-fold cq state, including X^n,Y^n. -/
def preparationTarget {n x y d : ℕ} (p : Law (Fin x × Fin y))
    (Q : QChannel (Fin x) (Fin d)) :
    Matrix ((Sequence n x × Sequence n y) × Sequence n d)
      ((Sequence n x × Sequence n y) × Sequence n d) ℂ :=
  fun a b => if a.1 = b.1 then
    ((∏ i, p.prob (a.1.1 i, a.1.2 i) : ℝ) : ℂ) * productDensity Q.rho a.1.1 a.2 b.2 else 0

/-- Definition 1, p.21: logarithmic message cardinality with vanishing rate slack,
and vanishing global trace norm error (not entropy communication cost or per-letter error). -/
def preparationRates {x y d : ℕ} (p : Law (Fin x × Fin y))
    (Q : QChannel (Fin x) (Fin d)) : Set ℝ :=
  {R | 0 ≤ R ∧ ∃ slack : ℕ → ℝ, (∀ n, 0 < slack n) ∧ Tendsto slack atTop (nhds 0) ∧
    ∃ C : (n : ℕ) → PreparationCode (n + 1) x y d,
      (∀ n, Real.logb 2 ((C n).messages : ℝ) ≤ (n + 1) * (R + slack n)) ∧
      Tendsto (fun n => traceNorm (preparationState p (C n) -
        preparationTarget (n := n + 1) p Q)) atTop (nhds 0)}

/-- Appendix C, pp.24–25: normalized CHSH correlation with uniform independent inputs.
The winning probability is (1+bias)/2, hence 0 ≤ bias ≤ 1 is required. -/
def chshWeights (bias : ℝ) (v : Fin 2 × Fin 2 × Fin 2 × Fin 2) : ℝ :=
  if ((v.1.val + v.2.1.val) % 2 = v.2.2.1.val * v.2.2.2.val) then
    (1 + bias) / 16 else (1 - bias) / 16

/-- Appendix C, p.24: the CHSH law, packaged with its source-domain normalization.
The proof fields are supplied as binders, rather than silently trusting arbitrary bias values. -/
def IsCHSHLaw (bias : ℝ) (p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2)) : Prop :=
  ∀ v, p.prob v = chshWeights bias v

example {X D : Type} (rho : X → Matrix D D ℂ) (xx : Fin 0 → X)
    (a b : Fin 0 → D) : productDensity rho xx a b = 1 := by simp [productDensity]

example (p : Law (Fin 2 × Fin 2 × Fin 2 × Fin 2)) (hp : IsCHSHLaw 0 p) :
    p.prob (0, 0, 0, 0) = 1 / 16 := by
  rw [hp]
  norm_num [chshWeights]

/-- Appendix A, p.17: H(F|X) for a cq channel. -/
def averageConditionalEntropy {X D : Type} [Fintype X] [Fintype D] [DecidableEq D]
    (p : Law X) (Q : QChannel X D) : ℝ := ∑ x, p.prob x * vnEntropy (Q.rho x)

/-- Appendix A, p.17: the printed delta-double-prime. -/
def deltaDouble (delta deltaPrime c : ℝ) (alphabet dimension : ℕ) : ℝ :=
  deltaPrime * alphabet * Real.logb 2 dimension + c * delta + alphabet * c * delta * deltaPrime

/-- Appendix B.3, p.23: the constructed normalized double projection, not a free poststate. -/
def doubleProjection {D : Type} [Fintype D] (rho Pc P : Matrix D D ℂ) : Matrix D D ℂ :=
  normalize (P * normalize (Pc * rho * Pc) * P)

/-- Appendix B.2, p.22: normalized (I tensor P)|Phi>, with coefficients P_(b,a)/sqrt(Tr P). -/
def flatPurification {D : Type} [Fintype D] (P : Matrix D D ℂ) : EuclideanSpace ℂ (D × D) :=
  WithLp.toLp 2 (fun v => P v.2 v.1 / (Real.sqrt P.trace.re : ℂ))

/-- Appendix B.2, p.22: success Kraus operator Q, including the source's transpose. -/
def preparationFilter {D : Type} [Fintype D] [DecidableEq D]
    (n : ℕ) (hConditional dd : ℝ) (rho Pc : Matrix D D ℂ) : Matrix D D ℂ :=
  (Real.sqrt ((2 : ℝ) ^ ((n : ℝ) * (hConditional - dd))) : ℂ) •
    (cfc Real.sqrt (Pc * rho * Pc)).transpose

/-- Appendix B.3, pp.22–23: the two Kraus operators Q and sqrt(I-Q^2), not POVM effects. -/
def filterKraus {D : Type} [Fintype D] [DecidableEq D] (Q : Matrix D D ℂ) :
    Fin 2 → Matrix D D ℂ := ![Q, cfc Real.sqrt (1 - Q * Q)]

/-- Appendix B.3, p.23: unnormalized success-branch state on Bob's side. -/
def filterBranch {D : Type} [Fintype D] [DecidableEq D]
    (P Q : Matrix D D ℂ) : Matrix D D ℂ :=
  traceLeft ((Q.kronecker (1 : Matrix D D ℂ)) * pureDensity (flatPurification P) *
    (Q.kronecker (1 : Matrix D D ℂ))ᴴ)

/-- Appendix B.2–B.3, pp.22,24: probability of at least two successes in m independent
binary measurements with success probability t. The m=0 case is also zero. -/
def moreThanOneProbability (m : ℕ) (t : ℝ) : ℝ :=
  1 - (1 - t) ^ m - (m : ℝ) * t * (1 - t) ^ (m - 1)

example (t : ℝ) : moreThanOneProbability 0 t = 0 := by simp [moreThanOneProbability]

example (t : ℝ) : moreThanOneProbability 1 t = 0 := by
  simp [moreThanOneProbability]

example {D : Type} [Fintype D] : normalize (0 : Matrix D D ℂ) = 0 := by simp [QAlgorithms.Papers.Independent.Information100.P48.normalize]

example {D : Type} [Fintype D] [DecidableEq D] : IsProjection (1 : Matrix D D ℂ) := by
  simp [IsProjection]

example : Law (Fin 1) := ⟨fun _ => 1, by intro x; norm_num, by simp⟩

example : QChannel (Fin 1) (Fin 1) :=
  ⟨fun _ => 1, fun _ => ⟨Matrix.PosSemidef.one, by simp⟩⟩

/-- Changing the desired correlation without changing its input marginal leaves the
law produced by a fixed physical simulation code unchanged (§3.2, pp.6–7). -/
example {n a b x y : ℕ} (p q : Law (Fin a × Fin b × Fin x × Fin y))
    (h : sourceXY p = sourceXY q) (C : SimulationCode n a b x y) :
    simulationWeights p C = simulationWeights q C := by
  funext v
  simp only [simulationWeights, h]

/-- Classical references have no off-diagonal blocks in the prepared state (p.21). -/
example {n x y d : ℕ} (p : Law (Fin x × Fin y)) (C : PreparationCode n x y d)
    (a b : (Sequence n x × Sequence n y) × Sequence n d) (h : a.1 ≠ b.1) :
    preparationState p C a b = 0 := by simp [preparationState, h]

example {D : Type} [Fintype D] [DecidableEq D] :
    filterKraus (0 : Matrix D D ℂ) 1 = 1 := by simp [filterKraus, cfc_one]

end QAlgorithms.Papers.Independent.Dependency50.P47



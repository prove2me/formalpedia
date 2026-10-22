-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P30
-- name    : QAlgorithms_Papers_Independent_Gap48_P30
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-22T04:14:10.732052+00:00
-- url     : https://prove2.me/theorems/385177c4-5940-4c91-91f3-1b61966a28e5
-- title:
--   Definitions for Majorization theory approach to the Gaussian channel minimum entropy conjecture
-- statement:
--   The objects the formalized statements of *Majorization theory approach to the Gaussian channel minimum entropy conjecture* (arXiv:1111.1986) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `loss`: PDF pp.2,5: vacuum-environment loss, specified by its accepted Kraus sum. The unique trace-norm sum is selected; theorems conclude existence of that sum.
--   - `phaseChannel`: PDF p.2, (4)-(5): the Gaussian channel is characterized on Weyl operators, not defined as the concatenation whose equality is to be proved. Vacuum covariance is I, so added noise nu contributes exp(-nu |z|^2/2).
--   - `intensityGain`: PDF pp.3,6: intensity gain, with lambda=tanh r and G=cosh(r)^2.
--   - `squeezing`: PDF pp.2,5-6: physical vacuum amplifier dilation, assembled from the accepted amplifier Kraus operators, with system first and environment second. It is not defined by a proposed Fock output vector. The coefficient and isometry properties are explicit conclusions of squeezing_schmidt below.
--   - `squeezed`: PDF pp.3,6, (11),(A.7): actual output for input |k> and vacuum environment.
--   - `fockSchmidtWeight`: PDF pp.3,6, (12),(A.17): indexed squared Schmidt weights, not sorted.
--   - `firstMarginal`: PDF pp.2,5: first marginal of a pure two-mode vector, through the actual partial-trace coefficients. Theorems conclude realization and density.
--   - `squeezingEntanglement`: PDF pp.2-3,5: pure-state entanglement, allowing infinite entropy, in nats.
--   - `ZeroMean`: PDF p.2: zero annihilation expectation only when its defining series exists. No global photon-energy assumption is added to any conjecture.
--   - `Conjecture1`: PDF p.2, C1: all phase-insensitive parameters precede every candidate input; there is no finite-energy, Gaussian-input, or optimizer-attainment restriction.
--   - `Conjecture2`: PDF p.2, C2: vacuum minimizes amplifier output entropy on centered pure inputs.
--   - `Conjecture3`: PDF p.2, C3: the same claim as a two-mode output entanglement minimum.
--   - `Conjecture4`: PDF p.3, C4: the conjectured majorization of the actual output marginals; exclusion of the vacuum is phrased on its density, hence ignores global phase.
--   - `ProbabilityLaw`: PDF p.5: a normalized countable probability law, including convergence.
--   - `largestMass`: PDF p.5, (A.2): mass of the q largest entries. The supremum over finite subsets is independent of the enumeration and is exactly the decreasing partial sum. ENNReal avoids empty or unbounded real-supremum defaults.
--   - `ProbabilityMajorizes`: PDF pp.3,5: decreasing-partial-sum majorization, with both laws normalized.
--   - `CountableSubunitalStochastic`: PDF p.5: the infinite stochastic witness has columns summing to one and rows summing to at most one, with all entries nonnegative.
--   - `fockKernel`: PDF pp.6-7, (A.24)-(A.27): actual arbitrary-increment kernel. The printed binomial choose(m+d-1,d-1) in A.27 is corrected to choose(n-m+d-1,d-1), forced by A.25 and the displayed D^2,D^3,D^4. d=0 is separately identity.
--   - `schmidtEntropy`: PDF pp.3-4,7: entropy of the squared Schmidt law, retaining infinity.
--   - `parity`: PDF p.3: parity in the complete number basis, for the Wigner function.
--   - `fockWignerFunction`: PDF p.3: Wigner distribution in complex phase-space coordinates, W_rho(alpha)=2/pi Tr[D(2 alpha) parity rho]. This bounded trace pairing exists for every trace-class state even when the Wigner function is not integrable.
--   - `Isotropic`: PDF p.3: isotropy means rotation invariance of the Wigner distribution.
--   - `tensorOp`: PDF pp.9-10: genuine tensor product of two bounded local operators. Every protocol predicate includes its matrix realization; no zero fallback can witness a physical transformation.
--   - `TensorRealized`: PDF pp.9-10: realization of a physical local tensor operation.
--   - `downShift`: PDF p.9, (A.54),(A.56): downward partial shift on its occupied support.
--   - `aliceKraus`: PDF p.9: CPTP extension to Alice's whole Hilbert space. The zeroth Kraus operator is the displayed shift; the remaining q operators reset its missing finite-dimensional support to vacuum. They vanish on the occupied support.
--   - `decrementWeight`: PDF p.9, (A.52),(A.55): Bob's outcome law. d=0 is the identity instrument.
--   - `decrementMatrix`: PDF p.9, (A.52),(A.55): explicit Bob measurement matrix. The denominator is positive for 0<lambda<1, the domain of the decrement theorems.
--   - `decrementBob`: PDF p.9: bounded local Kraus operator with the displayed matrix.
--   - `FockDecrementProtocol`: PDF p.9: deterministic one-way countable LOCC, with Bob's complete instrument, classical outcome m sent to Alice, and Alice's complete conditional instrument. Every branch is an unnormalized multiple of the target; normalization is never asserted for a zero-probability outcome.
--   - `countProbability`: PDF pp.9-10, (A.62): photon-count distribution. The direct splitter law covers T=0 and T=1 without intermediate (1-T)/T expressions.
--   - `countBranch`: PDF p.10, (A.63): actual unnormalized photon-count branch, with Bob's vacuum-environment splitter Kraus operator. Reflected phases are positive.
--   - `heterodyneMatrix`: PDF p.10: Bob's splitter followed by heterodyne detection of the reflected mode. The coherent bra contributes conjugate(z)^(n-m); density is relative to d^2z/pi. This fixes the physical instrument independently of the target.
--   - `heterodyneBob`: PDF p.10: bounded heterodyne branch operator on Bob's retained mode.
--   - `gaussianBranch`: PDF p.10: conditional displacements, with conjugation on Alice's outcome coordinate due to EPR correlations. The complex gains are to be constructed.
--   - `resetKraus`: PDF p.10: countable local preparation of |k>, including the zero-squeezing endpoint of the deterministic protocol. No shared resource is required.
--   - `ResetProtocol`: PDF p.10: independent local resets on Alice and Bob, a deterministic LOCC.
--   - `reductionTerminal`: PDF p.10: after photon-count ell, Bob performs the ell-photon decrement instrument at the target squeezing; he sends (ell,m) to Alice, who applies its complete shift extension. Every terminal outcome remains countable.
--   - `SqueezingReductionProtocol`: PDF p.10: exact deterministic adaptive three-step protocol, rather than an unrestricted LOCC existence predicate. Completeness holds on the whole local space and the total norm of terminal branches is one.
-- source:
--   Majorization theory approach to the Gaussian channel minimum entropy conjecture, arXiv:1111.1986v1, https://arxiv.org/abs/1111.1986v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39

/-!
arXiv:1111.1986v1, single use of one bosonic mode on the complete Fock space.
The two accepted imports supply actual bounded Kraus operators, trace-class
states, and extended spectral entropy in nats. New constructions are paper-local.
Realization and normalization are conclusions, never assumed answers.
Compilation is pending the authorized batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P30

open Filter MeasureTheory
open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace D
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator BipartiteFock BipartiteOperator fockKet fockDyad bipartiteKet
   IsDensity IsTraceClass HasFockMatrix operatorOfMatrix TraceHasSum krausTerm
   KrausComplete KrausWellDefined amplifierKraus amplifierMatrix AmplifierRealized
   attenuatorKraus attenuatorMatrix AttenuatorRealized coherentProjector
   CoherentRealized characteristic displacement DisplacementRealized coherentMeasure)
end D

namespace C
export QAlgorithms.Papers.Independent.Claimed50.P39
  (amplifier fockEntropyNats minimumEntropy pureMinimumEntropy pureState
   IsNormalFockChannel Majorizes fockPhaseRotation conjugateBy)
end C

/-- PDF pp.2,5: vacuum-environment loss, specified by its accepted Kraus sum.
The unique trace-norm sum is selected; theorems conclude existence of that sum. -/
def loss (T : ℝ) (X : D.FockOperator) : D.FockOperator :=
  if h : ∃ Y : D.FockOperator,
      D.TraceHasSum (fun j => D.krausTerm (D.attenuatorKraus (Real.sqrt T) j) X) Y
  then Classical.choose h else 0

/-- PDF p.2, (4)-(5): the Gaussian channel is characterized on Weyl operators,
not defined as the concatenation whose equality is to be proved. Vacuum
covariance is I, so added noise nu contributes exp(-nu |z|^2/2). -/
def phaseChannel (tau nu : ℝ) (X : D.FockOperator) : D.FockOperator :=
  if h : ∃ Y : D.FockOperator, D.IsTraceClass Y ∧ ∀ z : ℂ,
      D.characteristic Y z =
        D.characteristic X ((Real.sqrt tau : ℂ) * z) *
          Complex.exp (-(nu * Complex.normSq z / 2 : ℝ))
  then Classical.choose h else 0

/-- PDF pp.3,6: intensity gain, with lambda=tanh r and G=cosh(r)^2. -/
def intensityGain (lambda : ℝ) : ℝ := 1 / (1 - lambda ^ 2)

/-- PDF pp.2,5-6: physical vacuum amplifier dilation, assembled from the
accepted amplifier Kraus operators, with system first and environment second.
It is not defined by a proposed Fock output vector. The coefficient and
isometry properties are explicit conclusions of squeezing_schmidt below. -/
def squeezing (lambda : ℝ) : D.Fock →L[ℂ] D.BipartiteFock :=
  if h : ∃ V : D.Fock →L[ℂ] D.BipartiteFock, ∀ u a b,
      V u (a, b) = D.amplifierKraus (Real.sqrt (intensityGain lambda)) b u a
  then Classical.choose h else 0

/-- PDF pp.3,6, (11),(A.7): actual output for input |k> and vacuum environment. -/
def squeezed (k : ℕ) (lambda : ℝ) : D.BipartiteFock :=
  squeezing lambda (D.fockKet k)

/-- PDF pp.3,6, (12),(A.17): indexed squared Schmidt weights, not sorted. -/
def fockSchmidtWeight (k : ℕ) (lambda : ℝ) (n : ℕ) : ℝ :=
  (1 - lambda ^ 2) ^ (k + 1) * lambda ^ (2 * n) * (Nat.choose (n + k) n : ℝ)

/-- PDF pp.2,5: first marginal of a pure two-mode vector, through the actual
partial-trace coefficients. Theorems conclude realization and density. -/
def firstMarginal (psi : D.BipartiteFock) : D.FockOperator :=
  D.operatorOfMatrix (fun a c => ∑' b : ℕ, psi (a, b) * star (psi (c, b)))

/-- PDF pp.2-3,5: pure-state entanglement, allowing infinite entropy, in nats. -/
def squeezingEntanglement (psi : D.BipartiteFock) : ℝ≥0∞ :=
  C.fockEntropyNats (firstMarginal psi)

/-- PDF p.2: zero annihilation expectation only when its defining series exists.
No global photon-energy assumption is added to any conjecture. -/
def ZeroMean (u : D.Fock) : Prop :=
  HasSum (fun n : ℕ => (Real.sqrt (n + 1 : ℝ) : ℂ) *
    star (u n) * u (n + 1)) 0

/-- PDF p.2, C1: all phase-insensitive parameters precede every candidate input;
there is no finite-energy, Gaussian-input, or optimizer-attainment restriction. -/
def Conjecture1 : Prop :=
  ∀ tau nu : ℝ, 0 ≤ tau → |tau - 1| ≤ nu → ∀ alpha : ℂ,
    ∀ X : D.FockOperator, D.IsDensity X →
      C.fockEntropyNats (phaseChannel tau nu (D.coherentProjector alpha)) ≤
        C.fockEntropyNats (phaseChannel tau nu X)

/-- PDF p.2, C2: vacuum minimizes amplifier output entropy on centered pure inputs. -/
def Conjecture2 : Prop :=
  ∀ G : ℝ, 1 ≤ G → ∀ u : D.Fock, ‖u‖ = 1 → ZeroMean u →
    C.fockEntropyNats (C.amplifier G (D.fockDyad 0 0)) ≤
      C.fockEntropyNats (C.amplifier G (C.pureState u))

/-- PDF p.2, C3: the same claim as a two-mode output entanglement minimum. -/
def Conjecture3 : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ u : D.Fock, ‖u‖ = 1 → ZeroMean u →
    squeezingEntanglement (squeezed 0 (Real.tanh r)) ≤
      squeezingEntanglement (squeezing (Real.tanh r) u)

/-- PDF p.3, C4: the conjectured majorization of the actual output marginals;
exclusion of the vacuum is phrased on its density, hence ignores global phase. -/
def Conjecture4 : Prop :=
  ∀ r : ℝ, 0 ≤ r → ∀ u : D.Fock, ‖u‖ = 1 → ZeroMean u →
    C.pureState u ≠ D.fockDyad 0 0 →
    C.Majorizes (firstMarginal (squeezed 0 (Real.tanh r)))
      (firstMarginal (squeezing (Real.tanh r) u))

/-- PDF p.5: a normalized countable probability law, including convergence. -/
def ProbabilityLaw (p : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ p n) ∧ HasSum p 1

/-- PDF p.5, (A.2): mass of the q largest entries. The supremum over finite
subsets is independent of the enumeration and is exactly the decreasing
partial sum. ENNReal avoids empty or unbounded real-supremum defaults. -/
def largestMass (p : ℕ → ℝ) (q : ℕ) : ℝ≥0∞ :=
  ⨆ s : {s : Finset ℕ // s.card ≤ q}, ∑ n ∈ s.val, ENNReal.ofReal (p n)

/-- PDF pp.3,5: decreasing-partial-sum majorization, with both laws normalized. -/
def ProbabilityMajorizes (p q : ℕ → ℝ) : Prop :=
  ProbabilityLaw p ∧ ProbabilityLaw q ∧ ∀ j, largestMass q j ≤ largestMass p j

/-- PDF p.5: the infinite stochastic witness has columns summing to one and
rows summing to at most one, with all entries nonnegative. -/
def CountableSubunitalStochastic (Dmat : ℕ → ℕ → ℝ) : Prop :=
  (∀ n m, 0 ≤ Dmat n m) ∧
    (∀ m, HasSum (fun n => Dmat n m) 1) ∧
    (∀ n, Summable (Dmat n) ∧ (∑' m, Dmat n m) ≤ 1)

/-- PDF pp.6-7, (A.24)-(A.27): actual arbitrary-increment kernel. The printed
binomial choose(m+d-1,d-1) in A.27 is corrected to choose(n-m+d-1,d-1),
forced by A.25 and the displayed D^2,D^3,D^4. d=0 is separately identity. -/
def fockKernel (d : ℕ) (lambda : ℝ) (n m : ℕ) : ℝ :=
  if d = 0 then (if n = m then 1 else 0) else
    if m ≤ n then (1 - lambda ^ 2) ^ d *
      (Nat.choose (n - m + d - 1) (d - 1) : ℝ) * lambda ^ (2 * (n - m))
    else 0

/-- PDF pp.3-4,7: entropy of the squared Schmidt law, retaining infinity. -/
def schmidtEntropy (k : ℕ) (lambda : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, ENNReal.ofReal (-fockSchmidtWeight k lambda n * Real.log (fockSchmidtWeight k lambda n))

/-- PDF p.3: parity in the complete number basis, for the Wigner function. -/
def parity : D.FockOperator :=
  D.operatorOfMatrix (fun m n => if m = n then (-1 : ℂ) ^ n else 0)

/-- PDF p.3: Wigner distribution in complex phase-space coordinates,
W_rho(alpha)=2/pi Tr[D(2 alpha) parity rho]. This bounded trace pairing exists
for every trace-class state even when the Wigner function is not integrable. -/
def fockWignerFunction (X : D.FockOperator) (alpha : ℂ) : ℝ :=
  2 / Real.pi * (D.characteristic (parity.comp X) (2 * alpha)).re

/-- PDF p.3: isotropy means rotation invariance of the Wigner distribution. -/
def Isotropic (X : D.FockOperator) : Prop :=
  ∀ theta : ℝ, ∀ alpha : ℂ,
    fockWignerFunction X (Complex.exp (Complex.I * (theta : ℂ)) * alpha) = fockWignerFunction X alpha

/-- PDF pp.9-10: genuine tensor product of two bounded local operators.
Every protocol predicate includes its matrix realization; no zero fallback
can witness a physical transformation. -/
def tensorOp (A B : D.FockOperator) : D.BipartiteOperator :=
  if h : ∃ V : D.BipartiteOperator, ∀ a b c d : ℕ,
      V (D.bipartiteKet (c, d)) (a, b) = A (D.fockKet c) a * B (D.fockKet d) b
  then Classical.choose h else 0

/-- PDF pp.9-10: realization of a physical local tensor operation. -/
def TensorRealized (A B : D.FockOperator) : Prop :=
  ∀ a b c d : ℕ, tensorOp A B (D.bipartiteKet (c, d)) (a, b) =
    A (D.fockKet c) a * B (D.fockKet d) b

/-- PDF p.9, (A.54),(A.56): downward partial shift on its occupied support. -/
def downShift (q : ℕ) : D.FockOperator :=
  D.operatorOfMatrix (fun m n => if n = m + q then 1 else 0)

/-- PDF p.9: CPTP extension to Alice's whole Hilbert space. The zeroth Kraus
operator is the displayed shift; the remaining q operators reset its missing
finite-dimensional support to vacuum. They vanish on the occupied support. -/
def aliceKraus (q : ℕ) : ℕ → D.FockOperator
  | 0 => downShift q
  | j + 1 => if j < q then D.fockDyad 0 j else 0

/-- PDF p.9, (A.52),(A.55): Bob's outcome law. d=0 is the identity instrument. -/
def decrementWeight (d : ℕ) (lambda : ℝ) (m : ℕ) : ℝ :=
  if d = 0 then (if m = 0 then 1 else 0) else
    (1 - lambda ^ 2) ^ d * (Nat.choose (m + d - 1) (d - 1) : ℝ) * lambda ^ (2 * m)

/-- PDF p.9, (A.52),(A.55): explicit Bob measurement matrix. The denominator
is positive for 0<lambda<1, the domain of the decrement theorems. -/
def decrementMatrix (k d : ℕ) (lambda : ℝ) (m a b : ℕ) : ℂ :=
  if b = a + m then
    (Real.sqrt (decrementWeight d lambda m * fockSchmidtWeight k lambda a /
      fockSchmidtWeight (k + d) lambda b) : ℂ) else 0

/-- PDF p.9: bounded local Kraus operator with the displayed matrix. -/
def decrementBob (k d : ℕ) (lambda : ℝ) (m : ℕ) : D.FockOperator :=
  D.operatorOfMatrix (decrementMatrix k d lambda m)

/-- PDF p.9: deterministic one-way countable LOCC, with Bob's complete
instrument, classical outcome m sent to Alice, and Alice's complete conditional
instrument. Every branch is an unnormalized multiple of the target; normalization
is never asserted for a zero-probability outcome. -/
def FockDecrementProtocol (k d : ℕ) (lambda : ℝ) : Prop :=
  let psi := squeezed (k + d) lambda
  let phi := squeezed k lambda
  ‖psi‖ = 1 ∧ ‖phi‖ = 1 ∧
  D.KrausComplete (decrementBob k d lambda) ∧
  (∀ m, D.HasFockMatrix (decrementBob k d lambda m) (decrementMatrix k d lambda m)) ∧
  (∀ m, D.KrausComplete (aliceKraus (m + d))) ∧
  (∀ m, D.HasFockMatrix (downShift (m + d))
    (fun a b => if b = a + (m + d) then 1 else 0)) ∧
  (∀ m, TensorRealized 1 (decrementBob k d lambda m)) ∧
  (∀ m i, TensorRealized (aliceKraus (m + d) i) (decrementBob k d lambda m)) ∧
  HasSum (fun m => ‖tensorOp 1 (decrementBob k d lambda m) psi‖ ^ 2) 1 ∧
  (∀ m, ‖tensorOp 1 (decrementBob k d lambda m) psi‖ ^ 2 = decrementWeight d lambda m) ∧
  (∀ m, tensorOp (downShift (m + d)) (decrementBob k d lambda m) psi =
    (Real.sqrt (decrementWeight d lambda m) : ℂ) • phi) ∧
  (∀ m i, ∃ c : ℂ, tensorOp (aliceKraus (m + d) i)
    (decrementBob k d lambda m) psi = c • phi)

/-- PDF pp.9-10, (A.62): photon-count distribution. The direct splitter law
covers T=0 and T=1 without intermediate (1-T)/T expressions. -/
def countProbability (k : ℕ) (lambda T : ℝ) (ell : ℕ) : ℝ :=
  ((1 - T) * lambda ^ 2) ^ ell * (Nat.choose (k + ell) ell : ℝ) *
    (1 - lambda ^ 2) ^ (k + 1) / (1 - T * lambda ^ 2) ^ (k + ell + 1)

/-- PDF p.10, (A.63): actual unnormalized photon-count branch, with Bob's
vacuum-environment splitter Kraus operator. Reflected phases are positive. -/
def countBranch (k : ℕ) (lambda T : ℝ) (ell : ℕ) : D.BipartiteFock :=
  tensorOp 1 (D.attenuatorKraus (Real.sqrt T) ell) (squeezed k lambda)

/-- PDF p.10: Bob's splitter followed by heterodyne detection of the reflected
mode. The coherent bra contributes conjugate(z)^(n-m); density is relative to
d^2z/pi. This fixes the physical instrument independently of the target. -/
def heterodyneMatrix (T : ℝ) (z : ℂ) (m n : ℕ) : ℂ :=
  if m ≤ n then
    (Real.exp (-Complex.normSq z / 2) * Real.sqrt (Nat.choose n (n - m) : ℝ) *
      Real.sqrt (1 - T) ^ (n - m) * Real.sqrt T ^ m /
      Real.sqrt (Nat.factorial (n - m) : ℝ) : ℝ) * star z ^ (n - m)
  else 0

/-- PDF p.10: bounded heterodyne branch operator on Bob's retained mode. -/
def heterodyneBob (T : ℝ) (z : ℂ) : D.FockOperator :=
  D.operatorOfMatrix (heterodyneMatrix T z)

/-- PDF p.10: conditional displacements, with conjugation on Alice's outcome
coordinate due to EPR correlations. The complex gains are to be constructed. -/
def gaussianBranch (lambda T : ℝ) (a b : ℂ) (z : ℂ) : D.BipartiteFock :=
  tensorOp (D.displacement (a * star z)) (D.displacement (b * z))
    (tensorOp 1 (heterodyneBob T z) (squeezed 0 lambda))

/-- PDF p.10: countable local preparation of |k>, including the zero-squeezing
endpoint of the deterministic protocol. No shared resource is required. -/
def resetKraus (k : ℕ) (n : ℕ) : D.FockOperator := D.fockDyad k n

/-- PDF p.10: independent local resets on Alice and Bob, a deterministic LOCC. -/
def ResetProtocol (k : ℕ) (psi phi : D.BipartiteFock) : Prop :=
  ‖psi‖ = 1 ∧ ‖phi‖ = 1 ∧
  D.KrausComplete (resetKraus k) ∧ D.KrausComplete (resetKraus 0) ∧
  (∀ a b, TensorRealized (resetKraus k a) (resetKraus 0 b)) ∧
  HasSum (fun ab : ℕ × ℕ =>
    ‖tensorOp (resetKraus k ab.1) (resetKraus 0 ab.2) psi‖ ^ 2) 1 ∧
  ∀ a b, ∃ c : ℂ, tensorOp (resetKraus k a) (resetKraus 0 b) psi = c • phi

/-- PDF p.10: after photon-count ell, Bob performs the ell-photon decrement
instrument at the target squeezing; he sends (ell,m) to Alice, who applies
its complete shift extension. Every terminal outcome remains countable. -/
def reductionTerminal (k : ℕ) (lambda target T : ℝ) (idx : ℕ × ℕ × ℕ) :
    D.BipartiteFock :=
  tensorOp (aliceKraus (idx.2.1 + idx.1) idx.2.2) 1
    (tensorOp 1 (decrementBob k idx.1 target idx.2.1)
      (countBranch k lambda T idx.1))

/-- PDF p.10: exact deterministic adaptive three-step protocol, rather than
an unrestricted LOCC existence predicate. Completeness holds on the whole local
space and the total norm of terminal branches is one. -/
def SqueezingReductionProtocol (k : ℕ) (lambda target T : ℝ) : Prop :=
  ‖squeezed k lambda‖ = 1 ∧ ‖squeezed k target‖ = 1 ∧
  D.AttenuatorRealized (Real.sqrt T) ∧
  D.KrausComplete (D.attenuatorKraus (Real.sqrt T)) ∧
  (∀ ell, FockDecrementProtocol k ell target) ∧
  (∀ ell, TensorRealized 1 (D.attenuatorKraus (Real.sqrt T) ell)) ∧
  (∀ ell m, TensorRealized 1 (decrementBob k ell target m)) ∧
  (∀ ell m i, TensorRealized (aliceKraus (m + ell) i) 1) ∧
  HasSum (fun idx : ℕ × ℕ × ℕ => ‖reductionTerminal k lambda target T idx‖ ^ 2) 1 ∧
  ∀ idx : ℕ × ℕ × ℕ, ∃ c : ℂ,
    reductionTerminal k lambda target T idx = c • squeezed k target

example (k : ℕ) : fockSchmidtWeight k 0 0 = 1 := by simp [fockSchmidtWeight]

example (k n : ℕ) : fockSchmidtWeight k 0 (n + 1) = 0 := by simp [fockSchmidtWeight]

example (lambda : ℝ) (n m : ℕ) : fockKernel 0 lambda n m = (if n = m then 1 else 0) := by
  simp [fockKernel]

example (lambda : ℝ) (m : ℕ) : decrementWeight 0 lambda m = (if m = 0 then 1 else 0) := by
  simp [decrementWeight]

example (q : ℕ) : aliceKraus q 0 = downShift q := rfl

example (k : ℕ) (T : ℝ) : countProbability k 0 T 0 = 1 := by
  simp [countProbability]

example : intensityGain 0 = 1 := by norm_num [intensityGain]

example (z : ℂ) (n : ℕ) : heterodyneMatrix 1 z n n =
    (Real.exp (-Complex.normSq z / 2) : ℂ) := by
  simp [heterodyneMatrix]

end QAlgorithms.Papers.Independent.Gap48.P30



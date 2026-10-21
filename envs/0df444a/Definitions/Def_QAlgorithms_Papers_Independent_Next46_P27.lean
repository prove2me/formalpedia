-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P27
-- name    : QAlgorithms_Papers_Independent_Next46_P27
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T15:19:34.25081+00:00
-- url     : https://prove2.me/theorems/87e56187-dc38-470c-8712-14c2f1525bf1
-- title:
--   Definitions for The bosonic minimum output entropy conjecture and Lagrangian minimization
-- statement:
--   The objects the formalized statements of *The bosonic minimum output entropy conjecture and Lagrangian minimization* (arXiv:0906.2758) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `energy`: PDF pp.2,4: extended mean number on densities; infinite energy stays infinite.
--   - `gibbsMean`: PDF p.4, Eq.(12): Gibbs mean for beta>0; beta=0 is not an allowed input.
--   - `outputBeta`: PDF p.4, Eq.(13): output inverse temperature at exact added variance v.
--   - `numberDomain`: PDF pp.2,4: Number's operator domain, distinct from its first-moment form domain.
--   - `numberGraph`: PDF pp.2,4: actual unbounded Number, represented by its graph, never a bounded operator.
--   - `numberForm`: PDF pp.2,4: extended nonnegative number form, including infinite first moment.
--   - `formDomain`: PDF pp.2–4: finite-value form domain. This is not Number's operator domain.
--   - `displacedNumberForm`: PDF pp.2–4: displacement transports the number form by D(-alpha).
--   - `logTruncation`: PDF pp.3–4: bounded spectral truncation of -log X. On a zero eigenvalue this equals K, rather than the total Real.log(0) default.
--   - `negativeLogForm`: PDF pp.3–4: actual extended spectral form of -log X on densities. The supremum is over monotone bounded spectral truncations, not Fock cutoffs.
--   - `negativeLogGraph`: PDF pp.3–4: associated unbounded negative-log operator graph via strong spectral-truncation limits. It does not use a bounded-operator logarithm.
--   - `noisePullback`: PDF p.2, Eq.(1): actual positive integral giving extended Heisenberg action. D(-mu) is the adjoint displacement in the primal conjugation.
--   - `IsClosedForm`: PDF pp.3–4: closed densely defined nonnegative Hermitian quadratic forms. Closedness is lower semicontinuity of the extended form on the Hilbert space.
--   - `ThermalStationary`: PDF p.3, Eq.(8), full-space thermal witnesses. The Hermitian multiplier is represented as L-cI with L a closed nonnegative form and c real. Its actual pullback is noisePullback(L)-cI. All signed equations are evaluated on the common finite form domain, with domain equalities and closedness explicitly required. These are equations plus feasibility, not a definition of local minimality. The displacement parameter retains Section IV's displaced thermal solutions.
--   - `FixedEntropyLocalMinimum`: PDF pp.1–4: fixed-input-entropy local minimum of an extended objective, in trace-norm density neighborhoods. Nuclearity guards the infimum defining the norm.
--   - `LocalOutputMinimum`: PDF p.2: fixed-entropy output-entropy objective for the exact channel.
--   - `entropyIncrement`: PDF pp.2–3,5: entropy increment, used only when input entropy is finite. Truncated subtraction is valid because this random-unitary channel increases entropy.
--   - `entropyQuotient`: PDF pp.2–3: positive-time extended quotient; t>0 is imposed at every use.
--   - `entropyRate`: PDF pp.2–3: total lower right Dini rate on finite-entropy densities. Boundary theorems additionally assert the genuine limit, not just a liminf.
--   - `InfinitesimalConjecture`: PDF pp.1–2: infinitesimal conjecture as a proposition, including its separate zero-entropy thermal endpoint. All finite input entropies occur; no energy photonCutoffProjection.
--   - `PureLocalOutputMinimum`: PDF pp.4–5: pure-input version of local minimality; the state is explicitly represented by a unit vector. No normalization is inferred from a free ket.
--   - `orbitPoint`: PDF p.2: displacement orbit; the parameter is complex phase-space displacement.
--   - `TraceContinuous`: PDF p.2: continuity into trace-norm density space, expressed by epsilon-delta conditions to avoid the ambient operator-norm topology on bounded operators.
--   - `photonCutoffProjection`: PDF p.5, Appendix 1: projection onto the N-dimensional span of levels j<N.
--   - `photonCutoffCompression`: PDF p.5: raw compression; it is not presumed to have trace one.
--   - `retainedMass`: PDF p.5: retained probability mass in the photon cutoff.
--   - `normalizedCompression`: PDF p.5: normalized compression is used only with a positive-mass witness.
--   - `finiteDensities`: PDF p.5: finite density domain for entropy continuity; entropy itself is reused in nats.
--   - `finiteInterior`: PDF p.5: relative open interior of the trace-one Hermitian affine space.
-- source:
--   The bosonic minimum output entropy conjecture and Lagrangian minimization, arXiv:0906.2758v3, https://arxiv.org/abs/0906.2758v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P36

/-!
arXiv:0906.2758v3. One full countable oscillator; natural-log entropy.
Local neighborhoods below use the nuclear trace norm, not the ambient operator norm.
The instantaneous rate is the lower right Dini extension; divergence additionally
asserts an actual positive-time limit. Conjectures are never asserted outright.
Compilation is pending the batch handoff.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P27

open Filter MeasureTheory
open scoped Topology ENNReal ComplexOrder Matrix.Norms.L2Operator

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad IsDensity IsTraceClass nuclearTraceNorm
   displacement HasFockMatrix photonMean photonProbability fockTrace)
end B

namespace A
export QAlgorithms.Papers.Independent.Claimed50.P39
  (g photonMeanThermalState conjugateBy displacementNoiseChannel fockEntropyNats
   pureState meanA FiniteEnergy ClassicalEntropyConjecture)
end A

attribute [local instance] Classical.propDecidable

-- Mathlib deliberately leaves the general C*-algebra calculus opt-in.
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

/-- PDF pp.2,4: extended mean number on densities; infinite energy stays infinite. -/
def energy (rho : B.FockOperator) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal ((j : ℝ) * B.photonProbability rho j)

/-- PDF p.4, Eq.(12): Gibbs mean for beta>0; beta=0 is not an allowed input. -/
def gibbsMean (beta : ℝ) : ℝ := (Real.exp beta - 1)⁻¹

/-- PDF p.4, Eq.(13): output inverse temperature at exact added variance v. -/
def outputBeta (beta v : ℝ) : ℝ := Real.log (1 + (gibbsMean beta + v)⁻¹)

/-- PDF pp.2,4: Number's operator domain, distinct from its first-moment form domain. -/
def numberDomain : Set B.Fock :=
  {u | Summable (fun j : ℕ => (j : ℝ) ^ 2 * Complex.normSq (u j))}

/-- PDF pp.2,4: actual unbounded Number, represented by its graph, never a bounded operator. -/
def numberGraph : Set (B.Fock × B.Fock) :=
  {p | p.1 ∈ numberDomain ∧ ∀ j : ℕ, p.2 j = (j : ℂ) * p.1 j}

/-- PDF pp.2,4: extended nonnegative number form, including infinite first moment. -/
def numberForm (u : B.Fock) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal ((j : ℝ) * Complex.normSq (u j))

/-- PDF pp.2–4: finite-value form domain. This is not Number's operator domain. -/
def formDomain (q : B.Fock → ℝ≥0∞) : Set B.Fock := {u | q u < ⊤}

/-- PDF pp.2–4: displacement transports the number form by D(-alpha). -/
def displacedNumberForm (alpha : ℂ) (u : B.Fock) : ℝ≥0∞ :=
  numberForm (B.displacement (-alpha) u)

/-- PDF pp.3–4: bounded spectral truncation of -log X. On a zero eigenvalue
this equals K, rather than the total Real.log(0) default. -/
def logTruncation (X : B.FockOperator) (K : ℕ) : B.FockOperator :=
  letI : ContinuousFunctionalCalculus ℂ B.FockOperator IsStarNormal :=
    IsStarNormal.instContinuousFunctionalCalculus
  letI : ContinuousFunctionalCalculus ℝ B.FockOperator IsSelfAdjoint :=
    IsSelfAdjoint.instContinuousFunctionalCalculus
  cfc (fun x : ℝ => -Real.log (max x (Real.exp (-(K : ℝ))))) X
    (p := IsSelfAdjoint)

/-- PDF pp.3–4: actual extended spectral form of -log X on densities.
The supremum is over monotone bounded spectral truncations, not Fock cutoffs. -/
def negativeLogForm (X : B.FockOperator) (u : B.Fock) : ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal ((inner (𝕜 := ℂ) u (logTruncation X K u)).re)

/-- PDF pp.3–4: associated unbounded negative-log operator graph via strong
spectral-truncation limits. It does not use a bounded-operator logarithm. -/
def negativeLogGraph (X : B.FockOperator) : Set (B.Fock × B.Fock) :=
  {p | Tendsto (fun K : ℕ => logTruncation X K p.1) atTop (𝓝 p.2)}

/-- PDF p.2, Eq.(1): actual positive integral giving extended Heisenberg action.
D(-mu) is the adjoint displacement in the primal conjugation. -/
def noisePullback (v : ℝ) (q : B.Fock → ℝ≥0∞) (u : B.Fock) : ℝ≥0∞ :=
  if v = 0 then q u else
    ∫⁻ mu : ℂ, QAlgorithms.Papers.Independent.Frontier30.P07.noiseDensity v mu *
      q (B.displacement (-mu) u)

/-- PDF pp.3–4: closed densely defined nonnegative Hermitian quadratic forms.
Closedness is lower semicontinuity of the extended form on the Hilbert space. -/
def IsClosedForm (q : B.Fock → ℝ≥0∞) : Prop :=
  q 0 = 0 ∧ LowerSemicontinuous q ∧ Dense (formDomain q) ∧
    (∀ (c : ℂ) u, q (c • u) = ENNReal.ofReal (Complex.normSq c) * q u) ∧
    (∀ u w, q (u + w) + q (u - w) = 2 * q u + 2 * q w)

/-- PDF p.3, Eq.(8), full-space thermal witnesses. The Hermitian multiplier
is represented as L-cI with L a closed nonnegative form and c real. Its actual
pullback is noisePullback(L)-cI. All signed equations are evaluated on the common
finite form domain, with domain equalities and closedness explicitly required.
These are equations plus feasibility, not a definition of local minimality.
The displacement parameter retains Section IV's displaced thermal solutions. -/
def ThermalStationary (beta v : ℝ) (displacementAlpha : ℂ) : Prop :=
  let rho := A.conjugateBy (B.displacement displacementAlpha)
    (A.photonMeanThermalState (gibbsMean beta))
  let z := A.displacementNoiseChannel v rho
  B.IsDensity rho ∧ B.IsDensity z ∧
  0 < A.fockEntropyNats rho ∧ A.fockEntropyNats rho < ⊤ ∧
  ∃ (lambda alpha eta c : ℝ) (L : B.Fock → ℝ≥0∞),
    IsClosedForm (negativeLogForm rho) ∧ IsClosedForm (negativeLogForm z) ∧
    IsClosedForm L ∧ IsClosedForm (noisePullback v L) ∧
    formDomain (negativeLogForm rho) = formDomain numberForm ∧
    formDomain (negativeLogForm z) = formDomain numberForm ∧
    formDomain L = formDomain numberForm ∧
    formDomain (noisePullback v L) = formDomain numberForm ∧
    (∀ u, AEStronglyMeasurable
      (fun mu : ℂ => QAlgorithms.Papers.Independent.Frontier30.P07.noiseDensity v mu *
        L (B.displacement (-mu) u)) volume) ∧
    ∀ u ∈ formDomain numberForm,
      (negativeLogForm z u).toReal - (1 + eta) * ‖u‖ ^ 2 -
        (L u).toReal + c * ‖u‖ ^ 2 = 0 ∧
      (lambda + 1) * (‖u‖ ^ 2 - (negativeLogForm rho u).toReal) -
        alpha * ‖u‖ ^ 2 + (noisePullback v L u).toReal - c * ‖u‖ ^ 2 = 0

/-- PDF pp.1–4: fixed-input-entropy local minimum of an extended objective,
in trace-norm density neighborhoods. Nuclearity guards the infimum defining the norm. -/
def FixedEntropyLocalMinimum (F : B.FockOperator → ℝ≥0∞) (rho : B.FockOperator) : Prop :=
  B.IsDensity rho ∧ A.fockEntropyNats rho < ⊤ ∧
  ∃ r : ℝ, 0 < r ∧ ∀ X : B.FockOperator, B.IsDensity X →
    A.fockEntropyNats X = A.fockEntropyNats rho → B.IsTraceClass (X - rho) →
    B.nuclearTraceNorm (X - rho) < r → F rho ≤ F X

/-- PDF p.2: fixed-entropy output-entropy objective for the exact channel. -/
def LocalOutputMinimum (v : ℝ) (rho : B.FockOperator) : Prop :=
  FixedEntropyLocalMinimum (fun X => A.fockEntropyNats (A.displacementNoiseChannel v X)) rho

/-- PDF pp.2–3,5: entropy increment, used only when input entropy is finite.
Truncated subtraction is valid because this random-unitary channel increases entropy. -/
def entropyIncrement (gamma : ℝ) (rho : B.FockOperator) (t : ℝ) : ℝ≥0∞ :=
  A.fockEntropyNats (A.displacementNoiseChannel (gamma * t) rho) - A.fockEntropyNats rho

/-- PDF pp.2–3: positive-time extended quotient; t>0 is imposed at every use. -/
def entropyQuotient (gamma : ℝ) (rho : B.FockOperator) (t : ℝ) : ℝ≥0∞ :=
  entropyIncrement gamma rho t / ENNReal.ofReal t

/-- PDF pp.2–3: total lower right Dini rate on finite-entropy densities.
Boundary theorems additionally assert the genuine limit, not just a liminf. -/
def entropyRate (gamma : ℝ) (rho : B.FockOperator) : ℝ≥0∞ :=
  liminf (entropyQuotient gamma rho) (𝓝[Set.Ioi 0] (0 : ℝ))

/-- PDF pp.1–2: infinitesimal conjecture as a proposition, including its separate
zero-entropy thermal endpoint. All finite input entropies occur; no energy photonCutoffProjection. -/
def InfinitesimalConjecture : Prop :=
  ∀ gamma : ℝ, 0 < gamma → ∀ M : ℝ, 0 ≤ M →
    ∀ X : B.FockOperator, B.IsDensity X →
    A.fockEntropyNats X = ENNReal.ofReal (A.g M) →
    entropyRate gamma (A.photonMeanThermalState M) ≤ entropyRate gamma X

/-- PDF pp.4–5: pure-input version of local minimality; the state is explicitly
represented by a unit vector. No normalization is inferred from a free ket. -/
def PureLocalOutputMinimum (v : ℝ) (rho : B.FockOperator) : Prop :=
  B.IsDensity rho ∧ (∃ u : B.Fock, ‖u‖ = 1 ∧ rho = A.pureState u) ∧
  ∃ r : ℝ, 0 < r ∧ ∀ u : B.Fock, ‖u‖ = 1 →
    B.IsTraceClass (A.pureState u - rho) →
    B.nuclearTraceNorm (A.pureState u - rho) < r →
    A.fockEntropyNats (A.displacementNoiseChannel v rho) ≤
      A.fockEntropyNats (A.displacementNoiseChannel v (A.pureState u))

/-- PDF p.2: displacement orbit; the parameter is complex phase-space displacement. -/
def orbitPoint (rho : B.FockOperator) (alpha : ℂ) : B.FockOperator :=
  A.conjugateBy (B.displacement alpha) rho

/-- PDF p.2: continuity into trace-norm density space, expressed by epsilon-delta
conditions to avoid the ambient operator-norm topology on bounded operators. -/
def TraceContinuous {T : Type*} [PseudoMetricSpace T] (f : T → B.FockOperator) : Prop :=
  ∀ a : T, ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧
    ∀ b : T, dist b a < delta → B.IsTraceClass (f b - f a) ∧
      B.nuclearTraceNorm (f b - f a) < eps

/-- PDF p.5, Appendix 1: projection onto the N-dimensional span of levels j<N. -/
def photonCutoffProjection (N : ℕ) : B.FockOperator := ∑ j ∈ Finset.range N, B.fockDyad j j

/-- PDF p.5: raw compression; it is not presumed to have trace one. -/
def photonCutoffCompression (rho : B.FockOperator) (N : ℕ) : B.FockOperator :=
  ((photonCutoffProjection N).comp rho).comp (photonCutoffProjection N)

/-- PDF p.5: retained probability mass in the photon cutoff. -/
def retainedMass (rho : B.FockOperator) (N : ℕ) : ℝ :=
  ∑ j ∈ Finset.range N, B.photonProbability rho j

/-- PDF p.5: normalized compression is used only with a positive-mass witness. -/
def normalizedCompression (rho : B.FockOperator) (N : ℕ)
    (_h : 0 < retainedMass rho N) : B.FockOperator :=
  ((retainedMass rho N)⁻¹ : ℂ) • photonCutoffCompression rho N

/-- PDF p.5: finite density domain for entropy continuity; entropy itself is reused in nats. -/
def finiteDensities (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {X | X.PosSemidef ∧ X.trace = 1}

/-- PDF p.5: relative open interior of the trace-one Hermitian affine space. -/
def finiteInterior (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {X | X.PosDef ∧ X.trace = 1}

example (X : B.FockOperator) : A.displacementNoiseChannel 0 X = X := by
  simp [A.displacementNoiseChannel]

example : (0 : B.Fock) ∈ numberDomain := by
  simp [numberDomain]

example : ((0 : B.Fock), (0 : B.Fock)) ∈ numberGraph := by
  simp [numberGraph, numberDomain]

example : numberForm 0 = 0 := by
  simp [numberForm]

example : numberForm (B.fockKet 1) = 1 := by
  unfold numberForm
  rw [tsum_eq_single (1 : ℕ)]
  · norm_num [B.fockKet, lp.single_apply, Pi.single_apply]
  · intro j hj
    simp [B.fockKet, lp.single_apply, Pi.single_apply, hj, Ne.symm hj]

example (X : B.FockOperator) : negativeLogForm X 0 = 0 := by
  simp [negativeLogForm]

example (q : B.Fock → ℝ≥0∞) : noisePullback 0 q = q := by
  funext u
  simp [noisePullback]

example : photonCutoffProjection 0 = 0 := by
  simp [photonCutoffProjection]

example : photonCutoffProjection 1 = B.fockDyad 0 0 := by
  simp [photonCutoffProjection]

example (rho : B.FockOperator) : retainedMass rho 0 = 0 := by
  simp [retainedMass]

end QAlgorithms.Papers.Independent.Next46.P27



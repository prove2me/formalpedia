-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P05
-- name    : QAlgorithms_Papers_Independent_Frontier30_P05
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T09:10:15.268067+00:00
-- url     : https://prove2.me/theorems/2fd04d72-1a76-41fc-ab0f-d0ef59e0bd11
-- title:
--   Definitions for Advanced Alicki-Fannes-Winter method for energy-constrained quantum systems and its use
-- statement:
--   The objects the formalized statements of *Advanced Alicki-Fannes-Winter method for energy-constrained quantum systems and its use* (arXiv:1907.02458) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `EnergySpectrum`: PDF p.6, (12): all eigenvalues, including multiplicities, on the infinite effective Hilbert space. In eigenbasis coordinates these specify the positive self-adjoint diagonal operator on its maximal weighted l2 domain.
--   - `groundEnergy`: PDF p.6: the actual ground eigenvalue, not an independently chosen lower bound.
--   - `groundMultiplicity`: PDF p.6: dimension of the ground eigenspace. It is positive and finite for EnergySpectrum, since the eigenvalue list is ordered and tends to infinity.
--   - `partitionTrace`: PDF p.6, (11),(14): partition trace on the effective space. Summability is included in condition14 so a divergent real tsum cannot masquerade as zero.
--   - `Condition14`: PDF p.6, (14), together with its implied condition (11). The second clause is a genuine right-hand real limit, and the exponent is lambda.
--   - `entropyCapacityExtended`: PDF p.6, (10),(13): actual supremum of spectral von Neumann entropies of all normalized trace-class states satisfying the energy constraint. Infinity is retained; the empty set (budgets below E0) has supremum zero in ENNReal.
--   - `entropyCapacity`: PDF p.6, (13): the real entropy capacity. Under Condition14 and E≥E0 its extended value is finite; no conversion of infinite entropy is used by the stated results. All logarithms in the reused entropy are natural.
--   - `shiftedCapacity`: PDF p.7, (16): the actual entropy capacity shifted by the ground energy.
--   - `AdmissibleMajorant`: PDF p.7, (17),(18): continuity includes zero; the two monotonicity requirements apply on positive arguments, precisely as in the source. The quotient limit is the source's o(sqrt(x)) condition.
--   - `minimalMajorant`: PDF p.7, Proposition 1(A): the displayed square-root envelope at x>0. At zero use its continuous endpoint ln(m(E0)), rather than 0 times an unbounded supremum. The real supremum is nonempty and bounded for x>0 under Condition14. Values at x<0 are outside every stated domain.
--   - `spectralNumerator`: PDF p.7, Proposition 1(B): N-up counts ordered pairs and squares the FIRST level in each pair. It does not use the product of the two levels. Only finitely many pairs contribute at a finite cutoff.
--   - `spectralDenominator`: PDF p.7, Proposition 1(B): N-down, over the SAME ordered pairs. Its possible zero value at small cutoffs does not affect the limit at infinity.
--   - `SpectralRatioLimit`: PDF p.7, (20): finite real spectral ratio limit a>1, not a limsup.
--   - `firstDimension`: PDF p.8: the LEAST positive integer d with ln(d)>G(0). Since exp(G(0))>0, floor(exp(G(0)))+1 gives that integer exactly.
--   - `inverseMajorant`: PDF p.8: inverse of G on its actual nonnegative range. For an admissible majorant and d≥d0 the set is a singleton: continuity, strict increase and the unbounded actual entropy capacity ensure existence. Other inputs are unused.
--   - `entropyCorrection`: PDF p.9, (24): the actual g, including g(0)=0.
--   - `continuityBound`: PDF p.10, (27): the ACTUAL continuity-bound expression. Both additive constants remain outside G. It is used only at positive energy excess, epsilon and t.
--   - `parameterLimit`: PDF p.10: the admissible upper endpoint T, including the square root.
-- source:
--   Advanced Alicki-Fannes-Winter method for energy-constrained quantum systems and its use, arXiv:1907.02458v3, https://arxiv.org/abs/1907.02458v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

/-!
Statements from M. E. Shirokov, arXiv:1907.02458v3.
Only Proposition 1 and Remark 1 are asserted here. Other registered nodes have
individual deferrals in HARD.md and GAPS.json. The independent-paper workflow
permits reuse of the pinned accepted P13 module; its trace-class operators and
spectral entropy are reused unchanged. This is not an import of a new draft.

For the spectral statements the Hilbert space below is the effective closed
space cl(D(H)) of (10). The full eigenbasis in (12) lives on this space. States
of finite energy in a larger ambient space are supported here, so its entropy
capacity is exactly (13), including for a nondensely defined ambient operator.
No theorem about arbitrary composite systems is reduced to this single-system
representation. Compilation is pending the batch handoff.
-/

noncomputable section

open Filter
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Frontier30.P05

namespace TC

export QAlgorithms.Papers.Independent.Dependency50.P13
  (State stateEntropy spectralEnergy)

end TC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- PDF p.6, (12): all eigenvalues, including multiplicities, on the infinite
effective Hilbert space. In eigenbasis coordinates these specify the positive
self-adjoint diagonal operator on its maximal weighted l2 domain. -/
structure EnergySpectrum where
  levels : ℕ → ℝ≥0
  ordered : Monotone levels
  diverges : Tendsto (fun k => (levels k : ℝ)) atTop atTop

/-- PDF p.6: the actual ground eigenvalue, not an independently chosen lower bound. -/
def groundEnergy (S : EnergySpectrum) : ℝ := S.levels 0

/-- PDF p.6: dimension of the ground eigenspace. It is positive and finite for
EnergySpectrum, since the eigenvalue list is ordered and tends to infinity. -/
def groundMultiplicity (S : EnergySpectrum) : ℕ :=
  Set.ncard {k : ℕ | S.levels k = S.levels 0}

/-- PDF p.6, (11),(14): partition trace on the effective space. Summability is
included in condition14 so a divergent real tsum cannot masquerade as zero. -/
def partitionTrace (S : EnergySpectrum) (lambda : ℝ) : ℝ :=
  ∑' k : ℕ, Real.exp (-lambda * (S.levels k : ℝ))

/-- PDF p.6, (14), together with its implied condition (11). The second clause
is a genuine right-hand real limit, and the exponent is lambda. -/
def Condition14 (S : EnergySpectrum) : Prop :=
  (∀ lambda : ℝ, 0 < lambda →
    Summable (fun k : ℕ => Real.exp (-lambda * (S.levels k : ℝ)))) ∧
  Tendsto (fun lambda : ℝ => (partitionTrace S lambda) ^ lambda)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)

/-- PDF p.6, (10),(13): actual supremum of spectral von Neumann entropies of
all normalized trace-class states satisfying the energy constraint. Infinity
is retained; the empty set (budgets below E0) has supremum zero in ENNReal. -/
def entropyCapacityExtended (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (E : ℝ) : ℝ≥0∞ :=
  if 0 ≤ E then
    ⨆ rho : {rho : TC.State b // TC.spectralEnergy b S.levels rho ≤ ENNReal.ofReal E},
      TC.stateEntropy b rho.val
  else 0

/-- PDF p.6, (13): the real entropy capacity. Under Condition14 and E≥E0
its extended value is finite; no conversion of infinite entropy is used by
the stated results. All logarithms in the reused entropy are natural. -/
def entropyCapacity (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum) (E : ℝ) : ℝ :=
  (entropyCapacityExtended b S E).toReal

/-- PDF p.7, (16): the actual entropy capacity shifted by the ground energy. -/
def shiftedCapacity (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum) (x : ℝ) : ℝ :=
  entropyCapacity b S (x + groundEnergy S)

/-- PDF p.7, (17),(18): continuity includes zero; the two monotonicity
requirements apply on positive arguments, precisely as in the source.
The quotient limit is the source's o(sqrt(x)) condition. -/
def AdmissibleMajorant (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (G : ℝ → ℝ) : Prop :=
  ContinuousOn G (Set.Ici 0) ∧
  (∀ x : ℝ, 0 < x → shiftedCapacity b S x ≤ G x) ∧
  Tendsto (fun x : ℝ => G x / Real.sqrt x) atTop (nhds 0) ∧
  StrictMonoOn G (Set.Ioi 0) ∧
  AntitoneOn (fun x : ℝ => G x / Real.sqrt x) (Set.Ioi 0)

/-- PDF p.7, Proposition 1(A): the displayed square-root envelope at x>0.
At zero use its continuous endpoint ln(m(E0)), rather than 0 times an
unbounded supremum. The real supremum is nonempty and bounded for x>0
under Condition14. Values at x<0 are outside every stated domain. -/
def minimalMajorant (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum) (x : ℝ) : ℝ :=
  if 0 < x then
    Real.sqrt x * sSup ((fun y : ℝ => shiftedCapacity b S y / Real.sqrt y) '' Set.Ici x)
  else Real.log (groundMultiplicity S : ℝ)

/-- PDF p.7, Proposition 1(B): N-up counts ordered pairs and squares the
FIRST level in each pair. It does not use the product of the two levels.
Only finitely many pairs contribute at a finite cutoff. -/
def spectralNumerator (S : EnergySpectrum) (E : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, if (S.levels p.1 : ℝ) + (S.levels p.2 : ℝ) ≤ E
    then (S.levels p.1 : ℝ) ^ 2 else 0

/-- PDF p.7, Proposition 1(B): N-down, over the SAME ordered pairs. Its
possible zero value at small cutoffs does not affect the limit at infinity. -/
def spectralDenominator (S : EnergySpectrum) (E : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ, if (S.levels p.1 : ℝ) + (S.levels p.2 : ℝ) ≤ E
    then (S.levels p.1 : ℝ) * (S.levels p.2 : ℝ) else 0

/-- PDF p.7, (20): finite real spectral ratio limit a>1, not a limsup. -/
def SpectralRatioLimit (S : EnergySpectrum) (a : ℝ) : Prop :=
  1 < a ∧ Tendsto (fun E : ℝ => spectralNumerator S E / spectralDenominator S E)
    atTop (nhds a)

/-- PDF p.8: the LEAST positive integer d with ln(d)>G(0).
Since exp(G(0))>0, floor(exp(G(0)))+1 gives that integer exactly. -/
def firstDimension (G : ℝ → ℝ) : ℕ := ⌊Real.exp (G 0)⌋₊ + 1

/-- PDF p.8: inverse of G on its actual nonnegative range. For an admissible
majorant and d≥d0 the set is a singleton: continuity, strict increase and the
unbounded actual entropy capacity ensure existence. Other inputs are unused. -/
def inverseMajorant (G : ℝ → ℝ) (d : ℕ) : ℝ :=
  sInf {x : ℝ | 0 ≤ x ∧ G x = Real.log (d : ℝ)}

/-- PDF p.9, (24): the actual g, including g(0)=0. -/
def entropyCorrection (x : ℝ) : ℝ :=
  (x + 1) * Real.log (x + 1) - x * Real.log x

/-- PDF p.10, (27): the ACTUAL continuity-bound expression. Both additive
constants remain outside G. It is used only at positive energy excess,
epsilon and t. -/
def continuityBound (G : ℝ → ℝ) (Ebar epsilon C D t : ℝ) : ℝ :=
  C * epsilon * (1 + 4 * t) *
    (G (Ebar / (epsilon * t) ^ 2) + 1 / (firstDimension G : ℝ) + Real.log 2) +
  D * (2 * entropyCorrection (epsilon * t) + entropyCorrection (epsilon * (1 + 2 * t)))

/-- PDF p.10: the admissible upper endpoint T, including the square root. -/
def parameterLimit (G : ℝ → ℝ) (Ebar epsilon : ℝ) : ℝ :=
  epsilon⁻¹ * min 1 (Real.sqrt (Ebar / inverseMajorant G (firstDimension G)))

/-- A one-dimensional ground space gives the continuous envelope endpoint zero.
This checks the endpoint branch without evaluating a divergent supremum. -/
example (b : HilbertBasis ℕ ℂ H) (S : EnergySpectrum)
    (hm : groundMultiplicity S = 1) : minimalMajorant b S 0 = 0 := by
  simp [minimalMajorant, hm]

example : entropyCorrection 0 = 0 := by
  simp [entropyCorrection]

example (G : ℝ → ℝ) (Ebar epsilon t : ℝ) :
    continuityBound G Ebar epsilon 0 0 t = 0 := by
  simp [continuityBound]

end QAlgorithms.Papers.Independent.Frontier30.P05



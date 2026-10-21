-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P39
-- name    : QAlgorithms_Papers_Independent_Claimed50_P39
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T10:44:56.739418+00:00
-- url     : https://prove2.me/theorems/3dd299d0-ccf1-4357-837d-d9c3c6a5a6c2
-- title:
--   Definitions for Minimum output entropy of bosonic channels: a conjecture
-- statement:
--   The objects the formalized statements of *Minimum output entropy of bosonic channels: a conjecture* (arXiv:quant-ph/0404005) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `g`: Eq.(8), PDF p.2: nats, continuously interpreting 0 log 0.
--   - `thermalProbability`: Eq.(7), PDF p.2: thermal photon probabilities, M>=0.
--   - `photonMeanThermalState`: Eq.(7), PDF p.2: reparameterize the imported thermalDensity by photon mean. The frozen Information100.P08.thermalState is a fixed two-qubit Choi state.
--   - `beamAmplitude`: Eqs.(1)–(3), PDF p.2: exact real beam-splitter Fock matrix, on finite photon sectors with no global photon cutoff. U|1,0>=sqrt(eta)|1,0>-sqrt(1-eta)|0,1>. This sign gives precisely U-dagger a U=sqrt(eta)a+sqrt(1-eta)b.
--   - `thermalTerm`: Eq.(3): independent thermal input j and traced output environment ell. Photon conservation determines the signal's two input indices.
--   - `thermalOutputMatrix`: Eq.(3): full partial-trace coefficients; summability is concluded below.
--   - `thermal`: Eq.(3): the actual thermal dilation, including both transmissivity endpoints. characteristicTransform rules out the accepted operatorOfMatrix fallback.
--   - `conjugateBy`: Conjugation by A; density transformations below use unitary A.
--   - `classicalIntegrand`: Eq.(4), PDF p.2: Gaussian displacement average. Reuse the accepted planar noiseDensity via toReal; on n>0 its value is exp(-normSq(z)/n)/(pi*n).
--   - `displacementNoiseChannel`: Eq.(4) with the separately specified zero-noise identity.
--   - `eigenvalue`: Eq.(13): nth approximation number. For a positive compact operator this is the nth decreasing eigenvalue, with multiplicity, indexed from zero. Distances to sums of j rank-one maps form a nonempty, nonnegative set, so the real infimum never uses an empty/unbounded default. Infinite-rank zero eigenspaces are omitted.
--   - `fockEntropyNats`: Eq.(10), PDF p.2: full Fock-space entropy in nats, including +infinity. Frozen entropy declarations on finite matrices/laws cannot represent this domain.
--   - `minimumEntropy`: Eq.(10): unrestricted infimum; attainment is asserted only with a witness.
--   - `pureState`: Pure projector; theorems require norm-one u.
--   - `pureMinimumEntropy`: Pure-input entropy infimum over normalized vectors.
--   - `IsNormalFockChannel`: Normal CPTP maps on a separable oscillator via countable Kraus action on all trace-class inputs. Eq.(11) concerns trace-preserving maps; nonlinear functions on densities and non-trace-preserving operations are excluded.
--   - `partialSum`: Eq.(13): ordered sum of q+1 eigenvalues, not unsorted photon weights.
--   - `Majorizes`: Eq.(13): the majorizing first argument has larger partial sums.
--   - `ThermalEntropyConjecture`: Conjecture (i), PDF p.3, defined but never asserted. No input energy or additivity assumption. coherentOutput supplies attaining witnesses conditionally.
--   - `ClassicalEntropyConjecture`: Classical part of Conjecture (i); definition only.
--   - `ThermalMajorizationConjecture`: Conjecture (ii), PDF p.3, defined but never asserted.
--   - `ClassicalMajorizationConjecture`: Classical part of Conjecture (ii); definition only.
--   - `fockPhaseRotation`: PDF p.3: oscillator phase rotation exp(i phi Number). The frozen EquatorialQSP.rotation instead acts on a single qubit.
--   - `IsGaussian`: PDF p.5: actual Gaussian Fock densities. The linear Weyl term corrects the inconsistent printed mean contraction. Vacuum has c=1/2, b=0. Positivity and normalization come from the density, not assumed covariance inequalities.
--   - `meanA`: Actual first annihilation moment; its series converges on Gaussian states.
--   - `secondA`: Actual second annihilation moment of Eq.(28), PDF p.5.
--   - `FiniteEnergy`: Finite photon expectation; only the finite-domain trace formulas use this.
--   - `covarianceC`: Eq.(28): the common complex-covariance diagonal.
--   - `covarianceB`: Eq.(28): the centered off-diagonal covariance entry.
--   - `covarianceDet`: Eq.(28): determinant in the source's complex covariance convention.
--   - `lambdaBound`: Eq.(40), PDF p.6: smaller root on k>=1 and (k-1)/2<=n<=k/2.
--   - `boundC`: Eq.(39): bound c, continuously interpreting 0 log 0.
--   - `fockRealPowerTrace`: Eq.(46), PDF pp.6–7: full-Fock real-order spectral trace. The frozen Information100.P19.powerTrace accepts finite matrices and Nat orders.
--   - `onePhotonWeight`: Eq.(70), k=1 and n>0: photon-indexed, not already sorted.
--   - `onePhotonSumA`: Eq.(71): partial sum after inserting the vacuum-index weight.
--   - `onePhotonSumB`: Eq.(72): partial sum before inserting the vacuum-index weight.
--   - `rising`: Finite rising factorial, only for terminating polynomials.
--   - `terminatingF`: E5, PDF p.14: terminating 2F1, avoiding its singular analytic third parameter.
--   - `outputTerm`: Eq.(77)/E5: exact coefficient summand, including both factorial square roots.
--   - `amplifier`: Appendix B: actual amplifier through accepted Kraus maps. Intensity gain kappa corresponds to amplitude sqrt(kappa). Realization is concluded below.
--   - `thermalRelativeEntropy`: PDF p.9: thermal-reference Umegaki entropy on the finite-energy domain. Both spectral/diagonal traces are genuinely convergent for M>0 and finite energy. This is not a real-valued definition on unrestricted state pairs.
--   - `affineFockMixture`: Eq.(52), PDF pp.7–8: affine trajectory of two Fock operators. The frozen Information100.P47.mixture combines finite POVMs.
--   - `CoherentDerivative`: Eqs.(53)–(54): finite-energy derivative assertion for the specified C,zeta,M. The value is the right derivative and the entropy stays finite on the path.
--   - `FiniteRelativeIdentity`: Eqs.(61)–(62),(67): a finite thermal-reference trace identity and its pointwise lower-bound equivalence. Both traces and the output entropy are finite.
-- source:
--   Minimum output entropy of bosonic channels: a conjecture, arXiv:quant-ph/0404005v1, https://arxiv.org/abs/quant-ph/0404005v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P58

/-!
Statements from arXiv:quant-ph/0404005v1 on the full countable Fock space.
Natural logarithms and extended entropy. Conjectures are predicates, not theorems.
The constructed channels' realization is a conclusion of characteristicTransform.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Claimed50.P39

open Filter MeasureTheory
open scoped Topology ENNReal

namespace B
export QAlgorithms.Papers.Independent.Dependency50.P39
  (Fock FockOperator fockKet fockDyad IsDensity IsTraceClass HasFockMatrix
   operatorOfMatrix thermalDensity ThermalRealized coherentKet coherentProjector
   CoherentRealized displacement DisplacementRealized characteristic fockTrace
   photonMean photonProbability krausTerm TraceHasSum KrausWellDefined
   amplifierKraus AmplifierRealized)
end B

attribute [local instance] Classical.propDecidable

/-- Eq.(8), PDF p.2: nats, continuously interpreting 0 log 0. -/
def g (x : ℝ) : ℝ := (x + 1) * Real.log (x + 1) - x * Real.log x

/-- Eq.(7), PDF p.2: thermal photon probabilities, M>=0. -/
def thermalProbability (M : ℝ) (j : ℕ) : ℝ := (M / (M + 1)) ^ j / (M + 1)

/-- Eq.(7), PDF p.2: reparameterize the imported thermalDensity by photon mean.
The frozen Information100.P08.thermalState is a fixed two-qubit Choi state. -/
def photonMeanThermalState (M : ℝ) : B.FockOperator := B.thermalDensity (2 * M + 1)

/-- Eqs.(1)–(3), PDF p.2: exact real beam-splitter Fock matrix, on finite
photon sectors with no global photon cutoff. U|1,0>=sqrt(eta)|1,0>-sqrt(1-eta)|0,1>.
This sign gives precisely U-dagger a U=sqrt(eta)a+sqrt(1-eta)b. -/
def beamAmplitude (eta : ℝ) (m ell p q : ℕ) : ℝ :=
  if m + ell = p + q then
    Real.sqrt (((Nat.factorial m : ℝ) * (Nat.factorial ell : ℝ)) /
      ((Nat.factorial p : ℝ) * (Nat.factorial q : ℝ))) *
    ∑ r ∈ Finset.range (p + 1),
      if r ≤ m ∧ m - r ≤ q then
        (Nat.choose p r : ℝ) * (Nat.choose q (m - r) : ℝ) *
        Real.sqrt eta ^ (r + (q - (m - r))) *
        (-Real.sqrt (1 - eta)) ^ (p - r) * Real.sqrt (1 - eta) ^ (m - r)
      else 0
  else 0

/-- Eq.(3): independent thermal input j and traced output environment ell.
Photon conservation determines the signal's two input indices. -/
def thermalTerm (eta N : ℝ) (X : B.FockOperator) (m n : ℕ) (a : ℕ × ℕ) : ℂ :=
  if a.1 ≤ m + a.2 ∧ a.1 ≤ n + a.2 then
    (thermalProbability N a.1 *
      beamAmplitude eta m a.2 (m + a.2 - a.1) a.1 *
      beamAmplitude eta n a.2 (n + a.2 - a.1) a.1 : ℝ) *
      X (B.fockKet (n + a.2 - a.1)) (m + a.2 - a.1)
  else 0

/-- Eq.(3): full partial-trace coefficients; summability is concluded below. -/
def thermalOutputMatrix (eta N : ℝ) (X : B.FockOperator) (m n : ℕ) : ℂ :=
  ∑' a : ℕ × ℕ, thermalTerm eta N X m n a

/-- Eq.(3): the actual thermal dilation, including both transmissivity endpoints.
characteristicTransform rules out the accepted operatorOfMatrix fallback. -/
def thermal (eta N : ℝ) (X : B.FockOperator) : B.FockOperator :=
  B.operatorOfMatrix (thermalOutputMatrix eta N X)

/-- Conjugation by A; density transformations below use unitary A. -/
def conjugateBy (A X : B.FockOperator) : B.FockOperator :=
  (A.comp X).comp (ContinuousLinearMap.adjoint A)

/-- Eq.(4), PDF p.2: Gaussian displacement average. Reuse the accepted planar
noiseDensity via toReal; on n>0 its value is exp(-normSq(z)/n)/(pi*n). -/
def classicalIntegrand (n : ℝ) (X : B.FockOperator) (m k : ℕ) (z : ℂ) : ℂ :=
  ((QAlgorithms.Papers.Independent.Frontier30.P07.noiseDensity n z).toReal : ℂ) * conjugateBy (B.displacement z) X (B.fockKet k) m

/-- Eq.(4) with the separately specified zero-noise identity. -/
def displacementNoiseChannel (n : ℝ) (X : B.FockOperator) : B.FockOperator :=
  if n = 0 then X else B.operatorOfMatrix
    (fun m k => ∫ z : ℂ, classicalIntegrand n X m k z)

/-- Eq.(13): nth approximation number. For a positive compact operator this is
the nth decreasing eigenvalue, with multiplicity, indexed from zero. Distances
to sums of j rank-one maps form a nonempty, nonnegative set, so the real infimum
never uses an empty/unbounded default. Infinite-rank zero eigenspaces are omitted. -/
def eigenvalue (X : B.FockOperator) (j : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ u v : Fin j → B.Fock,
    r = ‖X - ∑ i, InnerProductSpace.rankOne ℂ (u i) (v i)‖}

/-- Eq.(10), PDF p.2: full Fock-space entropy in nats, including +infinity.
Frozen entropy declarations on finite matrices/laws cannot represent this domain. -/
def fockEntropyNats (X : B.FockOperator) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (-eigenvalue X j * Real.log (eigenvalue X j))

/-- Eq.(10): unrestricted infimum; attainment is asserted only with a witness. -/
def minimumEntropy (C : B.FockOperator → B.FockOperator) : ℝ≥0∞ :=
  ⨅ X : {X : B.FockOperator // B.IsDensity X}, fockEntropyNats (C X.val)

/-- Pure projector; theorems require norm-one u. -/
def pureState (u : B.Fock) : B.FockOperator := InnerProductSpace.rankOne ℂ u u

/-- Pure-input entropy infimum over normalized vectors. -/
def pureMinimumEntropy (C : B.FockOperator → B.FockOperator) : ℝ≥0∞ :=
  ⨅ u : {u : B.Fock // ‖u‖ = 1}, fockEntropyNats (C (pureState u.val))

/-- Normal CPTP maps on a separable oscillator via countable Kraus action on
all trace-class inputs. Eq.(11) concerns trace-preserving maps; nonlinear
functions on densities and non-trace-preserving operations are excluded. -/
def IsNormalFockChannel (C : B.FockOperator → B.FockOperator) : Prop :=
  ∃ K : ℕ → B.FockOperator, B.KrausWellDefined K ∧
    ∀ X, B.IsTraceClass X → B.TraceHasSum (fun j => B.krausTerm (K j) X) (C X)

/-- Eq.(13): ordered sum of q+1 eigenvalues, not unsorted photon weights. -/
def partialSum (X : B.FockOperator) (q : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (q + 1), eigenvalue X j

/-- Eq.(13): the majorizing first argument has larger partial sums. -/
def Majorizes (X Y : B.FockOperator) : Prop :=
  B.IsDensity X ∧ B.IsDensity Y ∧ ∀ q, partialSum Y q ≤ partialSum X q

/-- Conjecture (i), PDF p.3, defined but never asserted. No input energy or
additivity assumption. coherentOutput supplies attaining witnesses conditionally. -/
def ThermalEntropyConjecture (eta N : ℝ) : Prop :=
  ∀ X, B.IsDensity X → ENNReal.ofReal (g ((1 - eta) * N)) ≤ fockEntropyNats (thermal eta N X)

/-- Classical part of Conjecture (i); definition only. -/
def ClassicalEntropyConjecture (n : ℝ) : Prop :=
  ∀ X, B.IsDensity X → ENNReal.ofReal (g n) ≤ fockEntropyNats (displacementNoiseChannel n X)

/-- Conjecture (ii), PDF p.3, defined but never asserted. -/
def ThermalMajorizationConjecture (eta N : ℝ) : Prop :=
  ∀ (alpha : ℂ) X, B.IsDensity X →
    Majorizes (thermal eta N (B.coherentProjector alpha)) (thermal eta N X)

/-- Classical part of Conjecture (ii); definition only. -/
def ClassicalMajorizationConjecture (n : ℝ) : Prop :=
  ∀ (alpha : ℂ) X, B.IsDensity X →
    Majorizes (displacementNoiseChannel n (B.coherentProjector alpha)) (displacementNoiseChannel n X)

/-- PDF p.3: oscillator phase rotation exp(i phi Number).
The frozen EquatorialQSP.rotation instead acts on a single qubit. -/
def fockPhaseRotation (phi : ℝ) : B.FockOperator := B.operatorOfMatrix
  (fun m n => if m = n then Complex.exp (Complex.I * (phi * n : ℝ)) else 0)

/-- PDF p.5: actual Gaussian Fock densities. The linear Weyl term corrects the
inconsistent printed mean contraction. Vacuum has c=1/2, b=0. Positivity and
normalization come from the density, not assumed covariance inequalities. -/
def IsGaussian (X : B.FockOperator) : Prop :=
  B.IsDensity X ∧ ∃ (alpha : ℂ) (c : ℝ) (b : ℂ), ∀ z : ℂ,
    B.characteristic X z = Complex.exp
      (z * star alpha - star z * alpha - (c * Complex.normSq z : ℝ) +
        (b * star z ^ 2 + star b * z ^ 2) / 2)

/-- Actual first annihilation moment; its series converges on Gaussian states. -/
def meanA (X : B.FockOperator) : ℂ :=
  ∑' j : ℕ, (Real.sqrt (j + 1 : ℝ) : ℂ) * X (B.fockKet j) (j + 1)

/-- Actual second annihilation moment of Eq.(28), PDF p.5. -/
def secondA (X : B.FockOperator) : ℂ :=
  ∑' j : ℕ, (Real.sqrt ((j + 1 : ℝ) * (j + 2 : ℝ)) : ℂ) * X (B.fockKet j) (j + 2)

/-- Finite photon expectation; only the finite-domain trace formulas use this. -/
def FiniteEnergy (X : B.FockOperator) : Prop :=
  Summable (fun j : ℕ => (j : ℝ) * B.photonProbability X j)

/-- Eq.(28): the common complex-covariance diagonal. -/
def covarianceC (X : B.FockOperator) : ℝ :=
  B.photonMean X - Complex.normSq (meanA X) + 1 / 2

/-- Eq.(28): the centered off-diagonal covariance entry. -/
def covarianceB (X : B.FockOperator) : ℂ := secondA X - meanA X ^ 2

/-- Eq.(28): determinant in the source's complex covariance convention. -/
def covarianceDet (X : B.FockOperator) : ℝ := covarianceC X ^ 2 - Complex.normSq (covarianceB X)

/-- Eq.(40), PDF p.6: smaller root on k>=1 and (k-1)/2<=n<=k/2. -/
def lambdaBound (k : ℕ) (n : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - (k + 1 : ℝ) * (1 - (k : ℝ) / (2 * n + 1)))) / (k + 1 : ℝ)

/-- Eq.(39): bound c, continuously interpreting 0 log 0. -/
def boundC (k : ℕ) (n : ℝ) : ℝ :=
  -lambdaBound k n * Real.log (lambdaBound k n) -
    (1 - lambdaBound k n) * Real.log ((1 - lambdaBound k n) / k)

/-- Eq.(46), PDF pp.6–7: full-Fock real-order spectral trace.
The frozen Information100.P19.powerTrace accepts finite matrices and Nat orders. -/
def fockRealPowerTrace (X : B.FockOperator) (z : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (Real.rpow (eigenvalue X j) z)

/-- Eq.(70), k=1 and n>0: photon-indexed, not already sorted. -/
def onePhotonWeight (n : ℝ) (i : ℕ) : ℝ :=
  n ^ i / (n + 1) ^ (i + 2) * (n + (i : ℝ) / n)

/-- Eq.(71): partial sum after inserting the vacuum-index weight. -/
def onePhotonSumA (n : ℝ) (q : ℕ) : ℝ :=
  1 - (1 + (q + 1 : ℝ) / (n * (n + 1))) * (n / (n + 1)) ^ (q + 1)

/-- Eq.(72): partial sum before inserting the vacuum-index weight. -/
def onePhotonSumB (n : ℝ) (q : ℕ) : ℝ :=
  1 - (1 + (q + 2 : ℝ) / (n * (n + 1))) * (n / (n + 1)) ^ (q + 2) - n / (n + 1) ^ 2

/-- Finite rising factorial, only for terminating polynomials. -/
def rising (x : ℝ) (r : ℕ) : ℝ := ∏ t ∈ Finset.range r, (x + t)

/-- E5, PDF p.14: terminating 2F1, avoiding its singular analytic third parameter. -/
def terminatingF (j k ell : ℕ) (z : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (min j k + 1),
    rising (-(j : ℝ)) r * rising (-(k : ℝ)) r /
      (rising (-(j + k + ell : ℝ)) r * (Nat.factorial r : ℝ)) * z ^ r

/-- Eq.(77)/E5: exact coefficient summand, including both factorial square roots. -/
def outputTerm (n : ℝ) (u : B.Fock) (k ell j : ℕ) : ℂ :=
  (Real.sqrt ((Nat.factorial k : ℝ) / (Nat.factorial (k + ell) : ℝ)) *
    Real.sqrt ((Nat.factorial j : ℝ) / (Nat.factorial (j + ell) : ℝ)) *
    (Nat.factorial (j + k + ell) : ℝ) / ((Nat.factorial j : ℝ) * (Nat.factorial k : ℝ)) *
    n ^ (j + k) / (1 + n) ^ (j + k + ell + 1) *
    terminatingF j k ell (1 - n⁻¹ ^ 2) : ℝ) * u (j + ell) * star (u j)

/-- Appendix B: actual amplifier through accepted Kraus maps. Intensity gain
kappa corresponds to amplitude sqrt(kappa). Realization is concluded below. -/
def amplifier (kappa : ℝ) (X : B.FockOperator) : B.FockOperator :=
  if h : ∃ Y : B.FockOperator,
      B.TraceHasSum (fun j => B.krausTerm (B.amplifierKraus (Real.sqrt kappa) j) X) Y
  then Classical.choose h else 0

/-- PDF p.9: thermal-reference Umegaki entropy on the finite-energy domain.
Both spectral/diagonal traces are genuinely convergent for M>0 and finite
energy. This is not a real-valued definition on unrestricted state pairs. -/
def thermalRelativeEntropy (X : B.FockOperator) (M : ℝ) : ℝ :=
  (∑' j : ℕ, eigenvalue X j * Real.log (eigenvalue X j)) -
    ∑' j : ℕ, B.photonProbability X j * Real.log (thermalProbability M j)

/-- Eq.(52), PDF pp.7–8: affine trajectory of two Fock operators.
The frozen Information100.P47.mixture combines finite POVMs. -/
def affineFockMixture (X Y : B.FockOperator) (t : ℝ) : B.FockOperator :=
  ((1 - t : ℝ) : ℂ) • X + (t : ℂ) • Y

example : g 0 = 0 := by simp [g]

example : thermalProbability 0 0 = 1 := by simp [thermalProbability]

example (j : ℕ) : thermalProbability 0 (j + 1) = 0 := by simp [thermalProbability]

example (X : B.FockOperator) : displacementNoiseChannel 0 X = X := by simp [displacementNoiseChannel]

example (eta : ℝ) : beamAmplitude eta 0 0 0 0 = 1 := by simp [beamAmplitude]

example (z : ℝ) : terminatingF 0 0 0 z = 1 := by simp [terminatingF, rising]

example (X Y : B.FockOperator) : affineFockMixture X Y 0 = X := by simp [affineFockMixture]

example (X : B.FockOperator) : conjugateBy 1 X = X := by
  simp only [conjugateBy, ContinuousLinearMap.adjoint_one, ContinuousLinearMap.one_def,
    ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

example : pureState 0 = 0 := by simp [pureState]

example (eta : ℝ) : QAlgorithms.Papers.Independent.Information100.P58.binomialWeight 0 (1 - eta) 0 = 1 := by simp [QAlgorithms.Papers.Independent.Information100.P58.binomialWeight]

example (x : ℝ) : rising x 0 = 1 := by simp [rising]

example : onePhotonWeight 1 0 = 1 / 4 := by norm_num [onePhotonWeight]

example : onePhotonSumA 1 0 = 1 / 4 := by norm_num [onePhotonSumA]

example : boundC 1 0 = 0 := by norm_num [boundC, lambdaBound]

/-- Eqs.(53)–(54): finite-energy derivative assertion for the specified C,zeta,M.
The value is the right derivative and the entropy stays finite on the path. -/
def CoherentDerivative (C : B.FockOperator → B.FockOperator) (zeta M : ℝ)
    (alpha : ℂ) (X : B.FockOperator) : Prop :=
  let Y := conjugateBy (B.displacement (-alpha)) X
  let E := B.photonMean Y
  FiniteEnergy (C Y) ∧ B.photonMean (C Y) = zeta * E + M ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1, fockEntropyNats (C (affineFockMixture (B.coherentProjector alpha) X t)) ≠ ⊤) ∧
    HasDerivWithinAt (fun t : ℝ => (fockEntropyNats (C (affineFockMixture (B.coherentProjector alpha) X t))).toReal)
      (zeta * E * Real.log ((M + 1) / M)) (Set.Ici 0) 0 ∧
    0 ≤ zeta * E * Real.log ((M + 1) / M)

/-- Eqs.(61)–(62),(67): a finite thermal-reference trace identity and its
pointwise lower-bound equivalence. Both traces and the output entropy are finite. -/
def FiniteRelativeIdentity (C : B.FockOperator → B.FockOperator) (zeta M : ℝ)
    (X : B.FockOperator) : Prop :=
  FiniteEnergy (C X) ∧ fockEntropyNats (C X) ≠ ⊤ ∧
    Summable (fun j => eigenvalue (C X) j * Real.log (eigenvalue (C X) j)) ∧
    Summable (fun j => B.photonProbability (C X) j * Real.log (thermalProbability M j)) ∧
    (fockEntropyNats (C X)).toReal = g M + zeta * B.photonMean X * Real.log ((M + 1) / M) -
      thermalRelativeEntropy (C X) M ∧
    (ENNReal.ofReal (g M) ≤ fockEntropyNats (C X) ↔
      thermalRelativeEntropy (C X) M ≤ zeta * B.photonMean X * Real.log ((M + 1) / M))

end QAlgorithms.Papers.Independent.Claimed50.P39



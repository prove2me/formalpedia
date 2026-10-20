-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P15
-- name    : QAlgorithms_Papers_Independent_Dependency50_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T16:21:57.105979+00:00
-- url     : https://prove2.me/theorems/24f3426c-80f0-4c56-87f2-1b2fe309453f
-- title:
--   Definitions for Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints
-- statement:
--   The objects the formalized statements of *Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints* (arXiv:1507.07775) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `finiteConditionalEntropy`: Finite-system conditional entropy in bits, PDF p.2. Only used where both tensor factors are finite.
--   - `isotropicDensity`: Remark 3, PDF p.3: coefficient epsilon/(d²−1), with d≥2 in the theorem.
--   - `zeroProductDensity`: The pure product |00><00| in C^d tensor C^d, PDF p.6 sharpness example. Coordinates use natural values so the total definition also exists at d=0.
--   - `positiveOperatorRelativeEntropyBits`: Umegaki relative entropy in bits, PDF pp.3,5, for a normalized first argument and a possibly unnormalized PSD second argument. Support failure gives +infinity. EReal preserves negative values, for example D(1 || 2) = −1 bit. The frozen normalized-state relativeEntropyBits returns ENNReal and rejects unnormalized gamma, so it cannot represent this more general source concept.
--   - `relativeDistance`: Relative entropy distance to an operator set, PDF p.5, Eq.(6). The extended-real infimum handles empty or unsupported sets without a real default. Lemma 7 below includes attainment and finiteness under the source hypotheses.
--   - `relativeDistanceValue`: Finite real value of Eq.(6). Only used on the finite domain guaranteed by Lemma 7, or on normalized states and the finite-dimensional separable set.
--   - `relativeVariations`: The actual set of variations over pairs of states, PDF p.5, Lemma 7.
--   - `relativeVariation`: Kappa is constructed from C, rather than assumed as an unrelated constant, PDF p.5. On the Lemma 7 domain its range is nonempty and bounded, as asserted there.
--   - `relativeEntanglementValue`: Real projection of the frozen finite-dimensional E_R = D_SEP, PDF p.6. For density inputs its ENNReal value is finite (compare the full-rank product state). This wrapper does not redefine relative entropy or claim an infinite-B extension.
--   - `groupedTensorPower`: The actual tensor power regrouped as A^n:B^n, PDF p.6.
--   - `regularizedRelativeEntanglement`: Regularized E_R, PDF p.6: the infimum of E_R(rho^n)/n over positive n. For normalized states this equals the printed limit by subadditivity (Fekete). The set is nonempty and bounded below by zero; n=0 is explicitly excluded.
--   - `IsGibbsSpectrum`: Full eigenvalue list of a nonnegative discrete Hamiltonian with zero ground energy, PDF p.7. Summability for EVERY beta>0 is exactly the Gibbs Hypothesis. Multiplicities are repeated indices. On a countably infinite index set these conditions imply a finite, nonempty ground space and finite multiplicities below each finite cutoff.
--   - `partitionFunction`: Partition function of the full Hamiltonian, PDF p.7; used only at beta>0.
--   - `thermalMeanEnergy`: Mean energy in the positive-temperature Gibbs distribution, PDF p.7. Under the Gibbs Hypothesis both sums converge and the denominator is positive.
--   - `gibbsInverseTemperature`: Constructed inverse temperature, PDF p.7: the decreasing mean-energy function crosses a positive budget E exactly once. This infimum selects that beta, not an arbitrary optimizer field. The entropy construction below treats E=0 separately.
--   - `gibbsProbability`: Eigenvalues of the constructed Gibbs density, PDF p.7. At E=0 this is the normalized ground-space projector, including ground degeneracy. For E>0 these are exp(−beta(E) H)/Z. No unnormalizable maximally entangled vector is used.
--   - `gibbsEntropy`: Spectral von Neumann entropy of the constructed Gibbs state, in bits, PDF p.7. For a Gibbs spectrum on a countably infinite space and finite E≥0 this real series converges; it is the full spectral entropy, with 0 log 0 = 0.
--   - `oscillatorEnergy`: Full multimode Fock spectrum, Eq.(18), PDF p.10; a_i = hbar omega_i>0. The labels are ALL occupations in N^ell, without a finite energy cutoff.
-- source:
--   Tight uniform continuity bounds for quantum entropies: conditional entropy, relative entropy distance and energy constraints, arXiv:1507.07775v6, https://arxiv.org/abs/1507.07775v6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumOutputMetrics
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P54

/-!
# Winter: tight uniform continuity bounds for quantum entropies

Source: arXiv:1507.07775v6, PDF pp.3–7,10.
Only the results explicitly represented below are drafted. HARD.md and GAPS.json
record the remaining registered results; no finite-dimensional replacement for an
infinite-dimensional statement is asserted.

For Gibbs-entropy-only statements, a discrete Hamiltonian is represented by its
entire eigenvalue sequence, with multiplicities, in an orthonormal eigenbasis.
The associated operator on l²(I; C) is diagonal with its maximal weighted domain.
Countably infinite I represents an arbitrary infinite-dimensional separable system.
This representation does not restrict the states in a continuity theorem: the
continuity theorems requiring arbitrary trace-class states are deferred.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Dependency50.P15

open QAlgorithms.Papers.Independent.Information100.P08 (bellVector)

/-- Finite-system conditional entropy in bits, PDF p.2.
Only used where both tensor factors are finite. -/
def finiteConditionalEntropy {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  vnEntropy rho - vnEntropy (traceLeft rho)

/-- Remark 3, PDF p.3: coefficient epsilon/(d²−1), with d≥2 in the theorem. -/
def isotropicDensity (d : ℕ) (epsilon : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  ((1 - epsilon : ℝ) : ℂ) • (pureDensity (bellVector d)) +
    ((epsilon / ((d : ℝ)^2 - 1) : ℝ) : ℂ) • (1 - (pureDensity (bellVector d)))

/-- The pure product |00><00| in C^d tensor C^d, PDF p.6 sharpness example.
Coordinates use natural values so the total definition also exists at d=0. -/
def zeroProductDensity (d : ℕ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  pureDensity (WithLp.toLp 2 fun p => if p.1.val = 0 ∧ p.2.val = 0 then 1 else 0)

/-- Umegaki relative entropy in bits, PDF pp.3,5, for a normalized first argument
and a possibly unnormalized PSD second argument. Support failure gives +infinity.
EReal preserves negative values, for example D(1 || 2) = −1 bit.
The frozen normalized-state relativeEntropyBits returns ENNReal and rejects
unnormalized gamma, so it cannot represent this more general source concept. -/
def positiveOperatorRelativeEntropyBits {I : Type*} [Fintype I] [DecidableEq I]
    (rho gamma : Matrix I I ℂ) : EReal :=
  if LinearMap.ker gamma.mulVecLin ≤ LinearMap.ker rho.mulVecLin then
    (((cfc (fun x : ℝ => x * Real.logb 2 x) rho -
      rho * cfc (Real.logb 2) gamma).trace.re : ℝ) : EReal)
  else ⊤

/-- Relative entropy distance to an operator set, PDF p.5, Eq.(6).
The extended-real infimum handles empty or unsupported sets without a real default.
Lemma 7 below includes attainment and finiteness under the source hypotheses. -/
def relativeDistance {I : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Matrix I I ℂ)) (rho : Matrix I I ℂ) : EReal :=
  sInf (positiveOperatorRelativeEntropyBits rho '' C)

/-- Finite real value of Eq.(6). Only used on the finite domain guaranteed by Lemma 7,
or on normalized states and the finite-dimensional separable set. -/
def relativeDistanceValue {I : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Matrix I I ℂ)) (rho : Matrix I I ℂ) : ℝ :=
  (relativeDistance C rho).toReal

/-- The actual set of variations over pairs of states, PDF p.5, Lemma 7. -/
def relativeVariations {I : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Matrix I I ℂ)) : Set ℝ :=
  {v | ∃ rho sigma : Matrix I I ℂ, IsDensityMatrix rho ∧ IsDensityMatrix sigma ∧
    v = relativeDistanceValue C rho - relativeDistanceValue C sigma}

/-- Kappa is constructed from C, rather than assumed as an unrelated constant, PDF p.5.
On the Lemma 7 domain its range is nonempty and bounded, as asserted there. -/
def relativeVariation {I : Type*} [Fintype I] [DecidableEq I]
    (C : Set (Matrix I I ℂ)) : ℝ := sSup (relativeVariations C)

/-- Real projection of the frozen finite-dimensional E_R = D_SEP, PDF p.6.
For density inputs its ENNReal value is finite (compare the full-rank product state).
This wrapper does not redefine relative entropy or claim an infinite-B extension. -/
def relativeEntanglementValue {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  (QAlgorithms.Papers.Independent.Information100.P54.relativeEntanglement rho).toReal

/-- The actual tensor power regrouped as A^n:B^n, PDF p.6. -/
def groupedTensorPower {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  fun p q => ∏ i, rho (p.1 i, p.2 i) (q.1 i, q.2 i)

/-- Regularized E_R, PDF p.6: the infimum of E_R(rho^n)/n over positive n.
For normalized states this equals the printed limit by subadditivity (Fekete).
The set is nonempty and bounded below by zero; n=0 is explicitly excluded. -/
def regularizedRelativeEntanglement {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {v | ∃ n : ℕ, 0 < n ∧
    v = (n : ℝ)⁻¹ * relativeEntanglementValue (groupedTensorPower rho n)}

/-- Full eigenvalue list of a nonnegative discrete Hamiltonian with zero ground energy,
PDF p.7. Summability for EVERY beta>0 is exactly the Gibbs Hypothesis. Multiplicities
are repeated indices. On a countably infinite index set these conditions imply a finite,
nonempty ground space and finite multiplicities below each finite cutoff. -/
def IsGibbsSpectrum {I : Type*} (energy : I → ℝ) : Prop :=
  (∀ i, 0 ≤ energy i) ∧ (∃ i, energy i = 0) ∧
    ∀ beta : ℝ, 0 < beta → Summable (fun i => Real.exp (-beta * energy i))

/-- Partition function of the full Hamiltonian, PDF p.7; used only at beta>0. -/
def partitionFunction {I : Type*} (energy : I → ℝ) (beta : ℝ) : ℝ :=
  ∑' i, Real.exp (-beta * energy i)

/-- Mean energy in the positive-temperature Gibbs distribution, PDF p.7.
Under the Gibbs Hypothesis both sums converge and the denominator is positive. -/
def thermalMeanEnergy {I : Type*} (energy : I → ℝ) (beta : ℝ) : ℝ :=
  (∑' i, energy i * Real.exp (-beta * energy i)) / partitionFunction energy beta

/-- Constructed inverse temperature, PDF p.7: the decreasing mean-energy function
crosses a positive budget E exactly once. This infimum selects that beta, not an
arbitrary optimizer field. The entropy construction below treats E=0 separately. -/
def gibbsInverseTemperature {I : Type*} (energy : I → ℝ) (E : ℝ) : ℝ :=
  sInf {beta : ℝ | 0 < beta ∧ thermalMeanEnergy energy beta ≤ E}

/-- Eigenvalues of the constructed Gibbs density, PDF p.7. At E=0 this is the
normalized ground-space projector, including ground degeneracy. For E>0 these
are exp(−beta(E) H)/Z. No unnormalizable maximally entangled vector is used. -/
def gibbsProbability {I : Type*} (energy : I → ℝ) (E : ℝ) (i : I) : ℝ :=
  if E = 0 then
    if energy i = 0 then (Set.ncard {j | energy j = 0} : ℝ)⁻¹ else 0
  else
    let beta := gibbsInverseTemperature energy E
    Real.exp (-beta * energy i) / partitionFunction energy beta

/-- Spectral von Neumann entropy of the constructed Gibbs state, in bits, PDF p.7.
For a Gibbs spectrum on a countably infinite space and finite E≥0 this real series
converges; it is the full spectral entropy, with 0 log 0 = 0. -/
def gibbsEntropy {I : Type*} (energy : I → ℝ) (E : ℝ) : ℝ :=
  ∑' i, -(gibbsProbability energy E i * Real.logb 2 (gibbsProbability energy E i))

/-- Full multimode Fock spectrum, Eq.(18), PDF p.10; a_i = hbar omega_i>0.
The labels are ALL occupations in N^ell, without a finite energy cutoff. -/
def oscillatorEnergy {ell : ℕ} (a : Fin ell → ℝ) (n : Fin ell → ℕ) : ℝ :=
  ∑ i, a i * (n i : ℝ)

/-! Sanity examples for paper-local definitions. -/

example {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (rho : Matrix (A × B) (A × B) ℂ) :
    finiteConditionalEntropy rho = vnEntropy rho - vnEntropy (traceLeft rho) := rfl

example : pureDensity (bellVector 1) (0, 0) (0, 0) = 1 := by
  simp [QAlgorithms.Papers.Independent.Information100.P08.bellVector, pureDensity]

example (d : ℕ) : isotropicDensity d 0 = (pureDensity (bellVector d)) := by
  simp [isotropicDensity]

example : zeroProductDensity 1 (0, 0) (0, 0) = 1 := by
  simp [zeroProductDensity, pureDensity]

example : positiveOperatorRelativeEntropyBits (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [positiveOperatorRelativeEntropyBits, cfc_one]

example {I : Type*} [Fintype I] [DecidableEq I] (C : Set (Matrix I I ℂ)) :
    relativeVariation C = sSup (relativeVariations C) := rfl

example {A B : Type*} (rho : Matrix (A × B) (A × B) ℂ)
    (p q : (Fin 0 → A) × (Fin 0 → B)) : groupedTensorPower rho 0 p q = 1 := by
  simp [groupedTensorPower]

example {I : Type*} (beta : ℝ) :
    thermalMeanEnergy (fun _ : I => 0) beta = 0 := by
  simp [thermalMeanEnergy]

example {I : Type*} (energy : I → ℝ) (i : I) (hi : energy i ≠ 0) :
    gibbsProbability energy 0 i = 0 := by
  simp [gibbsProbability, hi]

example : gibbsEntropy (fun n : ℕ => (n : ℝ)) 0 = 0 := by
  unfold gibbsEntropy
  have hzero : ∀ n : ℕ,
      -(gibbsProbability (fun m : ℕ => (m : ℝ)) 0 n *
        Real.logb 2 (gibbsProbability (fun m : ℕ => (m : ℝ)) 0 n)) = 0 := by
    intro n
    by_cases hn : n = 0
    · subst n
      simp [gibbsProbability]
    · simp [gibbsProbability, hn]
  simp only [hzero, tsum_zero]

example {ell : ℕ} (a : Fin ell → ℝ) : oscillatorEnergy a (fun _ => 0) = 0 := by
  simp [oscillatorEnergy]

end QAlgorithms.Papers.Independent.Dependency50.P15



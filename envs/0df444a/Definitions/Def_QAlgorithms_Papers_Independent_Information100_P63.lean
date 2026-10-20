-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63
-- name    : QAlgorithms_Papers_Independent_Information100_P63
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T12:31:34.176231+00:00
-- url     : https://prove2.me/theorems/257e4dab-bb13-415b-a5db-14ee00eb817d
-- title:
--   Definitions for Approximate majorization and high-order capacity of quantum depolarizing channels
-- statement:
--   The objects the formalized statements of *Approximate majorization and high-order capacity of quantum depolarizing channels* (arXiv:2609.37240) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Mat`
--   - `logTwo`: Base-two logarithm, §2.1, PDF pp.3–4; `0 log 0 = 0` in weighted sums.
--   - `eigen`: Ordered spectrum with multiplicity, §2.2, PDF p.4. Used only on Hermitian matrices.
--   - `lorenz`: Integer Lorenz ordinate, Eq.(7), PDF p.4.
--   - `defect`: One-sided defect, Eq.(9), PDF p.4. The supremum is over a nonempty finite set.
--   - `logDet`: Shifted log determinant with natural logarithm, Eq.(12), PDF p.5.
--   - `schatten`: Finite Schatten norm for a positive operator, §2.1, PDF p.3.
--   - `schattenInfinity`: Operator norm of a positive operator, §2.1, PDF p.3; spectra of states are nonempty.
--   - `intervalMass`: Probability of spectral surprisal in `(a,a+1]`, Eq.(32), PDF p.7. Zero eigenvalues carry no sampling mass.
--   - `concentration`: Lévy concentration `Q(S_X,1)`, Eq.(32), PDF p.7. For a state its value is in `(0,1]`.
--   - `informationVariance`: Spectral information variance in bits squared, Theorem 7, PDF p.9.
--   - `tensorPower`: Matrix tensor power on the source's `Fin n → I` register.
--   - `pMax`: Complete-positive endpoint, Eq.(1), PDF p.2; the subtraction is real.
--   - `alpha`: Distinguished eigenvalue, §2.1, PDF p.3.
--   - `beta`: Repeated eigenvalue, §2.1, PDF p.3.
--   - `reference`: Pure computational-basis reference output, Eq.(1), PDF pp.2–3.
--   - `depolarizingN`: Independent channel uses, including entangled inputs, Eq.(1), PDF p.2. The branch at `d=0` is unused: all channel results assume `d≥2`.
--   - `defectRate`: Explicit majorization error in Theorems 1,7,8; both logarithms have base two.
--   - `block`: Basis blocks `(⟨u_i|⊗I)R(|u_j⟩⊗I)`, Lemma 3, PDF p.5.
--   - `phaseDamping`: Phase damping on the first subsystem in the indicated basis, Eq.(10), PDF p.4.
--   - `Code`: Unassisted classical code with arbitrary code states and a collective POVM, §4, PDF p.10. Repeated states and zero POVM elements are allowed.
--   - `averageError`: Average error with equiprobable messages, Eq.(57), PDF p.10.
--   - `optimalMessages`: Full optimization defining `M*`, §4, PDF p.10. For a channel and `0≤ε<1`, this set is nonempty and bounded by `dim(O)/(1-ε)`.
--   - `quantumMessages`: Optimal unrestricted message size for the tensor depolarizing channel.
--   - `basisTransition`: Classical channel induced by basis encoding and measurement, Eq.(64), PDF p.11.
--   - `BasisCode`: Full classical block code for the induced channel, §4.2, PDF p.11.
--   - `basisError`: Average error of the complete classical code after basis measurement.
--   - `basisMessages`: Optimizes all basis codes, not just a single product-state input.
--   - `mixed`: Maximally mixed state, §2.1, PDF p.3.
--   - `testingBeta`: Hypothesis-testing type-II error, Eq.(58), PDF p.10. At the parameters used below the feasible set contains `I`, and its infimum is positive.
--   - `testingDivergence`: Unnormalized hypothesis-testing divergence in bits, Eq.(58), PDF p.10.
--   - `capacity`: Capacity in bits per use, Eq.(6), PDF p.3.
--   - `dispersion`: Dispersion in bits squared, Eq.(6), PDF pp.3–4.
--   - `normalCDF`: Standard normal CDF in Theorem 2, PDF p.3. The Gaussian density is integrable.
--   - `normalQuantile`: Normal quantile; the defining set is nonempty and bounded below when `0<ε<1`.
--   - `thirdOrder`: The three explicit terms in Eq.(5), PDF p.3.
--   - `counterX`: Fixed diagonal state in Eq.(75), PDF p.14.
--   - `counterY`: Fixed diagonal reference in Eq.(75), PDF p.14.
-- source:
--   Approximate majorization and high-order capacity of quantum depolarizing channels, arXiv:2609.37240v1, https://arxiv.org/abs/2609.37240v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P63

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Base-two logarithm, §2.1, PDF pp.3–4; `0 log 0 = 0` in weighted sums. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Ordered spectrum with multiplicity, §2.2, PDF p.4. Used only on Hermitian matrices. -/
def eigen {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) :
    Fin (Fintype.card I) → ℝ :=
  fun j => ascEigenvalues X (Fin.rev j)

/-- Integer Lorenz ordinate, Eq.(7), PDF p.4. -/
def lorenz {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) (k : ℕ) : ℝ :=
  ∑ j : Fin (Fintype.card I), if j.val < k then eigen X j else 0

/-- One-sided defect, Eq.(9), PDF p.4. The supremum is over a nonempty finite set. -/
def defect {I : Type*} [Fintype I] [DecidableEq I] (X Y : Mat I) : ℝ :=
  sSup (Set.range fun k : Fin (Fintype.card I + 1) => lorenz X k.val - lorenz Y k.val)

/-- Shifted log determinant with natural logarithm, Eq.(12), PDF p.5. -/
def logDet {I : Type*} [Fintype I] [DecidableEq I] (t : ℝ) (X : Mat I) : ℝ :=
  Real.log ((Matrix.det ((t : ℂ) • (1 : Mat I) + X)).re)

/-- Finite Schatten norm for a positive operator, §2.1, PDF p.3. -/
def schatten {I : Type*} [Fintype I] [DecidableEq I] (q : ℝ) (X : Mat I) : ℝ :=
  (∑ j, (eigen X j) ^ q) ^ (1 / q)

/-- Operator norm of a positive operator, §2.1, PDF p.3; spectra of states are nonempty. -/
def schattenInfinity {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) : ℝ :=
  sSup (Set.range (eigen X))

/-- Probability of spectral surprisal in `(a,a+1]`, Eq.(32), PDF p.7.
Zero eigenvalues carry no sampling mass. -/
def intervalMass {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) (a : ℝ) : ℝ :=
  ∑ j, if 0 < eigen X j ∧ a < -logTwo (eigen X j) ∧ -logTwo (eigen X j) ≤ a + 1
    then eigen X j else 0

/-- Lévy concentration `Q(S_X,1)`, Eq.(32), PDF p.7. For a state its value is in `(0,1]`. -/
def concentration {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) : ℝ :=
  sSup (Set.range (intervalMass X))

/-- Spectral information variance in bits squared, Theorem 7, PDF p.9. -/
def informationVariance {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) : ℝ :=
  ∑ j, eigen X j * (-logTwo (eigen X j) - vnEntropy X) ^ 2

/-- Matrix tensor power on the source's `Fin n → I` register. -/
def tensorPower {I : Type*} (n : ℕ) (X : Mat I) : Mat (Fin n → I) :=
  fun a b => ∏ i, X (a i) (b i)

/-- Complete-positive endpoint, Eq.(1), PDF p.2; the subtraction is real. -/
def pMax (d : ℕ) : ℝ := (d : ℝ)^2 / ((d : ℝ)^2 - 1)

/-- Distinguished eigenvalue, §2.1, PDF p.3. -/
def alpha (d : ℕ) (p : ℝ) : ℝ := 1 - p + p / d

/-- Repeated eigenvalue, §2.1, PDF p.3. -/
def beta (d : ℕ) (p : ℝ) : ℝ := p / d

/-- Pure computational-basis reference output, Eq.(1), PDF pp.2–3. -/
def reference (d n : ℕ) (p : ℝ) : Mat (Fin n → Fin d) :=
  tensorPower n (Matrix.diagonal fun j : Fin d =>
    ((if j.val = 0 then alpha d p else beta d p : ℝ) : ℂ))

/-- Independent channel uses, including entangled inputs, Eq.(1), PDF p.2.
The branch at `d=0` is unused: all channel results assume `d≥2`. -/
def depolarizingN (d n : ℕ) (p : ℝ) : Superop (Fin n → Fin d) (Fin n → Fin d) :=
  if hd : 0 < d then piSuperop (fun _ => QuditFidelity.depolarizingMap d hd p)
  else fun _ => 0

/-- Explicit majorization error in Theorems 1,7,8; both logarithms have base two. -/
def defectRate (k : ℝ) (n : ℕ) : ℝ :=
  k / Real.sqrt n * (logTwo (logTwo n) + 6)

/-- Basis blocks `(⟨u_i|⊗I)R(|u_j⟩⊗I)`, Lemma 3, PDF p.5. -/
def block {d m : ℕ} (U : Matrix (Fin d) (Fin d) ℂ)
    (R : Mat (Fin d × Fin m)) (i j : Fin d) : Mat (Fin m) :=
  fun a b => ∑ x, ∑ y, conj (U x i) * R (x,a) (y,b) * U y j

/-- Phase damping on the first subsystem in the indicated basis, Eq.(10), PDF p.4. -/
def phaseDamping {d m : ℕ} (p : ℝ) (U : Matrix (Fin d) (Fin d) ℂ)
    (R : Mat (Fin d × Fin m)) : Mat (Fin d × Fin m) :=
  ((1-p : ℝ) : ℂ) • R + (p : ℂ) •
    (fun a b => ∑ i, U a.1 i * block U R i i a.2 b.2 * conj (U b.1 i))

/-- Unassisted classical code with arbitrary code states and a collective POVM,
§4, PDF p.10. Repeated states and zero POVM elements are allowed. -/
structure Code (I O : Type*) [Fintype I] [Fintype O] [DecidableEq O] (M : ℕ) where
  positive : 0 < M
  word : Fin M → Mat I
  state : ∀ x, IsDensityMatrix (word x)
  measurement : Fin M → Mat O
  positiveMeasurement : ∀ x, (measurement x).PosSemidef
  complete : ∑ x, measurement x = 1

/-- Average error with equiprobable messages, Eq.(57), PDF p.10. -/
def averageError {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    {M : ℕ} (N : Superop I O) (C : Code I O M) : ℝ :=
  1 - (M : ℝ)⁻¹ * ∑ x, effectProb (C.measurement x) (N (C.word x))

/-- Full optimization defining `M*`, §4, PDF p.10.
For a channel and `0≤ε<1`, this set is nonempty and bounded by `dim(O)/(1-ε)`. -/
def optimalMessages {I O : Type*} [Fintype I] [Fintype O] [DecidableEq O]
    (N : Superop I O) (e : ℝ) : ℕ :=
  sSup {M | ∃ C : Code I O M, averageError N C ≤ e}

/-- Optimal unrestricted message size for the tensor depolarizing channel. -/
def quantumMessages (d n : ℕ) (p e : ℝ) : ℕ :=
  optimalMessages (depolarizingN d n p) e

/-- Classical channel induced by basis encoding and measurement, Eq.(64), PDF p.11. -/
def basisTransition (d n : ℕ) (p : ℝ) (y x : Fin n → Fin d) : ℝ :=
  ∏ i, if y i = x i then alpha d p else beta d p

/-- Full classical block code for the induced channel, §4.2, PDF p.11. -/
structure BasisCode (d n M : ℕ) where
  positive : 0 < M
  word : Fin M → (Fin n → Fin d)
  decoder : (Fin n → Fin d) → Fin M

/-- Average error of the complete classical code after basis measurement. -/
def basisError {d n M : ℕ} (p : ℝ) (C : BasisCode d n M) : ℝ :=
  1 - (M : ℝ)⁻¹ * ∑ x, ∑ y, if C.decoder y = x
    then basisTransition d n p y (C.word x) else 0

/-- Optimizes all basis codes, not just a single product-state input. -/
def basisMessages (d n : ℕ) (p e : ℝ) : ℕ :=
  sSup {M | ∃ C : BasisCode d n M, basisError p C ≤ e}

/-- Maximally mixed state, §2.1, PDF p.3. -/
def mixed {O : Type*} [Fintype O] [DecidableEq O] : Mat O :=
  ((Fintype.card O : ℂ)⁻¹) • 1

/-- Hypothesis-testing type-II error, Eq.(58), PDF p.10.
At the parameters used below the feasible set contains `I`, and its infimum is positive. -/
def testingBeta {O : Type*} [Fintype O] [DecidableEq O] (e : ℝ) (X Y : Mat O) : ℝ :=
  sInf {b | ∃ Q : Mat O, IsEffect Q ∧ 1-e ≤ effectProb Q X ∧ b = effectProb Q Y}

/-- Unnormalized hypothesis-testing divergence in bits, Eq.(58), PDF p.10. -/
def testingDivergence {O : Type*} [Fintype O] [DecidableEq O]
    (e : ℝ) (X Y : Mat O) : ℝ := -logTwo (testingBeta e X Y)

/-- Capacity in bits per use, Eq.(6), PDF p.3. -/
def capacity (d : ℕ) (p : ℝ) : ℝ :=
  logTwo d + alpha d p * logTwo (alpha d p) +
    (d-1 : ℝ) * beta d p * logTwo (beta d p)

/-- Dispersion in bits squared, Eq.(6), PDF pp.3–4. -/
def dispersion (d : ℕ) (p : ℝ) : ℝ :=
  if p = 0 then 0 else alpha d p * (1-alpha d p) *
    (logTwo (alpha d p) - logTwo (beta d p)) ^ 2

/-- Standard normal CDF in Theorem 2, PDF p.3. The Gaussian density is integrable. -/
def normalCDF (z : ℝ) : ℝ :=
  ∫ x in Set.Iic z, Real.exp (-x^2 / 2) / Real.sqrt (2 * Real.pi)

/-- Normal quantile; the defining set is nonempty and bounded below when `0<ε<1`. -/
def normalQuantile (e : ℝ) : ℝ := sInf {z | e ≤ normalCDF z}

/-- The three explicit terms in Eq.(5), PDF p.3. -/
def thirdOrder (d n : ℕ) (p e : ℝ) : ℝ :=
  n * capacity d p + Real.sqrt (n * dispersion d p) * normalQuantile e +
    (1/2 : ℝ) * logTwo n

/-- Fixed diagonal state in Eq.(75), PDF p.14. -/
def counterX : Mat (Fin 3) := Matrix.diagonal ![(42/100 : ℂ), 29/100, 29/100]

/-- Fixed diagonal reference in Eq.(75), PDF p.14. -/
def counterY : Mat (Fin 3) := Matrix.diagonal ![(40/100 : ℂ), 35/100, 25/100]

/-! Sanity checks for the new interfaces, with complete proofs. -/

example : logTwo 1 = 0 := by simp [logTwo]

example {I : Type*} [Fintype I] [DecidableEq I] (X : Mat I) : lorenz X 0 = 0 := by
  simp [lorenz]

example {I : Type*} (X : Mat I) (a b : Fin 0 → I) : tensorPower 0 X a b = 1 := by
  simp [tensorPower]

example : alpha 2 1 = 1/2 ∧ beta 2 1 = 1/2 := by norm_num [alpha, beta]

example {d m : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) (R : Mat (Fin d × Fin m)) :
    phaseDamping 0 U R = R := by
  funext a b
  change (((1 - (0 : ℝ) : ℝ) : ℂ) * R a b +
    (0 : ℂ) * (∑ i, U a.1 i * block U R i i a.2 b.2 * conj (U b.1 i))) = R a b
  simp only [sub_zero, Complex.ofReal_one, one_mul, zero_mul, add_zero]

example : dispersion 2 0 = 0 := by simp [dispersion]

example : counterX.trace = 1 ∧ counterY.trace = 1 := by
  norm_num [counterX, counterY, Matrix.trace, Fin.sum_univ_succ]

example {I : Type*} [Fintype I] [DecidableEq I] : logDet 1 (0 : Mat I) = 0 := by
  simp [logDet]

example {d : ℕ} (p : ℝ) (x y : Fin 0 → Fin d) : basisTransition d 0 p y x = 1 := by
  simp [basisTransition]

example : pMax 2 = 4/3 ∧ alpha 2 (pMax 2) = 1/3 ∧ beta 2 (pMax 2) = 2/3 := by
  norm_num [pMax, alpha, beta]

end QAlgorithms.Papers.Independent.Information100.P63



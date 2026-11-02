-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P50
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:49:28.923028+00:00
-- url     : https://prove2.me/theorems/a6e369af-fad8-484c-8f6c-b11d686712d0
-- title:
--   Definitions for Quantum and private capacities of low-noise channels
-- statement:
--   The objects the formalized statements of *Quantum and private capacities of low-noise channels* (arXiv:1705.04335) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dilationQuantumCapacity`: §2.3, PDF p.6: the accepted operational quantum capacity applied to the receiver of this dilation; this adapter does not define capacity by an entropy formula.
--   - `channelDifference`: §2.2, PDF p.4: pointwise difference of channel maps on every input matrix. Distinct from the accepted entropy-difference scalar function.
--   - `maxEntry`: §2.2, PDF p.4: entrywise maximum. Used only on nonempty finite index types.
--   - `dilationChoiRank`: §2.1, PDF p.4: actual Choi rank; redundant environment coordinates do not count.
--   - `degradability`: Definition 5, PDF p.7: minimize full diamond error over all CPTP degraders. On physical nonempty finite systems the admissible set is nonempty in [0,2].
--   - `quantumCorrection`: §3.1, PDF p.8, (9): quantum correction, used for Choi rank e≥2 near eta=0.
--   - `privateCorrection`: §3.1, PDF p.10: full private correction f2, with coefficients 1,4,2,4. Only used on e≥2 and physical eta near zero.
--   - `quantumPolynomialLeading`: Lemma 9, PDF p.9: retained terms, evaluated only for c>0, p>0, e≥2.
--   - `privatePolynomialLeading`: Lemma 10, PDF p.10: retained private-capacity terms.
--   - `quantumLowNoiseLeading`: Theorem 12, PDF p.12: quantum expression; the exponent in the first term is 1.5.
--   - `privateLowNoiseLeading`: Theorem 12, PDF p.12: private expression, with all rank-dependent coefficients.
--   - `LowNoiseCapacityBounds`: Theorem 12, PDF p.12: rank-one and zero-noise branches are exact; log(0) is never used as a physical logarithm. Both eventual remainders are retained.
--   - `Probabilities`: §4, PDF p.12: all probabilities are nonnegative and sum to one.
--   - `pauliKrausOperator`: §4, PDF pp.12–13: canonical Kraus labels I,X,Y,Z.
--   - `pauliDilation`: Appendix A, PDF p.20: four-dimensional canonical Pauli dilation. Zero-probability labels remain present. Physicality is the probability simplex.
--   - `depolarizingDilation`: §4.1, PDF p.13, (15): p is TOTAL nonidentity Pauli error.
--   - `xzDilation`: §4.2, PDF p.17, (25): independent equal X and Z errors, each with probability p.
--   - `depolarizingHashing`: §4.1, PDF p.15: hashing expression, used only eventually near p=0.
--   - `polynomialWeights`: §4.2, PDF p.16: THREE noise polynomials; p0 is their complement.
--   - `PolynomialNoise`: §4.2, PDF p.16: zero constant terms and physical probabilities near zero. Eventual validity suffices for asymptotic conclusions; no constant-rank assumption.
--   - `linearCoefficient`: Theorem 15, PDF p.16: coefficient of the linear term of each polynomial.
--   - `pairCoefficient`: Corollary 16, PDF p.17: coefficient C_p; includes the zero case.
--   - `modifiedWeights`: §4.2, PDF p.16, (22) and footnote 2: EVALUATE each polynomial at p+a_i p².
--   - `positiveCyclicShift`: §4, PDF p.12: positive cyclic shift X|i>=|i+1>.
--   - `quditPauliDilation`: §4, PDF p.12: canonical generalized Pauli dilation in X^k Z^l ordering.
--   - `composedDilation`: §5, PDF pp.18–19: compatible sequential dilation; environment order E1,E2.
--   - `recoveryDegrader`: §5, PDF p.19: the explicitly constructed degrader for the ORIGINAL channel.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, https://arxiv.org/abs/1705.04335v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P80
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}
variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

/-! Exact accepted definitions are imported from the pinned library. The independent
paper workflow permits these accepted modules; no unreviewed module is imported.
The source role here is arXiv:1705.04335v3, §2.1–2.3, PDF pp.3–7.
Only genuine paper-specific constructions remain local. -/

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)
open QAlgorithms.Papers.Independent.Information100.P80 (log2)
open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)
open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)
open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- §2.3, PDF p.6: the accepted operational quantum capacity applied to the
receiver of this dilation; this adapter does not define capacity by an entropy formula. -/
def dilationQuantumCapacity (V : Matrix (B × E) A ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P80.quantumCapacity (receiverChannel V)

/-- §2.2, PDF p.4: pointwise difference of channel maps on every input matrix.
Distinct from the accepted entropy-difference scalar function. -/
def channelDifference (Phi Psi : Superop A B) : Superop A B := fun X => Phi X - Psi X

/-- §2.2, PDF p.4: entrywise maximum. Used only on nonempty finite index types. -/
def maxEntry (X : Matrix A B ℂ) : ℝ := sSup {v | ∃ i j, v = ‖X i j‖}

/-- §2.1, PDF p.4: actual Choi rank; redundant environment coordinates do not count. -/
def dilationChoiRank (V : Matrix (B × E) A ℂ) : ℕ := (choi (receiverChannel V)).rank

/-- Definition 5, PDF p.7: minimize full diamond error over all CPTP degraders.
On physical nonempty finite systems the admissible set is nonempty in [0,2]. -/
def degradability (V : Matrix (B × E) A ℂ) : ℝ :=
  sInf {eta : ℝ | 0 ≤ eta ∧ eta ≤ 2 ∧ ∃ D : Superop B E, IsChannel D ∧
    diamond (channelDifference (complementaryChannel V) (D ∘ receiverChannel V)) ≤ eta}

/-- §3.1, PDF p.8, (9): quantum correction, used for Choi rank e≥2 near eta=0. -/
def quantumCorrection (e : ℕ) (eta : ℝ) : ℝ :=
  eta / 2 * log2 ((e : ℝ) - 1) + eta * log2 e + binEntropy2 (eta / 2) +
    (1 + eta / 2) * binEntropy2 (eta / (2 + eta))

/-- §3.1, PDF p.10: full private correction f2, with coefficients 1,4,2,4.
Only used on e≥2 and physical eta near zero. -/
def privateCorrection (e : ℕ) (eta : ℝ) : ℝ :=
  eta * log2 ((e : ℝ) - 1) + 4 * eta * log2 e + 2 * binEntropy2 (eta / 2) +
    4 * (1 + eta / 2) * binEntropy2 (eta / (2 + eta))

/-- Lemma 9, PDF p.9: retained terms, evaluated only for c>0, p>0, e≥2. -/
def quantumPolynomialLeading (e : ℕ) (c r p : ℝ) : ℝ :=
  c * r * p ^ (r - 1) * (-p * log2 p) + c * p ^ r *
    (-log2 c + 1 + (Real.log 2)⁻¹ + log2 e + log2 ((e : ℝ) - 1) / 2)

/-- Lemma 10, PDF p.10: retained private-capacity terms. -/
def privatePolynomialLeading (e : ℕ) (c r p : ℝ) : ℝ :=
  3 * c * r * p ^ (r - 1) * (-p * log2 p) + c * p ^ r *
    (-3 * log2 c + 3 + 3 * (Real.log 2)⁻¹ + log2 ((e : ℝ) - 1) + 4 * log2 e)

/-- Theorem 12, PDF p.12: quantum expression; the exponent in the first term is 1.5. -/
def quantumLowNoiseLeading (e : ℕ) (eps : ℝ) : ℝ :=
  -3 * eps ^ (3 / 2 : ℝ) * log2 eps +
    ((Real.log 2)⁻¹ + log2 e + log2 ((e : ℝ) - 1) / 2) * 2 * eps ^ (3 / 2 : ℝ)

/-- Theorem 12, PDF p.12: private expression, with all rank-dependent coefficients. -/
def privateLowNoiseLeading (e : ℕ) (eps : ℝ) : ℝ :=
  -9 * eps ^ (3 / 2 : ℝ) * log2 eps +
    (3 * (Real.log 2)⁻¹ + 4 * log2 e + log2 ((e : ℝ) - 1)) * 2 * eps ^ (3 / 2 : ℝ)

/-- Theorem 12, PDF p.12: rank-one and zero-noise branches are exact; log(0) is
never used as a physical logarithm. Both eventual remainders are retained. -/
def LowNoiseCapacityBounds (V : Matrix (B × E) A ℂ) (eps Cq Cp : ℝ) : Prop :=
  if dilationChoiRank V = 1 ∨ eps = 0 then
    dilationQuantumCapacity V = maximumCoherentInformation V ∧ fullTracePrivateCapacity V = maximumCoherentInformation V
  else
    |dilationQuantumCapacity V - maximumCoherentInformation V| ≤
      quantumLowNoiseLeading (dilationChoiRank V) eps + Cq * eps ^ (9 / 2 : ℝ) ∧
    |fullTracePrivateCapacity V - maximumCoherentInformation V| ≤
      privateLowNoiseLeading (dilationChoiRank V) eps + Cp * eps ^ (3 : ℕ)

/-- §4, PDF p.12: all probabilities are nonnegative and sum to one. -/
def Probabilities {I : Type} [Fintype I] (w : I → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

/-- §4, PDF pp.12–13: canonical Kraus labels I,X,Y,Z. -/
def pauliKrausOperator : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![1, !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- Appendix A, PDF p.20: four-dimensional canonical Pauli dilation.
Zero-probability labels remain present. Physicality is the probability simplex. -/
def pauliDilation (w : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ :=
  fun be a => (Real.sqrt (w be.2) : ℂ) * pauliKrausOperator be.2 be.1 a

/-- §4.1, PDF p.13, (15): p is TOTAL nonidentity Pauli error. -/
def depolarizingDilation (p : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ :=
  pauliDilation ![1 - p, p / 3, p / 3, p / 3]

/-- §4.2, PDF p.17, (25): independent equal X and Z errors, each with probability p. -/
def xzDilation (p : ℝ) : Matrix (Fin 2 × Fin 4) (Fin 2) ℂ :=
  pauliDilation ![(1 - p) ^ 2, p - p ^ 2, p ^ 2, p - p ^ 2]

/-- §4.1, PDF p.15: hashing expression, used only eventually near p=0. -/
def depolarizingHashing (p : ℝ) : ℝ := 1 - binEntropy2 p - p * log2 3

/-- §4.2, PDF p.16: THREE noise polynomials; p0 is their complement. -/
def polynomialWeights (P : Fin 3 → Polynomial ℝ) (p : ℝ) : Fin 4 → ℝ :=
  ![1 - ∑ i, (P i).eval p, (P 0).eval p, (P 1).eval p, (P 2).eval p]

/-- §4.2, PDF p.16: zero constant terms and physical probabilities near zero.
Eventual validity suffices for asymptotic conclusions; no constant-rank assumption. -/
def PolynomialNoise (P : Fin 3 → Polynomial ℝ) : Prop :=
  (∀ i, (P i).eval 0 = 0) ∧ ∃ delta : ℝ, 0 < delta ∧
    ∀ p ∈ Set.Icc 0 delta, Probabilities (polynomialWeights P p)

/-- Theorem 15, PDF p.16: coefficient of the linear term of each polynomial. -/
def linearCoefficient (P : Fin 3 → Polynomial ℝ) (i : Fin 3) : ℝ := (P i).coeff 1

/-- Corollary 16, PDF p.17: coefficient C_p; includes the zero case. -/
def pairCoefficient (P : Fin 3 → Polynomial ℝ) : ℝ :=
  |linearCoefficient P 0 * linearCoefficient P 1 +
    linearCoefficient P 0 * linearCoefficient P 2 +
    linearCoefficient P 1 * linearCoefficient P 2|

/-- §4.2, PDF p.16, (22) and footnote 2: EVALUATE each polynomial at p+a_i p². -/
def modifiedWeights (P : Fin 3 → Polynomial ℝ) (a : Fin 3 → ℝ) (p : ℝ) : Fin 4 → ℝ :=
  let q := fun i : Fin 3 => (P i).eval (p + a i * p ^ 2)
  ![1 - ∑ i, q i, q 0, q 1, q 2]

/-- §4, PDF p.12: positive cyclic shift X|i>=|i+1>. -/
def positiveCyclicShift (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i.val = (j.val + 1) % d then 1 else 0

/-- §4, PDF p.12: canonical generalized Pauli dilation in X^k Z^l ordering. -/
def quditPauliDilation (d : ℕ) (w : (Fin d × Fin d) → ℝ) :
    Matrix (Fin d × (Fin d × Fin d)) (Fin d) ℂ :=
  fun be a => (Real.sqrt (w be.2) : ℂ) *
    (positiveCyclicShift d ^ be.2.1.val * clock d ^ be.2.2.val) be.1 a

/-! Sanity checks of local conventions, not proofs of source results. -/

example : log2 1 = 0 := by simp [log2]

example (V : Matrix (B × E) A ℂ) (rho : Matrix A A ℂ) :
    complementaryChannel V rho = traceLeft (V * rho * Vᴴ) := rfl

example (Phi : Superop A B) (a c : A) (b d : B) :
    choi Phi (a,b) (c,d) = Phi (Matrix.single a c 1) b d := rfl

example (V : Matrix (B × E) A ℂ)
    (be : (Fin 0 → B) × (Fin 0 → E)) (a : Fin 0 → A) :
    dilationPower V 0 be a = 1 := by simp [dilationPower]

example (m : ℕ) (sigma : Matrix E E ℂ) (i : Fin m) (e f : E) :
    idealJoint m sigma (i,(i,e)) (i,(i,f)) = (m : ℂ)⁻¹ * sigma e f := by
  simp [idealJoint]

example : pauliKrausOperator 1 0 1 = 1 ∧ pauliKrausOperator 2 0 1 = -Complex.I := by constructor <;> rfl

example (P : Fin 3 → Polynomial ℝ) (a : Fin 3 → ℝ) (p : ℝ) :
    modifiedWeights P a p 1 = (P 0).eval (p + a 0 * p ^ 2) := rfl

example : positiveCyclicShift 2 1 0 = 1 := by norm_num [positiveCyclicShift]

/-- The three-dimensional case distinguishes the forward shift from its inverse. -/
example : positiveCyclicShift 3 1 0 = 1 ∧ positiveCyclicShift 3 2 0 = 0 := by
  norm_num [positiveCyclicShift]

example (p : ℝ) : xzDilation p =
    pauliDilation ![(1 - p) ^ 2, p - p ^ 2, p ^ 2, p - p ^ 2] := rfl

example (e : ℕ) : quantumCorrection e 0 = 0 := by
  simp [quantumCorrection, binEntropy2]

example (e : ℕ) : privateCorrection e 0 = 0 := by
  simp [privateCorrection, binEntropy2]

example : depolarizingDilation 0 (0,0) 0 = 1 := by
  norm_num [depolarizingDilation, pauliDilation, pauliKrausOperator]

/-- §5, PDF pp.18–19: compatible sequential dilation; environment order E1,E2. -/
def composedDilation (V : Matrix (B × E) A ℂ) (W : Matrix (A × F) B ℂ) :
    Matrix (A × (E × F)) A ℂ :=
  fun ae a => ∑ b, W (ae.1, ae.2.2) b * V (b, ae.2.1) a

/-- §5, PDF p.19: the explicitly constructed degrader for the ORIGINAL channel. -/
def recoveryDegrader (V : Matrix (B × E) A ℂ) (W : Matrix (A × F) B ℂ) : Superop B E :=
  fun rho => traceRight (complementaryChannel (composedDilation V W) (receiverChannel W rho))

example (V : Matrix (B × E) A ℂ) (W : Matrix (A × F) B ℂ)
    (a c : A) (e : E) (f : F) :
    composedDilation V W (a,(e,f)) c = ∑ b, W (a,f) b * V (b,e) c := rfl

end QAlgorithms.Papers.Independent.Intakethird100.P50



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18
-- name    : QAlgorithms_Papers_Independent_Support21_P18
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:45:55.590427+00:00
-- url     : https://prove2.me/theorems/1319a39a-6d6b-4409-b8a7-5cd043afd3f0
-- title:
--   Definitions for Optimal Manipulations with Qubits: Universal NOT Gate
-- statement:
--   The objects the formalized statements of *Optimal Manipulations with Qubits: Universal NOT Gate* (arXiv:quant-ph/9901053) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `bitIndex`: PDF p.2: physical qubit coordinates, 0 for false and 1 for true.
--   - `SymmetricBasis`: PDF p.2: the real normalized occupation basis of the symmetric N-qubit space.
--   - `occupationEmbedding`: PDF p.2: the normalized Dicke columns, with k occurrences of |1>.
--   - `symmetricQubitKet`: PDF p.2: |psi> tensor N in occupation coordinates.
--   - `physicalPower`: PDF pp.2-3: the same tensor-power vector in the physical bit register.
--   - `theta`: PDF p.1, Eq.(1): the fixed antiunitary phase convention.
--   - `orthogonalDensity`: PDF p.2: the orthogonal pure-state complement, used only on unit vectors.
--   - `pureLaw`: PDF p.2: normalized invariant pure-qubit integration, lifted from rays to vectors. Every integrand used below is invariant under multiplying the vector by a phase.
--   - `estimationEffect`: PDF p.2, Eq.(3): the positive operator density on the symmetric input space.
--   - `estimationWeight`: PDF p.2, Eq.(3): complex-linear extension of the Born weight to every operator. Its real part is the probability density on density operators. Keeping the complex trace here is essential for the channel to be complex-linear on all matrices.
--   - `estimationLaw`: PDF p.2, Eq.(3): the actual outcome law, relative to normalized pure-state measure.
--   - `measurementNot`: PDF p.2, Eq.(4): the measurement-based single-qubit output, on every operator.
--   - `qubitOperatorPower`: PDF p.3: the accepted matrix tensor power, reindexed to physical Bool registers. The P63 construction is the same product on Fin-2 words; only coordinates change.
--   - `measurementMany`: PDF p.3 after Eq.(6): one common estimate prepares all M outputs. This is the integral of tensor powers, not a tensor power of the averaged state.
--   - `errorValues`: PDF p.2, Eq.(2): all overlaps whose maximum is the gate error. For lawful channels this nonempty set is compact and lies in [0,1], so sSup is the source's maximum, rather than an empty-set or unbounded-set default.
--   - `notError`: PDF p.2, Eq.(2): worst-case overlap with the original state.
--   - `complementOutput`: PDF p.3, Eq.(6): single-output complement density.
--   - `cloneShrink`: PDF p.3, Eq.(9): clone shrinkage; the second numerator is 2N.
--   - `cloneOutput`: PDF p.3, Eq.(9): a single clone's reduced density.
--   - `siteReduction`: PDF p.3: one-site partial trace on physical qubits, reindexed to Fin 2.
--   - `pairReduction`: PDF p.3: two distinct output sites, in the indicated order. The diagonal sum runs over the first site's and second site's fixed values exactly once.
--   - `braceKet`: PDF p.3, Eqs.(7),(8): normalized symmetric brace ket with j copies of v and L-j copies of u. It is normalized when u,v form an orthonormal pair and j<=L. No normalization is imposed as an extra hypothesis on the resulting gate.
--   - `notAmplitude`: PDF p.3, Eq.(7), checked in the rendered PDF: signed amplitude, with both square-root factors and denominator choose(N+M+1,M).
--   - `quantumOutput`: PDF p.3, Eqs.(7),(8): the explicit joint vector. The first factor has N+M clones (registers a,b) and the second has M complements (register c).
--   - `gateInput`: PDF p.3: input psi tensor N with one fixed state X on the b,c registers, regrouped onto the same carrier as quantumOutput.
--   - `quantumComplements`: PDF p.3: complementary output register c, with all clone qubits discarded.
--   - `quantumClones`: PDF p.3: clone register a,b, with all complemented qubits discarded.
--   - `tensorRotation`: PDF pp.2,4: actual tensor-power action on the physical qubits.
--   - `symmetricAction`: PDF pp.2,4: restriction of U tensor N to the real occupation basis.
--   - `rotateGate`: PDF p.2 after Eq.(2): rotating an arbitrary N-copy-to-qubit gate.
--   - `twirlGate`: PDF p.4, Eq.(10): the normalized Haar average, constructed on all operators.
--   - `IsUniversallyCovariant`: PDF pp.2,4: universality is covariance for every physical U(2) rotation.
--   - `lowerIsometry`: PDF p.4, Eq.(12): the spin-(N-1)/2 environment intertwiner. Zero boundary coefficients are omitted by the index tests. Theorems using it require N>=1.
--   - `upperIsometry`: PDF p.4, Eq.(12): the spin-(N+1)/2 environment intertwiner, in the fixed occupation phases. The minus sign is an amplitude, not a negative probability.
--   - `lowerChannel`: PDF p.4, Eq.(12): the actual channel obtained by discarding the environment.
--   - `upperChannel`: PDF p.4, Eq.(12): the other actual channel, discarding its larger environment.
--   - `realNotMatrix`: PDF pp.1-2,4: one input-independent linear operation for real input states.
--   - `HasRealCoordinates`: PDF p.4: reality is in the specified computational basis, not an arbitrary basis chosen separately for each unknown input. Density equality covers rays.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, https://arxiv.org/abs/quant-ph/9901053v1

import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
import Definitions.Def_QAlgorithms_Defs_BipartiteSeparability
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Defs_ContinuousPOVMDensities
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
Statements from Buzek, Hillery and Werner, *Optimal Manipulations with Qubits:
Universal NOT Gate*, arXiv:quant-ph/9901053v1 (1999), PDF pp.1-4.

The symmetric input space is represented in the real normalized occupation basis
indexed by `Fin (N+1)`. `occupationEmbedding` explicitly identifies it with the
permutation-fixed subspace of the frozen physical register `Qubits N`.
The physical qubit uses `Fin 2`; `bitIndex` fixes its identification with `Bool`.
All new objects are local to this paper. No channel depends on its unknown input.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter
open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

/-- PDF p.2: physical qubit coordinates, 0 for false and 1 for true. -/
def bitIndex (b : Bool) : Fin 2 := if b then 1 else 0

/-- PDF p.2: the real normalized occupation basis of the symmetric N-qubit space. -/
abbrev SymmetricBasis (N : ℕ) := Fin (N + 1)

/-- PDF p.2: the normalized Dicke columns, with k occurrences of |1>. -/
def occupationEmbedding (N : ℕ) : Matrix (Qubits N) (SymmetricBasis N) ℂ :=
  fun x k => if hammingWeight x = k.val then
    ((Real.sqrt (Nat.choose N k.val : ℝ))⁻¹ : ℂ) else 0

/-- PDF p.2: |psi> tensor N in occupation coordinates. -/
def symmetricQubitKet (N : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (SymmetricBasis N) :=
  WithLp.toLp 2 fun k => (Real.sqrt (Nat.choose N k.val : ℝ) : ℂ) *
    psi 0 ^ (N - k.val) * psi 1 ^ k.val

/-- PDF pp.2-3: the same tensor-power vector in the physical bit register. -/
def physicalPower (N : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Qubits N) :=
  WithLp.toLp 2 fun x => ∏ i, psi (bitIndex (x i))

/-- PDF p.1, Eq.(1): the fixed antiunitary phase convention. -/
def theta (psi : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![conj (psi 1), -conj (psi 0)]

/-- PDF p.2: the orthogonal pure-state complement, used only on unit vectors. -/
def orthogonalDensity (psi : EuclideanSpace ℂ (Fin 2)) : Matrix (Fin 2) (Fin 2) ℂ :=
  1 - pureDensity psi

/-- PDF p.2: normalized invariant pure-qubit integration, lifted from rays to vectors.
Every integrand used below is invariant under multiplying the vector by a phase. -/
def pureLaw : Measure (EuclideanSpace ℂ (Fin 2)) :=
  QuditFidelity.haarPureStateLaw 2 (by norm_num)

/-- PDF p.2, Eq.(3): the positive operator density on the symmetric input space. -/
def estimationEffect (N : ℕ) (phi : EuclideanSpace ℂ (Fin 2)) :
    Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ :=
  ((N + 1 : ℕ) : ℂ) • pureDensity (symmetricQubitKet N phi)

/-- PDF p.2, Eq.(3): complex-linear extension of the Born weight to every operator.
Its real part is the probability density on density operators. Keeping the complex
trace here is essential for the channel to be complex-linear on all matrices. -/
def estimationWeight (N : ℕ) (rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ)
    (phi : EuclideanSpace ℂ (Fin 2)) : ℂ :=
  (estimationEffect N phi * rho).trace

/-- PDF p.2, Eq.(3): the actual outcome law, relative to normalized pure-state measure. -/
def estimationLaw (N : ℕ) (rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ) :
    Measure (EuclideanSpace ℂ (Fin 2)) :=
  pureLaw.withDensity (fun phi => ENNReal.ofReal (estimationWeight N rho phi).re)

/-- PDF p.2, Eq.(4): the measurement-based single-qubit output, on every operator. -/
def measurementNot (N : ℕ) : Superop (SymmetricBasis N) (Fin 2) :=
  fun rho => ∫ phi, estimationWeight N rho phi • orthogonalDensity phi ∂pureLaw

/-- PDF p.3: the accepted matrix tensor power, reindexed to physical Bool registers.
The P63 construction is the same product on Fin-2 words; only coordinates change. -/
def qubitOperatorPower (M : ℕ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Qubits M) (Qubits M) ℂ :=
  (QAlgorithms.Papers.Independent.Information100.P63.tensorPower M A).submatrix
    (fun x i => bitIndex (x i)) (fun y i => bitIndex (y i))

/-- PDF p.3 after Eq.(6): one common estimate prepares all M outputs.
This is the integral of tensor powers, not a tensor power of the averaged state. -/
def measurementMany (N M : ℕ) : Superop (SymmetricBasis N) (Qubits M) :=
  fun rho => ∫ phi, estimationWeight N rho phi • qubitOperatorPower M (orthogonalDensity phi) ∂pureLaw

/-- PDF p.2, Eq.(2): all overlaps whose maximum is the gate error. For lawful
channels this nonempty set is compact and lies in [0,1], so sSup is the source's
maximum, rather than an empty-set or unbounded-set default. -/
def errorValues (N : ℕ) (T : Superop (SymmetricBasis N) (Fin 2)) : Set ℝ :=
  {r | ∃ psi : EuclideanSpace ℂ (Fin 2), IsState psi ∧
    r = effectProb (pureDensity psi) (T (pureDensity (symmetricQubitKet N psi)))}

/-- PDF p.2, Eq.(2): worst-case overlap with the original state. -/
def notError (N : ℕ) (T : Superop (SymmetricBasis N) (Fin 2)) : ℝ :=
  sSup (errorValues N T)

/-- PDF p.3, Eq.(6): single-output complement density. -/
def complementOutput (N : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  ((N : ℂ) / (N + 2)) • orthogonalDensity psi + (1 / (N + 2 : ℂ)) • 1

/-- PDF p.3, Eq.(9): clone shrinkage; the second numerator is 2N. -/
def cloneShrink (N M : ℕ) : ℝ :=
  (N : ℝ) / (N + 2) + 2 * N / (((N : ℝ) + M) * (N + 2))

/-- PDF p.3, Eq.(9): a single clone's reduced density. -/
def cloneOutput (N M : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (cloneShrink N M : ℂ) • pureDensity psi + ((1 - cloneShrink N M) / 2 : ℂ) • 1

/-- PDF p.3: one-site partial trace on physical qubits, reindexed to Fin 2. -/
def siteReduction {L : ℕ} (rho : Matrix (Qubits L) (Qubits L) ℂ) (i : Fin L) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => ∑ x : Qubits L,
    if bitIndex (x i) = a then rho x (Function.update x i (decide (b = 1))) else 0

/-- PDF p.3: two distinct output sites, in the indicated order. The diagonal
sum runs over the first site's and second site's fixed values exactly once. -/
def pairReduction {L : ℕ} (rho : Matrix (Qubits L) (Qubits L) ℂ) (i j : Fin L) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun a b => ∑ x : Qubits L,
    if bitIndex (x i) = a.1 ∧ bitIndex (x j) = a.2 then
      rho x (Function.update (Function.update x i (decide (b.1 = 1))) j (decide (b.2 = 1))) else 0

/-- PDF p.3, Eqs.(7),(8): normalized symmetric brace ket with j copies of v
and L-j copies of u. It is normalized when u,v form an orthonormal pair and j<=L.
No normalization is imposed as an extra hypothesis on the resulting gate. -/
def braceKet (L j : ℕ) (u v : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Qubits L) :=
  WithLp.toLp 2 fun x => ((Real.sqrt (Nat.choose L j : ℝ))⁻¹ : ℂ) *
    ∑ S : Finset (Fin L), if S.card = j then
      ∏ i, if i ∈ S then v (bitIndex (x i)) else u (bitIndex (x i)) else 0

/-- PDF p.3, Eq.(7), checked in the rendered PDF: signed amplitude, with both
square-root factors and denominator choose(N+M+1,M). -/
def notAmplitude (N M j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * Real.sqrt (Nat.choose (N + M - j) N : ℝ) *
    (Real.sqrt (Nat.choose (N + M + 1) M : ℝ))⁻¹

/-- PDF p.3, Eqs.(7),(8): the explicit joint vector. The first factor has
N+M clones (registers a,b) and the second has M complements (register c). -/
def quantumOutput (N M : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    EuclideanSpace ℂ (Qubits (N + M) × Qubits M) :=
  ∑ j : Fin (M + 1), (notAmplitude N M j.val : ℂ) •
    tensorVec (braceKet (N + M) j.val psi (theta psi))
      (braceKet M j.val (theta psi) psi)

/-- PDF p.3: input psi tensor N with one fixed state X on the b,c registers,
regrouped onto the same carrier as quantumOutput. -/
def gateInput (N M : ℕ) (psi : EuclideanSpace ℂ (Fin 2))
    (X : EuclideanSpace ℂ (Qubits M × Qubits M)) :
    EuclideanSpace ℂ (Qubits (N + M) × Qubits M) :=
  WithLp.toLp 2 fun x =>
    physicalPower N psi ((qubitsAppendEquiv N M x.1).1) *
      X ((qubitsAppendEquiv N M x.1).2, x.2)

/-- PDF p.3: complementary output register c, with all clone qubits discarded. -/
def quantumComplements (N M : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    Matrix (Qubits M) (Qubits M) ℂ :=
  traceLeft (pureDensity (quantumOutput N M psi))

/-- PDF p.3: clone register a,b, with all complemented qubits discarded. -/
def quantumClones (N M : ℕ) (psi : EuclideanSpace ℂ (Fin 2)) :
    Matrix (Qubits (N + M)) (Qubits (N + M)) ℂ :=
  traceRight (pureDensity (quantumOutput N M psi))

/-- PDF pp.2,4: actual tensor-power action on the physical qubits. -/
def tensorRotation (N : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Qubits N) (Qubits N) ℂ := qubitOperatorPower N U

/-- PDF pp.2,4: restriction of U tensor N to the real occupation basis. -/
def symmetricAction (N : ℕ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ :=
  (occupationEmbedding N)ᴴ * tensorRotation N U * occupationEmbedding N

/-- PDF p.2 after Eq.(2): rotating an arbitrary N-copy-to-qubit gate. -/
def rotateGate (N : ℕ) (U : Matrix.unitaryGroup (Fin 2) ℂ)
    (T : Superop (SymmetricBasis N) (Fin 2)) : Superop (SymmetricBasis N) (Fin 2) :=
  fun rho => conjSuperop (U.val)ᴴ (T (conjSuperop (symmetricAction N U.val) rho))

/-- PDF p.4, Eq.(10): the normalized Haar average, constructed on all operators. -/
def twirlGate (N : ℕ) (T : Superop (SymmetricBasis N) (Fin 2)) :
    Superop (SymmetricBasis N) (Fin 2) :=
  fun rho => ∫ U, rotateGate N U T rho ∂Schur.unitaryHaar 2

/-- PDF pp.2,4: universality is covariance for every physical U(2) rotation. -/
def IsUniversallyCovariant (N : ℕ) (T : Superop (SymmetricBasis N) (Fin 2)) : Prop :=
  ∀ U : Matrix.unitaryGroup (Fin 2) ℂ, rotateGate N U T = T

/-- PDF p.4, Eq.(12): the spin-(N-1)/2 environment intertwiner. Zero boundary
coefficients are omitted by the index tests. Theorems using it require N>=1. -/
def lowerIsometry (N : ℕ) : Matrix (Fin 2 × SymmetricBasis (N - 1)) (SymmetricBasis N) ℂ :=
  fun a k => if a.1 = 0 ∧ a.2.val = k.val then
      (Real.sqrt (((N - k.val : ℕ) : ℝ) / N) : ℂ)
    else if a.1 = 1 ∧ a.2.val + 1 = k.val then
      (Real.sqrt ((k.val : ℝ) / N) : ℂ) else 0

/-- PDF p.4, Eq.(12): the spin-(N+1)/2 environment intertwiner, in the fixed
occupation phases. The minus sign is an amplitude, not a negative probability. -/
def upperIsometry (N : ℕ) : Matrix (Fin 2 × SymmetricBasis (N + 1)) (SymmetricBasis N) ℂ :=
  fun a k => if a.1 = 0 ∧ a.2.val = k.val + 1 then
      (Real.sqrt (((k.val : ℝ) + 1) / (N + 2)) : ℂ)
    else if a.1 = 1 ∧ a.2.val = k.val then
      -(Real.sqrt ((((N - k.val : ℕ) : ℝ) + 1) / (N + 2)) : ℂ) else 0

/-- PDF p.4, Eq.(12): the actual channel obtained by discarding the environment. -/
def lowerChannel (N : ℕ) : Superop (SymmetricBasis N) (Fin 2) :=
  fun rho => traceRight (lowerIsometry N * rho * (lowerIsometry N)ᴴ)

/-- PDF p.4, Eq.(12): the other actual channel, discarding its larger environment. -/
def upperChannel (N : ℕ) : Superop (SymmetricBasis N) (Fin 2) :=
  fun rho => traceRight (upperIsometry N * rho * (upperIsometry N)ᴴ)

/-- PDF pp.1-2,4: one input-independent linear operation for real input states. -/
def realNotMatrix : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- PDF p.4: reality is in the specified computational basis, not an arbitrary
basis chosen separately for each unknown input. Density equality covers rays. -/
def HasRealCoordinates (psi : EuclideanSpace ℂ (Fin 2)) : Prop :=
  ∀ a, (psi a).im = 0

/-! Sanity examples for the local coordinate conventions. -/

example : bitIndex false = 0 ∧ bitIndex true = 1 := by simp [bitIndex]

example : Fintype.card (SymmetricBasis 0) = 1 := by simp [SymmetricBasis]

example (psi : EuclideanSpace ℂ (Fin 2)) : symmetricQubitKet 0 psi 0 = 1 := by
  simp [symmetricQubitKet]

example (psi : EuclideanSpace ℂ (Fin 2)) (x : Qubits 0) :
    physicalPower 0 psi x = 1 := by simp [physicalPower]

example (x : Qubits 0) : occupationEmbedding 0 x 0 = 1 := by
  simp [occupationEmbedding, hammingWeight]

example (A : Matrix (Fin 2) (Fin 2) ℂ) (x y : Qubits 0) :
    qubitOperatorPower 0 A x y = 1 := by simp [qubitOperatorPower, QAlgorithms.Papers.Independent.Information100.P63.tensorPower, Matrix.submatrix]

example {L : ℕ} (i : Fin L) :
    siteReduction (0 : Matrix (Qubits L) (Qubits L) ℂ) i = 0 := by
  ext a b
  simp [siteReduction]

example {L : ℕ} (i j : Fin L) :
    pairReduction (0 : Matrix (Qubits L) (Qubits L) ℂ) i j = 0 := by
  ext a b
  simp [pairReduction]

example (psi : EuclideanSpace ℂ (Fin 2)) : theta psi 0 = conj (psi 1) := rfl

example (N : ℕ) (rho : Matrix (SymmetricBasis N) (SymmetricBasis N) ℂ)
    (phi : EuclideanSpace ℂ (Fin 2)) :
    estimationWeight N rho phi = (estimationEffect N phi * rho).trace := rfl

example (M : ℕ) : measurementMany 0 M 0 = 0 := by
  simp [measurementMany, estimationWeight]

example : notAmplitude 1 1 0 = Real.sqrt 2 / Real.sqrt 3 := by
  norm_num [notAmplitude, div_eq_mul_inv]

example : lowerIsometry 1 (0, 0) 0 = 1 := by norm_num [lowerIsometry]

example : realNotMatrix 0 1 = 1 ∧ realNotMatrix 1 0 = -1 := by
  norm_num [realNotMatrix]

end QAlgorithms.Papers.Independent.Support21.P18



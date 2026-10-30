-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P45
-- name    : QAlgorithms_Papers_Independent_Extend50_P45
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T18:27:21.25208+00:00
-- url     : https://prove2.me/theorems/72d8078a-7416-4436-8ae5-bdbf7ea96f8e
-- title:
--   Definitions for Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$
-- statement:
--   The objects the formalized statements of *Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$* (arXiv:2203.16571) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `QMat`: PDF pp.2–4: matrices in the frozen most-significant-wire-first qubit basis.
--   - `haarLaw`: PDF p.3: normalized Haar law in the frozen bit-string coordinates.
--   - `convolve`: PDF p.3, Eq.(4): independent composition, the right factor acts first.
--   - `steps`: PDF p.3, Eq.(4): k independent steps; zero steps is the identity.
--   - `nextWire`: PDF p.4, Definition 2: successor on the periodic ring.
--   - `edgeLift`: PDF p.4: lift a two-qubit matrix to the ordered edge (i,i+1). The outside coordinates are left unchanged. Only n >= 2 is used in results.
--   - `edgeLaw`: PDF p.4: independent Haar U(4) on the chosen edge.
--   - `localHaarRingLaw`: PDF p.4, Definition 2(1): each of the n oriented adjacent pairs has weight 1/n. For n=2 the two oriented copies are retained. The unused n=0 extension is zero.
--   - `matchingLaw`: PDF p.4, Definition 2(2): a parity matching with independent gates. For even n, parity zero gives (1,2),(3,4),... and parity one ends in (n,1).
--   - `brickworkLaw`: PDF p.4: one brickwork step consists of the even matching followed by the odd matching, hence TWO parallel gate layers. All gates are independent.
--   - `qubitTensorPower`: PDF p.3, Eq.(3): tensor-power matrix, including the empty tensor product.
--   - `balancedUnitaryMoment`: PDF p.3, Eqs.(2)–(3): U^tensor(t) tensor conjugate(U)^tensor(t), entrywise expectation; vec(|i><j|)=|i> tensor |j>. Circuit integrands are continuous and bounded on their compact unitary supports.
--   - `momentDistance`: PDF p.3, Eq.(2): Schatten infinity norm relative to the Haar moment.
--   - `unitaryMomentTwirl`: PDF p.2, Eq.(1): twirl reconstructed from its vectorized moment matrix.
--   - `twirlDiamondDistance`: PDF p.3: stabilized induced trace norm (no factor 1/2), using a reference of input dimension. For these finite-dimensional linear maps the unit-ball image is bounded and nonempty.
--   - `IsApproximateDesign`: PDF p.3, Definition 1(1), Eq.(5): the additive diamond error is epsilon/2^(nt).
--   - `momentHamiltonian`: PDF p.4, Eq.(9): sum of complementary two-site Haar moment projections. The formula n(I-M(local,t)) equals that sum; ground-space multiplicity is unrestricted.
--   - `reductionLength`: PDF p.7, Observation 1: the ceiling, including the square-root correction.
--   - `designFactor`: PDF pp.7–8: the exact noninteger exponent; used only at integer t >= 2.
--   - `cliffordLaw`: PDF pp.4,9: uniform GLOBAL Clifford law modulo phase, using the frozen full normalizer quotient. The finite enumeration is a representation of the whole group, never a caller-selected subset or a hypothesis about spectral mixing.
--   - `firstWireLift`: PDF p.9: Haar U(2) on the first wire and identity on every other wire.
--   - `auxiliaryLaw`: PDF p.9, Eq.(26): two independent global Cliffords sandwich first-wire Haar. Scalar choices of Clifford representatives are absorbed by the Haar U(2) factor.
--   - `cliffordBrickworkLaw`: PDF p.13: Clifford brickwork, with independent uniform TWO-qubit Clifford gates.
--   - `couplingCosts`: PDF p.10, Eq.(28): probability couplings with the two prescribed marginals. Finite second moment is explicit; on the unitary supports it is automatic.
--   - `frobeniusWasserstein`: PDF p.10, Eq.(28): Wasserstein-2 for the Frobenius CHORD distance. For the laws used here product coupling makes the set nonempty; costs lie in [0,2 sqrt(2^n)], so the real infimum never uses an empty/unbounded default.
-- source:
--   Random quantum circuits are approximate unitary $t$-designs in depth $O\left(nt^{5+o(1)}\right)$, arXiv:2203.16571v3, https://arxiv.org/abs/2203.16571v3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
import Definitions.Def_QAlgorithms_Defs_ProjectiveCliffords

noncomputable section

open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace QAlgorithms.Papers.Independent.Extend50.P45

/-- PDF pp.2–4: matrices in the frozen most-significant-wire-first qubit basis. -/
abbrev QMat (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ

/-- PDF pp.2–3: the Borel sigma-algebra of the finite-dimensional matrix space.
All circuit measures below are supported on unitaries on their stated domains. -/
local instance qubitMatrixMeasurable (n : ℕ) : MeasurableSpace (QMat n) := borel _

/-- PDF pp.2–3: measurability uses exactly the matrix topology's Borel sets. -/
local instance qubitMatrixBorel (n : ℕ) : BorelSpace (QMat n) := ⟨rfl⟩

/-- PDF p.3: normalized Haar law in the frozen bit-string coordinates. -/
def haarLaw (n : ℕ) : Measure (QMat n) :=
  Measure.map (fun U : Matrix.unitaryGroup (Fin (2 ^ n)) ℂ =>
    (fun x y => U.val (bitsEquivFin n x) (bitsEquivFin n y) : QMat n))
    (Schur.unitaryHaar (2 ^ n))

/-- PDF p.3, Eq.(4): independent composition, the right factor acts first. -/
def convolve {n : ℕ} (mu nu : Measure (QMat n)) : Measure (QMat n) :=
  Measure.map (fun p : QMat n × QMat n => p.1 * p.2) (mu.prod nu)

/-- PDF p.3, Eq.(4): k independent steps; zero steps is the identity. -/
def steps {n : ℕ} (mu : Measure (QMat n)) : ℕ → Measure (QMat n)
  | 0 => Measure.dirac (1 : QMat n)
  | k + 1 => convolve mu (steps mu k)

/-- PDF p.4, Definition 2: successor on the periodic ring. -/
def nextWire {n : ℕ} (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1, h⟩
  else ⟨0, lt_of_le_of_lt (Nat.zero_le i.val) i.isLt⟩

/-- PDF p.4: lift a two-qubit matrix to the ordered edge (i,i+1).
The outside coordinates are left unchanged. Only n >= 2 is used in results. -/
def edgeLift {n : ℕ} (i : Fin n) (U : QMat 2) : QMat n :=
  fun x y => if ∀ q, q ≠ i → q ≠ nextWire i → x q = y q then
    U (fun j => if j.val = 0 then x i else x (nextWire i))
      (fun j => if j.val = 0 then y i else y (nextWire i)) else 0

/-- PDF p.4: independent Haar U(4) on the chosen edge. -/
def edgeLaw {n : ℕ} (i : Fin n) : Measure (QMat n) :=
  Measure.map (edgeLift i) (haarLaw 2)

/-- PDF p.4, Definition 2(1): each of the n oriented adjacent pairs has weight 1/n.
For n=2 the two oriented copies are retained. The unused n=0 extension is zero. -/
def localHaarRingLaw (n : ℕ) : Measure (QMat n) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, edgeLaw i

/-- PDF p.4, Definition 2(2): a parity matching with independent gates.
For even n, parity zero gives (1,2),(3,4),... and parity one ends in (n,1). -/
def matchingLaw (n parity : ℕ) (gateLaw : Measure (QMat 2)) : Measure (QMat n) :=
  ((List.finRange n).filter (fun i => i.val % 2 == parity)).foldl
    (fun mu i => convolve (Measure.map (edgeLift i) gateLaw) mu) (Measure.dirac (1 : QMat n))

/-- PDF p.4: one brickwork step consists of the even matching followed by the odd
matching, hence TWO parallel gate layers. All gates are independent. -/
def brickworkLaw (n : ℕ) : Measure (QMat n) :=
  convolve (matchingLaw n 1 (haarLaw 2)) (matchingLaw n 0 (haarLaw 2))

/-- PDF p.3, Eq.(3): tensor-power matrix, including the empty tensor product. -/
def qubitTensorPower {n : ℕ} (t : ℕ) (U : QMat n) :
    Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  fun x y => ∏ j, U (x j) (y j)

/-- PDF p.3, Eqs.(2)–(3): U^tensor(t) tensor conjugate(U)^tensor(t),
entrywise expectation; vec(|i><j|)=|i> tensor |j>. Circuit integrands are
continuous and bounded on their compact unitary supports. -/
def balancedUnitaryMoment {n : ℕ} (mu : Measure (QMat n)) (t : ℕ) :
    Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ :=
  fun x y => ∫ U, qubitTensorPower t U x.1 y.1 *
    conj (qubitTensorPower t U x.2 y.2) ∂mu

/-- PDF p.3, Eq.(2): Schatten infinity norm relative to the Haar moment. -/
def momentDistance {n : ℕ} (mu : Measure (QMat n)) (t : ℕ) : ℝ :=
  specNorm (balancedUnitaryMoment mu t - balancedUnitaryMoment (haarLaw n) t)

/-- PDF p.2, Eq.(1): twirl reconstructed from its vectorized moment matrix. -/
def unitaryMomentTwirl {n : ℕ} (mu : Measure (QMat n)) (t : ℕ)
    (A : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ) :
    Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  fun x y => ∑ a, ∑ b, balancedUnitaryMoment mu t (x,y) (a,b) * A a b

/-- PDF p.3: stabilized induced trace norm (no factor 1/2), using a reference of
input dimension. For these finite-dimensional linear maps the unit-ball image is
bounded and nonempty. -/
def twirlDiamondDistance {n : ℕ} (mu nu : Measure (QMat n)) (t : ℕ) : ℝ :=
  sSup {v : ℝ | ∃ X : Matrix
    ((Fin t → Qubits n) × (Fin t → Qubits n))
    ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ,
    traceNorm X ≤ 1 ∧ v = traceNorm
      (idTensorSuperop (R := Fin t → Qubits n)
        (fun A => unitaryMomentTwirl mu t A - unitaryMomentTwirl nu t A) X)}

/-- PDF p.3, Definition 1(1), Eq.(5): the additive diamond error is epsilon/2^(nt). -/
def IsApproximateDesign {n : ℕ} (mu : Measure (QMat n)) (t : ℕ) (epsilon : ℝ) : Prop :=
  twirlDiamondDistance mu (haarLaw n) t ≤ epsilon / (2 : ℝ) ^ (n * t)

/-- PDF p.4, Eq.(9): sum of complementary two-site Haar moment projections.
The formula n(I-M(local,t)) equals that sum; ground-space multiplicity is unrestricted. -/
def momentHamiltonian (n t : ℕ) :
    Matrix ((Fin t → Qubits n) × (Fin t → Qubits n))
      ((Fin t → Qubits n) × (Fin t → Qubits n)) ℂ :=
  (n : ℂ) • (1 - balancedUnitaryMoment (localHaarRingLaw n) t)

/-- PDF p.7, Observation 1: the ceiling, including the square-root correction. -/
def reductionLength (t : ℕ) : ℕ :=
  ⌈2 * Real.logb 2 (4 * (t : ℝ)) +
    (3 / 2 : ℝ) * Real.sqrt (Real.logb 2 (4 * (t : ℝ)))⌉₊

/-- PDF pp.7–8: the exact noninteger exponent; used only at integer t >= 2. -/
def designFactor (t : ℕ) : ℝ :=
  Real.log (t : ℝ) ^ 5 *
    (t : ℝ) ^ (4 + 3 / Real.sqrt (Real.logb 2 (t : ℝ)))

/-- PDF pp.4,9: uniform GLOBAL Clifford law modulo phase, using the frozen full
normalizer quotient. The finite enumeration is a representation of the whole group,
never a caller-selected subset or a hypothesis about spectral mixing. -/
def cliffordLaw (n : ℕ) [Fintype (Clifford.ProjectiveGroup n)] : Measure (QMat n) :=
  ∑ C : Clifford.ProjectiveGroup n,
    (Clifford.uniformGlobalEnsemble n C) •
      Measure.dirac ((Clifford.representative C).val.val)

/-- PDF p.9: Haar U(2) on the first wire and identity on every other wire. -/
def firstWireLift (n : ℕ) (U : QMat 1) : QMat n :=
  fun x y => if h : 0 < n then
    if ∀ q : Fin n, q.val ≠ 0 → x q = y q then
      U (fun _ => x ⟨0,h⟩) (fun _ => y ⟨0,h⟩) else 0
    else (1 : QMat n) x y

/-- PDF p.9, Eq.(26): two independent global Cliffords sandwich first-wire Haar.
Scalar choices of Clifford representatives are absorbed by the Haar U(2) factor. -/
def auxiliaryLaw (n : ℕ) [Fintype (Clifford.ProjectiveGroup n)] : Measure (QMat n) :=
  convolve (cliffordLaw n)
    (convolve (Measure.map (firstWireLift n) (haarLaw 1)) (cliffordLaw n))

/-- PDF p.13: Clifford brickwork, with independent uniform TWO-qubit Clifford gates. -/
def cliffordBrickworkLaw (n : ℕ) [Fintype (Clifford.ProjectiveGroup 2)] : Measure (QMat n) :=
  convolve (matchingLaw n 1 (cliffordLaw 2)) (matchingLaw n 0 (cliffordLaw 2))

/-- PDF p.10, Eq.(28): probability couplings with the two prescribed marginals.
Finite second moment is explicit; on the unitary supports it is automatic. -/
def couplingCosts {n : ℕ} (mu nu : Measure (QMat n)) : Set ℝ :=
  {v | ∃ gamma : Measure (QMat n × QMat n), IsProbabilityMeasure gamma ∧
    Measure.map Prod.fst gamma = mu ∧ Measure.map Prod.snd gamma = nu ∧
    Integrable (fun p => frobNorm (p.1 - p.2) ^ 2) gamma ∧
    v = Real.sqrt (∫ p, frobNorm (p.1 - p.2) ^ 2 ∂gamma)}

/-- PDF p.10, Eq.(28): Wasserstein-2 for the Frobenius CHORD distance.
For the laws used here product coupling makes the set nonempty; costs lie in
[0,2 sqrt(2^n)], so the real infimum never uses an empty/unbounded default. -/
def frobeniusWasserstein {n : ℕ} (mu nu : Measure (QMat n)) : ℝ :=
  sInf (couplingCosts mu nu)

/-! The short names flagged by the prior checker belong to unrelated accepted
objects (finite classical laws/marginals, a fixed rational sign-count tensor,
coherence moments, and task-specific twirls). They are not replacements for these
paper-specific constructions. See ASSESSMENT.json and MODERATION_NOTES.md. -/

/-! Definitional sanity examples. No theorem proofs are attempted. -/

example {n : ℕ} (mu : Measure (QMat n)) : steps mu 0 = Measure.dirac (1 : QMat n) := rfl

example {n : ℕ} (mu : Measure (QMat n)) (k : ℕ) :
    steps mu (k + 1) = convolve mu (steps mu k) := rfl

example {n : ℕ} (U : QMat n) (x y : Fin 0 → Qubits n) :
    qubitTensorPower 0 U x y = 1 := by simp [qubitTensorPower]

example : nextWire (n := 2) (0 : Fin 2) = 1 := rfl

example : nextWire (n := 2) (1 : Fin 2) = 0 := rfl

example (U : QMat 1) (x y : Qubits 1) :
    firstWireLift 1 U x y = U (fun _ => x 0) (fun _ => y 0) := by
  have hout : ∀ q : Fin 1, q.val ≠ 0 → x q = y q := by
    intro q hq
    have hz : q.val = 0 := by omega
    exact (hq hz).elim
  simp [firstWireLift, hout]

example (n : ℕ) : brickworkLaw n =
    convolve (matchingLaw n 1 (haarLaw 2)) (matchingLaw n 0 (haarLaw 2)) := rfl

end QAlgorithms.Papers.Independent.Extend50.P45



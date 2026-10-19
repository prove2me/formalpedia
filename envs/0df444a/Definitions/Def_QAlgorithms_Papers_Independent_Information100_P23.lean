-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23
-- name    : QAlgorithms_Papers_Independent_Information100_P23
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-19T10:09:06.660256+00:00
-- url     : https://prove2.me/theorems/086ae2ac-09f1-43b6-8c94-395f72373431
-- title:
--   Definitions for A sharp norm inequality for entanglement-breaking channels
-- statement:
--   The objects the formalized statements of *A sharp norm inequality for entanglement-breaking channels* (arXiv:2609.27906) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Operator`
--   - `ChannelMap`
--   - `BlochIndex`
--   - `BlochVector`
--   - `BlochMatrix`
--   - `BlochBasis`: PDF p.2, §2: the fixed normalized real basis of traceless Hermitian operators. The reconstruction field states spanning, using the coefficients forced by normalization.
--   - `IsCPTP`: PDF pp.1–2: completely positive, trace-preserving complex-linear maps.
--   - `vectorNorm`: PDF p.2: Euclidean vector norm, never the default norm on a function space.
--   - `nuclearNorm`: PDF pp.1–2: nuclear norm of the real Bloch matrix, via its complex embedding.
--   - `operatorNorm`: PDF pp.1,4: operator norm induced by the Euclidean norm.
--   - `blochState`: PDF p.2: reconstruct an operator from real Bloch coordinates. For d>2 a norm bound alone does not assert that this operator is a density matrix.
--   - `coordinates`: PDF p.2: Bloch coordinates obtained from the real trace pairing.
--   - `blochA`: PDF p.2: the linear part is computed from the channel, not a free parameter.
--   - `blochC`: PDF p.2: the translation is the Bloch vector of Phi(I/d).
--   - `affineMap`: PDF p.2, r ↦ Ar+c: the complex-linear map reconstructed from real affine data. No positivity or channel property is built into this constructor.
--   - `completelyDephasing`: PDF p.3, Proposition 2: the completely dephasing map in the computational basis.
--   - `projectivePreparation`: PDF p.3, §4: the actual two-outcome measure-and-prepare map. The effects are rho(m), rho(-m), and the two prepared states are rho(s1), rho(s2).
--   - `amplitudeDamping`: PDF p.4, §5: alpha is the coherence multiplier, not the damping probability.
--   - `iterateTranslation`: PDF p.4, §6: finite-sum translation of the n-fold affine iterate; c_0=0.
--   - `positiveIndex`: PDF p.4, §6: minimum over positive integers, with empty minimum equal to infinity. The paper leaves the empty-set convention implicit; this extended minimum handles channels with no finite EB iterate, including strictly contractive amplitude damping.
--   - `entanglementBreakingIndex`: PDF p.4, §6: EB index; channelhood is required separately in statements. For CPTP maps the accepted separable-positive predicate has trace-one outputs and is exactly separability of density matrices for every finite reference dimension.
--   - `quadraticCrossingIndex`: PDF p.4, §6: quadratic test on each positive iterate.
--   - `blindCrossingIndex`: PDF p.4, §6: the translation-blind crossing test, with the same infinity convention.
--   - `LinearCondition`: PDF p.4, §5: the three comparison regions for actual qubit channels.
--   - `QuadraticCondition`: PDF pp.3–4: Theorem 1's qubit region.
--   - `OperatorCondition`: PDF p.4: the weaker operator-norm region.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, https://arxiv.org/abs/2609.27906v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_MatrixDistances

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

abbrev Operator (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

abbrev ChannelMap (d : ℕ) := Operator d →ₗ[ℂ] Operator d

abbrev BlochIndex (d : ℕ) := Fin (d ^ 2 - 1)

abbrev BlochVector (d : ℕ) := BlochIndex d → ℝ

abbrev BlochMatrix (d : ℕ) := Matrix (BlochIndex d) (BlochIndex d) ℝ

/-- PDF p.2, §2: the fixed normalized real basis of traceless Hermitian operators.
The reconstruction field states spanning, using the coefficients forced by normalization. -/
structure BlochBasis (d : ℕ) where
  generator : BlochIndex d → Operator d
  hermitian : ∀ i, (generator i).IsHermitian
  traceless : ∀ i, (generator i).trace = 0
  normalized : ∀ i j, (generator i * generator j).trace = if i = j then 2 else 0
  reconstruction : ∀ X : Operator d, X.IsHermitian → X.trace = 0 →
    X = (1 / 2 : ℂ) • ∑ i, ((generator i * X).trace.re : ℂ) • generator i

/-- PDF pp.1–2: completely positive, trace-preserving complex-linear maps. -/
def IsCPTP {d : ℕ} (Phi : ChannelMap d) : Prop :=
  Entanglement.IsCompletelyPositive Phi ∧ ∀ X, (Phi X).trace = X.trace

/-- PDF p.2: Euclidean vector norm, never the default norm on a function space. -/
def vectorNorm {n : ℕ} (r : Fin n → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 r : EuclideanSpace ℝ (Fin n))‖

/-- PDF pp.1–2: nuclear norm of the real Bloch matrix, via its complex embedding. -/
def nuclearNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  QAlgorithms.traceNorm (A.map fun x => (x : ℂ))

/-- PDF pp.1,4: operator norm induced by the Euclidean norm. -/
def operatorNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖

/-- PDF p.2: reconstruct an operator from real Bloch coordinates.
For d>2 a norm bound alone does not assert that this operator is a density matrix. -/
def blochState {d : ℕ} (B : BlochBasis d) (r : BlochVector d) : Operator d :=
  (d : ℂ)⁻¹ • 1 + (1 / 2 : ℂ) • ∑ i, (r i : ℂ) • B.generator i

/-- PDF p.2: Bloch coordinates obtained from the real trace pairing. -/
def coordinates {d : ℕ} (B : BlochBasis d) (X : Operator d) : BlochVector d :=
  fun i => (B.generator i * X).trace.re

/-- PDF p.2: the linear part is computed from the channel, not a free parameter. -/
def blochA {d : ℕ} (B : BlochBasis d) (Phi : ChannelMap d) : BlochMatrix d :=
  fun i j => (B.generator i * Phi (B.generator j)).trace.re / 2

/-- PDF p.2: the translation is the Bloch vector of Phi(I/d). -/
def blochC {d : ℕ} (B : BlochBasis d) (Phi : ChannelMap d) : BlochVector d :=
  coordinates B (Phi ((d : ℂ)⁻¹ • 1))

/-- PDF p.2, r ↦ Ar+c: the complex-linear map reconstructed from real affine data.
No positivity or channel property is built into this constructor. -/
def affineMap {d : ℕ} (B : BlochBasis d) (c : BlochVector d) (A : BlochMatrix d) :
    ChannelMap d where
  toFun X := (X.trace / (d : ℂ)) • (1 + (d / 2 : ℂ) •
      ∑ i, (c i : ℂ) • B.generator i) +
    ∑ i, ((∑ j, (A i j : ℂ) * (B.generator j * X).trace) / 2) • B.generator i
  map_add' X Y := by
    simp [Matrix.trace_add, Matrix.mul_add, mul_add, Finset.sum_add_distrib, add_div, add_smul]
    abel
  map_smul' a X := by
    simp [Matrix.trace_smul, Matrix.mul_smul, ← Finset.mul_sum,
      mul_div_assoc, mul_smul, Finset.smul_sum, mul_left_comm]

/-- PDF p.3, Proposition 2: the completely dephasing map in the computational basis. -/
def completelyDephasing (d : ℕ) : ChannelMap d :=
  Entanglement.holevoMap (fun k : Fin d => Matrix.single k k 1)
    (fun k : Fin d => Matrix.single k k 1)

/-- PDF p.3, §4: the actual two-outcome measure-and-prepare map.
The effects are rho(m), rho(-m), and the two prepared states are rho(s1), rho(s2). -/
def projectivePreparation (B : BlochBasis 2) (m s1 s2 : BlochVector 2) : ChannelMap 2 :=
  Entanglement.holevoMap (![blochState B s1, blochState B s2])
    (![blochState B m, blochState B (-m)])

/-- PDF p.4, §5: alpha is the coherence multiplier, not the damping probability. -/
def amplitudeDamping (B : BlochBasis 2) (alpha : ℝ) : ChannelMap 2 :=
  affineMap B ![0, 0, 1 - alpha ^ 2] (Matrix.diagonal ![alpha, alpha, alpha ^ 2])

/-- PDF p.4, §6: finite-sum translation of the n-fold affine iterate; c_0=0. -/
def iterateTranslation {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (c : Fin k → ℝ) (n : ℕ) :
    Fin k → ℝ :=
  ∑ j ∈ Finset.range n, (A ^ j).mulVec c

/-- PDF p.4, §6: minimum over positive integers, with empty minimum equal to infinity.
The paper leaves the empty-set convention implicit; this extended minimum handles
channels with no finite EB iterate, including strictly contractive amplitude damping. -/
def positiveIndex (P : ℕ → Prop) : ℕ∞ :=
  sInf {v | ∃ n : ℕ, 1 ≤ n ∧ v = (n : ℕ∞) ∧ P n}

/-- PDF p.4, §6: EB index; channelhood is required separately in statements.
For CPTP maps the accepted separable-positive predicate has trace-one outputs and
is exactly separability of density matrices for every finite reference dimension. -/
def entanglementBreakingIndex {d : ℕ} (Phi : ChannelMap d) : ℕ∞ :=
  positiveIndex fun n => Entanglement.IsEntanglementBreakingPositive (Phi ^ n)

/-- PDF p.4, §6: quadratic test on each positive iterate. -/
def quadraticCrossingIndex {d : ℕ} (A : BlochMatrix d) (c : BlochVector d) : ℕ∞ :=
  positiveIndex fun n => nuclearNorm (A ^ n) ^ 2 +
    ((d : ℝ) * ((d : ℝ) - 1) / 2) * vectorNorm (iterateTranslation A c n) ^ 2 ≤
      ((d : ℝ) - 1) ^ 2

/-- PDF p.4, §6: the translation-blind crossing test, with the same infinity convention. -/
def blindCrossingIndex {d : ℕ} (A : BlochMatrix d) : ℕ∞ :=
  positiveIndex fun n => nuclearNorm (A ^ n) ≤ (d : ℝ) - 1

/-- PDF p.4, §5: the three comparison regions for actual qubit channels. -/
def LinearCondition (B : BlochBasis 2) (Phi : ChannelMap 2) : Prop :=
  nuclearNorm (blochA B Phi) + vectorNorm (blochC B Phi) ≤ 1

/-- PDF pp.3–4: Theorem 1's qubit region. -/
def QuadraticCondition (B : BlochBasis 2) (Phi : ChannelMap 2) : Prop :=
  nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ≤ 1

/-- PDF p.4: the weaker operator-norm region. -/
def OperatorCondition (B : BlochBasis 2) (Phi : ChannelMap 2) : Prop :=
  operatorNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ≤ 1

/-! Small sanity checks of the new interfaces, with no placeholder proofs. -/

example : BlochIndex 1 = Fin 0 := rfl

example (X : Operator 1) : completelyDephasing 1 X = X := by
  ext i j
  fin_cases i
  fin_cases j
  simp [completelyDephasing, Entanglement.holevoMap, Matrix.mul_apply, Matrix.trace]

example {d : ℕ} (B : BlochBasis d) (i j : BlochIndex d) :
    (B.generator i * B.generator j).trace = if i = j then 2 else 0 := B.normalized i j

example {d : ℕ} (Phi : ChannelMap d) (h : IsCPTP Phi) (X : Operator d) :
    (Phi X).trace = X.trace := h.2 X

example {d : ℕ} : vectorNorm (0 : BlochVector d) = 0 := by simp [vectorNorm]

example {d : ℕ} : nuclearNorm (0 : BlochMatrix d) = 0 := by
  simp [nuclearNorm, QAlgorithms.traceNorm, cfc_zero]

example {d : ℕ} : operatorNorm (0 : BlochMatrix d) = 0 := by
  simp only [operatorNorm, map_zero, norm_zero]

example {d : ℕ} (B : BlochBasis d) : blochState B 0 = (d : ℂ)⁻¹ • 1 := by
  simp [blochState]

example {d : ℕ} (B : BlochBasis d) : coordinates B 0 = 0 := by
  ext i
  simp [coordinates]

example {d : ℕ} (B : BlochBasis d) : blochA B (0 : ChannelMap d) = 0 := by
  ext i j
  simp [blochA]

example {d : ℕ} (B : BlochBasis d) : blochC B (0 : ChannelMap d) = 0 := by
  ext i
  simp [blochC, coordinates]

example {d : ℕ} (B : BlochBasis d) (c : BlochVector d) (A : BlochMatrix d) :
    affineMap B c A 0 = 0 := map_zero _

example (d : ℕ) : completelyDephasing d 0 = 0 := map_zero _

example (B : BlochBasis 2) (m s1 s2 : BlochVector 2) :
    projectivePreparation B m s1 s2 = Entanglement.holevoMap
      (![blochState B s1, blochState B s2]) (![blochState B m, blochState B (-m)]) := rfl

example (B : BlochBasis 2) : amplitudeDamping B 0 =
    affineMap B ![0, 0, 1 - (0 : ℝ) ^ 2] (Matrix.diagonal ![0, 0, (0 : ℝ) ^ 2]) := rfl

example {d : ℕ} (A : BlochMatrix d) (c : BlochVector d) :
    iterateTranslation A c 0 = 0 := by simp [iterateTranslation]

example : positiveIndex (fun _ => False) = ⊤ := by simp [positiveIndex]

example {d : ℕ} (Phi : ChannelMap d) : entanglementBreakingIndex Phi =
    positiveIndex (fun n => Entanglement.IsEntanglementBreakingPositive (Phi ^ n)) := rfl

example {d : ℕ} (A : BlochMatrix d) (c : BlochVector d) : quadraticCrossingIndex (d := d) A c =
    positiveIndex (fun n => nuclearNorm (A ^ n) ^ 2 +
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * vectorNorm (iterateTranslation A c n) ^ 2 ≤
        ((d : ℝ) - 1) ^ 2) := rfl

example {d : ℕ} (A : BlochMatrix d) : blindCrossingIndex (d := d) A =
    positiveIndex (fun n => nuclearNorm (A ^ n) ≤ (d : ℝ) - 1) := rfl

example (B : BlochBasis 2) (Phi : ChannelMap 2) : LinearCondition B Phi ↔
    nuclearNorm (blochA B Phi) + vectorNorm (blochC B Phi) ≤ 1 := Iff.rfl

example (B : BlochBasis 2) (Phi : ChannelMap 2) : QuadraticCondition B Phi ↔
    nuclearNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ≤ 1 := Iff.rfl

example (B : BlochBasis 2) (Phi : ChannelMap 2) : OperatorCondition B Phi ↔
    operatorNorm (blochA B Phi) ^ 2 + vectorNorm (blochC B Phi) ^ 2 ≤ 1 := Iff.rfl

end QAlgorithms.Papers.Independent.Information100.P23



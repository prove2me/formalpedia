-- Prove2me | Definitions.Def_HamLocality237_Testing_Locality
-- name    : HamLocality237_Testing_Locality
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:58.378657+00:00
-- url     : https://prove2.me/theorems/8db5586d-3486-4cb6-8835-3ed4061bb0d1
-- title:
--   Pauli locality, normalized distance, and the testing promise
-- statement:
--   Let $n$ be the number of qubits, let $P$ range over tensor products of $I,X,Y,Z$, and let $|P|$ count its nonidentity factors. For a complex operator $A$, define
--
--   $$\widehat A(P)=2^{-n}\operatorname{Tr}(PA),\qquad \|A\|_2=2^{-n/2}\|A\|_F.$$
--
--   A Hermitian operator $H$ is $k$-local when $\widehat H(P)=0$ for every $|P|>k$. Each term may have its own support. Its distance from locality is
--
--   $$\operatorname{dist}(H,k\text{-local})=\inf_{L\;k\text{-local}}\|H-L\|_2.$$
--
--   The low- and high-weight truncations retain respectively the Pauli words of weight at most $k$ and greater than $k$. For a real diagonal table $h$, the Boolean coefficient is its uniform average against the corresponding parity character. A testing input is Hermitian with operator norm at most one. A promise input is either $k$-local or has distance strictly greater than the threshold; no trace restriction is imposed.
--
--   These definitions specify the finite-dimensional objects used by Corollary 4.2 and the distance milestone. A structural proof establishes that the distance's defining set is nonempty and bounded below. The standard registers, Pauli matrices, weights, and Frobenius norm are reused from the published QAlgorithms definitions.
-- source:
--   Francisco Escudero Gutiérrez, Junseo Lee, Sebastian Zur, STOC 2027 submission #237 (October 2026), §2.1–2.2, pp.7–9; Definition 2.1, p.10. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/237.pdf

import Definitions.Def_QAlgorithms_Defs_QECC

open QAlgorithms
open scoped BigOperators
noncomputable section

namespace HamLocality237.Testing

abbrev Operator (n : ℕ) := Matrix (Qubits n) (Qubits n) ℂ
abbrev PauliWord (n : ℕ) := Fin n → QAlgorithms.Stabilizer.Pauli

/-- §2.2, p.8: phase +1, with the standard Y = iXZ convention. -/
def pauliCoefficient {n : ℕ} (A : Operator n) (P : PauliWord n) : ℂ :=
  ((2 : ℂ) ^ n)⁻¹ * Matrix.trace (QAlgorithms.pauliOps P * A)

/-- §2.2, p.8: the normalized Hilbert--Schmidt norm. -/
def normalizedFrobenius {n : ℕ} (A : Operator n) : ℝ :=
  ((2 : ℝ) ^ n).sqrt⁻¹ * QAlgorithms.frobNorm A

/-- §2.2, p.8: each term may have its own support. No common-support restriction. -/
def IsKLocal {n : ℕ} (k : ℕ) (H : Operator n) : Prop :=
  H.IsHermitian ∧ ∀ P : PauliWord n, k < QAlgorithms.opsWeight P →
    pauliCoefficient H P = 0

/-- §2.2, p.8: no operator-norm restriction is imposed on the approximants. -/
def distanceFromLocality {n : ℕ} (k : ℕ) (H : Operator n) : ℝ :=
  sInf {d : ℝ | ∃ L : Operator n, IsKLocal k L ∧ d = normalizedFrobenius (H - L)}

/-- §2.2, p.8: the low-weight Pauli truncation. -/
def lowWeight {n : ℕ} (k : ℕ) (A : Operator n) : Operator n :=
  ∑ P : PauliWord n, if QAlgorithms.opsWeight P ≤ k then
    pauliCoefficient A P • QAlgorithms.pauliOps P else 0

def highWeight {n : ℕ} (k : ℕ) (A : Operator n) : Operator n :=
  ∑ P : PauliWord n, if k < QAlgorithms.opsWeight P then
    pauliCoefficient A P • QAlgorithms.pauliOps P else 0

/-- §2.1, p.7: the real Boolean Fourier coefficient under the uniform law. -/
def booleanCoefficient {n : ℕ} (h : Qubits n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Qubits n,
    h x * ∏ j ∈ S, if x j then (-1 : ℝ) else 1

def diagonalHamiltonian {n : ℕ} (h : Qubits n → ℝ) : Operator n :=
  Matrix.diagonal (fun x => (h x : ℂ))

/-- Definition 2.1, p.10: bounded Hermitian input, with unrestricted trace. -/
def IsInput {n : ℕ} (H : Operator n) : Prop :=
  H.IsHermitian ∧ QAlgorithms.specNorm H ≤ 1

def IsPromise {n : ℕ} (k : ℕ) (ε : ℝ) (H : Operator n) : Prop :=
  IsInput H ∧ (IsKLocal k H ∨ ε < distanceFromLocality k H)

/-- The distance's defining set is nonempty and bounded below on every input. -/
theorem localityDistance_wellDefined {n : ℕ} (k : ℕ) (H : Operator n) :
    {d : ℝ | ∃ L : Operator n, IsKLocal k L ∧
      d = normalizedFrobenius (H - L)}.Nonempty ∧
    BddBelow {d : ℝ | ∃ L : Operator n, IsKLocal k L ∧
      d = normalizedFrobenius (H - L)} := by
  have hz : IsKLocal k (0 : Operator n) := by
    refine ⟨Matrix.isHermitian_zero, ?_⟩
    intro P _
    simp [pauliCoefficient]
  constructor
  · exact ⟨normalizedFrobenius (H - 0), 0, hz, rfl⟩
  · refine ⟨0, ?_⟩
    rintro d ⟨L, _, rfl⟩
    unfold normalizedFrobenius QAlgorithms.frobNorm
    apply mul_nonneg
    · positivity
    · exact @norm_nonneg _ Matrix.frobeniusNormedAddCommGroup.toSeminormedAddCommGroup.toSeminormedAddGroup _

end HamLocality237.Testing



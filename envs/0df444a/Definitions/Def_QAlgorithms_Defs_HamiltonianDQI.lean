-- Prove2me | Definitions.Def_QAlgorithms_Defs_HamiltonianDQI
-- name    : QAlgorithms_Defs_HamiltonianDQI
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:27.915998+00:00
-- url     : https://prove2.me/theorems/3afda54d-c633-4d36-bbe7-19fdf5e8e5e1
-- title:
--   HamiltonianDQI
-- statement:
--   HamiltonianDQI
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HamiltonianDQI.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
import Definitions.Def_QAlgorithms_Defs_CommutingPauli
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- w_y=∑_{j=0}^l a_j j! ∑_{μ∈ℕ^m:∑ μ_i=j, μ_i≡y_i mod 2} (∏ c_i^{μ_i})/(∏ μ_i!). Source: arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.8. -/
def parityMultinomialCoefficient {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ)
    (l : ℕ) (y : Qubits m) : ℝ :=
  ∑ j ∈ Finset.range (l + 1), P.coeff j * (j.factorial : ℝ) *
    ∑ mu : Fin m → Fin (l + 1),
      if (∑ i, (mu i : ℕ)) = j ∧ (∀ i, (mu i : ℕ) % 2 = if y i then 1 else 0)
      then (∏ i, c i ^ (mu i : ℕ)) / (∏ i, ((mu i : ℕ).factorial : ℝ)) else 0

/-- sqrt(sum_y parityMultinomialCoefficient(c,P,l,y)^2). Source: arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.8. -/
def hdqiReferenceNorm {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ) : ℝ :=
  Real.sqrt (∑ y : Qubits m, parityMultinomialCoefficient c P l y ^ 2)

/-- N=Real.sqrt(∑_y w_y²), R^l(H)=N^{-1}∑_y(w_y:ℂ)•ket y. Source: arxiv-2601.18773v1 PDF p.6; arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
def hdqiReference {m : ℕ} (c : Fin m → ℝ) (P : Polynomial ℝ) (l : ℕ) :
    EuclideanSpace ℂ (Qubits m) :=
  WithLp.toLp 2 fun y => ((parityMultinomialCoefficient c P l y / hdqiReferenceNorm c P l : ℝ) : ℂ)

/-- For P:Polynomial ℝ define P(H)=∑_j(P.coeff j:ℂ)•H^j, including j=0, and ρ_P(H)=(Tr[P(H)²])^{-1}•P(H)². Source: arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.5; arxiv-2601.18773v1 PDF p.8. -/
def polynomialDensity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (P : Polynomial ℝ) : Matrix ι ι ℂ :=
  let M : Matrix ι ι ℂ := Polynomial.aeval H P
  (M ^ 2).trace⁻¹ • M ^ 2

/-- Unitary D on Qubits m×Qubits (n+n), with act D (ket (y,Bᵀy))=ket (0,Bᵀy) for every y with 1≤weight(y)≤l; action elsewhere unconstrained. Source: arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
def IsWeightDecoder {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) (l : ℕ)
    (D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ) : Prop :=
  D ∈ Matrix.unitaryGroup _ ℂ ∧ ∀ y, 1 ≤ hammingWeight y → hammingWeight y ≤ l →
    act D (ket (y, hamiltonianSyndrome labels y)) = ket (0, hamiltonianSyndrome labels y)

/-- Unitary basis change mapping (W(α,β)⊗I)maxEntangled n to computational |α,β⟩, in the fixed syndrome order. Source: arxiv-2601.18773v1 PDF p.8; arxiv-2601.18773v1 PDF p.9. -/
def canonicalBellTransform (n : ℕ) : Matrix (Qubits (n + n)) (Qubits n × Qubits n) ℂ :=
  Matrix.of fun z p =>
    let v : CanonicalPauliLabel n :=
      (fun q => if (qubitsAppendEquiv n n z).1 q then 1 else 0,
       fun q => if (qubitsAppendEquiv n n z).2 q then 1 else 0)
    conj (act (Matrix.kronecker (canonicalPauli v).toMatrix
      (1 : Matrix (Qubits n) (Qubits n) ℂ)) (maxEntangled n) p)

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example {m : ℕ} (c : Fin m → ℝ) (l : ℕ) : hdqiReferenceNorm c 0 l = 0 := by
  simp [hdqiReferenceNorm, parityMultinomialCoefficient]

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) :
    polynomialDensity H 0 = 0 := by simp [polynomialDensity]

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n)
    (D : Matrix (Qubits m × Qubits (n + n)) (Qubits m × Qubits (n + n)) ℂ)
    (hD : D ∈ Matrix.unitaryGroup _ ℂ) : IsWeightDecoder labels 0 D := by
  refine ⟨hD, ?_⟩; intro y hy hl; omega

end QAlgorithms



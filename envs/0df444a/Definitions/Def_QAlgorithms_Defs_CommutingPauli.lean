-- Prove2me | Definitions.Def_QAlgorithms_Defs_CommutingPauli
-- name    : QAlgorithms_Defs_CommutingPauli
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:10.147164+00:00
-- url     : https://prove2.me/theorems/ceced97b-f2c6-41a4-8e2e-319c691a986e
-- title:
--   CommutingPauli
-- statement:
--   CommutingPauli
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\CommutingPauli.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

namespace QAlgorithms

/-- Labels (α,β)∈(Fin n→ZMod 2)² construct W(α,β). Source: arxiv-2601.18773v1 PDF p.3; arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
abbrev CanonicalPauliLabel (n : ℕ) := (Fin n → ZMod 2) × (Fin n → ZMod 2)

/-- Map binary (alpha,beta) to phase-zero PauliString with (0,0)=I,(0,1)=X,(1,0)=Z,(1,1)=Y; its matrix equals tensor i^(-alpha_q beta_q) Z^alpha_q X^beta_q. Source: arxiv-2601.18773v1 PDF p.3. -/
def canonicalPauli {n : ℕ} (v : CanonicalPauliLabel n) : Stabilizer.PauliString n :=
  ⟨0, fun q => if v.1 q = 1 then
    (if v.2 q = 1 then Stabilizer.Pauli.Y else Stabilizer.Pauli.Z)
    else (if v.2 q = 1 then Stabilizer.Pauli.X else Stabilizer.Pauli.I)⟩

/-- Compute sum_i (c_i:complex) times canonicalPauli(label_i) from known real coefficients/distinct labels. Source: arxiv-2601.18773v1 PDF p.3; arxiv-2601.18773v1 PDF p.8. -/
def pauliHamiltonian {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) (c : Fin m → ℝ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  ∑ i, (c i : ℂ) • (canonicalPauli (labels i)).toMatrix

/-- Multiply actual canonical term matrices with y_i=true, in ascending term order. Source: arxiv-2601.18773v1 PDF p.9. -/
def pauliSubsetProduct {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) (y : Qubits m) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  (List.ofFn fun i : Fin m => if y i then (canonicalPauli (labels i)).toMatrix else 1).prod

/-- Matrix Fin(n+n) Fin m (ZMod 2), column i is the supplied canonical label alpha_i followed by beta_i. Source: arxiv-2601.18773v1 PDF p.4. -/
def hamiltonianSymplecticMatrix {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) :
    Matrix (Fin (n + n)) (Fin m) (ZMod 2) :=
  Matrix.of fun q i => Fin.append (labels i).1 (labels i).2 q

/-- Bᵀ∈F₂^{2n×m} is constructed from term labels, α rows first and β second; its syndrome Bᵀy is encoded in the same order as a computational ket of 2n qubits. Source: arxiv-2601.18773v1 PDF p.4. -/
def hamiltonianSyndrome {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) (y : Qubits m) :
    Qubits (n + n) :=
  bitsOfZMod ((hamiltonianSymplecticMatrix labels).mulVec fun i => if y i then 1 else 0)

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.3; arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example : (canonicalPauli ((![1], ![1]) : CanonicalPauliLabel 1)).ops 0 = Stabilizer.Pauli.Y := by
  simp [canonicalPauli]

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.3; arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) :
    pauliSubsetProduct labels (fun _ => false) = 1 := by simp [pauliSubsetProduct]

/-- Sanity test. Source: arxiv-2601.18773v1 PDF p.3; arxiv-2601.18773v1 PDF p.4; arxiv-2601.18773v1 PDF p.9. -/
example {n m : ℕ} (labels : Fin m → CanonicalPauliLabel n) :
    hamiltonianSyndrome labels (fun _ => false) = fun _ => false := by
  funext q
  simp only [hamiltonianSyndrome, bitsOfZMod]
  change decide (((hamiltonianSymplecticMatrix labels).mulVec (0 : Fin m → ZMod 2)) q = 1) = false
  simp

/-- Actual Pauli products retain their phase: XX times ZZ is minus YY.
Source: arxiv-2601.18773v1 PDF pp.3–5. -/
example : Matrix.kronecker pauliX pauliX * Matrix.kronecker pauliZ pauliZ =
    -(Matrix.kronecker pauliY pauliY) := by
  simp only [Matrix.kronecker]
  rw [← Matrix.mul_kronecker_mul]
  ext ⟨a, b⟩ ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [Matrix.kroneckerMap, Matrix.mul_apply, Fintype.sum_bool, pauliX, pauliY, pauliZ]

end QAlgorithms



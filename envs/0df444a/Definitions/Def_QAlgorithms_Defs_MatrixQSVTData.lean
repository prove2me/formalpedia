-- Prove2me | Definitions.Def_QAlgorithms_Defs_MatrixQSVTData
-- name    : QAlgorithms_Defs_MatrixQSVTData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:20:22.614857+00:00
-- url     : https://prove2.me/theorems/9c6a1674-39de-4d7f-85ae-6825008c6c90
-- title:
--   MatrixQSVTData
-- statement:
--   MatrixQSVTData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\MatrixQSVTData.lean

import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Defs_Hamiltonian
noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.MatrixQSVT

universe u

/-- QAlgorithms.MatrixQSVT.PolynomialData: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
structure PolynomialData (r c d : ℕ) where
  rows_pos : 0 < r
  cols_pos : 0 < c
  polynomial : Matrix (Fin r) (Fin c) (Polynomial ℂ)
  degree : ∀ i j, (polynomial i j).natDegree ≤ d
  parity : ∀ i j, HasParity (polynomial i j) d
  mixingQubits : ℕ
  rows : Fin r ↪ Qubits mixingQubits
  cols : Fin c ↪ Qubits mixingQubits

/-- QAlgorithms.MatrixQSVT.PolynomialData.eval: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.3. Source domains are explicit below. -/
def PolynomialData.eval {r c d : ℕ} (P : PolynomialData r c d) (x : ℝ) :
    Matrix (Fin r) (Fin c) ℂ := P.polynomial.map (Polynomial.eval (x : ℂ))

/-- QAlgorithms.MatrixQSVT.PolynomialData.padded: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.3. Source domains are explicit below. -/
def PolynomialData.padded {r c d : ℕ} (P : PolynomialData r c d) :
    Matrix (Qubits P.mixingQubits) (Qubits P.mixingQubits) (Polynomial ℂ) :=
  Matrix.of fun y z => ∑ i, ∑ j, if P.rows i = y ∧ P.cols j = z then P.polynomial i j else 0

/-- QAlgorithms.MatrixQSVT.IsRectangularEncoding: arxiv-2408.01439v4 PDF p.3, arxiv-2408.01439v4 PDF p.7. Source domains are explicit below. -/
def IsRectangularEncoding {I O K : Type*} [Fintype I] [Fintype O] [Fintype K]
    [Nonempty I] [Nonempty O] [Nonempty K] [DecidableEq K]
    (input : I ↪ K) (output : O ↪ K) (U : Matrix K K ℂ) (A : Matrix O I ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup K ℂ ∧ U.submatrix output input = A

/-- QAlgorithms.MatrixQSVT.evenTransform: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.3. Source domains are explicit below. -/
def evenTransform {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I]
    (A : Matrix O I ℂ) (p : Polynomial ℂ) (d : ℕ) : Matrix I I ℂ :=
  ∑ l ∈ Finset.range (d/2+1), p.coeff (2*l) • (Aᴴ*A)^l

/-- QAlgorithms.MatrixQSVT.oddTransform: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.3. Source domains are explicit below. -/
def oddTransform {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I]
    (A : Matrix O I ℂ) (p : Polynomial ℂ) (d : ℕ) : Matrix O I ℂ :=
  ∑ l ∈ Finset.range (d/2+1), p.coeff (2*l+1) • (A*(Aᴴ*A)^l)

/-- QAlgorithms.MatrixQSVT.OutputIndex: arxiv-2408.01439v4 PDF p.4, arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8, arxiv-2408.01439v4 PDF p.3. Source domains are explicit below. -/
abbrev OutputIndex (d : ℕ) (I O : Type u) := if d%2 = 0 then I else O

/-- QAlgorithms.MatrixQSVT.singularValuePolynomial: arxiv-2408.01439v4 PDF p.3, arxiv-2408.01439v4 PDF p.7. Source domains are explicit below. -/
def singularValuePolynomial {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I]
    (A : Matrix O I ℂ) (p : Polynomial ℂ) (d : ℕ)
    (degree : p.natDegree ≤ d) (parity : HasParity p d) : Matrix (OutputIndex d I O) I ℂ :=
  if h : d%2 = 0 then by simpa only [OutputIndex, if_pos h] using evenTransform A p d
  else by simpa only [OutputIndex, if_neg h] using oddTransform A p d

/-- QAlgorithms.MatrixQSVT.matrixTransform: arxiv-2408.01439v4 PDF p.7, arxiv-2408.01439v4 PDF p.8. Source domains are explicit below. -/
def matrixTransform {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I]
    {r c d : ℕ} (P : PolynomialData r c d) (A : Matrix O I ℂ) :
    Matrix (Fin r × OutputIndex d I O) (Fin c × I) ℂ :=
  Matrix.of fun x y => singularValuePolynomial A (P.polynomial x.1 y.1) d (P.degree x.1 y.1) (P.parity x.1 y.1) x.2 y.2

/-- Finite parity-dependent output register; arxiv-2408.01439v4 PDF pp.3,7-8. -/
instance outputIndexFintype (d : ℕ) (I O : Type u) [Fintype I] [Fintype O] :
    Fintype (OutputIndex d I O) := by
  unfold OutputIndex
  split_ifs <;> infer_instance

/-- Decidable basis equality on the same register; arxiv-2408.01439v4 PDF pp.3,7-8. -/
instance outputIndexDecidableEq (d : ℕ) (I O : Type u) [DecidableEq I] [DecidableEq O] :
    DecidableEq (OutputIndex d I O) := Classical.decEq _

example {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I]
    (A : Matrix O I ℂ) (z : ℂ) : evenTransform A (Polynomial.C z) 0 = z • 1 := by
  simp [evenTransform]

example {I O : Type u} [Fintype I] [Fintype O] [DecidableEq I] (A : Matrix O I ℂ) :
    oddTransform A Polynomial.X 1 = A := by simp [oddTransform]



end QAlgorithms.MatrixQSVT



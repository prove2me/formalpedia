-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P43
-- name    : QAlgorithms_Papers_Independent_Advance50_P43
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-29T09:07:56.791302+00:00
-- url     : https://prove2.me/theorems/0bb29dd1-a0ec-4335-b17d-4ffd23d9384a
-- title:
--   Definitions for Quantum-capacity bounds in spin-network communication channels
-- statement:
--   The objects the formalized statements of *Quantum-capacity bounds in spin-network communication channels* (arXiv:1905.11920) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `onA`: PDF p.2: an operator supported on A, extended by identity on BC.
--   - `onB`: PDF p.2: an operator supported on B, extended by identity on A and C.
--   - `LRData`: PDF pp.2--3, (2)--(6): Hermitian H and a nonnegative even, state-independent LR bound for ALL supported operators. Norms here are L2 operator norms. The optional geometric estimates (7)--(9) are not additional hypotheses.
--   - `receive`: PDF p.3, (12),(15): free evolution followed by tracing A and C.
--   - `encodedNetwork`: PDF p.3, (10),(13): product memory input with tau, E_QA acting only on QA, then trace Q. BC off-diagonal blocks are retained; tau need not be a product.
--   - `snc`: PDF p.3, (12): the actual induced SNC map on all operators.
--   - `comparisonZero`: PDF p.3, (14)--(15): unperturbed comparison, retaining correlations in tau.
--   - `comparisonOne`: PDF p.4, (23)--(24): comparison from PRODUCT MARGINALS of the original tau.
--   - `swapChannel`: PDF pp.3--4, (17)--(18): swap-in/swap-out, memory isomorphic to A.
--   - `stateDistance`: PDF p.5, (34)--(35): supremum on density operators, WITHOUT the half. For CPTP maps on nonzero finite registers the set is nonempty and bounded by 2.
--   - `dimensionConstant`: PDF p.4, (26): the network dimension constant, independent of Q and E.
--   - `minDimension`: PDF p.5, (30): min dimension uses A, not the external memory Q.
--   - `continuityG`: PDF p.4, (21)--(22): base-two continuity function, defined at zero by g(0)=0.
--   - `choiDilation`: PDF p.4, private capacity C_P: canonical Stinespring matrix used only to supply the dilation argument of the accepted operational privateCapacity. Columns of sqrt(Choi(Phi)) give Kraus matrices K_e(b,q)=sqrt(Choi(Phi))[(q,b),e]. For CPTP Phi this is an isometry with receiver channel Phi; the full environment Q x B is retained. No dilation or complement is assumed as extra theorem data.
-- source:
--   Quantum-capacity bounds in spin-network communication channels, arXiv:1905.11920v2, https://arxiv.org/abs/1905.11920v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P45
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

/-!
Statements from Chessa--Fanizza--Giovannetti, arXiv:1905.11920v2.
PDF page numbers are used throughout. The finite graph is reduced to the three
nonzero register factors A, B, C and its state-independent LR estimate. In
particular an empty region C is a one-dimensional factor, not an empty type.
Classical, private and assisted capacities reuse accepted operational interfaces;
quantum capacity reuses the accepted regularized coherent-information interface.
The input memory Q has no dimension restriction. The printed A-versus-Q
continuity step in (29) is explicitly flagged for independent moderation.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P43

open QAlgorithms.Papers.Independent.Dependency50.P45
  (holevoCapacity resourceCapacity standardEbit)
open QAlgorithms.Papers.Independent.Information100.P32 (evolution)
open QAlgorithms.Papers.Independent.Information100.P69 (replacer diamond)
open QAlgorithms.Papers.Independent.Information100.P67 (mapFirst privateCapacity)
open QAlgorithms.Papers.Independent.Information100.P22 (quantumCapacity)
open QAlgorithms.Papers.Independent.Dependency50.P23 (ordinaryClassicalCapacity)
open QAlgorithms.Papers.Independent.Information100.P34 (choi)

variable {A B C Q : Type}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype Q]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq Q]

/-- PDF p.2: an operator supported on A, extended by identity on BC. -/
def onA (X : Matrix A A ℂ) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.kronecker X 1

/-- PDF p.2: an operator supported on B, extended by identity on A and C. -/
def onB (Y : Matrix B B ℂ) : Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  Matrix.kronecker 1 (Matrix.kronecker Y (1 : Matrix C C ℂ))

/-- PDF pp.2--3, (2)--(6): Hermitian H and a nonnegative even, state-independent
LR bound for ALL supported operators. Norms here are L2 operator norms.
The optional geometric estimates (7)--(9) are not additional hypotheses. -/
structure LRData (A B C : Type) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] where
  H : Matrix (A × (B × C)) (A × (B × C)) ℂ
  hermitian : H.IsHermitian
  epsilon : ℝ → ℝ
  nonnegative : ∀ t, 0 ≤ epsilon t
  even : ∀ t, epsilon (-t) = epsilon t
  bound : ∀ t (X : Matrix A A ℂ) (Y : Matrix B B ℂ),
    let U := evolution H t
    let Xt := Uᴴ * onA (B := B) (C := C) X * U
    ‖Xt * onB (A := A) (C := C) Y - onB (A := A) (C := C) Y * Xt‖ ≤
      epsilon t * ‖X‖ * ‖Y‖

/-- PDF p.3, (12),(15): free evolution followed by tracing A and C. -/
def receive (D : LRData A B C) (t : ℝ)
    (X : Matrix (A × (B × C)) (A × (B × C)) ℂ) : Matrix B B ℂ :=
  let U := evolution D.H t
  fun b bprime => ∑ a, ∑ c, (U * X * Uᴴ) (a, (b, c)) (a, (bprime, c))

/-- PDF p.3, (10),(13): product memory input with tau, E_QA acting only on QA,
then trace Q. BC off-diagonal blocks are retained; tau need not be a product. -/
def encodedNetwork (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (E : Superop (Q × A) (Q × A)) (rho : Matrix Q Q ℂ) :
    Matrix (A × (B × C)) (A × (B × C)) ℂ :=
  fun x y => ∑ q : Q,
    E (fun qa qaprime => rho qa.1 qaprime.1 * tau (qa.2, x.2) (qaprime.2, y.2))
      (q, x.1) (q, y.1)

/-- PDF p.3, (12): the actual induced SNC map on all operators. -/
def snc (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ)
    (E : Superop (Q × A) (Q × A)) (t : ℝ) : Superop Q B :=
  fun rho => receive D t (encodedNetwork tau E rho)

/-- PDF p.3, (14)--(15): unperturbed comparison, retaining correlations in tau. -/
def comparisonZero (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (t : ℝ) : Superop Q B :=
  replacer (receive D t tau)

/-- PDF p.4, (23)--(24): comparison from PRODUCT MARGINALS of the original tau. -/
def comparisonOne (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (t : ℝ) : Superop Q B :=
  replacer (receive D t (Matrix.kronecker (traceRight tau) (traceLeft tau)))

/-- PDF pp.3--4, (17)--(18): swap-in/swap-out, memory isomorphic to A. -/
def swapChannel (D : LRData A B C)
    (tau : Matrix (A × (B × C)) (A × (B × C)) ℂ) (t : ℝ) : Superop A B :=
  fun rho => receive D t (Matrix.kronecker rho (traceLeft tau))

/-- PDF p.5, (34)--(35): supremum on density operators, WITHOUT the half.
For CPTP maps on nonzero finite registers the set is nonempty and bounded by 2. -/
def stateDistance (Phi Psi : Superop Q B) : ℝ :=
  sSup {v | ∃ rho : Matrix Q Q ℂ, IsDensityMatrix rho ∧
    v = traceNorm (Phi rho - Psi rho)}

/-- PDF p.4, (26): the network dimension constant, independent of Q and E. -/
def dimensionConstant (A B C : Type*) [Fintype A] [Fintype B] [Fintype C] : ℝ :=
  2 * min ((Fintype.card A : ℝ) ^ 4)
    ((Fintype.card A : ℝ) ^ 3 * Fintype.card B * Fintype.card C)

/-- PDF p.5, (30): min dimension uses A, not the external memory Q. -/
def minDimension (A B : Type*) [Fintype A] [Fintype B] : ℝ :=
  min (Fintype.card A : ℝ) (Fintype.card B : ℝ)

/-- PDF p.4, (21)--(22): base-two continuity function, defined at zero by g(0)=0. -/
def continuityG (x : ℝ) : ℝ := (1 + x) * binEntropy2 (x / (1 + x))

/-- PDF p.4, private capacity C_P: canonical Stinespring matrix used only to
supply the dilation argument of the accepted operational privateCapacity.
Columns of sqrt(Choi(Phi)) give Kraus matrices K_e(b,q)=sqrt(Choi(Phi))[(q,b),e].
For CPTP Phi this is an isometry with receiver channel Phi; the full environment
Q x B is retained. No dilation or complement is assumed as extra theorem data. -/
def choiDilation (Phi : Superop Q B) : Matrix (B × (Q × B)) Q ℂ :=
  fun be q => (cfc Real.sqrt (choi Phi)) (q, be.1) be.2

/-! Sanity examples pin the formula normalization and tensor conventions. -/

example : continuityG 0 = 0 := by
  simp [continuityG, binEntropy2]

example : dimensionConstant Unit Unit Unit = 2 := by
  norm_num [dimensionConstant]

example (omega : Matrix B B ℂ) (X : Matrix Q Q ℂ) :
    replacer omega X = X.trace • omega := rfl

example (D : LRData A B C) (t : ℝ) :
    receive D t (0 : Matrix (A × (B × C)) (A × (B × C)) ℂ) = 0 := by
  ext b bprime
  simp [receive]

example (Phi : Superop Q B) (b : B) (e : Q × B) (q : Q) :
    choiDilation Phi (b, e) q = (cfc Real.sqrt (choi Phi)) (q, b) e := rfl

end QAlgorithms.Papers.Independent.Advance50.P43



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P97
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P97
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T08:50:57.989346+00:00
-- url     : https://prove2.me/theorems/e80566c1-2da7-4bdf-87ae-683e5a3f7e9a
-- title:
--   Definitions for Lower bound on the relative error of mixed-state cloning and related operations
-- statement:
--   The objects the formalized statements of *Lower bound on the relative error of mixed-state cloning and related operations* (arXiv:quant-ph/0208159) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `dilationInput`: Product initial state in Eq. (12), PDF p.3, regrouped as `(A B) E`. The ancillary state on `B E` may be correlated or mixed.
--   - `relativeError`: Relative error of two joint outputs against two ideal joint states, Eq. (14), PDF p.3. The numerator is an unweighted sum. At identical ideals Lean division returns zero; no theorem below uses this extraneous extension.
--   - `oneToTwoError`: Relative error of the `1 → 2` dilation in Eqs. (12)--(14), PDF p.3. The same `V` is applied for both input labels.
--   - `copiesError`: Computed `N → N+M` relative error, Eq. (23), PDF p.4. The ideal `(N+M)`-copy state is grouped as its first `N` and last `M` copies.
--   - `cloningBound`: Scalar lower bound, Eq. (23), PDF p.4; `L=N+M` avoids natural subtraction. The denominator divides only the second term. `N=M=1` gives Eq. (15).
--   - `standardBound`: Standard cloning lower bound, Eq. (22), PDF p.4.
-- source:
--   Lower bound on the relative error of mixed-state cloning and related operations, arXiv:quant-ph/0208159v2, https://arxiv.org/abs/quant-ph/0208159v2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_QAlgorithms_Defs_Measurement
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

/-!
Statements from A. E. Rastegin, arXiv:quant-ph/0208159v2, PDF pp.2--5.
The paper's fidelity is squared Uhlmann fidelity. All dilation outputs are
computed from product initial states and a single common unitary. Relative
error is used only for distinct input states, so its denominator is positive.
The environment is arbitrary finite dimensional, with no dimension bound.
Squared fidelity, sine distance, computed receiver evolution and tensor powers
reuse the pinned accepted library; only the cloning-specific expressions are local.
-/

noncomputable section

open scoped Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Intakenext100.P97

open QAlgorithms.Papers.Independent.Information100.P67
  (squaredFidelity sineDistance receiverChannel)
open QAlgorithms.Papers.Independent.Dependency50.P48 (densityPower)

/-- Product initial state in Eq. (12), PDF p.3, regrouped as `(A B) E`.
The ancillary state on `B E` may be correlated or mixed. -/
def dilationInput {A B E : Type*} (rho : Matrix A A ℂ)
    (tau : Matrix (B × E) (B × E) ℂ) : Matrix ((A × B) × E) ((A × B) × E) ℂ :=
  fun x y => rho x.1.1 y.1.1 * tau (x.1.2, x.2) (y.1.2, y.2)

/-- Relative error of two joint outputs against two ideal joint states,
Eq. (14), PDF p.3. The numerator is an unweighted sum. At identical ideals
Lean division returns zero; no theorem below uses this extraneous extension. -/
def relativeError {A : Type*} [Fintype A] [DecidableEq A]
    (out1 out2 ideal1 ideal2 : Matrix A A ℂ) : ℝ :=
  (sineDistance out1 ideal1 + sineDistance out2 ideal2) / sineDistance ideal1 ideal2

/-- Relative error of the `1 → 2` dilation in Eqs. (12)--(14), PDF p.3.
The same `V` is applied for both input labels. -/
def oneToTwoError {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (tau1 tau2 : Matrix (Fin d × E) (Fin d × E) ℂ)
    (V : Matrix.unitaryGroup ((Fin d × Fin d) × E) ℂ) : ℝ :=
  relativeError (receiverChannel (V : Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) (dilationInput rho1 tau1))
    (receiverChannel (V : Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) (dilationInput rho2 tau2))
    (Matrix.kronecker rho1 rho1) (Matrix.kronecker rho2 rho2)

/-- Computed `N → N+M` relative error, Eq. (23), PDF p.4.
The ideal `(N+M)`-copy state is grouped as its first `N` and last `M` copies. -/
def copiesError {d : ℕ} (N M : ℕ) {E : Type*} [Fintype E] [DecidableEq E]
    (rho1 rho2 : Matrix (Fin d) (Fin d) ℂ)
    (tau1 tau2 : Matrix ((Fin M → Fin d) × E) ((Fin M → Fin d) × E) ℂ)
    (V : Matrix.unitaryGroup (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) : ℝ :=
  relativeError (receiverChannel (V : Matrix (((Fin N → Fin d) × (Fin M → Fin d)) × E) (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) (dilationInput (densityPower rho1 N) tau1))
    (receiverChannel (V : Matrix (((Fin N → Fin d) × (Fin M → Fin d)) × E) (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) (dilationInput (densityPower rho2 N) tau2))
    (Matrix.kronecker (densityPower rho1 N) (densityPower rho1 M))
    (Matrix.kronecker (densityPower rho2 N) (densityPower rho2 M))

/-- Scalar lower bound, Eq. (23), PDF p.4; `L=N+M` avoids natural subtraction.
The denominator divides only the second term. `N=M=1` gives Eq. (15). -/
def cloningBound (N M : ℕ) (f phi : ℝ) : ℝ :=
  f ^ N * phi - f ^ (N + M) * Real.sqrt (1 - f ^ (2 * N) * phi ^ 2) /
    Real.sqrt (1 - f ^ (2 * (N + M)))

/-- Standard cloning lower bound, Eq. (22), PDF p.4. -/
def standardBound (f : ℝ) : ℝ :=
  f - f ^ 2 / Real.sqrt (1 + f ^ 2)

/-! Sanity examples pin square convention, register order, tensor powers,
identity evolution, the unweighted ratio, and the orthogonal endpoint. -/

example : squaredFidelity (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 1 := by
  simp [squaredFidelity, rootFidelity, cfc_one]

example : sineDistance (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 := by
  simp [sineDistance, squaredFidelity, rootFidelity, cfc_one]

example {A B E : Type*} (rho : Matrix A A ℂ)
    (tau : Matrix (B × E) (B × E) ℂ) (a a' : A) (b b' : B) (e e' : E) :
    dilationInput rho tau ((a,b),e) ((a',b'),e') = rho a a' * tau (b,e) (b',e') := by
  rfl

example {A B E : Type*} [Fintype A] [Fintype B] [Fintype E]
    [DecidableEq A] [DecidableEq B] [DecidableEq E]
    (rho : Matrix A A ℂ) (tau : Matrix (B × E) (B × E) ℂ) :
    receiverChannel (1 : Matrix ((A × B) × E) ((A × B) × E) ℂ)
      (dilationInput rho tau) = traceRight (dilationInput rho tau) := by
  simp [receiverChannel]

example {A : Type*} [Fintype A] [DecidableEq A] (o1 o2 t1 t2 : Matrix A A ℂ) :
    relativeError o1 o2 t1 t2 =
      (sineDistance o1 t1 + sineDistance o2 t2) / sineDistance t1 t2 := by
  rfl

example {d : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (r1 r2 : Matrix (Fin d) (Fin d) ℂ)
    (t1 t2 : Matrix (Fin d × E) (Fin d × E) ℂ)
    (V : Matrix.unitaryGroup ((Fin d × Fin d) × E) ℂ) :
    oneToTwoError r1 r2 t1 t2 V =
      relativeError (receiverChannel (V : Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) (dilationInput r1 t1))
        (receiverChannel (V : Matrix ((Fin d × Fin d) × E) ((Fin d × Fin d) × E) ℂ) (dilationInput r2 t2))
        (Matrix.kronecker r1 r1) (Matrix.kronecker r2 r2) := by
  rfl

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (x y : Fin 1 → Fin d) :
    densityPower rho 1 x y = rho (x 0) (y 0) := by
  simp [densityPower]

example {d : ℕ} (rho : Matrix (Fin d) (Fin d) ℂ) (x y : Fin 0 → Fin d) :
    densityPower rho 0 x y = 1 := by
  simp [densityPower]

example {d N M : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (r1 r2 : Matrix (Fin d) (Fin d) ℂ)
    (t1 t2 : Matrix ((Fin M → Fin d) × E) ((Fin M → Fin d) × E) ℂ)
    (V : Matrix.unitaryGroup (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) :
    copiesError N M r1 r2 t1 t2 V =
      relativeError (receiverChannel (V : Matrix (((Fin N → Fin d) × (Fin M → Fin d)) × E) (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) (dilationInput (densityPower r1 N) t1))
        (receiverChannel (V : Matrix (((Fin N → Fin d) × (Fin M → Fin d)) × E) (((Fin N → Fin d) × (Fin M → Fin d)) × E) ℂ) (dilationInput (densityPower r2 N) t2))
        (Matrix.kronecker (densityPower r1 N) (densityPower r1 M))
        (Matrix.kronecker (densityPower r2 N) (densityPower r2 M)) := by
  rfl

example (phi : ℝ) : cloningBound 1 1 0 phi = 0 := by
  norm_num [cloningBound]

example : standardBound 0 = 0 := by
  norm_num [standardBound]

end QAlgorithms.Papers.Independent.Intakenext100.P97



-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P83
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P83
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T07:06:34.550356+00:00
-- url     : https://prove2.me/theorems/ec68f379-9b85-4d5f-8a88-e50f5676cf59
-- title:
--   Definitions for Improved Semidefinite Programming Upper Bound on Distillable Entanglement
-- statement:
--   The objects the formalized statements of *Improved Semidefinite Programming Upper Bound on Distillable Entanglement* (arXiv:1601.07940) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `complexSpectralNorm`: Largest singular value: operator norm on the Euclidean Hilbert space. PDF p.1.
--   - `regroupedTensor`: Regroup (A:B) tensor (C:D) as (A,C):(B,D). PDF pp.2–3, property i).
--   - `regroupedPower`: Regrouped n-copy matrix, including the scalar empty tensor at n=0. PDF pp.2,4.
--   - `FidelityFeasible`: Eq. (3), for positive REAL k: 0 <= Q <= I and -I/k <= T_B(Q) <= I/k. PDF p.2. The positivity guard is part of the feasible set.
--   - `pptDistillationFidelity`: F_Gamma from the independent SDP (3). PDF p.2. For states and k>0 its objective set is nonempty (Q=0), bounded in [0,1], and compactly attained.
--   - `PPTAchievableRate`: An achievable rate in Eq. (4), without assuming the optimal rate is achieved. PDF p.2. All rates are in bits; convergence is to fidelity ONE.
--   - `entanglementGamma`: Eq. (4): supremum over all achievable real rates. PDF p.2. For a density matrix the set contains 0 and is bounded above by finite log dimension.
--   - `WFeasible`: The primal witness in Eq. (7). R is Hermitian but need not be positive. PDF p.2.
--   - `wValue`: The independently defined primal optimum (7), PDF p.2. The witness set contains 0 and is compact; hence the real supremum is bounded.
--   - `entanglementW`: E_W = log_2 W, PDF p.2. W is at least 1 on every density matrix.
--   - `DualUVFeasible`: The U,V dual constraints (8), PDF p.2. No trace normalization is imposed.
--   - `dualUVValue`: The independently defined two-variable dual (8), PDF p.2. For states U=3I,V=I is strictly feasible; the objective is bounded below by zero.
--   - `dualXValue`: The independently defined one-variable dual (9), PDF p.2. For states X=rho is feasible and the trace-norm objective is nonnegative.
--   - `entanglementN`: Logarithmic negativity (5), PDF p.2; the trace norm is the frozen Tr sqrt(M-adjoint M), not the entrywise sum. Its argument is at least 1 on a density matrix.
--   - `transposeConjugate`: Conjugation of a bipartite map by the input and output partial transposes. PDF pp.2–3.
--   - `PPTInstrument`: A discrete PPT instrument, PDF p.3, Theorem 3: each branch and its transpose conjugate are CP, branches are trace nonincreasing, and the unconditionally summable total map is a channel. The outcome type is arbitrary; finite and countable outcomes are included. Input and output dimensions may differ.
--   - `branchContribution`: The summand p_i E_W(rho_i) in (6). A zero-probability branch contributes zero and is never normalized. PDF pp.2–3.
--   - `supportSpace`: The support of a positive matrix is its range, equivalently the span of its positive-eigenvalue eigenvectors. PDF p.4.
--   - `oneCopyExact`: Independently defined one-copy exact PPT rate from F_Gamma, PDF p.4. The target k is positive real. For states the set contains log_2(1)=0 and is bounded above; attainment is asserted in the deterministic SDP theorem.
--   - `exactRegularized`: Independent supremum definition of E_Gamma,0, PDF p.4. Index n+1 ranges over exactly the positive blocklengths and avoids division by zero. Its defining set is nonempty and bounded above on density matrices.
--   - `WZeroFeasible`: Eq. (14): 0 <= R <= (Tr rho R)I and -I <= T_B(R) <= I. For Hermitian R the latter is equivalent to |T_B(R)| <= I. PDF p.5.
--   - `wZeroValue`: The independent linear SDP optimum W_0 in (14), PDF p.5. For states I is feasible and gives value 1; the objective is bounded above.
--   - `supportNormMinimum`: The independently defined norm minimization underlying (15), PDF p.5. Its feasible interval is P_rho <= R <= I. It is compact and nonempty (R=I), and the minimum is positive on a density matrix. The logarithm is applied AFTER it.
--   - `qutritKet`: Qutrit product-basis vector |ab>, PDF p.4.
--   - `qutritPsi`: The three vectors defining rho(alpha), PDF p.4 before Proposition 5.
--   - `rhoAlpha`: The actual qutrit state rho(alpha), not an abstract state specified by a value of its entanglement. Normalized for 0<alpha<=1/2. PDF p.4.
--   - `symmetricSupport`: The three-dimensional off-diagonal symmetric support S_plus, PDF p.4. This is not the full six-dimensional symmetric subspace.
--   - `antisymmetricSupport`: The qutrit antisymmetric support S_minus, PDF p.4, Remark.
--   - `qutritAntisymmetricState`: The normalized qutrit antisymmetric state (I-SWAP)/6, PDF p.4, Remark.
-- source:
--   Improved Semidefinite Programming Upper Bound on Distillable Entanglement, arXiv:1601.07940v4, https://arxiv.org/abs/1601.07940v4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_MatrixDistances
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_MatrixMapPositivity
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P11
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P32
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P63

/-!
Statements from Wang–Duan, arXiv:1601.07940v4. All spaces are finite dimensional,
with arbitrary finite local basis types. Partial transpose is on Bob's factor.
The positive-real target size in Eq. (3) is retained, including k = 3/2.
Compatible accepted definitions are imported; distinct paper objects and coordinate
adapters remain local. No frozen definitions are changed.
-/

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder
open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P83

open QAlgorithms.Papers.Independent.Support50.P11 (Loewner)
open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)
open QAlgorithms.Papers.Independent.Information100.P34 (supportProjector)

variable {A B C D : Type*}
variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]
variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Largest singular value: operator norm on the Euclidean Hilbert space. PDF p.1. -/
def complexSpectralNorm {I : Type*} [Fintype I] [DecidableEq I] (X : Matrix I I ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := I) (𝕜 := ℂ) X‖

/-- Regroup (A:B) tensor (C:D) as (A,C):(B,D). PDF pp.2–3, property i). -/
def regroupedTensor (rho : Matrix (A × B) (A × B) ℂ)
    (sigma : Matrix (C × D) (C × D) ℂ) :
    Matrix ((A × C) × (B × D)) ((A × C) × (B × D)) ℂ :=
  (Matrix.kronecker rho sigma).submatrix
    (fun p : (A × C) × (B × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    (fun p : (A × C) × (B × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))

/-- Regrouped n-copy matrix, including the scalar empty tensor at n=0. PDF pp.2,4. -/
def regroupedPower (rho : Matrix (A × B) (A × B) ℂ) (n : ℕ) :
    Matrix ((Fin n → A) × (Fin n → B)) ((Fin n → A) × (Fin n → B)) ℂ :=
  (QAlgorithms.Papers.Independent.Information100.P63.tensorPower n rho).submatrix
    (fun (p : (Fin n → A) × (Fin n → B)) t => (p.1 t, p.2 t)) (fun (p : (Fin n → A) × (Fin n → B)) t => (p.1 t, p.2 t))

/-- Eq. (3), for positive REAL k: 0 <= Q <= I and -I/k <= T_B(Q) <= I/k.
PDF p.2. The positivity guard is part of the feasible set. -/
def FidelityFeasible (k : ℝ) (Q : Matrix (A × B) (A × B) ℂ) : Prop :=
  0 < k ∧ Q.PosSemidef ∧ Loewner Q 1 ∧
    Loewner ((-(k⁻¹) : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)) (partialTranspose Q) ∧
    Loewner (partialTranspose Q) ((k⁻¹ : ℂ) • (1 : Matrix (A × B) (A × B) ℂ))

/-- F_Gamma from the independent SDP (3). PDF p.2. For states and k>0 its
objective set is nonempty (Q=0), bounded in [0,1], and compactly attained. -/
def pptDistillationFidelity (rho : Matrix (A × B) (A × B) ℂ) (k : ℝ) : ℝ :=
  sSup {v : ℝ | ∃ Q, FidelityFeasible k Q ∧ v = effectProb rho Q}

/-- An achievable rate in Eq. (4), without assuming the optimal rate is achieved.
PDF p.2. All rates are in bits; convergence is to fidelity ONE. -/
def PPTAchievableRate (rho : Matrix (A × B) (A × B) ℂ) (r : ℝ) : Prop :=
  Tendsto (fun n : ℕ => pptDistillationFidelity (regroupedPower rho n) ((2 : ℝ) ^ ((n : ℝ) * r)))
    atTop (nhds 1)

/-- Eq. (4): supremum over all achievable real rates. PDF p.2.
For a density matrix the set contains 0 and is bounded above by finite log dimension. -/
def entanglementGamma (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {r : ℝ | PPTAchievableRate rho r}

/-- The primal witness in Eq. (7). R is Hermitian but need not be positive.
PDF p.2. -/
def WFeasible (R : Matrix (A × B) (A × B) ℂ) : Prop :=
  R.IsHermitian ∧ complexSpectralNorm R ≤ 1 ∧ (partialTranspose R).PosSemidef

/-- The independently defined primal optimum (7), PDF p.2.
The witness set contains 0 and is compact; hence the real supremum is bounded. -/
def wValue (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ R, WFeasible R ∧ v = effectProb (partialTranspose rho) R}

/-- E_W = log_2 W, PDF p.2. W is at least 1 on every density matrix. -/
def entanglementW (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.logb 2 (wValue rho)

/-- The U,V dual constraints (8), PDF p.2. No trace normalization is imposed. -/
def DualUVFeasible (rho U V : Matrix (A × B) (A × B) ℂ) : Prop :=
  U.PosSemidef ∧ V.PosSemidef ∧ Loewner rho (partialTranspose (U - V))

/-- The independently defined two-variable dual (8), PDF p.2.
For states U=3I,V=I is strictly feasible; the objective is bounded below by zero. -/
def dualUVValue (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ U V, DualUVFeasible rho U V ∧ v = (U + V).trace.re}

/-- The independently defined one-variable dual (9), PDF p.2.
For states X=rho is feasible and the trace-norm objective is nonnegative. -/
def dualXValue (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ X, Loewner rho X ∧ v = traceNorm (partialTranspose X)}

/-- Logarithmic negativity (5), PDF p.2; the trace norm is the frozen Tr sqrt(M-adjoint M),
not the entrywise sum. Its argument is at least 1 on a density matrix. -/
def entanglementN (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  Real.logb 2 (traceNorm (partialTranspose rho))

/-- Conjugation of a bipartite map by the input and output partial transposes.
PDF pp.2–3. -/
def transposeConjugate
    (N : Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ) :
    Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ :=
  fun X => partialTranspose (N (partialTranspose X))

/-- A discrete PPT instrument, PDF p.3, Theorem 3: each branch and its
transpose conjugate are CP, branches are trace nonincreasing, and the
unconditionally summable total map is a channel. The outcome type is arbitrary;
finite and countable outcomes are included. Input and output dimensions may differ. -/
def PPTInstrument {O : Type*}
    (N : O → Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ) : Prop :=
  (∀ i,
    (∃ Phi Psi : Matrix (A × B) (A × B) ℂ →ₗ[ℂ] Matrix (C × D) (C × D) ℂ,
      Entanglement.IsCompletelyPositive Phi ∧ Entanglement.IsCompletelyPositive Psi ∧
      (∀ X, N i X = Phi X) ∧ (∀ X, transposeConjugate (N i) X = Psi X)) ∧
    ∀ X, X.PosSemidef → (N i X).trace.re ≤ X.trace.re) ∧
  ∃ total : Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ,
    IsChannel total ∧ ∀ X, HasSum (fun i => N i X) (total X)

/-- The summand p_i E_W(rho_i) in (6). A zero-probability branch contributes
zero and is never normalized. PDF pp.2–3. -/
def branchContribution
    (N : Matrix (A × B) (A × B) ℂ → Matrix (C × D) (C × D) ℂ)
    (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  let p := (N rho).trace.re
  if 0 < p then p * entanglementW ((p⁻¹ : ℂ) • N rho) else 0

/-- The support of a positive matrix is its range, equivalently the span of
its positive-eigenvalue eigenvectors. PDF p.4. -/
def supportSpace {I : Type*} [Fintype I] [DecidableEq I] (rho : Matrix I I ℂ) :
    Submodule ℂ (I → ℂ) :=
  LinearMap.range (Matrix.toLin' rho)

/-- Independently defined one-copy exact PPT rate from F_Gamma, PDF p.4.
The target k is positive real. For states the set contains log_2(1)=0 and is
bounded above; attainment is asserted in the deterministic SDP theorem. -/
def oneCopyExact (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ k : ℝ, 0 < k ∧ pptDistillationFidelity rho k = 1 ∧ v = Real.logb 2 k}

/-- Independent supremum definition of E_Gamma,0, PDF p.4.
Index n+1 ranges over exactly the positive blocklengths and avoids division by zero.
Its defining set is nonempty and bounded above on density matrices. -/
def exactRegularized (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup (Set.range (fun n : ℕ => oneCopyExact (regroupedPower rho (n + 1)) / (n + 1 : ℝ)))

/-- Eq. (14): 0 <= R <= (Tr rho R)I and -I <= T_B(R) <= I.
For Hermitian R the latter is equivalent to |T_B(R)| <= I. PDF p.5. -/
def WZeroFeasible (rho R : Matrix (A × B) (A × B) ℂ) : Prop :=
  R.PosSemidef ∧ Loewner R ((effectProb rho R : ℂ) • (1 : Matrix (A × B) (A × B) ℂ)) ∧
    Loewner (-1 : Matrix (A × B) (A × B) ℂ) (partialTranspose R) ∧
    Loewner (partialTranspose R) 1

/-- The independent linear SDP optimum W_0 in (14), PDF p.5.
For states I is feasible and gives value 1; the objective is bounded above. -/
def wZeroValue (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sSup {v : ℝ | ∃ R, WZeroFeasible rho R ∧ v = effectProb rho R}

/-- The independently defined norm minimization underlying (15), PDF p.5.
Its feasible interval is P_rho <= R <= I. It is compact and nonempty (R=I),
and the minimum is positive on a density matrix. The logarithm is applied AFTER it. -/
def supportNormMinimum (rho : Matrix (A × B) (A × B) ℂ) : ℝ :=
  sInf {v : ℝ | ∃ R, Loewner (supportProjector rho) R ∧ Loewner R 1 ∧
    v = complexSpectralNorm (partialTranspose R)}

/-- Qutrit product-basis vector |ab>, PDF p.4. -/
def qutritKet (a b : Fin 3) : (Fin 3 × Fin 3) → ℂ :=
  fun p => if p = (a, b) then 1 else 0

/-- The three vectors defining rho(alpha), PDF p.4 before Proposition 5. -/
def qutritPsi (alpha : ℝ) : Fin 3 → (Fin 3 × Fin 3) → ℂ :=
  ![(Real.sqrt alpha : ℂ) • qutritKet 0 1 + (Real.sqrt (1 - alpha) : ℂ) • qutritKet 1 0,
    (Real.sqrt alpha : ℂ) • qutritKet 0 2 + (Real.sqrt (1 - alpha) : ℂ) • qutritKet 2 0,
    (Real.sqrt alpha : ℂ) • qutritKet 1 2 + (Real.sqrt (1 - alpha) : ℂ) • qutritKet 2 1]

/-- The actual qutrit state rho(alpha), not an abstract state specified by a
value of its entanglement. Normalized for 0<alpha<=1/2. PDF p.4. -/
def rhoAlpha (alpha : ℝ) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 3 : ℂ) • ∑ m : Fin 3, pureDensity (WithLp.toLp 2 (qutritPsi alpha m))

/-- The three-dimensional off-diagonal symmetric support S_plus, PDF p.4.
This is not the full six-dimensional symmetric subspace. -/
def symmetricSupport : Submodule ℂ ((Fin 3 × Fin 3) → ℂ) :=
  Submodule.span ℂ (Set.range (![qutritKet 0 1 + qutritKet 1 0,
    qutritKet 0 2 + qutritKet 2 0, qutritKet 1 2 + qutritKet 2 1] :
    Fin 3 → (Fin 3 × Fin 3) → ℂ))

/-- The qutrit antisymmetric support S_minus, PDF p.4, Remark. -/
def antisymmetricSupport : Submodule ℂ ((Fin 3 × Fin 3) → ℂ) :=
  Submodule.span ℂ (Set.range (![qutritKet 0 1 - qutritKet 1 0,
    qutritKet 0 2 - qutritKet 2 0, qutritKet 1 2 - qutritKet 2 1] :
    Fin 3 → (Fin 3 × Fin 3) → ℂ))

/-- The normalized qutrit antisymmetric state (I-SWAP)/6, PDF p.4, Remark. -/
def qutritAntisymmetricState : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 6 : ℂ) • ((1 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) -
    (Matrix.of fun (p q : Fin 3 × Fin 3) => if p.1 = q.2 ∧ p.2 = q.1 then (1 : ℂ) else 0))

/-! Sanity examples pin transposition, regrouping, zero branches, and normalization
conventions; they introduce no assumed theorem content. -/

example (X : Matrix (A × B) (A × B) ℂ) :
    partialTranspose (partialTranspose X) = X := rfl

example (X : Matrix (A × B) (A × B) ℂ) (a c : A) (b d : B) :
    partialTranspose X (a, b) (c, d) = X (a, d) (c, b) := rfl

example {I : Type*} [Fintype I] [DecidableEq I] :
    complexSpectralNorm (0 : Matrix I I ℂ) = 0 := by
  simp [complexSpectralNorm]

example (rho : Matrix (A × B) (A × B) ℂ) (sigma : Matrix (C × D) (C × D) ℂ)
    (a c : A) (b d : B) (e g : C) (f h : D) :
    regroupedTensor rho sigma ((a,e),(b,f)) ((c,g),(d,h)) = rho (a,b) (c,d) * sigma (e,f) (g,h) := rfl

example (rho : Matrix (A × B) (A × B) ℂ)
    (p q : (Fin 0 → A) × (Fin 0 → B)) : regroupedPower rho 0 p q = 1 := by
  simp [regroupedPower, QAlgorithms.Papers.Independent.Information100.P63.tensorPower, Matrix.submatrix]

example (rho : Matrix (A × B) (A × B) ℂ) :
    branchContribution (fun _ => (0 : Matrix (C × D) (C × D) ℂ)) rho = 0 := by
  simp [branchContribution]

example : qutritKet 0 1 (0,1) = 1 ∧ qutritKet 0 1 (1,0) = 0 := by
  norm_num [qutritKet]

example : qutritAntisymmetricState (0,1) (0,1) = 1/6 ∧ qutritAntisymmetricState (0,1) (1,0) = -(1/6) := by
  norm_num [qutritAntisymmetricState, Matrix.smul_apply, Matrix.sub_apply,
    Matrix.of_apply, Matrix.one_apply]

end QAlgorithms.Papers.Independent.Intakethird100.P83



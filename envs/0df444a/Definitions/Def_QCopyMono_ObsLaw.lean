-- Prove2me | Definitions.Def_QCopyMono_ObsLaw
-- name    : QCopyMono_ObsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:44:28.408667+00:00
-- url     : https://prove2.me/theorems/1dbbc092-a21c-4207-b76d-fd1b226c844d
-- title:
--   Measuring an observable, and the joint law of the path estimator $\hat p_d$
-- statement:
--   Measuring a Hermitian observable $A$ with eigen-decomposition $A=\sum_i\lambda_i|v_i\rangle\langle v_i|$ on a state $|\psi\rangle$ reports $\lambda_i$ with probability $|\langle v_i|\psi\rangle|^2$; its outcome law is $\sum_i|\langle v_i|\psi\rangle|^2\,\delta_{\lambda_i}$, which does not depend on the choice of eigenbasis.
--
--   The path estimator (20) takes $m$ independent outcomes $U^{(1)},\dots,U^{(m)}$ of measuring $Q_d$ and, on independent copies, $m$ outcomes $V^{(1)},\dots,V^{(m)}$ of measuring $H_d\otimes Z$, each on a copy of $|\psi_f\rangle$, and forms
--   $$
--   \hat p_d=\tfrac12\overline U_d-\tfrac14\overline V_d,\qquad \overline U_d=\tfrac1m\sum_{j=1}^mU^{(j)},\quad \overline V_d=\tfrac1m\sum_{j=1}^mV^{(j)}.
--   $$
--   The joint law of the $2m$ outcomes is the product of $m$ copies of the $Q_d$-law and $m$ copies of the $H_d\otimes Z$-law.
--
--   **Formalization Note** The eigenbasis is Mathlib's `eigenvectorBasis`. The state is `fnVec f`, $|\psi_f\rangle$ as a vector of `EuclideanSpace ℂ (X n)`. The outcome laws are finite measures on $\mathbb R$ with finite support, so every moment exists.
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2.2, p.15, eq. (20); proof of Lemma 7, p.39

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_PathObservables

namespace QCopyMono

open QAlgorithms Matrix MeasureTheory

/-! # Measuring an observable, and the law of the path estimator `p̂_d`

P. Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2.2, p.15, eq. (20), and the proof of
Lemma 7, p.39.

**Formalization Note.** Measuring a Hermitian observable `A` on a state `ψ` is the projective
measurement in an orthonormal eigenbasis `(vᵢ)` of `A` (Mathlib's `eigenvectorBasis`), reporting
the eigenvalue: the outcome law is `∑ᵢ |⟨vᵢ, ψ⟩|² δ_{λᵢ}`. It does not depend on the choice of
eigenbasis (the weight of an eigenvalue is the squared norm of the projection of `ψ` on its
eigenspace). The estimator (20) uses `m` independent outcomes of each observable on independent
copies, so its inputs have the product law of `m` copies of the `Q_d`-law and `m` copies of the
`H_d ⊗ Z`-law. -/

/-- The function state `|ψ_f⟩` as a vector of `EuclideanSpace ℂ (X n)`. -/
noncomputable def fnVec {n : ℕ} (f : Qubits n → Bool) : EuclideanSpace ℂ (X n) :=
  WithLp.toLp 2 (fnState f)

/-- The outcome law of measuring the Hermitian observable `A` on `ψ`. -/
noncomputable def obsLaw {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ ι) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (‖inner ℂ (hA.eigenvectorBasis i) ψ‖ ^ 2) • Measure.dirac (hA.eigenvalues i)

instance obsLaw_isFiniteMeasure {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (ψ : EuclideanSpace ℂ ι) : IsFiniteMeasure (obsLaw A hA ψ) := by
  constructor
  simp only [obsLaw, Measure.coe_finsetSum, Measure.coe_smul, Finset.sum_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  exact ENNReal.sum_lt_top.mpr fun _ _ => ENNReal.ofReal_lt_top

/-- eq. (20), p.15: `p̂_d = ½ Ū_d − ¼ V̄_d`, with `Ū_d, V̄_d` the means of the `m` outcomes of
`Q_d` and of `H_d ⊗ Z`. -/
noncomputable def pathEstimate (m : ℕ) (p : (Fin m → ℝ) × (Fin m → ℝ)) : ℝ :=
  (∑ j, p.1 j) / m / 2 - (∑ j, p.2 j) / m / 4

/-- The joint law of the `2m` outcomes feeding (20): `m` independent outcomes of measuring
`Q_d` on copies of `|ψ_f⟩` and, independently, `m` of measuring `H_d ⊗ Z` (at `t_d = t`). -/
noncomputable def pathSampleLaw (n : ℕ) (ε : ℝ) (t m : ℕ) (f : Qubits n → Bool) :
    Measure ((Fin m → ℝ) × (Fin m → ℝ)) :=
  (Measure.pi fun _ : Fin m => obsLaw (pathQ n ε t) (pathQ_isHermitian n ε t) (fnVec f)).prod
    (Measure.pi fun _ : Fin m => obsLaw (pathHZ n ε t) (pathHZ_isHermitian n ε t) (fnVec f))

end QCopyMono



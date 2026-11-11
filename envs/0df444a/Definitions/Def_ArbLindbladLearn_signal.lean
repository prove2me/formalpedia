-- Prove2me | Definitions.Def_ArbLindbladLearn_signal
-- name    : ArbLindbladLearn_signal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:25:35.584864+00:00
-- url     : https://prove2.me/theorems/5d59acbf-f1ae-44d6-9cdc-d6df9d56b145
-- title:
--   Choi-matrix signals $f_{A,B}(t)$, Bell coherences $g_{ab}(t)$, witness signals $f_A(t)$
-- statement:
--   With $J_t=(\mathrm{id}\otimes e^{t\mathcal L})(|\Phi_0\rangle\langle\Phi_0|)$:
--   1. $f_{A,B}(t)=\langle\Phi_A|J_t|\Phi_B\rangle$ (Lemma 3.4);
--   2. the Bell coherences $g_{ab}(t)=\langle\Phi_a|J_t|\Phi_b\rangle$, with Pauli error rates $\lambda_a(t)=g_{aa}(t)$ (p.19);
--   3. the witness signals $f_A(t)=\langle\Phi_A|J_t|\Phi_A\rangle=\mathrm{tr}(\Pi_AJ_t)$ (§4.1).
--
--   Their endpoint derivatives at $t=0$ carry the Lindbladian coefficients.
--
--   **Formalization Note** $f_A(t)$ is real because $J_t$ is Hermitian; the real part is taken so that it is a real function of $t$.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), Lemma 3.4, p.20; p.19; §4.1, p.25

import Mathlib
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_bellVec
import Definitions.Def_ArbLindbladLearn_choiJ

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- The Choi-matrix signal `f_{A,B}(t) = ⟨Φ_A| J_t |Φ_B⟩` with `J_t = (id ⊗ e^{tℒ})(|Φ₀⟩⟨Φ₀|)`
(Lemma 3.4, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.20; `J_t` is defined on p.19). -/
def signal {n : ℕ} (c : Coeffs n) (A B : Op (Qubits n)) (t : ℝ) : ℂ :=
  bellForm (choiJ (evolution (gen c) t)) (bellVec A) (bellVec B)

/-- The Bell coherence `g_ab(t) = ⟨Φ_a| J_t |Φ_b⟩` of Pauli labels `a, b` (p.19). The Pauli error
rate is `λ_a(t) = g_aa(t)`. -/
def bellCoh {n : ℕ} (c : Coeffs n) (a b : Pauli n) (t : ℝ) : ℂ :=
  signal c (pauliMatrix a) (pauliMatrix b) t

/-- The witness signal `f_A(t) = ⟨Φ_A| J_t |Φ_A⟩ = tr(Π_A J_t)` (§4.1, p.25).

**Formalization Note** `J_t` is Hermitian, so `f_A(t)` is real; the real part is taken so that
`f_A` is a real function of `t` and `f′_A(0)` is its real derivative. -/
def witnessSignal {n : ℕ} (c : Coeffs n) (A : Op (Qubits n)) (t : ℝ) : ℝ :=
  (signal c A A t).re

end ArbLindbladLearn



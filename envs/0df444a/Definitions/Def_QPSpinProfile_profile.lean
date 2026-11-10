-- Prove2me | Definitions.Def_QPSpinProfile_profile
-- name    : QPSpinProfile_profile
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:26:06.486204+00:00
-- url     : https://prove2.me/theorems/ae777d7f-1f6e-4a0c-b14a-6435f739bfcc
-- title:
--   Pauli profile $f_\rho$, profile class, canonical norm and coordinate projection $M_J$
-- statement:
--   For an $n$-qubit state $\rho$, its **weight-$p$ Pauli profile** is the function
--   $$
--   f_\rho(P)=\operatorname{Tr}(P\rho),\qquad P\in\mathcal P_{n,p}.
--   $$
--   The energy $\operatorname{Tr}(H_{n,p}\rho)=\binom np^{-1/2}\sum_P g_P f_\rho(P)$ depends on $\rho$ only through $f_\rho$. For a class $\mathcal C_n$ of states, the **profile class** is $F_{n,p}(\mathcal C_n)=\{f_\rho:\rho\in\mathcal C_n\}$. Functions $f:\mathcal P_{n,p}\to\mathbb R$ carry the **canonical norm**
--   $$
--   \|f\|_{n,p}^2=\binom np^{-1}\sum_{P\in\mathcal P_{n,p}} f(P)^2 ,
--   $$
--   so that $\|f_\rho-f_\sigma\|_{n,p}^2=\operatorname{Var}(\operatorname{Tr}(H_{n,p}\rho)-\operatorname{Tr}(H_{n,p}\sigma))$ is the canonical metric of the energy process. For $J\subseteq[n]$, the **coordinate projection** keeps the interactions supported in $J$:
--   $$
--   (M_Jf)(P)=f(P)\,\mathbf 1\{\mathrm{supp}(P)\subseteq J\}.
--   $$
--
--   **Formalization Note** `profile p ρ P` is the real part of $\operatorname{Tr}(P\rho)$, which is real for a state.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §1.2, p.3 (PDF p.6); M_J: §2.1.4, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_QPSpinProfile_PauliString

namespace QPSpinProfile

open Matrix

/-- The weight-`p` Pauli profile `f_ρ(P) := Tr(Pρ)`, `P ∈ 𝒫_{n,p}`, of an `n`-qubit operator `ρ`
(arXiv:2610.02166, held version sha256 a0a1ec89…, §1.2, p.3, PDF p.6).

**Formalization Note** For a state `ρ` and a Hermitian Pauli string `P`, `Tr(Pρ)` is real; the
definition takes its real part. -/
noncomputable def profile {n : ℕ} (p : ℕ) (ρ : Matrix (Qubits n) (Qubits n) ℂ)
    (P : PauliString n p) : ℝ :=
  (Matrix.trace (P.mat * ρ)).re

/-- The profile class `F_{n,p}(C_n) := {f_ρ : ρ ∈ C_n}` (arXiv:2610.02166, §1.2, p.3, PDF p.6). -/
def profileClass (n p : ℕ) (C : Set (Matrix (Qubits n) (Qubits n) ℂ)) :
    Set (PauliString n p → ℝ) :=
  (fun ρ => profile p ρ) '' C

/-- The canonical norm `‖f‖_{n,p} := (C(n,p)^{-1} ∑_{P ∈ 𝒫_{n,p}} f(P)²)^{1/2}` on functions
`f : 𝒫_{n,p} → ℝ` (arXiv:2610.02166, §1.2, p.3, PDF p.6); the canonical metric of the energy
process is `d_{n,p}(f_ρ, f_σ) = ‖f_ρ − f_σ‖_{n,p}`. -/
noncomputable def profileNorm {n p : ℕ} (f : PauliString n p → ℝ) : ℝ :=
  Real.sqrt (((n.choose p : ℝ))⁻¹ * ∑ P : PauliString n p, f P ^ 2)

/-- The coordinate projection `(M_J f)(P) := f(P) 1{supp(P) ⊆ J}`, `P ∈ 𝒫_{n,p}`
(arXiv:2610.02166, §2.1.4, p.21, PDF p.24). -/
def coordProj {n p : ℕ} (J : Finset (Fin n)) (f : PauliString n p → ℝ) (P : PauliString n p) : ℝ :=
  if P.supp ⊆ J then f P else 0

end QPSpinProfile



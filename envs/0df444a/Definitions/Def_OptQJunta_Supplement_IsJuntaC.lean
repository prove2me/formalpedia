-- Prove2me | Definitions.Def_OptQJunta_Supplement_IsJuntaC
-- name    : OptQJunta_Supplement_IsJuntaC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:13:18.772921+00:00
-- url     : https://prove2.me/theorems/af324ee7-7eb0-4e42-ab1a-9f0118eb1808
-- title:
--   Unitary channels, junta channels $\mathcal C_T,\mathcal C_k$, the Choi matrix and the channel distance $\mathrm{dist}_{\mathcal C}$
-- statement:
--   Let $N=2^n$. A superoperator $\Phi$ on $n$ qubits is a **channel** if $\Phi(A)=\sum_jK_jAK_j^\dagger$ for a finite family with $\sum_jK_j^\dagger K_j=I_N$ (Fact 2.11); the **unitary channel** of $U$ is $\Phi_U(A)=UAU^\dagger$. For $T\subseteq[n]$, the **$T$-junta channels** are $\mathcal C_T=\{\Psi_T\otimes\mathrm{id}_{\overline T}:\Psi_T\text{ a channel on the qubits in }T\}$, and $\mathcal C_k=\bigcup_{|T|\le k}\mathcal C_T$ (Definition 2.17). The **Choi matrix** (Definition 2.7) is
--
--   $$
--   J(\Phi)=\sum_{a,b\in[N]}\Phi(|a\rangle\langle b|)\otimes|a\rangle\langle b|,
--   $$
--
--   the first factor the output and the second a reference copy, and the **channel distance** (Definition 2.18) is
--
--   $$
--   \mathrm{dist}_{\mathcal C}(\Phi,\Psi)=\frac{\|J(\Phi)-J(\Psi)\|_2}{N\sqrt2}.
--   $$
--
--   $\Phi$ is $\varepsilon$-far from $\mathcal C_k$ if $\inf_{\Psi\in\mathcal C_k}\mathrm{dist}_{\mathcal C}(\Phi,\Psi)\ge\varepsilon$, the infimum ranging over all $k$-junta channels, nonunitary ones included.
--
--   These are the YES and NO classes of Junta Channel Testing (Problem 6.1).
--
--   **Formalization Note** Channels and Kraus families are the published `QAlgorithms.IsChannel`, `IsKrausFamily`, `krausApply`; $\Phi_U$ is `conjSuperop U`. A junta channel is given by a Kraus family $L_j$ on the qubits in $T$, whose operators act as $L_j\otimes I_{\overline T}$; such a $\Phi$ is automatically a channel. $\varepsilon$-far is stated elementwise ($\mathcal C_k$ is nonempty).
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.2.3, pp.15–16 (Definition 2.7, Fact 2.11, Φ_U); §2.3.3, p.18 (Definitions 2.17, 2.18); Problem 6.1, p.71

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_OptQJunta_Supplement_IsJuntaU

namespace OptQJunta.Supplement

open QAlgorithms

/-- The unitary channel `Φ_U(A) = U A U†` of an `n`-qubit unitary `U` (Bao, Gao, Yao, *Optimal
Quantum Junta Testing*, preprint, version of November 3, 2026, sha256 a97d09a4…, §2.2.3, p.16).

**Formalization Note** It is the published `QAlgorithms.conjSuperop U`. -/
def unitChan {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) : Superop (Qubits n) (Qubits n) :=
  conjSuperop U

/-- **Definition 2.17** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.18):
`Φ ∈ 𝒞_T`, i.e. `Φ = Ψ_T ⊗ id_{T̄}` for a channel `Ψ_T ∈ C(ℋ_T)` on the qubits in `T`.

**Formalization Note** By the Kraus representation (Fact 2.11, p.15) `Ψ_T` is a channel iff
`Ψ_T(A) = Σ_j L_j A L_j†` for a finite family with `Σ_j L_j† L_j = I`; then `Ψ_T ⊗ id_{T̄}` has the
Kraus operators `L_j ⊗ I_{T̄}` (`liftT T (L j)`, acting as `L_j` on `T` and as the identity on `T̄`).
A superoperator is a function on all `N × N` matrices; equality holds on every matrix. -/
def IsJuntaCOn {n : ℕ} (Φ : Superop (Qubits n) (Qubits n)) (T : Finset (Fin n)) : Prop :=
  ∃ (m : ℕ) (L : Fin m → Matrix (↥T → Bool) (↥T → Bool) ℂ), IsKrausFamily L ∧
    ∀ A, Φ A = krausApply (fun j => liftT T (L j)) A

/-- **Definition 2.17** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.18):
`Φ ∈ 𝒞_k = ⋃_{T ⊆ [n], |T| ≤ k} 𝒞_T`, the `n`-qubit `k`-junta channels. -/
def IsJuntaC {n : ℕ} (Φ : Superop (Qubits n) (Qubits n)) (k : ℕ) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ k ∧ IsJuntaCOn Φ T

/-- **Definition 2.7** (Choi matrix; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.15): `J(Φ) = Σ_{a,b ∈ [N]} Φ(|a⟩⟨b|) ⊗ |a⟩⟨b|`, the first tensor factor the output
space and the second a reference copy of `ℋ`. -/
noncomputable def choi {n : ℕ} (Φ : Superop (Qubits n) (Qubits n)) :
    Matrix (Qubits n × Qubits n) (Qubits n × Qubits n) ℂ :=
  ∑ a : Qubits n, ∑ b : Qubits n,
    Matrix.kronecker (Φ (Matrix.single a b 1)) (Matrix.single a b (1 : ℂ))

/-- **Definition 2.18** (Channel distance; Bao–Gao–Yao preprint, version of November 3, 2026, sha256
a97d09a4…, p.18): `dist_𝒞(Φ, Ψ) = ‖J(Φ) − J(Ψ)‖₂ / (N√2)`, `N = 2^n`, `‖·‖₂` the Frobenius norm. -/
noncomputable def distC {n : ℕ} (Φ Ψ : Superop (Qubits n) (Qubits n)) : ℝ :=
  frobNorm (choi Φ - choi Ψ) / (2 ^ n * Real.sqrt 2)

/-- `dist_𝒞(Φ, 𝒞_k) ≥ ε` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
Definition 2.18, p.18, and Problem 6.1, p.71): every `k`-junta channel `Ψ`, nonunitary ones
included, has `dist_𝒞(Φ, Ψ) ≥ ε`.

**Formalization Note** The infimum over the nonempty set `𝒞_k` (it contains the identity channel)
is at least `ε` iff every element is. Every `Ψ` with `IsJuntaC Ψ k` is a channel (its Kraus family
`L_j ⊗ I_{T̄}` is normalized), so no separate channel hypothesis on `Ψ` is needed. -/
def FarC {n : ℕ} (Φ : Superop (Qubits n) (Qubits n)) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ Ψ : Superop (Qubits n) (Qubits n), IsJuntaC Ψ k → ε ≤ distC Φ Ψ

end OptQJunta.Supplement



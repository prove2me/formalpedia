-- Prove2me | Definitions.Def_OptQJunta_Supplement_IsJuntaU
-- name    : OptQJunta_Supplement_IsJuntaU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:12:11.177596+00:00
-- url     : https://prove2.me/theorems/8fd53c7b-8b88-4506-b5a9-964261e92b02
-- title:
--   Junta unitaries $\mathcal U_T,\mathcal U_k$ and the unitary distance $\mathrm{dist}_{\mathcal U}$ (Definitions 2.15, 2.16)
-- statement:
--   Let $N=2^n$. For $T\subseteq[n]$ write $\overline T=[n]\setminus T$ and $V_T\otimes I_{\overline T}$ for the operator acting as $V_T$ on the qubits in $T$ and as the identity elsewhere, with tensor factors in the original qubit order; in the computational basis,
--
--   $$
--   \langle x|V_T\otimes I_{\overline T}|y\rangle=\langle x_T|V_T|y_T\rangle\cdot[x_{\overline T}=y_{\overline T}].
--   $$
--
--   The **$T$-junta unitaries** are $\mathcal U_T=\{V_T\otimes I_{\overline T}:V_T\in U(2^{|T|})\}$ and the **$k$-junta unitaries** are $\mathcal U_k=\bigcup_{|T|\le k}\mathcal U_T$ (Definition 2.15). The **unitary distance** (Definition 2.16) is the phase-insensitive normalized Hilbert–Schmidt distance
--
--   $$
--   \mathrm{dist}_{\mathcal U}(U,V)=\min_{0\le\theta<2\pi}\frac{\|e^{i\theta}U-V\|_2}{\sqrt{2N}},
--   $$
--
--   $\|\cdot\|_2$ the Frobenius norm, and $U$ is **$\varepsilon$-far** from $\mathcal U_k$ if $\mathrm{dist}_{\mathcal U}(U,\mathcal U_k)=\inf_{V\in\mathcal U_k}\mathrm{dist}_{\mathcal U}(U,V)\ge\varepsilon$.
--
--   These are the YES and NO classes of Junta Unitary Testing (Problem 5.1).
--
--   **Formalization Note** $\mathcal H_T$ is $\mathbb C^{T\to\{0,1\}}$ (for $T=\varnothing$ this is $\mathbb C$, so $\mathcal U_\varnothing$ consists of global phases). The minimum over $\theta$ is written as an infimum over all real $\theta$ (same values by periodicity). $\varepsilon$-far is stated as: every $V\in\mathcal U_k$ has $\mathrm{dist}_{\mathcal U}(U,V)\ge\varepsilon$, equivalent because $\mathcal U_k$ is nonempty. Qubits are `Fin n` from $0$.
-- source:
--   Bao, Gao, Yao, Optimal Quantum Junta Testing, preprint (version of November 3, 2026, sha256 a97d09a4…), §2.3.2, p.17, Definitions 2.15 and 2.16 (Eq. (8)); Problem 5.1, p.62

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace OptQJunta.Supplement

open QAlgorithms

/-- The restriction `x_T = (x_i)_{i ∈ T}` of a basis string `x ∈ {0,1}^n` to the qubits in `T`
(Bao, Gao, Yao, *Optimal Quantum Junta Testing*, preprint, version of November 3, 2026, sha256
a97d09a4…, §2.1, p.12). -/
def restrictT {n : ℕ} (T : Finset (Fin n)) (x : Qubits n) : ↥T → Bool :=
  fun i => x i

/-- The operator `V_T ⊗ I_{T̄}` on `n` qubits that acts as `V_T` on the qubits in `T` and as the
identity on `T̄ = [n] ∖ T`, with tensor factors in the original qubit order (Bao–Gao–Yao preprint,
version of November 3, 2026, sha256 a97d09a4…, §2.3.2, p.17). Its matrix entries are
`⟨x|V_T ⊗ I_{T̄}|y⟩ = ⟨x_T|V_T|y_T⟩ · [x_{T̄} = y_{T̄}]`.

**Formalization Note** `ℋ_T` is `ℂ^{↥T → Bool}` (for `T = ∅` this is `ℂ`, one basis state). -/
def liftT {n : ℕ} (T : Finset (Fin n)) (V : Matrix (↥T → Bool) (↥T → Bool) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun x y => if ∀ i, i ∉ T → x i = y i then V (restrictT T x) (restrictT T y) else 0

/-- **Definition 2.15** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.17):
`U ∈ 𝒰_T`, i.e. `U = V_T ⊗ I_{T̄}` for some unitary `V_T ∈ U(2^{|T|})`. -/
def IsJuntaUOn {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (T : Finset (Fin n)) : Prop :=
  ∃ V ∈ Matrix.unitaryGroup (↥T → Bool) ℂ, U = liftT T V

/-- **Definition 2.15** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.17):
`U ∈ 𝒰_k = ⋃_{T ⊆ [n], |T| ≤ k} 𝒰_T`, the `n`-qubit `k`-junta unitaries. -/
def IsJuntaU {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (k : ℕ) : Prop :=
  ∃ T : Finset (Fin n), T.card ≤ k ∧ IsJuntaUOn U T

/-- **Definition 2.16** (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…, p.17,
Eq. (8)): the phase-insensitive normalized Hilbert–Schmidt distance
`dist_𝒰(U, V) = min_{0 ≤ θ < 2π} ‖e^{iθ}U − V‖₂ / √(2N)`, `N = 2^n`, `‖·‖₂` the Frobenius norm.

**Formalization Note** Written as the infimum over all real `θ`: `e^{iθ}` is `2π`-periodic, so the
set of values is the same as over `[0, 2π)`, and the minimum is attained (continuity on the circle);
the infimum of this nonempty set of nonnegative reals is that minimum. -/
noncomputable def distU {n : ℕ} (U V : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  ⨅ θ : ℝ, frobNorm (Complex.exp (θ * Complex.I) • U - V) / Real.sqrt (2 * 2 ^ n)

/-- `dist_𝒰(U, 𝒰_k) ≥ ε` (Bao–Gao–Yao preprint, version of November 3, 2026, sha256 a97d09a4…,
Definition 2.16, p.17, and Problem 5.1, p.62): every `k`-junta unitary `V` has `dist_𝒰(U, V) ≥ ε`.

**Formalization Note** `dist_𝒰(U, 𝒮) = inf_{V ∈ 𝒮} dist_𝒰(U, V)` over the nonempty set `𝒮 = 𝒰_k`
(it contains the identity), so the infimum is at least `ε` iff every element is. -/
def FarU {n : ℕ} (U : Matrix (Qubits n) (Qubits n) ℂ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ V : Matrix.unitaryGroup (Qubits n) ℂ, IsJuntaU (V : Matrix (Qubits n) (Qubits n) ℂ) k →
    ε ≤ distU U V

end OptQJunta.Supplement



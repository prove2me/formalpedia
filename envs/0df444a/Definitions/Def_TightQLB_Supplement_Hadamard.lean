-- Prove2me | Definitions.Def_TightQLB_Supplement_Hadamard
-- name    : TightQLB_Supplement_Hadamard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:24:12.199137+00:00
-- url     : https://prove2.me/theorems/084df0c1-3512-4a23-b54a-f4fd8e3f1a88
-- title:
--   Quantum Hadamard products $|\alpha\circ\beta\rangle$ and algorithms with state-preparation and reflection access
-- statement:
--   For unit vectors $|\alpha\rangle,|\beta\rangle\in\mathbb C^N$ whose coordinatewise product is not zero, the **quantum Hadamard product** is
--
--   $$
--   |\alpha\circ\beta\rangle=\frac{\sum_z\alpha_z\beta_z|z\rangle}{\big(\sum_y|\alpha_y\beta_y|^2\big)^{1/2}} .
--   $$
--
--   An algorithm of the shape used in §8.1 is fixed before $\alpha$ and $\beta$: it prepares $|\alpha\rangle$ in each of $m$ registers $S_1,\dots,S_m$ and $|\beta\rangle$ in a register $Y$ ($m+1$ preparation queries), starts a finite ancilla in a fixed basis state, and then applies fixed unitaries $W_0,\dots,W_k$ interleaved with $k$ reflections $2|\beta\rangle\langle\beta|-I$ on $Y$ ($2k$ further queries). Its output $\rho$ is the reduced state of $Y$. The trace distance is $\frac12\|\rho-\sigma\|_1$.
--
--   These objects state Theorem 8.1, an $O(N^{1/3})$-query algorithm for the Hadamard product of two states with amplitudes of magnitude $N^{-1/2}$.
--
--   **Formalization Note** The inputs enter only through the prepared states and the reflections, as with any state-preparation and reflection access (canonical oracles, or preparation unitaries with inverses).
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §8, p. 73 (PDF p. 76); Theorem 8.1 and its proof, pp. 73–74 (PDF pp. 76–77)

import Mathlib
import Definitions.Def_TightQLB_Supplement_Squaring
import Definitions.Def_TightQLB_Supplement_Entropy
open QAlgorithms
open scoped Matrix

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Quantum Hadamard products and algorithms with state-preparation and reflection access

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §8, p.73 (PDF p.76);
Theorem 8.1 and its proof, pp.73–74 (PDF pp.76–77).

"For two unit vectors `|α⟩ = Σ_z α_z|z⟩` and `|β⟩ = Σ_z β_z|z⟩` in `C^N` whose coordinatewise
product is not zero, the quantum Hadamard product is the normalized state
`|α ∘ β⟩ = Σ_z α_zβ_z|z⟩ / (Σ_y |α_yβ_y|²)^{1/2}`." "We assume oracle access for state preparation
and reflection, as in Section 6.1, that is, one query prepares each input state, and two queries
reflect about it."

**Formalization Note.**
* `HadamardAlg n m k K` is an algorithm, fixed before `α` and `β`, that prepares `|α⟩` in each of
  `m` registers `S₁, …, S_m` and `|β⟩` in a register `Y` (`m + 1` preparation queries), starts a
  finite ancilla `K` in a fixed basis state `k₀`, and then applies fixed unitaries `W₀, …, W_k` of
  the whole register interleaved with `k` reflections `2|β⟩⟨β| − I` on `Y` (two queries each,
  `2k` further queries). Its output is the reduced state of `Y`. The inputs `α`, `β` enter only
  through the prepared states and the reflections, as with any form of state-preparation and
  reflection access. This is the shape of the algorithm in the proof of Theorem 8.1; an algorithm of
  this shape is in particular an algorithm with that access.
* The trace distance is `(1/2)‖ρ − σ‖₁` with the trace norm of the entropy module.
-/

variable {n : ℕ}

/-- §8, p.73 (PDF p.76): `|α ∘ β⟩ = Σ_z α_zβ_z|z⟩ / (Σ_y |α_yβ_y|²)^{1/2}`. -/
noncomputable def hadamardProd (α β : EuclideanSpace ℂ (Qubits n)) : Qubits n → ℂ :=
  fun z => α z * β z / ((Real.sqrt (∑ y, ‖α y * β y‖ ^ 2) : ℝ) : ℂ)

/-- The register `S₁ ⋯ S_m ⊗ Y ⊗ K` of an algorithm with `m` copy registers and ancilla `K`. -/
abbrev HReg (n m : ℕ) (K : Type) := ((Fin m → Qubits n) × Qubits n) × K

/-- An algorithm with `m` preparations of `|α⟩`, one preparation of `|β⟩` and `k` reflections about
`|β⟩`, all other operations fixed unitaries. -/
structure HadamardAlg (n m k : ℕ) (K : Type) [Fintype K] [DecidableEq K] where
  /-- The fixed initial basis state of the ancilla. -/
  k₀ : K
  /-- The fixed unitaries `W₀, …, W_k`, independent of `α` and `β`. -/
  Wu : Fin (k + 1) → Matrix.unitaryGroup (HReg n m K) ℂ

namespace HadamardAlg

variable {m k : ℕ} {K : Type} [Fintype K] [DecidableEq K]

/-- The state `|α⟩^{⊗m} ⊗ |β⟩ ⊗ |k₀⟩` after the `m + 1` preparations. -/
noncomputable def startVec (A : HadamardAlg n m k K) (α β : EuclideanSpace ℂ (Qubits n)) :
    HReg n m K → ℂ :=
  fun i => (∏ j, α (i.1.1 j)) * β i.1.2 * (if i.2 = A.k₀ then 1 else 0)

/-- The reflection `2|β⟩⟨β| − I` on `Y`, identity on `S₁ ⋯ S_m` and `K`. -/
noncomputable def reflY (β : EuclideanSpace ℂ (Qubits n)) : Matrix (HReg n m K) (HReg n m K) ℂ :=
  Matrix.kronecker (Matrix.kronecker (1 : Matrix (Fin m → Qubits n) (Fin m → Qubits n) ℂ)
    (reflect β)) (1 : Matrix K K ℂ)

/-- The state after `W₀` and after each further reflection and unitary:
`ψ₀ = W₀ v`, `ψ_{t+1} = W_{t+1} R_β ψ_t`. -/
noncomputable def stateAt (A : HadamardAlg n m k K) (α β : EuclideanSpace ℂ (Qubits n)) :
    Fin (k + 1) → HReg n m K → ℂ :=
  Fin.induction ((A.Wu 0 : Matrix _ _ ℂ) *ᵥ A.startVec α β)
    (fun t ψ => ((A.Wu t.succ : Matrix _ _ ℂ) * reflY β) *ᵥ ψ)

/-- The output state `ρ`: the reduced state of the register `Y`. -/
noncomputable def output (A : HadamardAlg n m k K) (α β : EuclideanSpace ℂ (Qubits n)) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun y y' => ∑ s : Fin m → Qubits n, ∑ j : K,
    A.stateAt α β (Fin.last k) ((s, y), j) * star (A.stateAt α β (Fin.last k) ((s, y'), j))

end HadamardAlg

/-- The trace distance `(1/2)‖ρ − σ‖₁`. -/
noncomputable def traceDist (ρ σ : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  (1 / 2 : ℝ) * traceNorm (ρ - σ)

end TightQLB.Supplement



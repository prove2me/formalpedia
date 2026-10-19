-- Prove2me | Definitions.Def_QAlgorithms_Papers_LinTong20Ground_Model
-- name    : QAlgorithms_Papers_LinTong20Ground_Model
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:00:50.150285+00:00
-- url     : https://prove2.me/theorems/960cde73-92ee-425c-bf63-d0c34afa7bb5
-- title:
--   Near-optimal ground state preparation (Lin, Tong): supporting definitions
-- statement:
--   Supporting mathematical objects and conventions for the selected original paper results. Exact source hypotheses and labels are documented in the Lean declarations.
-- source:
--   Near-optimal ground state preparation (Lin, Tong), arXiv:2002.12508v3, https://arxiv.org/abs/2002.12508v3. Exact locators in declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_SpectralFilter
/-!
# Lin–Tong, *Near-optimal ground state preparation* (arXiv:2002.12508v3)

Cited "LT-gs p.N" (PDF pages). Theorem 6 (p.7): ground state preparation with an a priori
ground energy bound.

Model (pp.2–3, 5–7).
* `H ∈ ℂ^{N×N}`, `N = 2^n`, Hermitian, eigenvalues `λ₀ ≤ λ₁ ≤ ⋯` (frozen `ascEigenvalues`,
  increasing, `minEigenvalue = λ₀`); a ground state `|ψ₀⟩` is a unit eigenvector for `λ₀`
  (frozen `IsGroundState`).
* `U_H` is an `(α, m, 0)`-block-encoding of `H` (Eq. (1), p.3: an `(m + n)`-qubit unitary with
  `‖H − α(⟨0^m| ⊗ I) U_H (|0^m⟩ ⊗ I)‖ = 0`, ancilla register first): the frozen
  `IsQubitBlockEncoding m n U_H α 0 H`.
* `U_I` is an `n`-qubit unitary with `U_I |0^n⟩ = |φ₀⟩` (p.6).
* Fidelity between states `|x⟩, |y⟩` is `|⟨x|y⟩|` (footnote 1, p.2).
* The algorithm is an oracle circuit over one- and two-qubit gates (frozen
  `oneTwoQubitGateSet`) with two oracles, oracle `0` = `U_H` (on `m + n` wires) and oracle `1` =
  `U_I` (on `n` wires); plain, adjoint and controlled applications are all counted (frozen
  `queryCount`).
-/

namespace QAlgorithms.Papers.LinTong20Ground

open QAlgorithms

/-- The pair of oracles of Theorem 6: index `0` is the block-encoding `U_H` (on `m + n` qubits),
index `1` the initial-state preparation `U_I` (on `n` qubits). -/
def oraclePair {m n : ℕ} (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
    (UI : Matrix (Qubits n) (Qubits n) ℂ) :
    (k : Fin 2) → Matrix (Qubits (![m + n, n] k)) (Qubits (![m + n, n] k)) ℂ
  | ⟨0, _⟩ => UH
  | ⟨1, _⟩ => UI

example {m n : ℕ} (UH : Matrix (Qubits (m + n)) (Qubits (m + n)) ℂ)
    (UI : Matrix (Qubits n) (Qubits n) ℂ) : oraclePair UH UI 0 = UH ∧ oraclePair UH UI 1 = UI :=
  ⟨rfl, rfl⟩

/-- The (unnormalized) system state left on the first `n` wires of an `(n + w)`-qubit state `φ`
when the last `w` (ancilla) wires are measured with outcome `a`: `y ↦ φ(y, a)`. Its squared norm
is the probability of the ancilla outcome `a`. -/
noncomputable def ancillaBranch {n w : ℕ} (φ : EuclideanSpace ℂ (Qubits (n + w))) (a : Qubits w) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun y => φ (Fin.append y a)


end QAlgorithms.Papers.LinTong20Ground



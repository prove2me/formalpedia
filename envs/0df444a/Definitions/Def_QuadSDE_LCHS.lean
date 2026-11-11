-- Prove2me | Definitions.Def_QuadSDE_LCHS
-- name    : QuadSDE_LCHS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:31.70855+00:00
-- url     : https://prove2.me/theorems/7ad7e0f8-1585-4747-a684-d8118d433e97
-- title:
--   Block of an operator, time-controlled oracles (81) and the time-ordered propagator
-- statement:
--   For an operator $U$ on $b$ ancilla qubits followed by $n$ data qubits, its **block** is $(\langle0^b|\otimes I)U(|0^b\rangle\otimes I)$. Given a family $t\mapsto U(t)$ of operators and a time register of $m$ qubits, the **time-controlled operator** is
--   $$\sum_{\tau=0}^{2^m-1}|\tau\rangle\langle\tau|\otimes U(t_\tau),\qquad t_\tau=\tau T/2^m \qquad(81),$$
--   and the LCHS circuit of Lemma 8 calls two of them, for $U_L$ and $U_H$. For a matrix family $G(t)$, $V$ is the **propagator** $\mathcal T\exp(\int_0^tG)$ on $[0,T]$ if
--   $$V(0)=I,\qquad V'(t)=G(t)V(t)\quad(t\in[0,T]);$$
--   $\mathcal T\exp(\int_0^TG)$ is $V(T)$.
--
--   **Formalization Note** Registers are qubit strings with wire $0$ most significant; ancillas come first in the block, the time register first in the time-controlled operator. Derivatives of matrix families are entrywise, one-sided at the endpoints.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), §4.6, Lemma 8, Eq. (63), p. 27; Eq. (81), p. 30

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

open QAlgorithms

noncomputable section

namespace QuadSDE

/-- Bravyi–Byrne–Zayats–Zhuk–Zlokapa, arXiv:2606.08349 (sha256 29bd9b01…), §4.6, p. 27 (Eq. (63)):
the top-left block `(⟨0^b| ⊗ I) U (|0^b⟩ ⊗ I)` of an operator on `b` ancilla qubits followed by
`n` data qubits (ancillas first). -/
def blockOf {b n : ℕ} (U : Matrix (Qubits (b + n)) (Qubits (b + n)) ℂ) :
    Matrix (Qubits n) (Qubits n) ℂ :=
  Matrix.of fun i j => U (Fin.append (fun _ : Fin b => false) i) (Fin.append (fun _ : Fin b => false) j)

/-- §4.6, Eq. (81), p. 30: a coherent time-controlled operator `Σ_τ |τ⟩⟨τ|_T ⊗ U(t_τ)` on a time
register of `m` qubits followed by the `b + n` qubits of `U`, with the grid `t_τ = τ T / 2^m`,
`τ = 0, …, 2^m − 1` (the value `τ` of the time register, most significant bit first). This is the
form in which Lemma 8's "access to controlled block encodings of `L(t)` and `H(t)`" is used. -/
def timeSelect (m b n : ℕ) (T : ℝ) (U : ℝ → Matrix (Qubits (b + n)) (Qubits (b + n)) ℂ) :
    Matrix (Qubits (m + (b + n))) (Qubits (m + (b + n))) ℂ :=
  Matrix.of fun z z' =>
    if (fun i : Fin m => z (Fin.castAdd (b + n) i)) = (fun i : Fin m => z' (Fin.castAdd (b + n) i))
    then U (bitsToNat (fun i : Fin m => z (Fin.castAdd (b + n) i)) * T / 2 ^ m)
        (fun j => z (Fin.natAdd m j)) (fun j => z' (Fin.natAdd m j))
    else 0

/-- §4.6, Lemma 8, Eq. (63), p. 27: `V` is the propagator `𝒯exp(∫₀ᵗ G(s) ds)` of the linear ODE
`V′(t) = G(t) V(t)`, `V(0) = I`, on `[0, T]` (one-sided derivatives at the endpoints, entrywise);
`𝒯exp(∫₀ᵀ G)` is `V(T)`.

**Formalization Note.** Every solution of the matrix ODE is covered (for continuous `G` it is
unique). -/
def IsPropagator {n : ℕ} (G : ℝ → Matrix (Qubits n) (Qubits n) ℂ) (T : ℝ)
    (V : ℝ → Matrix (Qubits n) (Qubits n) ℂ) : Prop :=
  V 0 = 1 ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt V (G t * V t) (Set.Icc 0 T) t

/-- Lemma 8, p. 27: the arities of the two oracles of the LCHS circuit, the time-controlled
encodings of `L(t)` (oracle `0`: `m_T` time qubits, `b_L` ancillas, `n` data qubits) and of `H(t)`
(oracle `1`: `m_T` time qubits, `b_H` ancillas, `n` data qubits). -/
def lchsArity (mT bL bH n : ℕ) : Fin 2 → ℕ
  | 0 => mT + (bL + n)
  | 1 => mT + (bH + n)

/-- Lemma 8, p. 27, with Eq. (81), p. 30: the oracle pair handed to the LCHS circuit,
`O_L = Σ_τ |τ⟩⟨τ| ⊗ U_L(t_τ)` and `O_H = Σ_τ |τ⟩⟨τ| ⊗ U_H(t_τ)` on the grid `t_τ = τT/2^{m_T}`. -/
def lchsOracles (mT bL bH n : ℕ) (T : ℝ)
    (UL : ℝ → Matrix (Qubits (bL + n)) (Qubits (bL + n)) ℂ)
    (UH : ℝ → Matrix (Qubits (bH + n)) (Qubits (bH + n)) ℂ) :
    (k : Fin 2) → Matrix (Qubits (lchsArity mT bL bH n k)) (Qubits (lchsArity mT bL bH n k)) ℂ
  | 0 => timeSelect mT bL n T UL
  | 1 => timeSelect mT bH n T UH

end QuadSDE



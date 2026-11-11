-- Prove2me | Definitions.Def_QFairEx_winProb
-- name    : QFairEx_winProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:23:24.9202+00:00
-- url     : https://prove2.me/theorems/ca5966e3-f223-4afc-bb45-0ecea2e79af5
-- title:
--   Winning probability in the parallel BB84 basis guessing game (Algorithm 4.4)
-- statement:
--   In the **parallel BB84 basis guessing game** with parameter $n\ge 1$, the challenger samples $x,\theta\in\{0,1\}^n$ independently and uniformly, sends the $n$ qubits $|\phi_i\rangle=H^{\theta_i}X^{x_i}|0\rangle$, and the adversary answers an index $j$ and a guess $\theta^*_j$; it wins if $\theta^*_j=\theta_j$.
--
--   An adversary is a classical–quantum instrument $A$ from the $n$ qubits to the classical answer $(j,g)$, with branch probabilities $\Pr[A\text{ answers }(j,g)\mid\rho]$. Its winning probability is
--   $$\operatorname{win}(A)=4^{-n}\sum_{x,\theta\in\{0,1\}^n}\ \sum_{j=1}^n\Pr\bigl[A\text{ answers }(j,\theta_j)\ \big|\ |\phi_{x,\theta}\rangle\langle\phi_{x,\theta}|\bigr].$$
--
--   Theorem 4.5 bounds this by $1/2$; the impossibility proof builds an adversary that would exceed it.
--
--   **Formalization Note** Indices are 0-based (`Fin n`). An instrument with no quantum output is the same as a POVM; physicality of $A$ is the hypothesis `IsCPInstrument A` of the theorems, not part of this definition.
-- source:
--   Chung, Lee, Raizes, Thyagarajan, Quantum Fair Exchange, STOC 2027 submission (manuscript of 2026-11-02, sha256 0099b883bc58c8a8ab3f2031fadc6e6c71b4ef1289bb55028fbbebcd070a9b6e), Algorithm 4.4, p.21

import Mathlib
import Definitions.Def_QFairEx_SupportedOn
import Definitions.Def_QFairEx_bb84

namespace QFairEx

open Matrix

/-- **Winning probability in the parallel BB84 basis guessing game** (Algorithm 4.4).
Chung, Lee, Raizes, Thyagarajan, *Quantum Fair Exchange*, STOC 2027 submission (manuscript of
2026-11-02, sha256 0099b883…), Algorithm 4.4, p.21: "1. The challenger samples
x, θ ← {0,1}^n independently and uniformly. 2. For each i ∈ [n], the challenger prepares a
register Q_i in state |ϕ_i⟩ = H^{θ_i} X^{x_i} |0⟩. It sends Q_1, …, Q_n to the adversary. 3. The
adversary sends an index j ∈ [n] and a guess θ*_j ∈ {0, 1} to the challenger. The adversary wins
if θ*_j = θ_j and loses otherwise."

An adversary is a cq-operation `A` from (no classical input, the `n` qubits `Q_1 ⋯ Q_n`) to
(classical output `(j, θ*) ∈ Fin n × Bool`, no quantum output): `A () (j, g) ρ` is the `1 × 1`
matrix holding the probability of answering `(j, g)` on input `ρ`. It is a physical procedure
when `IsCPInstrument A`. Then
`winProb A = 4^{−n} ∑_{x, θ} ∑_j Pr[A answers (j, θ_j) on |ϕ_{x,θ}⟩⟨ϕ_{x,θ}|]`.

**Formalization Note.** Indices `j ∈ [n]` are `Fin n` (0-based). An instrument with trivial
quantum output is the same thing as a POVM indexed by `Fin n × Bool`. -/
noncomputable def winProb {n : ℕ}
    (A : Unit → Fin n × Bool → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ → Matrix Unit Unit ℂ) : ℝ :=
  (1 / 4 ^ n : ℝ) * ∑ x : Fin n → Bool, ∑ θ : Fin n → Bool, ∑ j : Fin n,
    (A () (j, θ j) (pureDensity (bb84Vec θ x)) () ()).re

end QFairEx



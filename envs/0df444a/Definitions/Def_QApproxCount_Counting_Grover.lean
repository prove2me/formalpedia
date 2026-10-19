-- Prove2me | Definitions.Def_QApproxCount_Counting_Grover
-- name    : QApproxCount_Counting_Grover
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:10:40.997107+00:00
-- url     : https://prove2.me/theorems/a147fef5-a3c8-4903-87f8-fcece4c5ca42
-- title:
--   Padded instance, phase oracle U, uniform superposition |ψ⟩, Grover operator G = (I − 2|ψ⟩⟨ψ|)U and the Born probability of the marked set (pp. 4–5)
-- statement:
--   This file fixes the quantum model of the algorithm box of Theorem 1.
--
--   1. **Padding.** For a list size $N$ put $N' := (10^6+1)N$. A marked set $S\subseteq[N]=\{0,\dots,N-1\}$ is viewed as the same set inside $[N']$; the $10^6N$ added items $N,\dots,N'-1$ are unmarked. This is the paper's "padding out the list with $10^6N$ unmarked items", which guarantees $K/N' \le (10^6+1)^{-1}$.
--   2. **Oracle.** For $T\subseteq[n]$, the membership oracle is the diagonal unitary $U$ on $\mathbb C^n$ with $U|x\rangle=(-1)^{[x\in T]}|x\rangle$.
--   3. **Uniform superposition.** $|\psi\rangle = n^{-1/2}\sum_{x\in[n]}|x\rangle$.
--   4. **Grover operator.** Exactly as printed,
--   $$G := (I-2|\psi\rangle\langle\psi|)\,U .$$
--   5. **Grover state and Born probability.** For $j\in\mathbb N$, the state after $j$ applications is $G^j|\psi\rangle$ (it uses $j$ oracle queries), and the probability of observing a marked item when it is measured in the computational basis is
--   $$p_T(j) := \sum_{x\in T} \big|\langle x|G^j|\psi\rangle\big|^2 .$$
--
--   The algorithm uses $j=(r-1)/2$ for an odd rotation count $r$. These objects let the algorithm see the marked set only through the oracle and measurement statistics.
--
--   **Formalization Note** States are vectors `Fin n → ℂ`, operators are `Matrix (Fin n) (Fin n) ℂ`, and $|\psi\rangle\langle\psi|$ is `vecMulVec ψ (star ψ)`. The padding embeds `Fin N` into `Fin N'` by `Fin.castLE` (the first $N$ indices).
-- source:
--   Aaronson & Rall, Quantum Approximate Counting, Simplified, arXiv:1908.10846v6, pp. 4–5, algorithm box of Theorem 1 and eq. (1)

import Mathlib

namespace QApproxCount.Counting

open Matrix

/-- The padded list size `N' = (10^6 + 1) N` of the algorithm box (p. 4): the list `[N]` is
padded with `10^6 N` unmarked items. -/
def paddedSize (N : ℕ) : ℕ := (10 ^ 6 + 1) * N

/-- `N ≤ N'`. -/
theorem le_paddedSize (N : ℕ) : N ≤ paddedSize N := by
  unfold paddedSize; omega

/-- The marked set `S ⊆ [N]` viewed inside the padded list `[N']` (items `0, …, N-1`;
the `10^6 N` new items `N, …, N'-1` are unmarked). -/
def padSet (N : ℕ) (S : Finset (Fin N)) : Finset (Fin (paddedSize N)) :=
  S.map (Fin.castLEEmb (le_paddedSize N))

/-- The membership (phase) oracle `U|x⟩ = (-1)^{[x ∈ T]} |x⟩` on `ℂ^n`. -/
noncomputable def phaseOracle {n : ℕ} (T : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun x => if x ∈ T then -1 else 1

/-- The uniform superposition `|ψ⟩ = n^{-1/2} Σ_x |x⟩` over all `n` items. -/
noncomputable def uniformState (n : ℕ) : Fin n → ℂ :=
  fun _ => (((Real.sqrt n)⁻¹ : ℝ) : ℂ)

/-- The Grover operator `G := (I - 2|ψ⟩⟨ψ|) U` exactly as printed on p. 4. -/
noncomputable def groverOp {n : ℕ} (T : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  (1 - (2 : ℂ) • vecMulVec (uniformState n) (star (uniformState n))) * phaseOracle T

/-- The state `G^j |ψ⟩` obtained with `j` applications of `G` (that is, `j` oracle queries). -/
noncomputable def groverState {n : ℕ} (T : Finset (Fin n)) (j : ℕ) : Fin n → ℂ :=
  (groverOp T ^ j) *ᵥ uniformState n

/-- Born-rule probability of observing a marked item when `G^j |ψ⟩` is measured in the
computational basis: `Σ_{x ∈ T} |⟨x| G^j |ψ⟩|²`. -/
noncomputable def markedProb {n : ℕ} (T : Finset (Fin n)) (j : ℕ) : ℝ :=
  ∑ x ∈ T, ‖groverState T j x‖ ^ 2

end QApproxCount.Counting



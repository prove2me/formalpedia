-- Prove2me | Definitions.Def_QubitTracking_Supplement_ndDist95
-- name    : QubitTracking_Supplement_ndDist95
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:13:06.63405+00:00
-- url     : https://prove2.me/theorems/37fb839c-862d-4e0c-8dee-ff10d488984f
-- title:
--   Trace distance and the expected destruction $\mathbb E[\mathrm{TD}(\rho_{\mathbf{AB}},\rho_{\mathbf{AB}'})]$ of the anchor-state protocols
-- statement:
--   The **trace distance** of two operators $\rho,\sigma$ on the same space is $\mathrm{TD}(\rho,\sigma)=\tfrac12\|\rho-\sigma\|_1$, with $\|\cdot\|_1$ the trace norm.
--
--   For a prover in the anchor-state protocols (Constructions 8.3, 9.2 and 9.5 share the setup and the oracles), each sample $\omega$ of the classical randomness gives two states on $\mathbf A\mathbf B$:
--
--   1. $\rho_{\mathbf{AB}}=|\Psi^{\mathsf{sk}}\rangle\langle\Psi^{\mathsf{sk}}|$, the anchor state produced by $\mathsf{Setup}$;
--   2. $\rho_{\mathbf{AB}'}$, the reduced state on the anchor $\mathbf A$ and the prover's input cells (read in their designated order) of the final global state after $\mathsf{Localize}$.
--
--   The **expected destruction** of the prover is the average over all samples of the per-sample trace distances,
--   $$\mathbb E_\omega\big[\mathrm{TD}(\rho_{\mathbf{AB}}(\omega),\rho_{\mathbf{AB}'}(\omega))\big].$$
--   A scheme is non-destructive when the honest prover's expected destruction is negligible (Definitions 8.1 and 9.1).
--
--   **Formalization Note** The prover's output register $\mathbf B'$ is its input cells after $\mathsf{Localize}$. The trace distance is taken sample by sample and averaged afterwards, which is the paper's $\mathbb E[\mathrm{TD}(\cdot,\cdot)]$ (the trace distance of the averaged states would be smaller).
-- source:
--   Bartusek, Huang, Orshansky, Yuen, How To Track Qubits Through Space and Time (Or: Sailing in a Quantum Boat), arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 8.1 (Non-destructive), p.57; Definition 9.1 (Non-destructive), p.62

import Definitions.Def_QubitTracking_sched95
import Definitions.Def_WildeQIT_traceDist

set_option autoImplicit false

open Matrix

namespace QubitTracking.Supplement

/-! Non-destructiveness (Definitions 8.1 and 9.1) for the anchor-state protocols.

Source: Bartusek, Huang, Orshansky, Yuen, *How To Track Qubits Through Space and Time (Or:
Sailing in a Quantum Boat)*, arXiv:2605.30732 (held version, sha256 bf98e5b5…), Definition 8.1,
p.57, Definition 9.1, p.62, Definition 9.7, p.69. -/

/-- **The trace distance** `TD(ρ, σ) = ½‖ρ − σ‖₁` of two operators on the same space, via the
trace norm `‖·‖₁` of `WildeQIT.traceDist`. -/
noncomputable def TD {β : Type} [Fintype β] [DecidableEq β] (ρ σ : Matrix β β ℂ) : ℝ :=
  (1 / 2 : ℝ) * WildeQIT.traceDist ρ σ

open Classical in
/-- **The reduced state on `𝐀 ⊗ (input cells)`** of a global pure state `ψ` on `A ⊗ (cells)`: the
partial trace over every cell that is not one of the prover's input cells `input j`, with the
input cells read in the order `j = 0, 1, …` (the register `𝐁′` of the prover's output).

**Formalization Note** For a valid prover the input cells are pairwise distinct, so
`h.choose` is the unique index `j` with `input j = c`. -/
noncomputable def inputState {σ : Sched} {lam inLen respLen : ℕ} {κ : Type} {inL outL : κ → ℕ}
    (P : Prover σ lam inLen respLen κ inL outL) {A : Type} [Fintype A] [DecidableEq A]
    (ψ : Bits (A ⊕ P.Cell) → ℂ) :
    Matrix (Bits A × Bits (Fin inLen)) (Bits A × Bits (Fin inLen)) ℂ :=
  fun p q =>
    ∑ e : Bits {c // ¬ ∃ j, P.input j = c},
      ψ (Sum.elim p.1 (fun c => if h : ∃ j, P.input j = c then p.2 h.choose else e ⟨c, h⟩)) *
        star (ψ (Sum.elim q.1
          (fun c => if h : ∃ j, P.input j = c then q.2 h.choose else e ⟨c, h⟩)))

/-- **The expected destruction `𝔼[TD(ρ_{𝐀𝐁}, ρ_{𝐀𝐁′})]`** of a prover in the anchor-state
protocols (Constructions 8.3, 9.2 and 9.5 share the setup and the oracles; the schedule `σ` is
part of the prover's type): for each sample `ω`, `ρ_{𝐀𝐁}` is the anchor state `|Ψ^{sk}⟩⟨Ψ^{sk}|`
on `𝐀𝐁` after `Setup`, `ρ_{𝐀𝐁′}` the reduced state on `𝐀 ⊗ (input cells)` of the final state
after `Localize`; the per-sample trace distances are averaged over all samples. -/
noncomputable def ndDist95 {n m lam : ℕ} {σ : Sched} (P : Prover95 n m lam σ) : ℝ :=
  avg fun ω : Omega95 n m lam σ.N =>
    TD (proj (anchorVec n n n ω.1 ω.2.1 ω.2.2.1))
      (inputState P (P.finalState (Fin n) (fun _ _ => orc95 ω) (initState95 P ω)))

end QubitTracking.Supplement



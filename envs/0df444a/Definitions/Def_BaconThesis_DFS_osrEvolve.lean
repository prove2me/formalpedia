-- Prove2me | Definitions.Def_BaconThesis_DFS_osrEvolve
-- name    : BaconThesis_DFS_osrEvolve
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:58:40.781584+00:00
-- url     : https://prove2.me/theorems/ef57c7a0-6791-46d2-8cd7-fb4a61cfd47f
-- title:
--   The reduced evolution $\rho_S(t)=\mathrm{Tr}_E[U(t)\,\rho_S(0)\otimes\rho_E(0)\,U^\dagger(t)]$
-- statement:
--   Let a system $S$ and an environment $E$ have finite-dimensional Hilbert spaces $\mathcal H_S=\mathbb C^{s}$ and $\mathcal H_E=\mathbb C^{e}$, and let $H$ be an operator on $\mathcal H_S\otimes\mathcal H_E$ with evolution operator $U(t)=\exp[-iHt]$. For an environment state $\rho_E$, a time $t$ and a system operator $\rho$, the **reduced evolution** is
--   $$
--   \rho\;\longmapsto\;\mathrm{Tr}_E\!\left[\,U(t)\,(\rho\otimes\rho_E)\,U^\dagger(t)\,\right],
--   $$
--   the partial trace over the environment of the jointly evolved product state. When $\rho=\rho_S(0)$ is the initial system state this is $\rho_S(t)$, eq. (2.8) of the thesis; by eqs. (2.9)–(2.11) it equals the operator-sum form $\sum_i A_i(t)\rho A_i^\dagger(t)$ used in (5.2), (5.11) and (5.12).
--
--   This is the evolution under which decoherence-free subspaces are defined.
--
--   **Formalization Note** The joint space is indexed by pairs (system index, environment index), system first, and $\rho\otimes\rho_E$ is the Kronecker product. The partial trace is the published `WildeQIT.partialTraceRight` over the second factor. $\rho$ and $\rho_E$ are arbitrary matrices in the definition; statements restrict them to states where the thesis does.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, §2.2.1, eq. (2.8), p.16 (PDF p.33)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_BaconThesis_DFS_evolOp

open scoped Matrix Kronecker

namespace BaconThesis.DFS

/-- **The reduced (OSR) evolution of the system.**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
§2.2.1, eq. (2.8), p.16 (PDF p.33):
`ρ_S(t) = Tr_E[U(t) ρ_S(0) ⊗ ρ_E(0) U†(t)]`.

For a joint Hamiltonian `H` on system ⊗ environment, an environment state `ρE`, a time `t` and a
system operator `ρ`, `osrEvolve H ρE t ρ` is the partial trace over the environment of
`U(t) (ρ ⊗ ρE) U(t)†` with `U(t) = evolOp H t`. By eqs. (2.9)–(2.11) this equals the
operator-sum form `∑ᵢ Aᵢ(t) ρ Aᵢ†(t)` of (2.10), (5.2), (5.11) and (5.12) (milestone
`eq_2_9_2_11`).

**Formalization Note.** The joint space is indexed by `s × e`, system first and environment
second, and `ρ ⊗ ρE` is `Matrix.kronecker`. The partial trace is the published
`WildeQIT.partialTraceRight` over the second (environment) factor. `ρ` and `ρE` are arbitrary
matrices here; the statements restrict them to states where the book does. -/
noncomputable def osrEvolve {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    (H : Matrix (s × e) (s × e) ℂ) (ρE : Matrix e e ℂ) (t : ℝ) (ρ : Matrix s s ℂ) :
    Matrix s s ℂ :=
  WildeQIT.partialTraceRight (evolOp H t * (ρ ⊗ₖ ρE) * (evolOp H t)ᴴ)

end BaconThesis.DFS



-- Prove2me | Definitions.Def_BaconThesis_DFS_IsDFS
-- name    : BaconThesis_DFS_IsDFS
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:59:28.855501+00:00
-- url     : https://prove2.me/theorems/88eee06f-daec-464f-a8b7-42d8cc561977
-- title:
--   Decoherence-free subspace (Definition 5.3.1)
-- statement:
--   Let a system with Hilbert space $\mathcal H_S$ be coupled to an environment with Hilbert space $\mathcal H_E$ (both finite dimensional) by a joint Hamiltonian $H$, and write $U(t)=\exp[-iHt]$. A subspace $\mathcal S\subseteq\mathcal H_S$ is a **decoherence-free subspace (DFS)** with respect to $H$ if every pure state from $\mathcal S$ is invariant under the corresponding OSR evolution for every environment initial condition:
--   $$
--   \mathrm{Tr}_E\!\left[\,U(t)\,\big(|j\rangle\langle j|\otimes\rho_E\big)\,U^\dagger(t)\,\right]=|j\rangle\langle j|
--   $$
--   for every unit vector $|j\rangle\in\mathcal S$, every density operator $\rho_E$ of the environment, and every time $t\ge 0$. The left side is the OSR evolution $\sum_i A_i(t)|j\rangle\langle j|A_i^\dagger(t)$ of eq. (5.12).
--
--   A DFS is a perfect quantum memory: states encoded in it are untouched by the coupling to the environment.
--
--   **Formalization Note** A pure state is a vector $j\in\mathcal S$ with $\langle j|j\rangle=1$, and $|j\rangle\langle j|$ is its rank-one projector. "Any possible environment initial condition" ranges over every density operator (positive semidefinite, trace one; the published `WildeQIT.IsDensityOperator`), mixed or pure. The evolution runs forward from the initial time $0$, so $t\ge 0$.
-- source:
--   Bacon, Decoherence, Control, and Symmetry in Quantum Computers, arXiv:quant-ph/0305025v1, Definition 5.3.1, eq. (5.12), p.72 (PDF p.89)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_BaconThesis_DFS_osrEvolve

open scoped Matrix

namespace BaconThesis.DFS

/-- **Decoherence-free subspace (Definition 5.3.1).**
Bacon, *Decoherence, Control, and Symmetry in Quantum Computers*, arXiv:quant-ph/0305025v1,
Definition 5.3.1, eq. (5.12), p.72 (PDF p.89): a subspace `S` of the system's Hilbert space is a
decoherence-free subspace with respect to a system-environment coupling if every pure state from
`S` is invariant under the corresponding OSR evolution for any possible environment initial
condition: `∑ᵢ Aᵢ(t)|j⟩⟨j|Aᵢ†(t) = |j⟩⟨j|` for all `|j⟩ ∈ S` and all `ρ_E(0)`.

`IsDFS H W` holds when for every unit vector `j ∈ W`, every density operator `ρE` on the
environment and every time `t ≥ 0`, the reduced evolution `Tr_E[U(t)(|j⟩⟨j| ⊗ ρE)U(t)†]` of the
pure state `|j⟩⟨j|` is `|j⟩⟨j|` again.

**Formalization Note.** The OSR sum `∑ᵢ Aᵢ(t) ρ Aᵢ†(t)` is written as the reduced evolution
`osrEvolve` (eq. (2.8)), which equals it by eqs. (2.9)–(2.11). A pure state from `W` is a vector
`j ∈ W` with `⟨j|j⟩ = 1` (`star j ⬝ᵥ j = 1`), and `|j⟩⟨j|` is `Matrix.vecMulVec j (star j)`.
"Any possible environment initial condition" ranges over every density operator on the
environment (`WildeQIT.IsDensityOperator`: positive semidefinite, trace one), mixed or pure. The
evolution runs forward from the initial time `0`, so `t` ranges over `0 ≤ t`. -/
def IsDFS {s e : Type} [Fintype s] [DecidableEq s] [Fintype e] [DecidableEq e]
    (H : Matrix (s × e) (s × e) ℂ) (W : Submodule ℂ (s → ℂ)) : Prop :=
  ∀ j ∈ W, star j ⬝ᵥ j = 1 →
    ∀ ρE : Matrix e e ℂ, WildeQIT.IsDensityOperator ρE →
      ∀ t : ℝ, 0 ≤ t →
        osrEvolve H ρE t (Matrix.vecMulVec j (star j)) = Matrix.vecMulVec j (star j)

end BaconThesis.DFS



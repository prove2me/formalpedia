-- Prove2me | Definitions.Def_ShorEBAdditivity_IsEnsemble
-- name    : ShorEBAdditivity_IsEnsemble
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:17:50.948881+00:00
-- url     : https://prove2.me/theorems/9dec51c1-d209-4a0e-bad0-993667db0d7f
-- title:
--   Finite ensemble $\{p_i,\rho_i\}$ of quantum states
-- statement:
--   Let $\mathcal H_A$ be a finite-dimensional space and $n \in \mathbb N$. A family $\{p_i, \rho_i\}_{i=1}^n$ is an **ensemble** of states on $\mathcal H_A$ if
--
--   1. $p_i \ge 0$ for every $i$ and $\sum_i p_i = 1$ (a probability distribution), and
--   2. every $\rho_i$ is a density matrix: positive semidefinite with $\operatorname{Tr}\rho_i = 1$.
--
--   These are the objects over which the Holevo capacity $\chi^*$ is maximized ("over probability distributions $p_i$ and density matrices $\rho_i$").
--
--   **Formalization Note** The ensemble is indexed by `Fin n` for an arbitrary size $n$. The states may be mixed and zero weights are allowed.
-- source:
--   Shor, Additivity of the Classical Capacity of Entanglement-Breaking Quantum Channels, arXiv:quant-ph/0201149v3, eq. (1), p.1 ("the maximization is over probability distributions pi on density matrices ρi") and eq. (15), p.3 ("over probability distributions pi and density matrices ρi")

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information

open QAlgorithms

namespace ShorEBAdditivity

/-- Shor, arXiv:quant-ph/0201149v3, eq. (1), p.1 ("the maximization is over probability
distributions pi on density matrices ρi over the input space of the channel") and eq. (15), p.3
("over probability distributions pi and density matrices ρi"): a finite ensemble
`{p_i, ρ_i}_{i < n}` of states on the space indexed by `A`: the weights `p_i` form a probability
distribution and each `ρ_i` is a density matrix (positive semidefinite, trace one).

**Formalization Note.** The ensemble is indexed by `Fin n`; its size `n` is arbitrary. The
states `ρ_i` may be mixed. Zero weights are allowed. -/
def IsEnsemble {A : Type*} [Fintype A] {n : ℕ} (p : Fin n → ℝ) (ρ : Fin n → Matrix A A ℂ) :
    Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧ ∀ i, IsDensityMatrix (ρ i)

end ShorEBAdditivity



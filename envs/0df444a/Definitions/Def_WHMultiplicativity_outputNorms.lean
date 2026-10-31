-- Prove2me | Definitions.Def_WHMultiplicativity_outputNorms
-- name    : WHMultiplicativity_outputNorms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T15:23:45.895977+00:00
-- url     : https://prove2.me/theorems/ed345966-6e47-4e58-8c3c-bacfb716c469
-- title:
--   Output norms $\{\|\Phi(\rho)\|_p : \rho \text{ a density matrix}\}$
-- statement:
--   Let $\Phi$ be a map from the $n\times n$ to the $m\times m$ complex matrices and let $p \in [1,\infty]$. The set of **output norms** of $\Phi$ is
--
--   $$
--   \big\{\, \|\Phi(\rho)\|_p \;:\; \rho \ge 0,\ \operatorname{tr}\rho = 1 \,\big\} \subseteq \mathbb R,
--   $$
--
--   where $\rho$ ranges over **all** density matrices of the input space. When the input space is a tensor product $\mathbb C^d\otimes\mathbb C^d$, entangled density matrices are included.
--
--   The maximal output norm $\nu_p(\Phi)$ of eq. (1) is the supremum of this set.
--
--   **Formalization Note** $\Phi$ is a plain function on matrices (`QAlgorithms.Superop`); density matrices are `WHAdditivity.Renyi.IsDensity` (positive semidefinite, trace one); the norm is `WHMultiplicativity.schattenNorm`.
-- source:
--   Werner and Holevo, Counterexample to an additivity conjecture for output purity of quantum channels, arXiv:quant-ph/0203003v1, eq. (1), p.1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model
import Definitions.Def_WHMultiplicativity_schattenNorm

open scoped ENNReal

namespace WHMultiplicativity

/-- Werner and Holevo, arXiv:quant-ph/0203003v1, eq. (1), p.1: the set of output norms
`{‖Φ(ρ)‖_p : ρ an input density operator}` over which `ν_p(Φ)` is the supremum.

**Formalization Note.** The input ranges over **every** density matrix (positive semidefinite,
trace one) on the input index type `ι`; when `ι` is a product such as `Fin 2 → Fin 3` this
includes the entangled density matrices of `ℂ³ ⊗ ℂ³`. `Φ` is an arbitrary superoperator
(`QAlgorithms.Superop`); statements assume it is a channel where the paper does. -/
def outputNorms {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] (p : ℝ≥0∞)
    (Φ : QAlgorithms.Superop ι κ) : Set ℝ :=
  {s | ∃ ρ : Matrix ι ι ℂ, WHAdditivity.Renyi.IsDensity ρ ∧ s = schattenNorm p (Φ ρ)}

end WHMultiplicativity



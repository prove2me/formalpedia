-- Prove2me | Definitions.Def_HolevoCQ_IsSubPOVM
-- name    : HolevoCQ_IsSubPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:40.948077+00:00
-- url     : https://prove2.me/theorems/b0a9e43c-25b0-49c5-8aa5-02867b18c32d
-- title:
--   Decision operators of a code: $X_k\ge0$, $\sum_k X_k\le I$
-- statement:
--   A family $\{X_k\}_{k=1}^N$ of operators on a finite-dimensional Hilbert space is a family of decision operators of a code if every $X_k$ is positive and
--
--   $$
--   \sum_{k=1}^N X_k\le I .
--   $$
--
--   Then $X_0=I-\sum_kX_k$ completes it to a resolution of identity; outcome $0$ is the evasion of any decision.
--
--   **Formalization Note** The operator order $A\le B$ is written as positive semidefiniteness of $B-A$.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, p.2 (definition of a code)

import Mathlib

open scoped ComplexOrder

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, p.2: the decision operators `{X_k}_{k=1}^N` of a code are positive
operators in `H^{⊗n}` with `Σ_{j=1}^N X_j ≤ I` (so that `X₀ = I − Σ_j X_j` completes them to a
resolution of identity).

**Formalization Note.** Operator order `A ≤ B` is written `(B - A).PosSemidef`. -/
def IsSubPOVM {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (X : Fin N → Matrix ι ι ℂ) : Prop :=
  (∀ k, (X k).PosSemidef) ∧ (1 - ∑ k, X k).PosSemidef

end HolevoCQ



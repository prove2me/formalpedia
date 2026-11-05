-- Prove2me | Definitions.Def_DHRUniq_IsSeparable
-- name    : DHRUniq_IsSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:50.004372+00:00
-- url     : https://prove2.me/theorems/e6267200-85a9-4c1b-9bee-58c479be663e
-- title:
--   Separable state
-- statement:
--   A density operator $\varrho$ on $\mathcal H^A\otimes\mathcal H^B$ is **separable** (or disentangled) if there are a sequence $(r_i)$ of positive real numbers and sequences $(\varrho_i^A)$, $(\varrho_i^B)$ of density operators on $\mathcal H^A$ and $\mathcal H^B$ such that
--
--   $$
--   \varrho=\sum_i r_i\,\varrho_i^A\otimes\varrho_i^B,
--   $$
--
--   the sum converging in trace class norm.
--
--   **Formalization Note** A sequence is a family over a countable index set, finite or infinite. In finite dimension every norm gives the same topology, and a convergent series of positive operators converges unconditionally, so `HasSum` expresses the convergence.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Definition 1, p. 3

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator

open Kronecker
open WildeQIT (IsDensityOperator)

namespace DHRUniq

/-- **Separable state** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, Definition 1, p. 3): a density operator `ϱ` on `H^A ⊗ H^B` is
separable if there exist a sequence `(r_i)` of positive real numbers and sequences `(ϱ_i^A)`,
`(ϱ_i^B)` of density operators on `H^A` and `H^B` with `ϱ = ∑_i r_i ϱ_i^A ⊗ ϱ_i^B`, the sum
converging in trace class norm.

**Formalization Note** A sequence is a family over a countable index type (finite or infinite).
All norms on a finite-dimensional space define the same topology, and a series of positive
operators that converges does so unconditionally, so `HasSum` for the entrywise topology of
`Matrix` is convergence in trace class norm. The published `WildeQIT.IsSeparable` allows only
finite sums and is not this definition. -/
def IsSeparable {a b : Type} [Fintype a] [Fintype b] (σ : Matrix (a × b) (a × b) ℂ) : Prop :=
  IsDensityOperator σ ∧
    ∃ (ι : Type) (_ : Countable ι) (r : ι → ℝ) (ρA : ι → Matrix a a ℂ) (ρB : ι → Matrix b b ℂ),
      (∀ i, 0 < r i) ∧ (∀ i, IsDensityOperator (ρA i)) ∧ (∀ i, IsDensityOperator (ρB i)) ∧
        HasSum (fun i => (r i : ℂ) • (ρA i ⊗ₖ ρB i)) σ

end DHRUniq



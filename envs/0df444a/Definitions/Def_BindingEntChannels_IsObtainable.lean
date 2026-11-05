-- Prove2me | Definitions.Def_BindingEntChannels_IsObtainable
-- name    : BindingEntChannels_IsObtainable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:38.548656+00:00
-- url     : https://prove2.me/theorems/41e0ba86-2f9d-45b9-8663-941b57d8f023
-- title:
--   A bipartite state obtainable from the channel by LQCC protocols
-- statement:
--   A bipartite state $\rho$ on $\mathbb C^c\otimes\mathbb C^d$ is **obtainable** from the channel $\Lambda$ if some protocol using $\Lambda$ some number of times, started with both memories one-dimensional (no shared state, no prior entanglement), succeeds with positive probability and its normalized output is $\rho$:
--
--   $$
--   \rho=\frac{\omega}{\operatorname{Tr}\omega},\qquad \omega=\text{the protocol's unnormalized output},\quad \operatorname{Tr}\omega>0 .
--   $$
--
--   This is "it is possible to obtain bipartite … state by means of (possibly multiply) use of the channel and LQCC operations", clause (ii) of the Definition.
--
--   **Formalization Note** The initial state is the $1\times1$ matrix $1$; the positive trace excludes the zero output, whose normalization would be a junk value.
-- source:
--   Horodecki, Horodecki, Horodecki, Binding entanglement channels, arXiv:quant-ph/9904092v1, Definition, clause (ii), pp. 1–2

import Mathlib
import Definitions.Def_BindingEntChannels_AdaptiveState

open scoped Matrix

namespace BindingEntChannels

/-- Horodecki, Horodecki, Horodecki, *Binding entanglement channels*, arXiv:quant-ph/9904092v1,
Definition, clause (ii), pp. 1–2: the bipartite state `ρ` on `Fin c × Fin d` "is possible to
obtain … by means of (possibly multiply) use of the channel and LQCC operations": some protocol
(`AdaptiveState`) using `Λ` some number `n` of times, started from no shared state, succeeds with
positive probability, and its normalized output is `ρ`.

**Formalization Note.** The start is the `1 × 1` matrix `1` on `Fin 1 × Fin 1`: both memories
are one-dimensional, so there is no prior entanglement; local states are prepared by Kraus
instruments out of the one-dimensional memory. The unnormalized output `run 1` has trace equal to
the success probability; it must be positive (otherwise `0⁻¹ = 0` would make the zero matrix
"obtainable"), and `ρ` is `run 1` divided by its trace. -/
def IsObtainable {I O : Type*} [Fintype I] [Fintype O] (Λ : QAlgorithms.Superop I O) {c d : ℕ}
    (ρ : Matrix (Fin c × Fin d) (Fin c × Fin d) ℂ) : Prop :=
  ∃ (n : ℕ) (run : QAlgorithms.Superop (Fin 1 × Fin 1) (Fin c × Fin d)),
    AdaptiveState Λ c d (n := n) run ∧ 0 < (run 1).trace.re ∧ ρ = ((run 1).trace)⁻¹ • run 1

end BindingEntChannels



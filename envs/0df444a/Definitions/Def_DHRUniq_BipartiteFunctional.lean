-- Prove2me | Definitions.Def_DHRUniq_BipartiteFunctional
-- name    : DHRUniq_BipartiteFunctional
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:46.137827+00:00
-- url     : https://prove2.me/theorems/0ba9c8e2-915a-4e02-b8a8-5f932c81a7b2
-- title:
--   A real functional on bipartite states of all finite dimensions
-- statement:
--   A **functional on bipartite states** assigns a real number $E(\sigma)$ to operators $\sigma$ on $\mathcal H^A\otimes\mathcal H^B$, for every pair of finite-dimensional Hilbert spaces $\mathcal H^A,\mathcal H^B$.
--
--   This is the type of the objects studied by the paper: entanglement measures on mixed states and, when only pure states matter, functionals on pure states.
--
--   **Formalization Note** $\mathcal H^A=\mathbb C^a$ and $\mathcal H^B=\mathbb C^b$ for finite types $a,b$, and $E$ is a total function on matrices. All conditions read $E$ only at density operators, and the pure-state conditions only at $|\psi\rangle\langle\psi|$ with $\psi$ a unit vector, so its other values play no role. Nonnegativity is not built in.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, §5.1, p. 8 and §5.2, p. 9

import Mathlib

namespace DHRUniq

/-- **A real functional on the states of all bipartite systems** (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2, §5.1, p. 8: "a …
real-valued functional `E` defined on `Σ(H^A ⊗ H^B)` for all finite-dimensional Hilbert spaces
`H^A` and `H^B`"; §5.2, p. 9: "it might not even be required that the measure is defined except
on pure states").

**Formalization Note** `H^A = ℂ^a` and `H^B = ℂ^b` for finite types `a b : Type`, Alice's factor
first. The functional is a total function on all matrices over `a × b`; every condition of the
mission only reads it at density operators, and the pure-state conditions (P0)–(P5′′) only at
`|ψ⟩⟨ψ|` for a unit `ψ`, so a functional on pure states is any such function, its other values
being irrelevant. No nonnegativity is built in: Theorem 23 is about an arbitrary functional. -/
abbrev BipartiteFunctional : Type 1 :=
  ∀ ⦃a b : Type⦄ [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b],
    Matrix (a × b) (a × b) ℂ → ℝ

end DHRUniq



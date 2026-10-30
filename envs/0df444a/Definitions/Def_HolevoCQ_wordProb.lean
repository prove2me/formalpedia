-- Prove2me | Definitions.Def_HolevoCQ_wordProb
-- name    : HolevoCQ_wordProb
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:30.349981+00:00
-- url     : https://prove2.me/theorems/1dc81aaf-0139-4ab5-b227-65b760984765
-- title:
--   Product law on words $\pi_{i_1}\cdots\pi_{i_n}$ (eq. 9)
-- statement:
--   For a distribution $\pi=\{\pi_i\}$ on the finite alphabet $A$, the product law on the words $A^n$ is
--
--   $$
--   \mathsf P\{u=(i_1,\dots,i_n)\}=\pi_{i_1}\cdots\pi_{i_n}.
--   $$
--
--   Holevo draws the code words independently from this law in the random-coding argument.
--
--   **Formalization Note** Words are `u : Fin n → A`; the function is defined for any real vector $\pi$, and the statements that use it assume $\pi$ is a probability vector.
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (9), p.4

import Mathlib

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (9), p.4: the product law on words,
`P{u = (i₁, …, iₙ)} = π_{i₁} ⋯ π_{iₙ}`.

**Formalization Note.** Words are `u : Fin n → A`; `π : A → ℝ` is a probability vector in the
statements that use this definition. -/
def wordProb {A : Type} (π : A → ℝ) (n : ℕ) (u : Fin n → A) : ℝ :=
  ∏ l, π (u l)

end HolevoCQ



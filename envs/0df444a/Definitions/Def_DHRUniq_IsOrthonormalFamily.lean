-- Prove2me | Definitions.Def_DHRUniq_IsOrthonormalFamily
-- name    : DHRUniq_IsOrthonormalFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:32:40.622305+00:00
-- url     : https://prove2.me/theorems/dd9dca46-5f4e-42ae-8e34-deed984b496d
-- title:
--   Orthonormal family of vectors of $\mathbb C^a$
-- statement:
--   A family $(u_i)_{i\in\iota}$ of vectors of $\mathbb C^a$ is **orthonormal** if
--
--   $$
--   \langle u_i,u_j\rangle=\sum_{x\in a}\overline{u_i(x)}\,u_j(x)=\delta_{ij}\qquad\text{for all } i,j.
--   $$
--
--   These families are the Schmidt vectors of the decompositions used throughout the paper.
-- source:
--   Donald, Horodecki, Rudolph, The uniqueness theorem for entanglement measures, arXiv:quant-ph/0105017v2, Lemma 2, p. 3 and Theorem 7, p. 6

import Mathlib

namespace DHRUniq

/-- **Orthonormal family** of vectors of `ℂ^a`, indexed by `ι`: `⟨u_i, u_j⟩ = δ_{ij}` (Donald, Horodecki, Rudolph, *The uniqueness theorem for entanglement measures*, arXiv:quant-ph/0105017v2,
Lemma 2, p. 3 and Theorem 7, p. 6, where such families are the Schmidt vectors).

**Formalization Note** The inner product is conjugate-linear in the first slot. -/
def IsOrthonormalFamily {ι a : Type} [DecidableEq ι] [Fintype a] (u : ι → a → ℂ) : Prop :=
  ∀ i j, ∑ x, star (u i x) * u j x = if i = j then 1 else 0

end DHRUniq



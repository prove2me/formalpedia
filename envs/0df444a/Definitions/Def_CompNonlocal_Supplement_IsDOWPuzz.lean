-- Prove2me | Definitions.Def_CompNonlocal_Supplement_IsDOWPuzz
-- name    : CompNonlocal_Supplement_IsDOWPuzz
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:52.792216+00:00
-- url     : https://prove2.me/theorems/5a273f62-94cd-4f0a-953f-a31f8551c65c
-- title:
--   Distributional one-way puzzles (Definition 7)
-- statement:
--   A **distributional one-way puzzle** is a uniform quantum polynomial-time sampler $\mathrm{Samp}(1^\kappa)\to(\mathrm{puzz},\mathrm{ans})$ of two classical strings such that there is a polynomial $p$ with the following property: for every polynomial-size quantum adversary $A$ with classical advice, for all sufficiently large $\kappa$,
--   $$\mathrm{SD}\Big(\big(\mathrm{puzz},A(1^\kappa,\mathrm{puzz})\big),\ (\mathrm{puzz},\mathrm{ans})\Big)\ \ge\ \frac1{p(\kappa)}.$$
--
--   No efficient algorithm can sample the answer conditioned on the puzzle, even approximately. This is the conclusion of Theorem 10.
--
--   **Formalization Note** The puzzle is the first $l(\kappa)$ bits of the sampler's output. $1/p(\kappa)$ is written $1/(p(\kappa)+1)$ with $p$ a polynomial with natural coefficients. The polynomial is chosen before the adversary.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7b7dd5f4c52119a37e0ee1d00eaf20185262775b8ab7d3067a9f2fcae), Definition 7, p.23

import Mathlib
import Definitions.Def_CompNonlocal_Supplement_puzzSD
import Definitions.Def_CompNonlocal_Uniform
import Definitions.Def_CompNonlocal_PolySize

set_option autoImplicit false

namespace CompNonlocal.Supplement

/-- Distributional one-way puzzles. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 7, p.23: "A distributional one-way puzzle
(dOWPuzz) is an algorithm Samp with the following syntax. Samp(1^κ) → (puzz, ans): It is a QPT
algorithm that takes the security parameter κ as input and outputs two classcal bit strings puzz
and ans. We require the following security: there exists a polynomial p such that for any
polynomial-size quantum adversary A with classical advice,
SD((puzz, A(1^κ, puzz)), (puzz, ans)) ≥ 1/p(κ) (9) for all sufficiently large κ ∈ N."

`IsDOWPuzz Samp l`: the sampler `Samp` is uniform QPT, and its output split as
`(puzz, ans) = (o.take (l κ), o.drop (l κ))` satisfies Eq. (9) (`puzzSD`).

**Formalization Note** "1/p(κ)" is `1 / (p(κ) + 1)` with `p : Polynomial ℕ` (the same class of
bounds, and never a division by zero). The polynomial is chosen before the adversary; the onset of
"sufficiently large" may depend on the adversary. -/
def IsDOWPuzz (Samp : Family) (l : ℕ → ℕ) : Prop :=
  Uniform Samp ∧ ∃ p : Polynomial ℕ, ∀ A : Family, PolySize A →
    ∀ᶠ κ in Filter.atTop, 1 / ((p.eval κ : ℕ) + 1 : ℝ) ≤ puzzSD Samp l κ (A κ)

end CompNonlocal.Supplement



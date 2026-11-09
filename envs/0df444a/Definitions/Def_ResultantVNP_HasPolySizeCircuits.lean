-- Prove2me | Definitions.Def_ResultantVNP_HasPolySizeCircuits
-- name    : ResultantVNP_HasPolySizeCircuits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:39.025103+00:00
-- url     : https://prove2.me/theorems/2f24e095-eb08-408f-9cbd-ccec28a1a314
-- title:
--   Polynomial-size arithmetic circuits for a family $\{p_n\}_{n\ge1}$
-- statement:
--   A family $\{p_n\}_{n\ge1}$ of polynomials over $\mathbb C$ **has poly($n$)-size arithmetic circuits** if there is a constant $c$ such that, for every $n\ge1$, some arithmetic circuit with at most $c\,n^c+c$ gates computes $p_n$.
--
--   Only the size is bounded: no bound on degree or number of variables is required. This is the hypothesis of Theorem 1.4, where $p_n=\mathrm{Res}^{(2)}_n$ has degree $n2^{n-1}$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Theorem 1.4, p.6

import Mathlib
import Definitions.Def_ResultantVNP_Circuit

namespace ResultantVNP

/-- The family `{p_n}_{n ≥ 1}` **has poly(n)-size arithmetic circuits over `ℂ`**: there is a constant
`c` such that for every `n ≥ 1` some circuit of size `≤ c·n^c + c` computes `p_n`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Theorem 1.4, p.6 ("If the polynomial family {Res^{(2)}_n}_{n≥1} has poly(n)-size arithmetic
circuits over ℂ").

**Formalization Note** Size only: no bound on the degree or the number of variables is required (the
resultant of quadratic forms has degree `n·2^{n−1}`). Circuits are `Circuit` (fan-in two, size =
number of gates). The index set is `n ≥ 1`. -/
def HasPolySizeCircuits {σ : ℕ → Type} (p : ∀ n, MvPolynomial (σ n) ℂ) : Prop :=
  ∃ c : ℕ, ∀ n, 1 ≤ n → ∃ C : Circuit (σ n), C.value = p n ∧ C.size ≤ c * n ^ c + c

end ResultantVNP



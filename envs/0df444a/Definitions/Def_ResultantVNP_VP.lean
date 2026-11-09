-- Prove2me | Definitions.Def_ResultantVNP_VP
-- name    : ResultantVNP_VP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:56.90008+00:00
-- url     : https://prove2.me/theorems/eb29544b-48ad-45c8-83e8-62fa7d3e7f63
-- title:
--   Valiant's class $\mathrm{VP}$ over $\mathbb C$
-- statement:
--   A polynomial family $(p_n)$ is in **VP** if its number of variables, its degree and its circuit size are polynomially bounded in the index $n$: there is $c$ such that, for every $n$, $p_n$ has at most $c\,n^c+c$ variables, total degree at most $c\,n^c+c$, and is computed by an arithmetic circuit with at most $c\,n^c+c$ gates.
--
--   The class is nonuniform: circuits and their constants may depend on $n$.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib
import Definitions.Def_ResultantVNP_Circuit
import Definitions.Def_ResultantVNP_PolyBounded
import Definitions.Def_ResultantVNP_PolyFamily

namespace ResultantVNP

/-- **Valiant's class VP** over `ℂ`: the polynomial families whose number of variables, degree and
circuit size are polynomially bounded in the index `n`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14: "A polynomial family (p_n)_n is in VP if its number of variables, degree,
and circuit size are polynomially bounded in its index n."

**Formalization Note** Circuits are `Circuit` (fan-in two, size = number of gates, complex
constants); the circuit-size clause asks for one constant `c` and, for every `n`, a circuit of size
`≤ c·n^c + c` computing `p_n`. Degree is `totalDegree`. The class is nonuniform, as on p.14. -/
def VP : Set PolyFamily :=
  {f | PolyBounded f.nvars ∧ PolyBounded (fun n => (f.p n).totalDegree) ∧
    ∃ c : ℕ, ∀ n, ∃ C : Circuit (Fin (f.nvars n)), C.value = f.p n ∧ C.size ≤ c * n ^ c + c}

end ResultantVNP



-- Prove2me | Definitions.Def_ResultantVNP_VNP
-- name    : ResultantVNP_VNP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:34:05.658067+00:00
-- url     : https://prove2.me/theorems/1bd2e750-1c73-4756-8ebb-6299c4930ba3
-- title:
--   Valiant's class $\mathrm{VNP}$ over $\mathbb C$
-- statement:
--   A polynomial family $(p_n)$ is in **VNP** if there are a family $(g_n)\in\mathrm{VP}$ and a polynomially bounded $q(n)$ such that
--
--   $$
--   p_n(x)=\sum_{y\in\{0,1\}^{q(n)}} g_n(x,y)\qquad\text{for all }n .
--   $$
--
--   **Formalization Note** $g_n$ has exactly $v(n)+q(n)$ variables, the first $v(n)$ being $x$ and the last $q(n)$ being $y$; each $y_j\in\{0,1\}$ is substituted as a complex constant.
-- source:
--   Bhargav–Curticapean–Jindal–Shukla, Multivariate Resultants: Complexity and Applications to Real Feasibility, STOC 2027 submission (manuscript sha256 8827709b…7f8271), Section 3.1, p.14

import Mathlib
import Definitions.Def_ResultantVNP_VP

namespace ResultantVNP

/-- **Valiant's class VNP** over `ℂ`: the families `(p_n)` for which there are `(g_n) ∈ VP` and a
polynomially bounded `q(n)` with `p_n(x) = ∑_{y ∈ {0,1}^{q(n)}} g_n(x, y)`.

Bhargav–Curticapean–Jindal–Shukla, *Multivariate Resultants: Complexity and Applications to Real Feasibility*, STOC 2027 submission manuscript (sha256 8827709b…7f8271), Section 3.1, p.14: "It is in VNP if it admits (g_n) in VP and polynomially bounded q(n) such
that p_n(𝒙) = Σ_{𝒚∈{0,1}^{q(n)}} g_n(𝒙, 𝒚)."

**Formalization Note** `g_n` has exactly `nvars n + q n` variables: the first `nvars n` are `x`, the
last `q n` are `y`; `g_n(x, y)` substitutes `x_i ↦ x_i` and `y_j ↦ y_j ∈ {0, 1}` (as complex
constants). -/
def VNP : Set PolyFamily :=
  {f | ∃ g ∈ VP, ∃ q : ℕ → ℕ, PolyBounded q ∧ ∀ n, ∃ h : g.nvars n = f.nvars n + q n,
    f.p n = ∑ y : Fin (q n) → Fin 2,
      MvPolynomial.aeval
        (fun v : Fin (g.nvars n) =>
          Fin.append (fun i : Fin (f.nvars n) => (MvPolynomial.X i : MvPolynomial (Fin (f.nvars n)) ℂ))
            (fun j : Fin (q n) => MvPolynomial.C (((y j : ℕ) : ℂ))) (Fin.cast h v))
        (g.p n)}

end ResultantVNP



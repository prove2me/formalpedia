-- Prove2me | Definitions.Def_MinCostMaj_HasConsMajPol
-- name    : MinCostMaj_HasConsMajPol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:10:44.697882+00:00
-- url     : https://prove2.me/theorems/99e35c0b-133b-4d5a-815c-ad99bb8e4799
-- title:
--   $\mathbf A$ admits a conservative majority polymorphism
-- statement:
--   Let $\mathbf A=(A;R_1,\dots,R_p)$ be a finite relational structure. A ternary operation $m:A^3\to A$ is a **polymorphism** of $\mathbf A$ if it preserves every $R_i$: applying $m$ coordinatewise to any three tuples of $R_i$ gives a tuple of $R_i$. It is **conservative** if $m(x_1,x_2,x_3)\in\{x_1,x_2,x_3\}$ for all arguments, and it is a **majority** operation if
--   $$m(a,a,b)=m(a,b,a)=m(b,a,a)=a\qquad\text{for all }a,b\in A.$$
--   The structure $\mathbf A$ *admits a conservative majority polymorphism* if such an $m$ exists.
--
--   This is the standing hypothesis of the main theorem: by DeHaan, Huang and Lee, a conservative near-unanimity polymorphism is necessary for constant-factor approximability of $\mathrm{MinCostCSP}(\mathbf A)$, and the mission settles the majority case.
--
--   **Formalization Note** Preservation is the published `FunctionAlgebras.Preserves`, and the majority identities are the published `FunctionAlgebras.IsNearUnanimity` for ternary operations.
-- source:
--   Kozik, Živný, Constant-factor approximation of MinCostCSP with a conservative majority polymorphism, arXiv:2607.10667 (held version, sha256 ec17e13c…), §2, p.5 (polymorphism); §1, pp.2–3 (conservative, majority) (PDF pp.3–4, 6)

import Mathlib
import Definitions.Def_FunctionAlgebras_defs
import Definitions.Def_MinCostMaj_Struct

namespace MinCostMaj

/-- **`A` admits a conservative majority polymorphism.**

Kozik, Živný, *Constant-factor approximation of MinCostCSP with a conservative majority
polymorphism*, arXiv:2607.10667, §2, p.5 (polymorphism: "f preserves all relations in A"),
§1, p.2 (conservative: "f(x1, . . . , xk) ∈ {x1, . . . , xk}") and p.3 (majority:
"m(a, a, b) = m(a, b, a) = m(b, a, a) = a").

There is a ternary `m : A³ → A` that preserves every relation of `A` (published
`FunctionAlgebras.Preserves`: applied coordinatewise to any three tuples of `Rᵢ` it gives a tuple
of `Rᵢ`), returns one of its arguments, and is a majority operation (published
`FunctionAlgebras.IsNearUnanimity` with `d + 1 = 3`: `m(y,x,x) = m(x,y,x) = m(x,x,y) = x`). -/
def HasConsMajPol {d : ℕ} (A : Struct d) : Prop :=
  ∃ m : (Fin 3 → Fin d) → Fin d,
    (∀ i : Fin A.p, FunctionAlgebras.Preserves m (A.rel i)) ∧
    (∀ x : Fin 3 → Fin d, ∃ j : Fin 3, m x = x j) ∧
    FunctionAlgebras.IsNearUnanimity (d := 2) m

end MinCostMaj



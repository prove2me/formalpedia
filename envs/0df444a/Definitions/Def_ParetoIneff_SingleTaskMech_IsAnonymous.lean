-- Prove2me | Definitions.Def_ParetoIneff_SingleTaskMech_IsAnonymous
-- name    : ParetoIneff_SingleTaskMech_IsAnonymous
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:27.507952+00:00
-- url     : https://prove2.me/theorems/a22cf09a-4d70-483d-aafd-46acf51af263
-- title:
--   Anonymous single-task mechanism
-- statement:
--   A single-task mechanism $\mathcal A$ is **anonymous** if, for any true cost vector $t$ with no ties (that is, $t_i\ne t_{i'}$ for $i\ne i'$) and any permutation $\pi$ of the machines, whenever $s$ is an equilibrium under $t$ there is an equilibrium $\tilde s$ under the true vector $\pi(t)$ with allocation
--   $$
--   x(\tilde s)=\pi(x(s)).
--   $$
--   Here $\pi(y)=(y_{\pi(1)},\dots,y_{\pi(n)})$. The notion refers to true costs and to equilibria: it says that an outcome available to one machine is available to whichever machine takes its place.
--
--   **Formalization Note** The permuted vector is $t\circ\pi$. If $w$ is the winner at $s$, then $\pi(x(s))$ has its $1$ at $\pi^{-1}(w)$, so the condition says that the winner at $\tilde s$ is $\pi^{-1}(w)$.
-- source:
--   Filos-Ratsikas, Giannakopoulos, Lazos, The Pareto frontier of inefficiency in mechanism design, arXiv:1809.03454v7 (24 Feb 2021), https://arxiv.org/abs/1809.03454v7, Definition 2 and footnotes 5, 6, p.6

import Mathlib
import Definitions.Def_ParetoIneff_SingleTaskMech_IsEq

open NNReal

namespace ParetoIneff

/-- A single-task mechanism `A` is **anonymous**, Definition 2, arXiv:1809.03454v7, p.6: for every
true vector `v` with no ties (footnote 5: `vᵢ ≠ vᵢ'` for `i ≠ i'`) and every permutation `π` of the
machines, if `s` is an equilibrium under `v`, then there is an equilibrium `s̃` under `π(v)` with
allocation `x(s̃) = π(x(s))`.

**Formalization Note** Footnote 6 defines `π(x) = (x_{π(1)}, …, x_{π(n)})`, i.e. `π(v) = v ∘ π`.
The allocation `x(s)` is the 0/1 vector with a `1` at the winner `w = A.alloc s`, so
`π(x(s))` has its `1` at the machine `i` with `π i = w`, i.e. at `π⁻¹ w`; hence the condition
`x(s̃) = π(x(s))` reads `A.alloc s̃ = π.symm (A.alloc s)`. -/
def SingleTaskMech.IsAnonymous {n : ℕ} (A : SingleTaskMech n) : Prop :=
  ∀ v : Fin n → ℝ≥0, Function.Injective v →
    ∀ (π : Equiv.Perm (Fin n)) (s : Fin n → ℝ≥0), A.IsEq v s →
      ∃ s' : Fin n → ℝ≥0, A.IsEq (v ∘ π) s' ∧ A.alloc s' = π.symm (A.alloc s)

end ParetoIneff



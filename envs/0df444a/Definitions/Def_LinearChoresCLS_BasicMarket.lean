-- Prove2me | Definitions.Def_LinearChoresCLS_BasicMarket
-- name    : LinearChoresCLS_BasicMarket
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:47:45.646196+00:00
-- url     : https://prove2.me/theorems/6812a00e-e4d6-4ed4-861a-c3fe683ed245
-- title:
--   The basic market of Section 5, $\Phi_0$ and the remainder $R_0$
-- statement:
--   The **basic market** has the $n+1$ basic chores $0,\dots,n$ with unit supply and one agent per chore with earning requirement $1$; the agent associated with chore $j$ has disutility $1$ on chores $\{0,j\}$ and $1+t$ on every other chore. Its logarithmic objective at the basic price family is $\Phi_0(x)=\Psi_0(p(x))$, and
--   $$
--   R_0(x)=\Phi_0(x)-\frac{t^2}{2(n+1)}\sum_{0\le j<j'\le n}(x_j-x_{j'})^2 .
--   $$
--
--   Theorem 5.1 bounds the coordinate variation of $R_0$ by $2t^3|h|$.
--
--   **Formalization Note** $\Psi_0$ is the generic objective $\Psi$ of this market, not the closed form $-\sum_j\log p_j(x)$ that the paper derives from it. Agents and chores are both `Fin (n+1)`.
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), Section 5, pp.13–15, and Appendix B, p.45

import Mathlib
import Definitions.Def_LinearChoresCLS_Psi
import Definitions.Def_LinearChoresCLS_Params

open Finset

namespace LinearChoresCLS

/-- The **basic market** of Section 5 (arXiv:2611.06589, held version sha256 85d34a9e…, p.13): the
`n + 1` basic chores `0, …, n` with unit supplies `S_j = 1`, and one agent per chore with earning
requirement `B_a = 1`; the agent associated with chore `j` has disutility `1` on the chores
`{0, j}` and `1 + t` on every other chore.

**Formalization Note.** Agents and chores are both indexed by `Fin (n+1)`; agent `j` is the agent
associated with chore `j`. -/
noncomputable def basicMarket (n : ℕ) (t : ℝ) : ChoresMarket (Fin (n + 1)) (Fin (n + 1)) where
  disutil a ℓ := if ℓ = 0 ∨ ℓ = a then 1 else 1 + t
  earn _ := 1
  supply _ := 1

variable {n : ℕ}

/-- `Φ₀(x) := Ψ₀(p(x))`: the logarithmic objective `Ψ₀ = −∑_a log μ_a` of the basic market
evaluated at the basic price family (5.2) (arXiv:2611.06589, p.14).

**Formalization Note.** `Ψ₀` is the generic `ChoresMarket.Psi` of `basicMarket n t`, not the
closed form `−∑_j log p_j(x)` the paper derives from it. -/
noncomputable def Phi0 (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  (basicMarket n t).Psi (basicPrice t x)

/-- The remainder `R₀` of (5.3) (arXiv:2611.06589, Theorem 5.1, p.15, and Appendix B, p.45):
`R₀(x) := Φ₀(x) − (t² / (2(n+1))) ∑_{0≤j<j′≤n} (x_j − x_{j′})²`, with `x₀ = 0`. -/
noncomputable def R0 (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  Phi0 t x - t ^ 2 / (2 * (n + 1)) * ∑ π : Pair n, (xExt x π.1.1 - xExt x π.1.2) ^ 2

end LinearChoresCLS



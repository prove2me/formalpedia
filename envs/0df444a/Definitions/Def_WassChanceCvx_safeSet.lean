-- Prove2me | Definitions.Def_WassChanceCvx_safeSet
-- name    : WassChanceCvx_safeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:58.279304+00:00
-- url     : https://prove2.me/theorems/468d6889-bf95-4d87-8c55-3530a4814d81
-- title:
--   The safe event $\mathcal S(x)=\{\xi: A(x)\xi\le b(x)\}$
-- statement:
--   Let $E$ be a real normed space, $a_1,\dots,a_k$ continuous linear functionals on $E$ and $\beta\in\mathbb R^k$. The **safe set** is
--
--   $$
--   \mathcal S(a,\beta)=\{\xi\in E:\ a_i(\xi)\le\beta_i\ \text{for } i=1,\dots,k\}.
--   $$
--
--   With $a=A(x)$ (the rows of $A(x)$) and $\beta=b(x)$, this is the event $\mathcal S(x)=\{\xi: A(x)\xi\le b(x)\}$ of the paper; its complement $\mathcal S^c(x)$ is the unsafe set.
--
--   **Formalization Note** $\mathbb R^q$ with a norm is a finite-dimensional normed space $E$, and row $i$ of $A(x)$ is the functional $a_i$. With $k=0$ rows the safe set is all of $E$.
-- source:
--   Shen, Jiang, Convex Chance-Constrained Programs with Wasserstein Ambiguity, arXiv:2111.02486v2, Notation, p.4

import Mathlib

namespace WassChanceCvx

/-- **The safe event `𝒮(x) = {ξ : A(x)ξ ≤ b(x)}`.**
Shen, Jiang, arXiv:2111.02486v2, Notation, p.4: "For a given decision `x`, we denote by `𝒮(x)` the
event `{ξ : A(x)ξ ≤ b(x)}` and by `𝒮ᶜ(x)` its complement."

`safeSet a β` is `{ξ ∈ E : aᵢ(ξ) ≤ βᵢ for every row i}`, for rows `a : Fin k → StrongDual ℝ E`
and right-hand side `β : Fin k → ℝ`. With `a = A(x)` and `β = b(x)` it is `𝒮(x)`.

**Formalization Note.** `ℝ^q` with an arbitrary norm is a finite-dimensional real normed space
`E`; row `i` of `A(x)`, `aᵢ(x)ᵀ`, is the continuous linear functional `a i` on `E`. With no rows
(`k = 0`) the safe set is all of `E`. -/
def safeSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ}
    (a : Fin k → StrongDual ℝ E) (β : Fin k → ℝ) : Set E :=
  {ξ | ∀ i, a i ξ ≤ β i}

end WassChanceCvx



-- Prove2me | Definitions.Def_SmoothedNash_grid
-- name    : SmoothedNash_grid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:17.717914+00:00
-- url     : https://prove2.me/theorems/3dcb3ad8-36db-4b52-a1ea-c784412487d7
-- title:
--   Level-$t$ grid $N_t(A)$ (numerator vectors)
-- statement:
--   For a support profile $A$ and a level $t \ge 0$, the **level-$t$ grid** is
--   $$
--   N_t(A) := \{x \in K_A : q_t x_i(a) \in \mathbb Z_{\ge 0} \text{ for all } i \in [m],\ a \in A_i\}.
--   $$
--   Its points are stored by their numerators: a grid point is a vector $k = (k_i(a))$ of nonnegative integers with $k_i(a) = 0$ for $a \notin A_i$ and $\sum_a k_i(a) = q_t$ for each player $i$; it represents the profile $x_i(a) = k_i(a)/q_t$.
--
--   The grids are fixed (they do not depend on the game). Lemma 2.1 shows they are $\rho_t$-nets of $K_A$ and nested through the children relation.
--
--   **Formalization Note** The finite set of numerator vectors is in bijection with $N_t(A)$ through $k \mapsto k/q_t$; clause 0 of Lemma 2.1 states this.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_q

namespace SmoothedNash

/-- The level-`t` grid `N_t(A) := {x ∈ K_A : q_t x_i(a) ∈ ℤ_{≥0} for all i ∈ [m], a ∈ A_i}`
(Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), Lemma 2.1, p.14), stored by numerators.

**Formalization Note** A grid point is its numerator vector `k : Fin m → Fin n → ℕ`, with
`k_i(a) = 0` for `a ∉ A_i` and `Σ_a k_i(a) = q_t` for each player; its profile is
`gridPt A t k = k / q_t`. Since `q_t ≥ 1`, `gridPt A t` maps this finite set bijectively onto the
paper's `N_t(A)`; Lemma 2.1 (`lemma_2_1`) records this. -/
def grid {m n : ℕ} (A : SupportProfile m n) (t : ℕ) : Finset (Fin m → Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin m => Fintype.piFinset fun _ : Fin n => Finset.range (q A t + 1)).filter
    fun k => ∀ i, (∀ a, a ∉ A.1 i → k i a = 0) ∧ ∑ a, k i a = q A t

end SmoothedNash



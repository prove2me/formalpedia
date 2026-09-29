-- Prove2me | Definitions.Def_SteuerChoo_Discrete_IdealVector
-- name    : SteuerChoo_Discrete_IdealVector
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:43:41.015767+00:00
-- url     : https://prove2.me/theorems/8aaced54-cf18-4c6e-ac48-67dc3ce213e5
-- title:
--   Steuer–Choo §2: the ideal criterion vector z* with the ε-rule
-- statement:
--   Let $Z \subset \mathbb R^k$ be a finite set of criterion vectors with nondominated set $N$. A vector $z^* \in \mathbb R^k$ is an *ideal criterion vector* for $Z$ if there are numbers $\varepsilon_1,\dots,\varepsilon_k \ge 0$ with
--   $$z^*_i = \max\{z_i \mid z \in Z\} + \varepsilon_i, \qquad i = 1,\dots,k,$$
--   where $\varepsilon_i = 0$ is permitted, except that $\varepsilon_i > 0$ is required whenever
--
--   1. (i) more than one nondominated criterion vector maximizes the $i$-th objective, or
--   2. (ii) the only nondominated criterion vector that maximizes the $i$-th objective also maximizes one of the other objectives.
--
--   The ideal vector is the reference point from which the weighted Tchebycheff metrics measure distance. The $\varepsilon$-rule is what makes the weights of the paper's construction (b) well defined and what lets each nondominated vector be singled out by a Tchebycheff program; replacing it by "$z^* > z$ for all $z\in Z$" would change the class of admissible reference points.
--
--   **Formalization Note** The paper writes $\max\{f_i(x)\mid x\in S\}$; with $S$ and $f$ eliminated this is the maximum of the $i$-th coordinate over $Z$, and the definition asks that the maximum be attained by some $z \in Z$ (automatic for a nonempty finite $Z$, and it forces $Z$ to be nonempty when $k \ge 1$). Condition (i) is "there are two distinct vectors in $N$ that both maximize objective $i$"; condition (ii) is "there is a vector in $N$ maximizing objective $i$, it is the only vector of $N$ doing so, and it also maximizes some objective $j \ne i$".
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983) 326–344, https://doi.org/10.1007/BF02591870, p. 327, §2, definition of the ideal criterion vector z* and conditions (i)–(ii)

import Mathlib
import Definitions.Def_SteuerChoo_Discrete_Nondominated

/-!
# Steuer–Choo (1983), §2: the ideal criterion vector

R. E. Steuer and E.-U. Choo, Math. Programming 26 (1983), §2, p. 327.

`z*ᵢ = max {fᵢ(x) | x ∈ S} + εᵢ`, where a given `εᵢ ≥ 0` (`εᵢ = 0` is permissible) unless
(i) there is more than one nondominated criterion vector that maximizes the `i`th objective, or
(ii) the only nondominated criterion vector that maximizes the `i`th objective also maximizes one of
the other objectives, in which case `εᵢ` must be strictly positive.

`max {fᵢ(x) | x ∈ S}` is the maximum of the `i`-th coordinate over `Z`.
-/

namespace SteuerChoo.Discrete

/-- Condition (i) of §2, p. 327: more than one nondominated criterion vector maximizes the `i`-th
objective. -/
def CondI {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, ∃ w ∈ nondominated Z, z ≠ w ∧ MaximizesObj Z i z ∧ MaximizesObj Z i w

/-- Condition (ii) of §2, p. 327: the only nondominated criterion vector that maximizes the `i`-th
objective also maximizes one of the other objectives. -/
def CondII {k : ℕ} (Z : Finset (Fin k → ℝ)) (i : Fin k) : Prop :=
  ∃ z ∈ nondominated Z, MaximizesObj Z i z ∧
    (∀ w ∈ nondominated Z, MaximizesObj Z i w → w = z) ∧
    ∃ j, j ≠ i ∧ MaximizesObj Z j z

/-- `IsIdealVector Z zstar`: `zstar` is an ideal criterion vector for `Z` in the sense of §2, p. 327:
there are `εᵢ ≥ 0` with `z*ᵢ = max_{z ∈ Z} zᵢ + εᵢ` for every `i` (the maximum being attained), and
`εᵢ > 0` whenever condition (i) or (ii) holds for objective `i`. -/
def IsIdealVector {k : ℕ} (Z : Finset (Fin k → ℝ)) (zstar : Fin k → ℝ) : Prop :=
  ∃ ε : Fin k → ℝ, (∀ i, 0 ≤ ε i) ∧
    (∀ i, ∃ z, MaximizesObj Z i z ∧ zstar i = z i + ε i) ∧
    ∀ i, (CondI Z i ∨ CondII Z i) → 0 < ε i

end SteuerChoo.Discrete



-- Prove2me | Definitions.Def_FullForesight_Randomized_Constants
-- name    : FullForesight_Randomized_Constants
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:16:03.342232+00:00
-- url     : https://prove2.me/theorems/c0428cf6-86bc-4b34-aef7-0f18e8e19927
-- title:
--   The constants $\Psi$, $\xi^\star$, $\Phi$, $u_1$, $u_2$ (§2, Proposition 1, Lemma 4)
-- statement:
--   This definition fixes the numerical constants of the tight randomized bound.
--
--   1. $\Psi(\xi) = 89\xi^4 - 44\xi^3 - 19\xi^2 - 3\xi + 1$ (p. 5).
--   2. $\xi^\star$ is the root of $\Psi$ in $(1/2, 1)$ (footnote ‡, p. 2). Concretely,
--   $$\xi^\star = \sup\{\xi \in [1/2, 1] : \Psi(\xi) = 0\}.$$
--   3. $\Phi(x) = x^4 + x^3 - 2x^2 - 3x + 2$ (Lemma 4, p. 9).
--   4. $u_1$ is the root of $\Phi$ in $(0, 1)$; concretely $u_1 = \sup\{x \in [0, 1] : \Phi(x) = 0\}$.
--   5. $u_2 = u_1^2(1 + u_1)$.
--
--   Numerically $\xi^\star \approx 0.7941970147$, $u_1 \approx 0.550794645$, $u_2 \approx 0.470471923$, and $\xi^\star = 1/(1 + u_1 u_2)$. These numbers are the threshold of Main Result 1 and the parameters of its extremal instance.
--
--   **Formalization Note** The roots are defined as suprema of the zero sets on the closed intervals, so the definitions carry no proof obligation. That each zero set is exactly one point of the open interval is Proposition 1 (for $\Psi$) and part of Lemma 4 (for $\Phi$), and both facts are stated in the conclusions of `proposition_1`, `lemma_4` and `main_result_1`.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission (sha256 ef7bb5aa…), p. 2, footnote ‡; p. 5, §2; p. 9, Lemma 4; p. 18, Proposition 1

import Mathlib

/-!
# The constants `Ψ`, `ξ⋆`, `Φ`, `u₁`, `u₂`

Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, *Consistent
Submodular Maximization with Full Foresight*, STOC 2027 submission, p. 2 (footnote ‡), p. 5
(§2), p. 9 (Lemma 4), p. 18 (Proposition 1).

* `Ψ ξ = 89ξ⁴ − 44ξ³ − 19ξ² − 3ξ + 1`; `ξ⋆` is its unique root in `(1/2, 1)`.
* `Φ x = x⁴ + x³ − 2x² − 3x + 2`; `u₁` is its unique root in `(0, 1)`; `u₂ = u₁²(1 + u₁)`.

The roots are defined concretely as the supremum of the zero set of the polynomial on the closed
interval; that this zero set is a single point of the open interval is Proposition 1 (for `Ψ`)
and part of Lemma 4 (for `Φ`), and both facts appear in the conclusions of the theorems.
-/

namespace FullForesight.Randomized

/-- `Ψ(ξ) = 89ξ⁴ − 44ξ³ − 19ξ² − 3ξ + 1` (p. 5). -/
def Psi (ξ : ℝ) : ℝ := 89 * ξ ^ 4 - 44 * ξ ^ 3 - 19 * ξ ^ 2 - 3 * ξ + 1

/-- `ξ⋆`: the supremum of the roots of `Ψ` in `[1/2, 1]` (the unique root in `(1/2, 1)`,
Proposition 1). -/
noncomputable def xiStar : ℝ := sSup {ξ : ℝ | ξ ∈ Set.Icc (1 / 2 : ℝ) 1 ∧ Psi ξ = 0}

/-- `Φ(x) = x⁴ + x³ − 2x² − 3x + 2` (Lemma 4, p. 9). -/
def Phi (x : ℝ) : ℝ := x ^ 4 + x ^ 3 - 2 * x ^ 2 - 3 * x + 2

/-- `u₁`: the supremum of the roots of `Φ` in `[0, 1]` (the unique root in `(0, 1)`, Lemma 4). -/
noncomputable def u1 : ℝ := sSup {x : ℝ | x ∈ Set.Icc (0 : ℝ) 1 ∧ Phi x = 0}

/-- `u₂ = u₁²(1 + u₁)` (Lemma 4, p. 9). -/
noncomputable def u2 : ℝ := u1 ^ 2 * (1 + u1)

end FullForesight.Randomized



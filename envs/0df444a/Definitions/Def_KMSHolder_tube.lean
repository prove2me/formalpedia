-- Prove2me | Definitions.Def_KMSHolder_tube
-- name    : KMSHolder_tube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:39:04.317214+00:00
-- url     : https://prove2.me/theorems/f36cf3f5-61cb-4654-9445-d5c8d4ff7324
-- title:
--   The tube $I^{(n)}_\alpha = \{z \in \mathbb C^n : \Re z_j \ge 0,\ \sum_j \Re z_j \le \alpha\}$
-- statement:
--   For $n \ge 0$ and $\alpha \in \mathbb R$ let
--
--   $$
--   I^{(n)}_\alpha = \Big\{ (z_1, \dots, z_n) \in \mathbb C^n : \sum_{j=1}^n \Re z_j \le \alpha,\ 0 \le \Re z_j \Big\},
--   \qquad I^{(n)} \equiv I^{(n)}_1 .
--   $$
--
--   This is the domain on which Araki's multiple-time correlation $\omega(A_n \Delta^{z_n} \cdots A_1 \Delta^{z_1} A_0)$ is defined: the real parts of the "imaginary times" are nonnegative and sum to at most one.
--
--   **Formalization Note** A point of $\mathbb C^n$ is a function `Fin n → ℂ`, so the Lean index $j$ is the paper's $z_{j+1}$.
-- source:
--   Jäkel–Robl, The Hölder Inequality for KMS States, arXiv:1103.3608v2, §3.1, eq. (5), p.5

import Mathlib

namespace KMSHolder

/-- Jäkel–Robl, *The Hölder Inequality for KMS States*, arXiv:1103.3608v2, §3.1, eq. (5), p.5:
the tube
`I⁽ⁿ⁾_α = {(z₁, …, zₙ) ∈ ℂⁿ : Σⱼ ℜzⱼ ≤ α, 0 ≤ ℜzⱼ}`, with `I⁽ⁿ⁾ ≡ I⁽ⁿ⁾₁`.

**Formalization Note.** A point of `ℂⁿ` is a function `Fin n → ℂ`; the Lean index `j`
corresponds to the paper's `z_{j+1}` (0-based indices). For `n = 0` the tube is the single
point of `Fin 0 → ℂ` whenever `0 ≤ α`. -/
def tube (n : ℕ) (α : ℝ) : Set (Fin n → ℂ) :=
  {z | (∀ j, 0 ≤ (z j).re) ∧ ∑ j, (z j).re ≤ α}

end KMSHolder



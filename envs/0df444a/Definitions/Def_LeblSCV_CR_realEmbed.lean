-- Prove2me | Definitions.Def_LeblSCV_CR_realEmbed
-- name    : LeblSCV_CR_realEmbed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T06:34:38.054311+00:00
-- url     : https://prove2.me/theorems/92a1f67b-61ed-454a-8781-94aa2c1b0762
-- title:
--   The natural inclusion $\mathbb{R}^n \subset \mathbb{C}^n$
-- statement:
--   The **natural inclusion** of $\mathbb{R}^n$ in $\mathbb{C}^n$ sends a real vector $x = (x_1, \dots, x_n)$ to the complex vector with the same coordinates:
--   $$x \mapsto (x_1 + 0i, \dots, x_n + 0i).$$
--   Its image is the set $\{z \in \mathbb{C}^n : \operatorname{Im} z_k = 0 \text{ for all } k\}$, written $\mathbb{R}^n \subset \mathbb{C}^n$ in Lemma 3.1.2 and Proposition 3.1.3.
--
--   **Formalization Note.** $\mathbb{R}^n$ is `Fin n → ℝ` and $\mathbb{C}^n$ is `Fin n → ℂ`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 104–105 (the natural inclusion in Lemma 3.1.2 and Proposition 3.1.3)

import Mathlib

namespace LeblSCV.CR

/-- The natural inclusion `ℝⁿ ⊂ ℂⁿ` (Lebl, pp. 104–105): `x ↦ (x₁ + 0i, …, xₙ + 0i)`. -/
def realEmbed {n : ℕ} (x : Fin n → ℝ) : Fin n → ℂ :=
  fun k => (x k : ℂ)

end LeblSCV.CR



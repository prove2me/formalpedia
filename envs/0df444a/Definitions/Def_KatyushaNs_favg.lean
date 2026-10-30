-- Prove2me | Definitions.Def_KatyushaNs_favg
-- name    : KatyushaNs_favg
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:44:53.828885+00:00
-- url     : https://prove2.me/theorems/77619c16-8a9a-4e71-b2e9-989f5b61db22
-- title:
--   Finite average $f = \frac1n\sum_i f_i$
-- statement:
--   For functions $f_1, \dots, f_n : \mathbb{R}^d \to \mathbb{R}$, the finite average is
--   $$f(x) = \frac{1}{n}\sum_{i=1}^n f_i(x).$$
--   It is the smooth part of the objective of Problem (1.1).
--
--   **Formalization Note** The index set $\{1,\dots,n\}$ is `Fin n`. At $n = 0$ the value is $0$; every theorem assumes $n \ge 1$.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, Problem (1.1), p. 1

import Mathlib

namespace KatyushaNs

/-- **The finite average `f = (1/n) Σᵢ fᵢ` of Problem (1.1).**
Allen-Zhu, *Katyusha: The First Direct Acceleration of Stochastic Gradient Methods*,
arXiv:1603.05953v6, Problem (1.1), p. 1 (PDF p. 2): "F(x) def= f(x) + ψ(x) def=
(1/n) Σ_{i=1}^n fi(x) + ψ(x)".

`favg fi x = (1/n) Σ_{i} fi i x`.

**Formalization Note.** The paper's index set `{1, …, n}` is `Fin n`. At `n = 0` the value is the
junk `0`; every theorem using `favg` assumes `0 < n`. -/
noncomputable def favg {d n : ℕ} (fi : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) :
    EuclideanSpace ℝ (Fin d) → ℝ :=
  fun x => (n : ℝ)⁻¹ * ∑ i, fi i x

end KatyushaNs



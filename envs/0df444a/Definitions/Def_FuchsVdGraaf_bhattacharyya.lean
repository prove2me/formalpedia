-- Prove2me | Definitions.Def_FuchsVdGraaf_bhattacharyya
-- name    : FuchsVdGraaf_bhattacharyya
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:15.962828+00:00
-- url     : https://prove2.me/theorems/cd1e1f46-fe13-42df-b388-c93a8ed73326
-- title:
--   Bhattacharyya coefficient $B(p_0,p_1)$ (Definition 7)
-- statement:
--   For two probability distributions $p_0, p_1$ on a finite set $\mathcal X$, the **Bhattacharyya coefficient** is
--
--   $$
--   B(p_0,p_1) = \sum_{x\in\mathcal X} \sqrt{p_0(x)\,p_1(x)} .
--   $$
--
--   It is an overlap measure: identical distributions have $B = 1$, orthogonal ones $B = 0$. Geometrically it is the inner product of the vectors $(\sqrt{p_0(x)})_x$ and $(\sqrt{p_1(x)})_x$.
--
--   **Formalization Note** This is the unsquared coefficient (its square is sometimes called the classical fidelity).
-- source:
--   Fuchs and van de Graaf, Cryptographic Distinguishability Measures for Quantum Mechanical States, arXiv:quant-ph/9712042v2, Definition 7, eq. (22), p.13

import Mathlib

namespace FuchsVdGraaf

/-- Fuchs and van de Graaf, arXiv:quant-ph/9712042v2, Definition 7, eq. (22), p.13: the
Bhattacharyya coefficient between two probability distributions,
`B(p₀, p₁) = ∑_{x∈X} √(p₀(x) p₁(x))`.

**Formalization Note.** This is the unsquared coefficient. `Real.sqrt` is applied to
`p₀(x) p₁(x) ≥ 0` for probability distributions. -/
noncomputable def bhattacharyya {X : Type} [Fintype X] (p0 p1 : X → ℝ) : ℝ :=
  ∑ x, Real.sqrt (p0 x * p1 x)

end FuchsVdGraaf



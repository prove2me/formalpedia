-- Prove2me | Definitions.Def_CloudAlloc_MWU_IsKLProj
-- name    : CloudAlloc_MWU_IsKLProj
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:35:35.105712+00:00
-- url     : https://prove2.me/theorems/f04fd07f-149b-4c99-baa1-105bf22cc3eb
-- title:
--   $x=\pi_{\Delta_\varepsilon}(y)$: KL projection onto the truncated simplex
-- statement:
--   For $y\in\mathbb R^N$, a vector $x$ is the **KL projection** of $y$ onto $\Delta_\varepsilon$, written $x=\pi_{\Delta_\varepsilon}(y)$, if $x\in\Delta_\varepsilon$ and
--
--   $$
--   \sum_i x(i)\log\frac{x(i)}{y(i)}\ \le\ \sum_i z(i)\log\frac{z(i)}{y(i)}\qquad\text{for every } z\in\Delta_\varepsilon .
--   $$
--
--   Algorithm 1 applies this projection after each multiplicative update.
--
--   **Formalization Note** The argmin is a predicate, so no choice function is needed. For $y$ with positive entries and $0<\varepsilon<1$ the minimizer exists and is unique.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §2.1, p. 9 (definition of π_{Δ_ε})

import Mathlib
import Definitions.Def_CloudAlloc_MWU_truncSimplex
import Definitions.Def_CloudAlloc_MWU_klDiv

namespace CloudAlloc.MWU

/-- **`x = π_{Δ_ε}(y)`: the KL projection onto the truncated simplex.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency*, arXiv:1809.02688v3, §2.1, p. 9 (unnumbered):
"let `π∆ε(·)` be the projection function onto `∆ε` using Kullback–Leibler divergence
(KL-divergence for short), i.e., `π∆ε(y) := argmin_{x∈∆ε} Σ_i x(i) log(x(i)/y(i))`, where
`y = (y(1), . . . , y(N)) ∈ R^N_{≥0}`".

`IsKLProj N ε y x` says that `x` lies in `Δ_ε` and minimizes `Σ_i z(i) log(z(i)/y(i))` over all
`z ∈ Δ_ε`.

**Formalization Note.** The argmin is expressed as a predicate, so no choice function is needed. For
`y` with positive entries and `0 < ε < 1` the minimizer exists (continuous objective on a compact
nonempty set) and is unique (strictly convex objective). Algorithm 1 only projects vectors with
positive entries. -/
def IsKLProj (N : ℕ) (ε : ℝ) (y x : Fin N → ℝ) : Prop :=
  x ∈ truncSimplex N ε ∧ ∀ z ∈ truncSimplex N ε, klDiv x y ≤ klDiv z y

end CloudAlloc.MWU



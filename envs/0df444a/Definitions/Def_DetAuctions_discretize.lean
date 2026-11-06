-- Prove2me | Definitions.Def_DetAuctions_discretize
-- name    : DetAuctions_discretize
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:08.486365+00:00
-- url     : https://prove2.me/theorems/e659f0b3-b338-4fb9-a7af-3f201947b10b
-- title:
--   Downward $1/K$-lattice discretization $F^{(K)}$
-- statement:
--   Let $F$ be a distribution on $\mathbb R_+^m$ and $X=(X_1,\dots,X_m)\sim F$. For a positive integer $K$, the **(downward) $1/K$-lattice discretization** $F^{(K)}$ is the law of
--   $$X^{(K)}=\frac{\lfloor K\cdot X\rfloor}{K}=\Big(\frac{\lfloor KX_1\rfloor}{K},\dots,\frac{\lfloor KX_m\rfloor}{K}\Big).$$
--   Rounding each value down to the grid $I_K$ (for values in $[0,1]$) is how the paper transfers bounds proved on the grid to general distributions (Proposition 2.2).
--
--   **Formalization Note** The push-forward of the law $\mu$ on $\mathbb R_{\ge0}^\iota$ under the coordinatewise map $x\mapsto(\lfloor Kx_j\rfloor/K)_j$, which is measurable.
-- source:
--   Giannakopoulos, Hahn, On the Power of Determinism in Multi-Item Auctions, arXiv:2609.35711 (version of Nov. 3, 2026) [preprint], Definition 2.1 (Distribution Discretization), p.10 (pdf p.12)

import Mathlib

open MeasureTheory
open scoped NNReal

namespace DetAuctions

/-- The **downward `1/K`-lattice discretization** `F^(K)` of a value law `F`: the law of
`X^(K) = ⌊K·X⌋/K = (⌊K X₁⌋/K, …, ⌊K X_m⌋/K)` when `X ∼ F`.

Giannakopoulos, Hahn, *On the Power of Determinism in Multi-Item Auctions*, arXiv:2609.35711
(version of Nov. 3, 2026), Definition 2.1 (Distribution Discretization), p.10.

**Formalization Note** Values live in `ι → ℝ≥0` (`ι` the finite set of items), laws are
measures on it, and `X^(K)` is the push-forward of `μ` under the coordinatewise map
`x ↦ (⌊K·xⱼ⌋₊ / K)ⱼ` (`Nat.floor` on `ℝ≥0`, which is the integer part since `K·xⱼ ≥ 0`). This map
is measurable (checked in the sanity file), so `Measure.map` is the genuine push-forward.
It is used only for positive integers `K`. -/
noncomputable def discretize {ι : Type*} (K : ℕ) (μ : Measure (ι → ℝ≥0)) :
    Measure (ι → ℝ≥0) :=
  μ.map (fun x j => ((⌊(K : ℝ≥0) * x j⌋₊ : ℕ) : ℝ≥0) / (K : ℝ≥0))

end DetAuctions



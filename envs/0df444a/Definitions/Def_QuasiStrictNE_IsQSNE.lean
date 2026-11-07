-- Prove2me | Definitions.Def_QuasiStrictNE_IsQSNE
-- name    : QuasiStrictNE_IsQSNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:52.999699+00:00
-- url     : https://prove2.me/theorems/1514b6ee-3d56-426a-a856-dcd9b4e5d91c
-- title:
--   Quasi-strict Nash equilibrium of a bimatrix game
-- statement:
--   For a bimatrix game $(A,B)$ with $A,B\in\mathbb R^{m\times n}$, a pair $(x^*,y^*)$ with $x^*\in\Delta_m$, $y^*\in\Delta_n$ is a **quasi-strict Nash equilibrium** when
--   $$
--   \mathrm{supp}(x^*)= BR_1(y^*)\qquad\text{and}\qquad \mathrm{supp}(y^*)= BR_2(x^*):
--   $$
--   every pure best response is played with positive probability, and only best responses are played.
--
--   Every quasi-strict equilibrium is a Nash equilibrium; Example 1 of the paper shows the converse fails.
--
--   **Formalization Note** $\Delta_k$ is Mathlib's `stdSimplex ℝ (Fin k)`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2

namespace QuasiStrictNE

/-- **Quasi-strict Nash equilibrium of a bimatrix game** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4: "A
quasi-strict Nash equilibrium further requires that supp(x∗) = BR1(y∗) and supp(y∗) = BR2(x∗)").

`IsQSNE A B x y` holds iff `x ∈ Δm`, `y ∈ Δn`, the support of `x` is exactly the set of pure best
responses of player 1 to `y`, and the support of `y` is exactly the set of pure best responses of
player 2 to `x`.

**Formalization Note** `Δk` is Mathlib's `stdSimplex ℝ (Fin k)`; supports and best-response sets are
`Finset`s of 0-based indices. -/
def IsQSNE {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin m) ∧ y ∈ stdSimplex ℝ (Fin n) ∧ supp x = BR1 A y ∧ supp y = BR2 B x

end QuasiStrictNE



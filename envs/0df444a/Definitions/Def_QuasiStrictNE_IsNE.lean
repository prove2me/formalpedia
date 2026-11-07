-- Prove2me | Definitions.Def_QuasiStrictNE_IsNE
-- name    : QuasiStrictNE_IsNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:53.646392+00:00
-- url     : https://prove2.me/theorems/757e1240-d59c-470c-978b-5c98fb11e182
-- title:
--   Nash equilibrium of a bimatrix game
-- statement:
--   For a bimatrix game $(A,B)$ with $A,B\in\mathbb R^{m\times n}$, a pair $(x^*,y^*)$ with $x^*\in\Delta_m$, $y^*\in\Delta_n$ is a **Nash equilibrium** when
--   $$
--   \mathrm{supp}(x^*)\subseteq BR_1(y^*)\qquad\text{and}\qquad \mathrm{supp}(y^*)\subseteq BR_2(x^*).
--   $$
--   Here $\Delta_k=\{z\in\mathbb R^k : z_i\ge 0,\ \sum_i z_i=1\}$ is the set of mixed strategies.
--
--   **Formalization Note** $\Delta_k$ is Mathlib's `stdSimplex ℝ (Fin k)`. The paper's support form is used.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 1, p.4

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2

namespace QuasiStrictNE

/-- **Nash equilibrium of a bimatrix game** (Hansen & Nie, *On Existence and Computational Complexity
of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 1, p.4: "A Nash equilibrium is a pair of
mixed strategies (x∗, y∗) satisfying supp(x∗) ⊆ BR1(y∗) and supp(y∗) ⊆ BR2(x∗)").

`IsNE A B x y` holds iff `x ∈ Δm`, `y ∈ Δn`, every pure strategy played with positive probability by
player 1 is a best response to `y`, and every one played by player 2 is a best response to `x`.

**Formalization Note** `Δk` is Mathlib's `stdSimplex ℝ (Fin k)` (nonnegative coordinates summing to
`1`). The paper's support form is used, not the equivalent "no profitable deviation" form. -/
def IsNE {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  x ∈ stdSimplex ℝ (Fin m) ∧ y ∈ stdSimplex ℝ (Fin n) ∧ supp x ⊆ BR1 A y ∧ supp y ⊆ BR2 B x

end QuasiStrictNE



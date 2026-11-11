-- Prove2me | Definitions.Def_PosIndexNash_PPADS_Nondegenerate
-- name    : PosIndexNash_PPADS_Nondegenerate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:31:35.775257+00:00
-- url     : https://prove2.me/theorems/c406f980-7bad-4755-909b-afcffb5f87fd
-- title:
--   Nondegenerate bimatrix game (Definition 2.2)
-- statement:
--   A **bimatrix game** is a pair of payoff matrices $A, B \in \mathbb{R}^{m\times n}$: the row player picks a mixed strategy $x \in \Delta_m$, the column player a mixed strategy $y \in \Delta_n$, where $\Delta_k = \{z \in \mathbb{R}^k_{\ge 0} : \mathbf 1^\top z = 1\}$. Write $\mathrm{supp}(z) = \{i : z_i > 0\}$, $BR_1(y) = \arg\max_{i} e_i^\top A y$ and $BR_2(x) = \arg\max_j x^\top B e_j$ for the sets of pure best responses.
--
--   The game is **nondegenerate** when no mixed strategy has more pure best responses than the size of its support:
--   $$\forall x \in \Delta_m,\ \forall y \in \Delta_n:\qquad |BR_2(x)| \le |\mathrm{supp}(x)| \quad\text{and}\quad |BR_1(y)| \le |\mathrm{supp}(y)|.$$
--
--   This is the promise of the search problem Positive-Index Nash. At every equilibrium of a nondegenerate game the two supports have equal size, so the Shapley index is defined.
--
--   **Formalization Note** The quantifiers range over all real mixed strategies (Mathlib's `stdSimplex ℝ (Fin k)`), not only rational ones. Supports and best-response sets are the public `QuasiStrictNE.supp`, `BR1`, `BR2`. A rational game is passed through the cast $\mathbb{Q} \to \mathbb{R}$.
-- source:
--   Kontogiannis, Panageas, Pollatos, Yan, Finding a Positive Index Nash Equilibrium is PPADS-Complete, arXiv:2609.23879 (held PDF, sha256 00d5c5ce…cbb6), p. 12, Definition 2.2

import Mathlib
import Definitions.Def_QuasiStrictNE_supp
import Definitions.Def_QuasiStrictNE_BR1
import Definitions.Def_QuasiStrictNE_BR2

namespace PosIndexNash.PPADS

/-- **Nondegenerate bimatrix game** (Kontogiannis, Panageas, Pollatos, Yan, *Finding a Positive
Index Nash Equilibrium is PPADS-Complete*, arXiv:2609.23879, p. 12, Definition 2.2).

The game `(A, B)` with `A, B ∈ ℝ^{m×n}` is nondegenerate iff for every mixed strategy `x ∈ Δm` of
the row player and every mixed strategy `y ∈ Δn` of the column player,
`|BR2(x)| ≤ |supp(x)|` and `|BR1(y)| ≤ |supp(y)|`.

**Formalization Note** `Δk` is Mathlib's `stdSimplex ℝ (Fin k)`: all real mixed strategies, not
only rational ones. Supports and pure best-response sets are the public `QuasiStrictNE.supp`,
`QuasiStrictNE.BR1`, `QuasiStrictNE.BR2` (`Finset`s of 0-based indices). A rational game is
passed through the cast `ℚ → ℝ`. -/
def Nondegenerate {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x ∈ stdSimplex ℝ (Fin m), ∀ y ∈ stdSimplex ℝ (Fin n),
    (QuasiStrictNE.BR2 B x).card ≤ (QuasiStrictNE.supp x).card ∧
    (QuasiStrictNE.BR1 A y).card ≤ (QuasiStrictNE.supp y).card

end PosIndexNash.PPADS



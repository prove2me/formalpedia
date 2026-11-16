-- Prove2me | Definitions.Def_SelectiveDPT_Supplement_approxSelRel
-- name    : SelectiveDPT_Supplement_approxSelRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:26:50.51927+00:00
-- url     : https://prove2.me/theorems/c60c7d17-b4d3-44a0-8d09-c3fe3de3023d
-- title:
--   $(1-\delta)$-correctness for the selective direct product $f^{(k,m)}$
-- statement:
--   Let $f \subseteq D \times Y$ be a relation, $1 \le k \le m$ and $\delta \in \mathbb R$. An output is a set of at most $k$ pairs $(i_1, y_1), \dots, (i_\ell, y_\ell) \in [m] \times Y$ with pairwise distinct copy indices $i_j$. It is **$(1-\delta)$-correct** for $f^{(k,m)}$ on the input $x = (x_1, \dots, x_m)$ iff
--   $$\big|\{\, j \in [\ell] : (x_{i_j}, y_j) \in f \,\}\big| \;\ge\; (1-\delta)\,k .$$
--
--   This relaxes the selective direct product, which asks for $k$ pairs that are all correct; it is the threshold version used in Theorem 4.11.
--
--   **Formalization Note** An output is a map from $k$ slots to optional pairs (an empty slot is an unused one). The copy indices of the pairs are pairwise distinct, as in $f^{(k,m)}$ (the proof of Theorem 4.11 orders them $i_1 < \dots < i_k$); without this the theorem fails ($m = 1$, $k = 2$, $\delta = 0$ and the same correct pair written twice).
-- source:
--   Beame–Kornerup–Whitmeyer, Strong Selective and List-Decoding Direct Product Theorems for Quantum Query Complexity, arXiv:2609.26678, Definition 4.10, p.37

import Mathlib
import Definitions.Def_SelectiveDPT_copy

namespace SelectiveDPT.Supplement

/-- `(1 − δ)`-correctness for the selective direct product `R^(k,m)` (arXiv:2609.26678,
Definition 4.10, p.37: "an algorithm `A` is `(1 − δ)`-correct at computing `f^(k,m)` on input
`x ∈ X^m` iff there is an `ℓ ≤ k`, such that `A` produces a set of pairs
`(i_1, y_1), …, (i_ℓ, y_ℓ)` and `(x_{i_j}, y_j) ∈ f` for at least `(1 − δ)k` choices of
`j ∈ [ℓ]`"), as a relation between an `m`-copy input and an output.

**Formalization Note.** An output of at most `k` pairs is a map `o : Fin k → Option (Fin m × Y)`
(the `some` entries are the pairs, `none` marks an unused slot). The copy indices of the pairs are
pairwise distinct, as for `R^(k,m)` (the proof of Theorem 4.11 orders them `i_1 < ⋯ < i_k`;
without distinctness Theorem 4.11 is false: `m = 1`, `k = 2`, `δ = 0` and the same correct pair
written twice). The count of correct pairs is compared with `(1 − δ)k` as a real number. -/
def approxSelRel {ι Y α : Type*} (k m : ℕ) (δ : ℝ) (R : (ι → α) → Y → Prop) :
    (Fin m × ι → α) → (Fin k → Option (Fin m × Y)) → Prop := by
  classical
  exact fun x o =>
    (∀ (j j' : Fin k) (i : Fin m) (y y' : Y), o j = some (i, y) → o j' = some (i, y') → j = j') ∧
    (1 - δ) * k ≤
      ((Finset.univ.filter fun j => ∃ i y, o j = some (i, y) ∧ R (copy x i) y).card : ℝ)

end SelectiveDPT.Supplement



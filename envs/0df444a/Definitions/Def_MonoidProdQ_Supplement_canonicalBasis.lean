-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_canonicalBasis
-- name    : MonoidProdQ_Supplement_canonicalBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:10:26.311294+00:00
-- url     : https://prove2.me/theorems/d5e18c29-79aa-4ae0-8460-01d518ce9fa5
-- title:
--   Canonical minimum-weight basis of weighted matroid records
-- statement:
--   Let $\mathcal M$ be a known matroid on a finite ground set $E$ and $W\subseteq\mathbb R$ a finite set of weights. The input consists of $n$ records $x_i\in(E\times W)\cup\{\bot\}$, where $x_i=(e_i,w_i)$ or $x_i=\bot$ (a null record). An index set $I\subseteq[n]$ is **independent** if all its records are nonnull, the elements $e_i$ ($i\in I$) are distinct, and $\{e_i:i\in I\}$ is independent in $\mathcal M$; repeated elements are parallel copies. The **canonical minimum-weight basis** is the output of the greedy algorithm that scans the nonnull indices in increasing order of $(w_i,i)$ and adds an index whenever the set stays independent.
--
--   Equivalently, by the rank-increase characterization of greedy bases (p.43), an index $i$ is selected iff its record is nonnull and
--
--   $$e_i\notin \operatorname{cl}\bigl(\{e_j:\ x_j\neq\bot,\ (w_j,j)<_{\mathrm{lex}}(w_i,i)\}\bigr),$$
--
--   the matroid closure of the elements of the earlier records.
--
--   **Formalization Note** Records are optional pairs (none = $\bot$), positions are $\{0,\dots,n-1\}$, and the matroid is a Mathlib matroid; the statements take its ground set to be all of $E$. The definition uses the closure characterization above, which the paper states (p.43: "e is retained exactly when the rank increases between the prefix strictly before e and the prefix ending at e"); it selects exactly the indices the greedy scan retains (a repeat of an earlier element lies in its closure, and loops are never selected).
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §6.2.2, p.44 (greedy characterization p.43)

import Mathlib

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §6.2.2, p.44: for a known matroid `M` on
`E` and a finite weight alphabet `W ⊆ ℝ`, the input is `n` records `xᵢ = (eᵢ, wᵢ) ∈ E × W` or a
null record `⊥`. "An index set I is independent if all its records are nonnull, the elements eᵢ
for i ∈ I are distinct, and {eᵢ : i ∈ I} ∈ I. … We choose a canonical answer by applying the
greedy algorithm in increasing order of (wᵢ, i)." This is that canonical minimum-weight basis,
as a set of input indices.

**Formalization Note.** A record is `Option (E × W)` (`none` = `⊥`), positions are `Fin n`. The
greedy basis is written through its rank-increase characterization (p.43: "e is retained exactly
when the rank increases between the prefix strictly before e and the prefix ending at e"): index
`i` is selected iff its record `(eᵢ, wᵢ)` is nonnull and `eᵢ` is not in the matroid closure
`cl({eⱼ : xⱼ nonnull, (wⱼ, j) < (wᵢ, i)})` of the elements of the nonnull records that precede
it in the lexicographic order of `(weight, index)`. Repeated elements are parallel copies (a
repeat of an earlier element lies in its closure) and loops are never selected. The matroid's
ground set is assumed to be all of `E` by the statements. -/
noncomputable def canonicalBasis {E : Type*} (M : Matroid E) (W : Finset ℝ) {n : ℕ}
    (x : Fin n → Option (E × W)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∃ (e : E) (w : W), x i = some (e, w) ∧
    e ∉ M.closure {e' : E | ∃ (j : Fin n) (w' : W), x j = some (e', w') ∧
      ((w' : ℝ) < w ∨ ((w' : ℝ) = w ∧ j < i))}

end MonoidProdQ.Supplement



-- Prove2me | Definitions.Def_WildeQIT_mutualInfo
-- name    : WildeQIT_mutualInfo
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:15:35.117755+00:00
-- url     : https://prove2.me/theorems/215d1155-9302-4358-9fa1-e8ff6d9d7feb
-- title:
--   Mutual information $I(X;Y)$ (Definition 10.4.1)
-- statement:
--   **Definition 10.4.1 (Mutual information).** Let $X$ and $Y$ be discrete random variables with joint probability distribution $p_{XY}(x,y)$. The mutual information $I(X;Y)$ is the marginal entropy $H(X)$ less the conditional entropy $H(X|Y)$:
--
--   $$
--   I(X;Y) \equiv H(X) - H(X|Y),
--   $$
--
--   where $H(X)=-\sum_x p_X(x)\log p_X(x)$ is the entropy of the marginal $p_X(x)=\sum_y p_{XY}(x,y)$ and $H(X|Y)=-\sum_{x,y}p_{XY}(x,y)\log\bigl(p_{XY}(x,y)/p_Y(y)\bigr)$ (Definition 10.2.1); logarithms are base $2$.
--
--   The mutual information quantifies how much uncertainty about $X$ is removed by learning $Y$; it is the classical correlation measure underlying channel capacity, and Wilde's Chapter 10 establishes its symmetry, non-negativity, and data-processing property.
--
--   **Formalization Note.** `WildeQIT.mutualInfo p` is `WildeQIT.entropy p.fst - WildeQIT.condEntropy p` for a joint distribution `p : WildeQIT.FinDist (α × β)`; here `p.fst` is the marginal of the first component and `condEntropy p` conditions the first component on the second, exactly matching $H(X)-H(X|Y)$.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Mutual Information, Definition 10.4.1, LaTeX label eq-cie:mut-info-def (book source roster-items.csv line 16541).

import Definitions.Def_WildeQIT_entropy
import Definitions.Def_WildeQIT_condEntropy

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.4.1 (Mutual information):
`I(X;Y) ≡ H(X) - H(X|Y)`.
-/

namespace WildeQIT

/-- Definition 10.4.1. The mutual information of a pair with joint distribution `p` on `α × β`:
`I(X;Y) = H(X) - H(X|Y)`, the marginal entropy of the first component less the conditional
entropy of the first component given the second. -/
noncomputable def mutualInfo {α β : Type} [Fintype α] [Fintype β] (p : FinDist (α × β)) : ℝ :=
  entropy p.fst - condEntropy p

end WildeQIT



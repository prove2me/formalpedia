-- Prove2me | Definitions.Def_WildeQIT_condMutualInfo
-- name    : WildeQIT_condMutualInfo
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:15:35.406814+00:00
-- url     : https://prove2.me/theorems/2587bd71-4ec4-49b8-9e88-4f198c4df44b
-- title:
--   Conditional mutual information $I(X;Y|Z)$ (Definition 10.6.1)
-- statement:
--   **Definition 10.6.1 (Conditional mutual information).** Let $X$, $Y$, and $Z$ be discrete random variables with joint distribution $p_{XYZ}$. The conditional mutual information is
--
--   $$
--   I(X;Y|Z) \equiv H(Y|Z) - H(Y|X,Z),
--   $$
--
--   where $H(Y|Z)$ is the conditional entropy (Definition 10.2.1) of $Y$ given $Z$ computed from the marginal $p_{YZ}(y,z)=\sum_x p_{XYZ}(x,y,z)$, and $H(Y|X,Z)$ is the conditional entropy of $Y$ given the pair $(X,Z)$ computed from $p_{XYZ}$ regrouped as the pair distribution of $\bigl(Y,(X,Z)\bigr)$. (Wilde also records the equivalent forms $H(X|Z)-H(X|Y,Z)$ and $H(X|Z)+H(Y|Z)-H(X,Y|Z)$.) Logarithms are base $2$.
--
--   The conditional mutual information measures the correlation between $X$ and $Y$ that remains once $Z$ is known; its non-negativity is the strong subadditivity of classical entropy (Theorem 10.6.1), and it drives the chain rule for mutual information and the data-processing inequality.
--
--   **Formalization Note.** `WildeQIT.condMutualInfo p`, for `p : WildeQIT.FinDist (α × β × γ)` (components $X,Y,Z$ in this order; note `α × β × γ` is `α × (β × γ)`), is `condEntropy p.margYZ - condEntropy p.groupY_XZ`, where `margYZ` is the $(Y,Z)$ marginal and `groupY_XZ` presents $p_{XYZ}$ as the pair distribution of $(Y,(X,Z))$, so that `condEntropy` (first component given second) yields $H(Y|Z)$ and $H(Y|X,Z)$ respectively. The definition uses the first of Wilde's three displayed forms; the other two are theorems.
-- source:
--   Wilde, Quantum Information Theory, 2nd ed. (Cambridge University Press, 2017; arXiv:1106.1445v8), Chapter 10 (Classical Information and Entropy), §Conditional Mutual Information, Definition 10.6.1 (book source roster-items.csv line 16720); first displayed form I(X;Y|Z) = H(Y|Z) − H(Y|X,Z).

import Definitions.Def_WildeQIT_condEntropy

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definition 10.6.1 (Conditional mutual
information): for discrete random variables `X, Y, Z`, `I(X;Y|Z) ≡ H(Y|Z) - H(Y|X,Z)`.
-/

namespace WildeQIT

/-- Definition 10.6.1. The conditional mutual information of a triple with joint distribution
`p` on `α × β × γ` (components `X, Y, Z`): `I(X;Y|Z) = H(Y|Z) - H(Y|X,Z)`, where `H(Y|Z)` is
the conditional entropy of the marginal pair `(Y,Z)` and `H(Y|X,Z)` is the conditional entropy
of `Y` given the pair `(X,Z)`. -/
noncomputable def condMutualInfo {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinDist (α × β × γ)) : ℝ :=
  condEntropy p.margYZ - condEntropy p.groupY_XZ

end WildeQIT



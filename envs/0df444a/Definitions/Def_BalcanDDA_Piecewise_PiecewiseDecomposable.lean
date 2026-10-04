-- Prove2me | Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable
-- name    : BalcanDDA_Piecewise_PiecewiseDecomposable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T05:58:04.781043+00:00
-- url     : https://prove2.me/theorems/971f9e67-32a8-4b28-b67d-067d87d4c693
-- title:
--   $(\mathcal F, \mathcal G, k)$-piecewise decomposable function class (Definition 3.2)
-- statement:
--   Let $\mathcal Y$ be a domain, $\mathcal G \subseteq \{0,1\}^{\mathcal Y}$ a class of **boundary functions**, $\mathcal F \subseteq \mathbb R^{\mathcal Y}$ a class of **piece functions**, and $k \in \mathbb N$. A function class $\mathcal H \subseteq \mathbb R^{\mathcal Y}$ is **$(\mathcal F, \mathcal G, k)$-piecewise decomposable** if for every $h \in \mathcal H$ there are $k$ boundary functions $g^{(1)}, \dots, g^{(k)} \in \mathcal G$ and, for each bit vector $\boldsymbol b \in \{0,1\}^k$, a piece function $f_{\boldsymbol b} \in \mathcal F$, such that
--   $$h(y) = f_{\boldsymbol b_y}(y) \quad\text{for all } y \in \mathcal Y, \qquad \boldsymbol b_y = \bigl(g^{(1)}(y), \dots, g^{(k)}(y)\bigr) \in \{0,1\}^k.$$
--   In words: the $k$ boundary functions cut $\mathcal Y$ into at most $2^k$ regions, and on each region $h$ agrees with one function from $\mathcal F$.
--
--   The paper applies this to the dual class $\mathcal U^*$ of a parameterized algorithm's utility functions; its main theorem bounds the pseudo-dimension of $\mathcal U$ in terms of $k$ and the complexity of $\mathcal F^*$ and $\mathcal G^*$.
--
--   **Formalization Note.** Bit vectors are `Fin k → Bool`. The same $k$ serves every $h \in \mathcal H$, and neither the boundary functions nor the piece functions need be distinct, as in the paper.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 7, Definition 3.2

import Mathlib

namespace BalcanDDA.Piecewise

/-- `(F, G, k)`-piecewise decomposability (Balcan et al., arXiv:1908.02894v4, p. 7,
Definition 3.2). A class `H ⊆ ℝ^Y` is `(F, G, k)`-piecewise decomposable for a class
`G ⊆ {0,1}^Y` of boundary functions and a class `F ⊆ ℝ^Y` of piece functions if for every
`h ∈ H` there are `k` boundary functions `g⁽¹⁾, …, g⁽ᵏ⁾ ∈ G` and a piece function `f_b ∈ F` for
each bit vector `b ∈ {0,1}^k` such that `h(y) = f_{b_y}(y)` for all `y ∈ Y`, where
`b_y = (g⁽¹⁾(y), …, g⁽ᵏ⁾(y))`. Bit vectors are `Fin k → Bool`; the same `k` serves every `h`;
neither the `g⁽ⁱ⁾` nor the `f_b` need be distinct. -/
def PiecewiseDecomposable {Y : Type*} (H : Set (Y → ℝ)) (F : Set (Y → ℝ))
    (G : Set (Y → Bool)) (k : ℕ) : Prop :=
  ∀ h ∈ H, ∃ g : Fin k → Y → Bool, (∀ i, g i ∈ G) ∧
    ∃ f : (Fin k → Bool) → Y → ℝ, (∀ b, f b ∈ F) ∧ ∀ y, h y = f (fun i => g i y) y

end BalcanDDA.Piecewise



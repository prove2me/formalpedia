-- Prove2me | Definitions.Def_PhyloCSP_Consistent
-- name    : PhyloCSP_Consistent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:25:02.063963+00:00
-- url     : https://prove2.me/theorems/350cfe2b-fbaa-4216-ad6e-8dbb8fc4ec94
-- title:
--   Consistent tree transformations
-- statement:
--   A tree transformation $F$ is **consistent** if, for every finite rooted binary tree $T$ and every nonempty $A\subseteq T_L$,
--   $$
--   F[T]{\restriction}A\ \overset{d}{=}\ F[T{\restriction}A],
--   $$
--   that is, restricting the random output to $A$ has the same law as applying $F$ to the restricted input.
--
--   For consistent transformations the guarantee $p(\varphi,F)$ depends only on the outputs on the finitely many patterns satisfying $\varphi'$ (eq. (2)); Theorem 3.2(i) shows that every transformation can be replaced by a consistent one.
--
--   **Formalization Note** Restriction is the pull-back along the inclusion $A\hookrightarrow S$; equality in distribution is equality of probability mass functions.
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Definition 3.1, p.7 (PDF p.9)

import Mathlib
import Definitions.Def_PhyloCSP_TreeTransformation

set_option autoImplicit false

namespace PhyloCSP

/-- **Consistent tree transformations (Definition 3.1).**

Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027 submission
(manuscript sha256 3444b6c0…682dac), Definition 3.1, p.7 (PDF p.9): "A tree transformation F is
consistent if, for every finite rooted binary tree T and every nonempty A ⊆ T_L,
F[T]↾A =ᵈ F[T↾A]."

The push-forward of `F[T]` under restriction to `A` equals `F[T↾A]`.

**Formalization Note.** Restriction to `A ⊆ S` is `Pattern.comap` along the inclusion
`inclEmb hA : ↥A ↪ ↥S`; equality in distribution is equality of `PMF`s. -/
def Consistent (F : TreeTransformation) : Prop :=
  ∀ (S : Finset ℕ) (T : Pattern ↥S) (A : Finset ℕ) (hA : A ⊆ S), A.Nonempty →
    (F.law S T).map (Pattern.comap (inclEmb hA)) = F.law A (T.comap (inclEmb hA))

end PhyloCSP



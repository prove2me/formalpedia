-- Prove2me | Definitions.Def_SP4Ends
-- name    : SP4Ends
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-08T05:08:12.233594+00:00
-- url     : https://prove2.me/theorems/42556d33-e4d0-4c82-acc4-50310d23c5c3
-- title:
--   Simple connectivity at infinity (Freedman's definition)
-- statement:
--   A topological space $X$ is **simply connected at infinity** if for every compact set $K\subseteq X$ there is a compact set $L\subseteq X$ with $K\subseteq L$ such that every loop in $X\setminus L$ contracts in $X\setminus K$: the loop, regarded via the inclusion $X\setminus L\hookrightarrow X\setminus K$, is homotopic relative to its base point to the constant loop. Equivalently, the inclusion-induced homomorphism
--
--   $$
--   \pi_1(X\setminus L,\,x)\longrightarrow\pi_1(X\setminus K,\,x)
--   $$
--
--   is trivial for every base point $x\in X\setminus L$.
--
--   This is the condition on ends under which Stallings (dimension $\ge5$) and Freedman (dimension $4$) characterize Euclidean space among contractible open manifolds, and the hypothesis on the ends in Freedman's proper $h$-cobordism theorem (Theorem 10.3 of his 1982 paper). No connectedness or one-endedness is built into the definition; for instance $S^3\times\mathbb R$, which has two ends, is simply connected at infinity, while $\mathbb R^2$ is not.
--
--   **Formalization Note** `SP4Ends.SimplyConnectedAtInfinity X` quantifies over compact sets `K : Set X`, produces a compact `L` together with a proof `hKL : K ⊆ L`, and requires, for every point `x` of the subtype `↥Lᶜ` and every loop `γ : Path x x` in that subtype, that `γ.map (continuous_inclusion _)` is `Path.Homotopic` (homotopic relative to end points) to `Path.refl` in the subtype `↥Kᶜ`. A loop is freely null-homotopic if and only if it is null-homotopic relative to its base point, so this agrees with the source's "every loop in $X-K_2$ contracts in $X-K_1$".
-- source:
--   Michael H. Freedman, The topology of four-dimensional manifolds, J. Differential Geom. 17 (1982), 357–453, https://doi.org/10.4310/jdg/1214437136 (scan: https://www.maths.gla.ac.uk/~mpowell/1982_The%20topology%20of%20four-dimensional%20manifolds.pdf). Section 10, Note following Theorem 10.3, p. 436: "A space X is simply connected at infinity if given any compactum K₁ ⊂ X there exists a larger compactum K₂ ⊂ X, K₁ ⊂ K₂, such that every loop in X − K₂ contracts in X − K₁. A space with more than one end, such as S³ × R, may be simply connected at infinity." See also C. R. Guilbault, Ends, shapes, and boundaries in manifold topology and geometric group theory, in: Topology and Geometric Group Theory, Springer Proc. Math. Stat. 184 (2016), 45–125, arXiv:1210.6741, Proposition 3.4.36(a) and the paragraph following it (pro-trivial fundamental group at infinity; such spaces "are called simply connected at infinity").

import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Homotopy.Path

set_option autoImplicit false

namespace SP4Ends

/-- **Simple connectivity at infinity** (Freedman 1982, note after Theorem 10.3, p. 436):
a space `X` is simply connected at infinity if for every compact set `K ⊆ X` there is a
compact set `L ⊇ K` such that every loop in `X ∖ L` contracts in `X ∖ K`. Here "contracts"
is expressed as a based null-homotopy: the loop, pushed forward along the inclusion
`X ∖ L → X ∖ K`, is path-homotopic to the constant loop at its base point; equivalently the
inclusion induces the trivial homomorphism on fundamental groups at every base point of `X ∖ L`. -/
def SimplyConnectedAtInfinity (X : Type*) [TopologicalSpace X] : Prop :=
  ∀ K : Set X, IsCompact K → ∃ L : Set X, IsCompact L ∧ ∃ hKL : K ⊆ L,
    ∀ (x : (Lᶜ : Set X)) (γ : Path x x),
      (γ.map (continuous_inclusion (Set.compl_subset_compl.mpr hKL))).Homotopic
        (Path.refl (Set.inclusion (Set.compl_subset_compl.mpr hKL) x))

end SP4Ends



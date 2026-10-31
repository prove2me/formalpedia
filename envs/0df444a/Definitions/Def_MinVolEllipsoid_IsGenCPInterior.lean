-- Prove2me | Definitions.Def_MinVolEllipsoid_IsGenCPInterior
-- name    : MinVolEllipsoid_IsGenCPInterior
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:44:45.677241+00:00
-- url     : https://prove2.me/theorems/6882363d-0231-44e9-b560-1dee7a07ca9a
-- title:
--   Interior of $\mathcal C^*(\mathcal K)$ in $\mathbb S$: the strict inequality $M\succ_{\mathcal C^*(\mathcal K)}0$
-- statement:
--   A matrix $M$ satisfies $M\succ_{\mathcal C^*(\mathcal K)}0$ (Lemma 4) when it lies in the **interior** of the cone $\mathcal C^*(\mathcal K)\subseteq\mathbb S^K$: there is $\varepsilon>0$ such that
--
--   $$
--   M+N\in\mathcal C^*(\mathcal K)\qquad\text{for every symmetric }N\text{ with }|N_{ij}|<\varepsilon\text{ for all }i,j.
--   $$
--
--   This is the Slater condition that the paper uses to obtain strong duality between the completely positive program (7) and its copositive dual (8).
--
--   **Formalization Note** The interior is taken relative to the space of symmetric matrices $\mathbb S^K$, the ambient space in which the paper defines $\mathcal C^*(\mathcal K)$ (p.5); in the space of all square matrices the interior of a set of symmetric matrices is empty. The entrywise bound describes the usual topology of the finite-dimensional space $\mathbb S^K$.
-- source:
--   Mittal & Hanasusanto, Finding Minimum Volume Circumscribing Ellipsoids Using Generalized Copositive Programming, arXiv:1807.07507v4, Lemma 4 and its proof, p.7 (int(C*(K))); interior int(S), notation, p.5

import Mathlib
import Definitions.Def_MinVolEllipsoid_GenCompletelyPositive

namespace MinVolEllipsoid

/-- **Interior of `𝒞*(𝒦)`: the strict conic inequality `M ≻_{𝒞*(𝒦)} 0`** (Mittal & Hanasusanto,
arXiv:1807.07507v4, Lemma 4 and its proof, p.7: "Consider M ∈ int(𝒞*(𝒦))"; `int(S)` is the
interior, notation, p.5).

`IsGenCPInterior C M` says that `M` is an interior point of `𝒞*(C)` within the space of symmetric
matrices: there is `ε > 0` such that `M + N ∈ 𝒞*(C)` for every symmetric `N` all of whose entries
have absolute value `< ε`.

**Formalization Note** The interior is taken relative to the symmetric matrices `𝕊ᴷ`, the ambient
space of `𝒞*(𝒦) ⊆ 𝕊ᴷ` on p.5; in the space of all matrices the interior of `𝒞*(𝒦)` would be empty.
The entrywise bound `|Nᵢⱼ| < ε` defines the usual topology of the finite-dimensional space `𝕊ᴷ`. -/
def IsGenCPInterior {ι : Type*} [Fintype ι] (C : Set (ι → ℝ)) (M : Matrix ι ι ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ N : Matrix ι ι ℝ, N.IsSymm → (∀ i j, |N i j| < ε) →
    GenCompletelyPositive C (M + N)

end MinVolEllipsoid



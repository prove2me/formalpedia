-- Prove2me | Definitions.Def_GPHigherGauge_Flatness_curvature
-- name    : GPHigherGauge_Flatness_curvature
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:28.265266+00:00
-- url     : https://prove2.me/theorems/a58913af-73db-4c8b-811a-593894c194d7
-- title:
--   The conventional curvature $F_{\mu\nu}=\partial_\mu A_\nu-\partial_\nu A_\mu+[A_\mu,A_\nu]$
-- statement:
--   Let $G$ be a real Lie group with Lie algebra $\mathfrak g$, and let $A_\mu(x)$ be the connection 1-form of a family of edge labels. Its **curvature** is
--   $$F_{\mu\nu}(x)=\partial_\mu A_\nu(x)-\partial_\nu A_\mu(x)+[A_\mu(x),A_\nu(x)]\in\mathfrak g,$$
--   where $\partial_\mu A_\nu(x)$ is the derivative of $x\mapsto A_\nu(x)$ in the direction $e_\mu$ and $[\cdot,\cdot]$ is the Lie bracket of $\mathfrak g$.
--
--   This is the conventional curvature of the connection $A$, the first part of the fake curvature of the 2-connection $(A,B)$.
--
--   **Formalization Note** The bracket is Mathlib's `GroupLieAlgebra` bracket (the bracket at $1$ of the left-invariant vector fields), written out explicitly; on a matrix group it is $XY-YX$, the convention of the paper's Baker–Hausdorff formula (3.19).
-- source:
--   Girelli, Pfeiffer, Higher gauge theory — differential versus integral formulation, arXiv:hep-th/0309173v2, §3.3, Eq. (3.23), p. 16

import Mathlib
import Definitions.Def_GPHigherGauge_Flatness_connectionOneForm

open scoped Manifold ContDiff
open VectorField

namespace GPHigherGauge.Flatness

/-- The conventional curvature `F_μν = ∂_μA_ν − ∂_νA_μ + [A_μ, A_ν]` of the connection 1-form.

Girelli, Pfeiffer, *Higher gauge theory — differential versus integral formulation*,
arXiv:hep-th/0309173v2, §3.3, Eq. (3.23), p. 16:
"F̃_µν = ∂_µA_ν − ∂_νA_µ + [A_µ, A_ν] + τ(B_µν) = F_µν + τ(B_µν), where F denotes the conventional
curvature of A."

Here `∂_μA_ν(x)` is the derivative of `x ↦ A_ν(x)` in the direction `e_μ`, and `[A_μ, A_ν]` is the
Lie bracket of `𝔤`.

**Formalization Note** The bracket is Mathlib's `GroupLieAlgebra` bracket written out as in
`GroupLieAlgebra.bracket_def`: the Lie bracket at `1` of the left-invariant vector fields of
`A_μ(x)` and `A_ν(x)` (with `lieBracket V W = DW·V − DV·W`, so `XY − YX` on a matrix group, the
convention of (3.19)). It is written explicitly so that no bracket instance of the model space
`E` can be picked up (Reading 5). `e_μ = EuclideanSpace.single μ 1`. -/
noncomputable def curvature {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [TopologicalSpace G] [ChartedSpace E G] [Group G] {n : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ → G) (μ ν : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : GroupLieAlgebra 𝓘(ℝ, E) G :=
  fderiv ℝ (connectionOneForm g ν) x (EuclideanSpace.single μ (1 : ℝ))
    - fderiv ℝ (connectionOneForm g μ) x (EuclideanSpace.single ν (1 : ℝ))
    + mlieBracket 𝓘(ℝ, E) (mulInvariantVectorField (connectionOneForm g μ x))
        (mulInvariantVectorField (connectionOneForm g ν x)) (1 : G)

end GPHigherGauge.Flatness



-- Prove2me | Definitions.Def_BrownianEnergyRep_Rotation
-- name    : BrownianEnergyRep_Rotation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:14.442039+00:00
-- url     : https://prove2.me/theorems/ed898867-1144-45c4-a2d8-56f340efb2cd
-- title:
--   Rotations $R\in O(W^*)$ and their adjoints $R^*$
-- statement:
--   A rotation of $W^*$ is an orthogonal transformation $R$ of $H$ which is a homeomorphism of $W^*$. Its adjoint $R^*$ is defined by
--   $$
--   \langle\varphi,R^*w\rangle=\langle R^{-1}\varphi,w\rangle,\qquad w\in W,\ \varphi\in W^* .
--   $$
--
--   **Formalization Note** For $R^*$ to be a map of $W$ onto itself, the homeomorphism must be one for the weak-$*$ topology, which says exactly that $R^*$ is a bounded bijection of $W$. Testing the definition on $w=j(h)$ shows it is equivalent to $R^*j=jR$, so $R^*$ extends $R$ from $H$ to $W$. This is the form stored in the structure.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Notation 5.1, p.16

import Mathlib
import Definitions.Def_BrownianEnergyRep_AbstractWienerSpace

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- A rotation `R ∈ O(W*)` with its adjoint `R*` (arXiv:1511.07378v1, Notation 5.1, p.16).

**Formalization Note** `R` is an orthogonal transformation of `H` and `R*` its adjoint,
`⟨φ, R*w⟩ = ⟨R⁻¹φ, w⟩`. For `R*` to be a map of `W`, the homeomorphism of `W*` in Notation 5.1 must
be one for the weak-* topology, which says exactly that `R*` is a bounded bijection of `W`. In terms of
`j`, the defining identity is `R* j = j R`: `R*` extends `R` from `H` to `W`. -/
structure Rotation {H W : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [MeasurableSpace W] (A : AbstractWienerSpace H W) where
  R : H ≃ₗᵢ[ℝ] H
  adj : W ≃L[ℝ] W
  adj_j : ∀ h, adj (A.j h) = A.j (R h)

end BrownianEnergyRep



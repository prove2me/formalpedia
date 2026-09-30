-- Prove2me | Definitions.Def_SP4Homology
-- name    : SP4Homology
-- status  : Definition
-- author  : @ryanshin
-- created : 2026-09-09T01:53:22.340287+00:00
-- url     : https://prove2.me/theorems/f06e8ade-01ee-480b-bbd7-8a034d316e32
-- title:
--   Integral singular homology $H_k(X;\mathbb Z)$ as an object of `ModuleCat ℤ`
-- statement:
--   For a topological space $X$ (in universe zero) and $k\ge0$, `SP4Homology.H k X` is the integral singular homology group
--
--   $$
--   H_k(X;\mathbb Z),
--   $$
--
--   the $k$-th homology of the singular chain complex of $X$ with coefficients in $\mathbb Z$, regarded as an object of the category of $\mathbb Z$-modules. This is exactly Mathlib's singular homology functor `AlgebraicTopology.singularHomologyFunctor` with coefficient object the $\mathbb Z$-module $\mathbb Z$, applied to $X$; it is functorial in $X$ and homotopy invariant. The definition exists so that homological hypotheses and conclusions about the spaces of this mission can be stated in one fixed, auditable way.
--
--   **Formalization Note** `SP4Homology.H k X : ModuleCat ℤ` is `((singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)`. Vanishing of a homology group is expressed categorically as `IsZero (SP4Homology.H k X)`, which for a module means it is the zero module.
-- source:
--   Allen Hatcher, Algebraic Topology, Cambridge University Press, 2002 (author's edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, p. 108 (definition of singular homology Hₙ(X)). Mathlib: `AlgebraicTopology.singularHomologyFunctor` (Mathlib/AlgebraicTopology/SingularHomology/Basic.lean), with homotopy invariance in Mathlib/AlgebraicTopology/SingularHomology/HomotopyInvariance.lean.

import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

set_option autoImplicit false

open CategoryTheory AlgebraicTopology

namespace SP4Homology

/-- **Integral singular homology** `H_k(X; ℤ)` of a topological space `X` (in universe zero), as
an object of `ModuleCat ℤ`: the `k`-th singular homology functor of Mathlib
(`AlgebraicTopology.singularHomologyFunctor`) with coefficients in the `ℤ`-module `ℤ`, applied to
`X` (Hatcher, *Algebraic Topology*, §2.1, p. 108). -/
noncomputable def H (k : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat.{0} ℤ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X)

end SP4Homology



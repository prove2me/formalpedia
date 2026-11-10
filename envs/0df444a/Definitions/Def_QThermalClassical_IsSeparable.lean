-- Prove2me | Definitions.Def_QThermalClassical_IsSeparable
-- name    : QThermalClassical_IsSeparable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:37.860953+00:00
-- url     : https://prove2.me/theorems/7cebee17-0549-456b-a5a7-daa575c5c090
-- title:
--   Fully separable states $\mathrm{Sep}_n$
-- statement:
--   An operator $\rho$ on $n$ qubits is **fully separable** if
--   $$
--   \rho\in\mathrm{Sep}_n=\mathrm{conv}\left\{\rho_1\otimes\cdots\otimes\rho_n:\ \rho_i\in\mathbb C^{2\times2},\ \rho_i\succeq0,\ \mathrm{Tr}\,\rho_i=1\right\}
--   $$
--   (Definition 2.1, eq. (7)): a finite convex combination of tensor products of (mixed) single-qubit states. A state that is not separable is **entangled**.
--
--   **Formalization Note** The convex hull is the plain convex hull over $\mathbb R$, with mixed single-qubit factors and no closure, exactly as in (7).
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, eq. (7), p.11

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

open scoped ComplexOrder

namespace QThermalClassical

/-- Full separability, eq. (7): `ρ ∈ Sep_n = conv{ρ_1 ⊗ ⋯ ⊗ ρ_n : ρ_i ∈ ℂ^{2×2}, ρ_i ⪰ 0,
Tr ρ_i = 1}`, the convex hull of tensor products of (mixed) single-qubit states. A state is
*entangled* when it is not separable.

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), Definition 2.1, eq. (7), p.11.

**Formalization Note.** The convex hull is the plain (finite-combination) convex hull over
`ℝ`, exactly as in (7), with no closure; the generating states are mixed. -/
def IsSeparable {Q : Type} [Fintype Q] (ρ : Op Q) : Prop :=
  ρ ∈ convexHull ℝ {σ : Op Q | ∃ ρs : Q → Matrix Bool Bool ℂ,
    (∀ q, (ρs q).PosSemidef ∧ (ρs q).trace = 1) ∧ σ = tensorOp ρs}

end QThermalClassical



-- Prove2me | Definitions.Def_ChapterNsNonlinearFarisLavine
-- name    : ChapterNsNonlinearFarisLavine
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-25T02:59:55.900338+00:00
-- url     : https://prove2.me/theorems/d417d588-bd0d-43ea-91a8-823eaf4601dd
-- title:
--   Chapter NsNonlinearFarisLavine
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNsNonlinearFarisLavine.lean`): generated def bundle for ChapterNsNonlinearFarisLavine. See BookProof/ChapterNsNonlinearFarisLavine.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNsNonlinearFarisLavine.lean

import Definitions.Def_ChapterNsKoopman
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The nonlinear Navier–Stokes Koopman generator and the Faris–Lavine criterion

The operator is the Koopman–von Neumann generator of `ChapterNsKoopman`,

```
H_NS = ½ Σ_m (π_m F_m + F_m π_m),      F_m(u) = −ν λ_m u_m + Σ_{j,k} b_{mjk} u_j u_k ,
```

with the **exact quadratic advection** `B(u,u)`: no linearization and no perturbative
splitting.  The coefficients `b_{mjk}` are the momentum-space (convolution) form of
`(u·∇)u` followed by the Leray projection.  The spatial derivative becomes the symbol `i k`, and
the product `u_j ∂_j u_m` becomes the triad convolution `Σ_{p+q=k} i (û_p · q) û_q`
(`NsAdvectionConvolution.fourier_advection_convolution`).  The only properties of the
coefficients used are the two structural identities recorded in `NsSystem`: Leray's energy
identity `Σ_m u_m B_m(u,u) = 0` and the Liouville identity `div_u B = 0`.

## The comparison operator

The Faris–Lavine criterion needs a positive `N` with `𝒟(N) ⊆ 𝒟(H)` and `±i[H,N] ≤ cN`.  The
Leray energy `E = 1 + ‖u‖²` has the right commutator, since `i[H_NS, E] = −2ν Σ λ_m u_m²` and the
advection drops out by Leray's identity (`NsKoopman.commForm_kvn_energy_bound`).  But `E` does not
dominate the first-order operator `H_NS`.  This module takes

```
N_NS := H_NS² + E = H_NS² + 1 + ‖u‖² .
```

It is positive, and its form is `⟪x, N x⟫ = ‖H x‖² + ⟪x, E x⟫ ≥ ‖x‖²`
(`nsSquareComparison_quadForm`).  It dominates `H_NS`: `‖H x‖ ≤ ‖N x‖ + ‖x‖`
(`nsSquareComparison_relBound`).  Its commutation relation with `H_NS` is exact:
`H_NS` commutes with `H_NS²`, so

```
⟪x, i[H_NS, N_NS] x⟫ = ⟪x, i[H_NS, E] x⟫ = ⟪x, (−2ν Σ λ_m u_m²) x⟫
|⟪x, i[H_NS, N_NS] x⟫| ≤ 2νΛ ⟪x, N_NS x⟫
```

(`nsSquareComparison_commForm`, `nsSquareComparison_commForm_bound`).  Here `Λ` bounds the
Stokes eigenvalues `λ_m = |k_m|²`.  All of this holds on the Gauss–polynomial core, for the full
nonlinear operator.

## The conclusion

`nsKoopman_esa_of_squareComparison_esa`: **if `N_NS` is essentially self-adjoint on the core,
then so is the nonlinear Navier–Stokes generator `H_NS`.**  The proof is the core form of
Faris–Lavine, `FarisLavine.essentiallySelfAdjointOn_of_square_comparison`.

## Honest boundary

* The one input that is **not** proved is the essential self-adjointness of `N_NS` itself
  (equivalently, since `N_NS ≥ 1`, density of `(N_NS + 1)` applied to the core).  It is carried
  as an explicit hypothesis.  This is a genuine reduction, not a proof of essential
  self-adjointness of `H_NS`.  The commutator part of Faris–Lavine is fully discharged, and what
  is left is the self-adjointness of the positive operator `N_NS`.
* Why no simpler `N` was used: a comparison operator for a first-order generator must be
  invariant under the classical flow up to a bounded exponential rate, in both time directions.
  For a polynomial `N` built from `u` and `π`, the quadratic advection makes the
  linearized flow stretch the momenta at a rate proportional to `|u|`, which is unbounded.
  So no polynomial in `u`, `π` of the harmonic-oscillator type satisfies `±i[H,N] ≤ cN`.  The
  invariant `H_NS` itself, plus the energy, is the algebraic choice that does.  This argument
  is informal and is not formalized here.
* The constant `2νΛ` depends on the largest Stokes eigenvalue kept.  With **all** Fourier modes
  (no truncation) the commutator `2ν Σ |k|² |û_k|²` is not bounded by any multiple of
  `1 + ‖u‖²`.  This reflects the fact that viscous Navier–Stokes is not well posed backward in
  time, so a unitary (two-sided) Koopman group cannot be expected in infinite dimensions.  The
  statements here are for every finite set of modes, with the exact nonlinearity on those modes.
-/

namespace BookProof.NsNonlinearFarisLavine

open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman

noncomputable section

variable {d : ℕ} (S : NsSystem d)

/-- The nonlinear Navier–Stokes generator as a map of the Gauss–polynomial core into itself. -/
def nsKoopmanCore : (polyGaussCore (d := d)) →ₗ[ℂ] (polyGaussCore (d := d)) :=
  (coreRepPoly d).op (kvnPoly S)



/-- **The comparison operator** `N_NS = H_NS² + (1 + ‖u‖²)` on the Gauss–polynomial core. -/
def nsSquareComparison : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  nsKoopmanOp S ∘ₗ nsKoopmanCore S + nsEnergyOp (d := d)

















end

end BookProof.NsNonlinearFarisLavine



-- Prove2me | Definitions.Def_LatticePrepro_Tables_Hankel
-- name    : LatticePrepro_Tables_Hankel
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:19:58.805254+00:00
-- url     : https://prove2.me/theorems/9e2644d4-caa5-4afa-b126-1639a4c2f0bb
-- title:
--   Hankel length $\ell=p(r-1)+1$ (Theorem A.7)
-- statement:
--   For natural numbers $p$ and $r$, the *Hankel length* (`hankelLen p r`) is
--   $$\ell=p\,(r-1)+1 .$$
--   In the moment reconstruction theorem, $p$ is the characteristic, $r\ge2$ is the moment parameter, and a sequence $y_0,\dots,y_{2\ell-2}$ is arranged into the $\ell\times\ell$ Hankel matrix $(y_{i+j})_{0\le i,j<\ell}$.
--
--   The length is chosen so that the Frobenius identities $y_{pk}=y_k^{\,p}$ are available for all $k<r$ (as then $pk\le\ell-1$), which forces the reconstructed coefficients into $\mathbb{F}_p$, while $r\le\ell$. In Construction A.4, with $r=B^m$, it is the size $p(B^m-1)+1$ of the polynomial matrix and of the Hankel matrix of moments.
--
--   **Formalization Note**: The bundle contains only this definition; the functionals used in the proof of Theorem A.7 are in the source module. The paper writes $\nu$ and $\kappa$ for $\ell$ and $r$.
-- source:
--   G. Weissenberg, G. Fenzi, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847), Theorem A.7 (\label{thm:moment-hankel-reconstruction}); Lean: LatticePrepro/Tables/Hankel.lean, LatticePrepro.hankelLen

import Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic

namespace LatticePrepro.Hankel end LatticePrepro.Hankel
/-!
# Moment reconstruction from a Hankel matrix (Theorem A.7)

Let `Ω` be an algebraically closed field of characteristic `p`, `r ≥ 2`, and
`ℓ = p · (r - 1) + 1`. Suppose `y_0, …, y_{2ℓ-2} ∈ Ω` satisfy the Frobenius identities
`y_{p k} = y_k ^ p` and the first `t + 1` columns of the Hankel matrix `(y_{i+j})_{i,j<ℓ}` are
linearly dependent for some `t < r`. Then there is a coefficient function `f : Ω →₀ 𝔽_p` with at
most `t` support points whose moments of order `< ℓ` are `y_0, …, y_{ℓ-1}`.

The proof follows the paper: extract a shortest linear recurrence `χ` from the first dependent
column, define the functional `ψ(f) = ∑ (f mod χ)_i y_i`, show `ψ(f^p) = ψ(f)^p` using the
Frobenius identities, deduce that `χ` has distinct roots, and read off the coefficients by
Lagrange interpolation; they lie in `𝔽_p` because they are fixed by Frobenius.

## Implementation

* `Hankel.seqFun y j` is the linear functional `f ↦ ∑ i, f_i · y (j + i)` on `Polynomial Ω`.
* `Hankel.Annihilates y ℓ χ` says `seqFun y j χ = 0` for all `j < ℓ`, i.e. the coefficients of
  `χ` give a linear recurrence valid on the first `ℓ` shifts (equivalently, a linear dependence
  among the first `deg χ + 1` columns of the Hankel matrix).
* `Hankel.psi y χ f = seqFun y 0 (f %ₘ χ)` is the functional `ψ` of the paper. It agrees with
  `seqFun y 0` on polynomials of degree `< ℓ + deg χ` (`psi_eq_seqFun`).
-/

namespace LatticePrepro

open Polynomial

/-- The Hankel length `ℓ = p · (r - 1) + 1`. -/
def hankelLen (p r : ℕ) : ℕ := p * (r - 1) + 1

open Hankel

end LatticePrepro



-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_Defs
-- name    : WeierstrassEllipticZeta_Defs
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-04T23:38:59.448285+00:00
-- url     : https://prove2.me/theorems/0f7afa64-6c3d-4386-88e2-6e679c10ccb8
-- title:
--   Canonical Weierstrass zeta series and Theorem 1 data
-- statement:
--   For a period pair $L=(\omega_1,\omega_2)$, let $\Omega=\mathbb Z\omega_1+\mathbb Z\omega_2$. Define the canonical Weierstrass zeta function by
--   $$\zeta_L(z)=\frac1z+\sum_{\lambda\in\Omega\setminus\{0\}}\left(\frac1{z-\lambda}+\frac1\lambda+\frac z{\lambda^2}\right),$$
--   and define the fixed-base-point increment
--   $$\eta_L(\omega)=\zeta_L(\omega_1/2+\omega)-\zeta_L(\omega_1/2).$$
--   For lattice periods this represents the usual quasi-period. The functions are defined as total Lean expressions; convergence and base-point independence are not assumed as axioms.
--
--   For a finite indexed family, `HasAlgebraicallyIndependentPair` means that two entries with distinct indices form an algebraically independent pair over $\mathbb Q$. The ten-entry family for the main theorem is
--   $$\bigl(g_2,g_3,\omega,\eta_L(\omega),u_1,u_2,\wp(u_1),\zeta_L(u_1),\wp(u_2),\zeta_L(u_2)\bigr).$$
--   The lattice, $\wp$, $g_2$, and $g_3$ use Mathlib's `PeriodPair` definitions. No theorem is asserted by this definition bundle.
-- source:
--   Senthil Kumar K (2026), §1, notation for Theorem 1, https://doi.org/10.1017/S001309152610145X; zeta series: NIST DLMF 23.2.5, https://dlmf.nist.gov/23.2.E5; quasi-period normalization: DLMF 23.2.11, https://dlmf.nist.gov/23.2.E11.

import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.RingTheory.AlgebraicIndependent.Basic

noncomputable section

namespace WeierstrassEllipticZeta

/-- The canonical lattice series for Weierstrass zeta (DLMF 23.2.5).
This is a total function; claims about analytic values must exclude lattice points.
Convergence and quasi-periodicity are mathematical obligations, not assumptions here. -/
def weierstrassZeta (L : PeriodPair) (z : ℂ) : ℂ :=
  1 / z + ∑' l : L.lattice,
    if l = 0 then 0 else
      1 / (z - (l : ℂ)) + 1 / (l : ℂ) + z / (l : ℂ) ^ 2

/-- A fixed-base-point increment of the canonical zeta function.
For a lattice period this is the usual quasi-period. Both base points are
outside the lattice when `ω ∈ L.lattice`. -/
def zetaQuasiPeriod (L : PeriodPair) (ω : ℂ) : ℂ :=
  weierstrassZeta L (L.ω₁ / 2 + ω) - weierstrassZeta L (L.ω₁ / 2)

/-- Two entries at distinct indices are algebraically independent over `ℚ`. -/
def HasAlgebraicallyIndependentPair {n : ℕ} (values : Fin n → ℂ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ AlgebraicIndependent ℚ ![values i, values j]

/-- The ten entries in Senthil Kumar's Theorem 1, in their displayed order. -/
def theoremOneValues (L : PeriodPair) (ω u₁ u₂ : ℂ) : Fin 10 → ℂ :=
  ![L.g₂, L.g₃, ω, zetaQuasiPeriod L ω, u₁, u₂,
    L.weierstrassP u₁, weierstrassZeta L u₁,
    L.weierstrassP u₂, weierstrassZeta L u₂]

end WeierstrassEllipticZeta



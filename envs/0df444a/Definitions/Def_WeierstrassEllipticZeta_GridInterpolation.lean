-- Prove2me | Definitions.Def_WeierstrassEllipticZeta_GridInterpolation
-- name    : WeierstrassEllipticZeta_GridInterpolation
-- status  : Definition
-- author  : @tomasz
-- created : 2026-09-07T13:09:46.929302+00:00
-- url     : https://prove2.me/theorems/85f5ff5e-5df5-463b-8087-024a7b8afda1
-- title:
--   Analytic regularization and interpolation on shifted auxiliary grids
-- statement:
--   Fix complex numbers $\omega,u_1,u_2$. For a triple of nonnegative integers $A=(A_1,A_2,A_3)$, let
--
--   $$
--   S_A=\{a_1u_1+a_2u_2+a_3\omega+u_1/2:
--              0\le a_i<A_i,\ a_i\in\mathbb Z\},
--   $$
--
--   $$
--   q_A=A_1|u_1|+A_2|u_2|+A_3|\omega|+|u_1|/2.
--   $$
--
--   Auxiliary-grid interpolation data mean the following property. Choose a nonnegative integer $T$, functions $f,G,\psi:\mathbb C\to\mathbb C$, with $G$ entire and $f,\psi$ analytic at every point of $S_A$. Suppose $G=\psi f$ in a neighborhood of each grid point and
--
--   $$
--   f^{(j)}(x)=0\qquad(x\in S_A,\ 0\le j<T).
--   $$
--
--   For all $0<r<R$ and $C\in\mathbb R$ with $q_A\le r$ and $|G(z)|\le C$ on $|z|=R$, put $N_A=TA_1A_2A_3$. Then
--
--   $$
--   |G(z)|\le C\left(\frac{2r}{R}\right)^{N_A}\qquad(|z|\le r),
--   $$
--
--   and, whenever $\rho>0$ and $|w|+\rho\le r$,
--
--   $$
--   |G^{(n)}(w)|\le\frac{n!}{\rho^n}\,C
--                      \left(\frac{2r}{R}\right)^{N_A}\qquad(n\ge0).
--   $$
--
--   The multiplier need not be nonzero. Empty grids and $T=0$ are included. This predicate records the effect of analytic regularization and interpolation once the regularized entire function and its outer-circle bound have been provided. It does not assert existence or growth estimates for a Weierstrass sigma regularizer.
-- source:
--   Supporting interface for Senthil Kumar K (2026), Section 4 equations (14)-(15) and Lemma 6, as used on the Section 5 grids after equation (29). It records the interpolation consequences of an entire regularization and an outer bound, which remain explicit inputs. https://doi.org/10.1017/S001309152610145X

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryGrids
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Analytic.Basic

noncomputable section

open scoped Topology
open Filter Metric Set

namespace WeierstrassEllipticZeta

/-- Schwarz and Cauchy estimates after analytic regularization of an auxiliary
function whose jets vanish on the shifted integer grid. -/
def AuxiliaryGridInterpolationData (ω u₁ u₂ : ℂ) : Prop :=
  ∀ (A : Fin 3 → ℕ) (T : ℕ) (f G ψ : ℂ → ℂ),
    AnalyticOnNhd ℂ G univ →
    (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, AnalyticAt ℂ f x) →
    (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, AnalyticAt ℂ ψ x) →
    (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A,
      G =ᶠ[𝓝 x] fun z => ψ z * f z) →
    (∀ x ∈ shiftedAuxiliaryGrid u₁ u₂ ω A, ∀ j < T, iteratedDeriv j f x = 0) →
    ∀ r R C : ℝ, 0 < r → r < R →
      (A 0 : ℝ) * ‖u₁‖ + (A 1 : ℝ) * ‖u₂‖ +
        (A 2 : ℝ) * ‖ω‖ + ‖u₁‖ / 2 ≤ r →
      (∀ z ∈ sphere (0 : ℂ) R, ‖G z‖ ≤ C) →
      (∀ z : ℂ, ‖z‖ ≤ r → ‖G z‖ ≤ C * (2 * r / R) ^ (T * ∏ i, A i)) ∧
      ∀ (w : ℂ) (ρ : ℝ), 0 < ρ → ‖w‖ + ρ ≤ r → ∀ n : ℕ,
        ‖iteratedDeriv n G w‖ ≤
          n.factorial * (C * (2 * r / R) ^ (T * ∏ i, A i)) / ρ ^ n

end WeierstrassEllipticZeta



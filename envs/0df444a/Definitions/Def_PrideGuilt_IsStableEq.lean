-- Prove2me | Definitions.Def_PrideGuilt_IsStableEq
-- name    : PrideGuilt_IsStableEq
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:55:30.07698+00:00
-- url     : https://prove2.me/theorems/3d1bb40e-199b-49c6-ac40-21dce200789e
-- title:
--   Stable equilibrium of the recycling rate (Definition 1)
-- statement:
--   Fix the pride and guilt parameters $\gamma_P,\gamma_G$ and the reward $f$. A recycling rate $\tau$ is a **stable equilibrium** if one of the following holds:
--
--   1. $\tau=1$ and $U_N(1)<U_R(f,1)$;
--   2. $\tau=0$ and $U_N(0)>U_R(f,0)$;
--   3. $0<\tau<1$, $U_N(\tau)=U_R(f,\tau)$, and $U_N'(\tau)>U_R'(f,\tau)$, where the primes are derivatives with respect to $\tau$.
--
--   Cases 1 and 2 are the boundary equilibria (everyone recycles, nobody recycles); case 3 is an interior equilibrium at which consumers are indifferent and a small perturbation is pushed back. Lemma 1 identifies the stable equilibria for every reward.
--
--   **Formalization Note** The derivatives are taken of $t\mapsto U_N(t)$ and $t\mapsto U_R(f,t)$ at $\tau$, as on the page; since both utilities are affine in $\tau$ they equal $-\gamma_G$ and $-\gamma_P$. Each case forces $\tau\in[0,1]$.
-- source:
--   W. Huang, J. Nguyen, C.-L. Tseng, W. Chen, S. N. Kirshner, Pride or Guilt? Impacts of Consumers' Socially Influenced Recycling Behaviors on Closed-Loop Supply Chains, Manufacturing & Service Operations Management 26(6) (2024), doi:10.1287/msom.2023.0721 (accepted manuscript, printed page = PDF page - 1), Definition 1, p.8

import Mathlib
import Definitions.Def_PrideGuilt_UR
import Definitions.Def_PrideGuilt_UN

namespace PrideGuilt

/-- **Definition 1 (stable equilibrium).**
Huang–Nguyen–Tseng–Chen–Kirshner, *Pride or Guilt?*, M&SOM 26(6) (2024), doi:10.1287/msom.2023.0721, Definition 1, p.8 (PDF 9).

For the reward `f`, a recycling rate `τ` is a stable equilibrium if one of
(i) `τ = 1` and `U_N|_{τ=1} < U_R|_{τ=1}`;
(ii) `τ = 0` and `U_N|_{τ=0} > U_R|_{τ=0}`;
(iii) `0 < τ < 1`, `U_N|_τ = U_R|_τ` and `U'_N|_τ > U'_R|_τ`, the primes being derivatives in `τ`.

**Formalization Note.** The derivatives are `deriv` of `t ↦ U_N(t)` and `t ↦ U_R(f, t)` at `τ`,
as on the page (both functions are affine, so they equal `−γ_G` and `−γ_P`). The requirement
`τ ∈ [0, 1]` is implied by each of the three cases. -/
def IsStableEq (P : Params) (γP γG f τ : ℝ) : Prop :=
  (τ = 1 ∧ UN P γG 1 < UR P γP f 1) ∨
  (τ = 0 ∧ UN P γG 0 > UR P γP f 0) ∨
  (0 < τ ∧ τ < 1 ∧ UN P γG τ = UR P γP f τ ∧
    deriv (fun t => UN P γG t) τ > deriv (fun t => UR P γP f t) τ)

end PrideGuilt



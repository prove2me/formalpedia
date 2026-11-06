-- Prove2me | Definitions.Def_GeomDRSub_upperPt
-- name    : GeomDRSub_upperPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:14.287801+00:00
-- url     : https://prove2.me/theorems/c2d6a978-15f3-426d-ab50-4bfb053f1c97
-- title:
--   Upper-path point $u_{i,s}$
-- statement:
--   Write $p=h_\zeta(x)$. The upper path starts at $U^0=\mathbf 1$ and processes the coordinates in the order $\pi$: $U^k=U^{k-1}-(1-p_{\pi(k)})e_{\pi(k)}$. For $i=\pi(k)$ and $s\in[0,1]$,
--   $$
--   u_{i,s}=U^{k-1}-s(1-p_i)e_i .
--   $$
--   Coordinatewise, $u_{i,s}$ has value $p_j$ at every coordinate $j$ processed before $i$, value $1-s(1-p_i)$ at $i$, and $1$ at the coordinates processed after $i$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eqs. (13)–(14)

import Mathlib
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_Before

namespace GeomDRSub

open Classical in
/-- **The upper-path point `u_{i,s}`** of Eqs. (13)–(14). Aggarwal–Lu, arXiv:2610.00545,
Section 4.1, p.10: with `p = h_ζ(x)`, `U⁰ = 1`, `Uᵏ = Uᵏ⁻¹ − (1 − p_{π(k)}) e_{π(k)}`, and for
`i = π(k)` and `s ∈ [0,1]`, `u_{i,s} = Uᵏ⁻¹ − s(1 − pᵢ) eᵢ`.

Since `Uᵏ⁻¹` has coordinate `pⱼ` on the coordinates processed before `i` and `1` elsewhere (p.10),
`u_{i,s}` has coordinate `pⱼ` if `j` is processed before `i`, `1 − s(1 − pᵢ)` if `j = i`, and `1`
otherwise.

**Formalization Note.** The processing order is `Before ζ x` (ties by increasing index). -/
noncomputable def upperPt {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (s : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    if Before ζ x j i then hAct ζ x j else if j = i then 1 - s * (1 - hAct ζ x i) else 1)

end GeomDRSub



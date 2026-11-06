-- Prove2me | Definitions.Def_GeomDRSub_lowerPt
-- name    : GeomDRSub_lowerPt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:12:57.255481+00:00
-- url     : https://prove2.me/theorems/60073fb1-afce-4271-8a68-d37961341f2a
-- title:
--   Lower-path point $\ell_{i,s}$
-- statement:
--   Write $p=h_\zeta(x)$. The lower path starts at $L^0=\mathbf 0$ and processes the coordinates in the order $\pi$: $L^k=L^{k-1}+p_{\pi(k)}e_{\pi(k)}$. For $i=\pi(k)$ and $s\in[0,1]$,
--   $$
--   \ell_{i,s}=L^{k-1}+s\,p_i e_i .
--   $$
--   Coordinatewise, $\ell_{i,s}$ has value $p_j$ at every coordinate $j$ processed before $i$, value $s p_i$ at $i$, and $0$ at the coordinates processed after $i$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Section 4.1, p.10, Eqs. (13)–(14)

import Mathlib
import Definitions.Def_GeomDRSub_hAct
import Definitions.Def_GeomDRSub_Before

namespace GeomDRSub

open Classical in
/-- **The lower-path point `ℓ_{i,s}`** of Eqs. (13)–(14). Aggarwal–Lu, arXiv:2610.00545,
Section 4.1, p.10: with `p = h_ζ(x)`, `L⁰ = 0`, `Lᵏ = Lᵏ⁻¹ + p_{π(k)} e_{π(k)}`, and for `i = π(k)`
and `s ∈ [0,1]`, `ℓ_{i,s} = Lᵏ⁻¹ + s pᵢ eᵢ`.

Since `Lᵏ⁻¹` has coordinate `pⱼ` on the coordinates processed before `i` and `0` elsewhere (p.10),
`ℓ_{i,s}` has coordinate `pⱼ` if `j` is processed before `i`, `s pᵢ` if `j = i`, and `0` otherwise.

**Formalization Note.** The processing order is `Before ζ x` (ties by increasing index). -/
noncomputable def lowerPt {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) (s : ℝ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    if Before ζ x j i then hAct ζ x j else if j = i then s * hAct ζ x i else 0)

end GeomDRSub



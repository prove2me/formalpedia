-- Prove2me | Definitions.Def_BNCovPack_Routing_Potential
-- name    : BNCovPack_Routing_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T18:54:31.140583+00:00
-- url     : https://prove2.me/theorems/628d27d1-10cb-49ce-9c69-1216a493ccfe
-- title:
--   The online potential $ hi =  hi_1 +  hi_2$ and the rounding scale $B$ (Section 5.2)
-- statement:
--   Let $E$ be a non-empty finite set of $m$ edges with capacities $u(e) > 0$, and let $u(\min) = \min_e u(e)$. The **rounding scale** is
--
--   $$
--   B = \exp\Big(1 + \frac{\ln(2m)}{u(\min)}\Big) - 1 .
--   $$
--
--   For a state of the online routing algorithm, write $T = \sum_{r_i}\sum_{P} f(r_i,P)$ for the total fractional flow, $L_e = \sum_{P \ni e}\sum_{r_i} f(r_i,P)$ for the fractional load of edge $e$, $\chi(e)$ for the number of chosen integral paths that use $e$, and $s = \sum_{r_i} \chi(r_i)$ for the number of served requests. The **potential** is $\Phi = \Phi_1 + \Phi_2$ with
--
--   $$
--   \Phi_1 = \frac12 \exp\Big(\frac{T}{2B} - \ln 2 \cdot s\Big), \qquad \Phi_2 = \frac{1}{2m} \sum_{e \in E} \exp\Big(\Big(1 + \frac{\ln(2m)}{u(e)}\Big)\chi(e) - L_e\Big).
--   $$
--
--   It is the online version of the pessimistic estimator for randomized rounding of multicommodity flows; the algorithm serves a request on a path only when doing so does not increase $\Phi$.
--
--   **Formalization Note** $\Phi$ is a function of the numbers $B, T, L, \chi, s$; the algorithm feeds it its current state. All logarithms are natural.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 15, Section 5.2, definition of Φ1, Φ2 and B

import Mathlib

namespace BNCovPack.Routing

/-- `u(min) = min_e u(e)`, the minimum edge capacity (p. 15). -/
noncomputable def uMin {E : Type*} [Fintype E] [Nonempty E] (u : E → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty u

/-- The rounding scale `B = exp(1 + ln(2m)/u(min)) − 1` of §5.2 (p. 15), where `m = |E|` is the
number of edges. -/
noncomputable def roundingScale {E : Type*} [Fintype E] [Nonempty E] (u : E → ℝ) : ℝ :=
  Real.exp (1 + Real.log (2 * (Fintype.card E : ℝ)) / uMin u) - 1

/-- The online potential `Φ = Φ₁ + Φ₂` of §5.2 (p. 15), as a function of the rounding scale `B`,
the total fractional flow `T = ∑_{r_i} ∑_P f(r_i, P)`, the edge loads `L e = ∑_{P ∋ e} ∑_{r_i}
f(r_i, P)`, the integral edge usage `χ e = χ(e)` (number of chosen paths using `e`) and the
number `s = ∑_{r_i} χ(r_i)` of served requests:

`Φ₁ = (1/2) exp(T/(2B) − ln 2 · s)`,
`Φ₂ = (1/(2m)) ∑_{e ∈ E} exp((1 + ln(2m)/u(e)) χ(e) − L e)`, with `m = |E|`. -/
noncomputable def potential {E : Type*} [Fintype E] (u : E → ℝ) (B T : ℝ) (L : E → ℝ)
    (χ : E → ℕ) (s : ℕ) : ℝ :=
  (1 / 2) * Real.exp (T / (2 * B) - Real.log 2 * (s : ℝ)) +
    (1 / (2 * (Fintype.card E : ℝ))) *
      ∑ e, Real.exp ((1 + Real.log (2 * (Fintype.card E : ℝ)) / u e) * (χ e : ℝ) - L e)

end BNCovPack.Routing



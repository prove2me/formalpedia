-- Prove2me | Definitions.Def_ScarceIdeas_hjbBracket
-- name    : ScarceIdeas_hjbBracket
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:15:53.468343+00:00
-- url     : https://prove2.me/theorems/4d82528a-619f-4f7c-9f48-82e416fd91e4
-- title:
--   Bracket of the HJB equation (19)/(41)
-- statement:
--   For a state $\phi$, a value $w$, a slope $w'$ and a reward $p$,
--
--   $$\mathcal H(\phi,w,w',p)=m_1(\phi)\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)\,dc-\bigl(r+m_1(\phi)F(p)\bigr)w+w'F(p).$$
--
--   With $w=V(\phi)$ and $w'=dV/d\phi$ this is the expression maximised in the HJB equation (19)/(41), the last term being $\frac{dV}{d\phi}\frac{d\phi}{dt}$ with $\frac{d\phi}{dt}=F(p)$.
-- source:
--   Basov, Erkal, Minehart, Scotchmer, Scarcity of Ideas and Optimal R&D Policy, SSRN 4628270, §4.2, (19), p.22; Appendix, (41)–(42), p.37

import Mathlib
import Definitions.Def_ScarceIdeas_moment
import Definitions.Def_ScarceIdeas_costCDF

namespace ScarceIdeas

/-- **The bracket of the Hamilton–Jacobi–Bellman equation (19)/(41).**
Basov, Erkal, Minehart, Scotchmer, *Scarcity of Ideas and Optimal R&D Policy*, SSRN 4628270,
§4.2, (19), p.22, and Appendix, proof of Theorem 3, (41)–(42), p.37.

For a state `ϕ`, a value `w` (standing for `V(ϕ)`), a slope `w'` (standing for `dV/dϕ`) and a
reward `p`,

$$\mathcal H(\phi,w,w',p)=m_1(\phi)\int_{\underline c}^{p}\Bigl(\frac vr-c\Bigr)f(c)\,dc
-\bigl(r+m_1(\phi)F(p)\bigr)\,w+w'\,F(p),$$

the last term being `(dV/dϕ)(dϕ/dt)` with `dϕ/dt = F(p)` by (42).

**Formalization Note** `w` and `w'` are plain real arguments; the theorems substitute the value
function and its derivative. -/
noncomputable def hjbBracket (r v cL : ℝ) (f h0 : ℝ → ℝ) (ϕ w w' p : ℝ) : ℝ :=
  moment h0 1 ϕ * (∫ c in cL..p, (v / r - c) * f c) - (r + moment h0 1 ϕ * costCDF cL f p) * w +
    w' * costCDF cL f p

end ScarceIdeas



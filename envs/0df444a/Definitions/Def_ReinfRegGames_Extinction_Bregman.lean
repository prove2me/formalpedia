-- Prove2me | Definitions.Def_ReinfRegGames_Extinction_Bregman
-- name    : ReinfRegGames_Extinction_Bregman
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T09:16:24.599166+00:00
-- url     : https://prove2.me/theorems/f2f29523-41e2-468d-b445-68d5452116f2
-- title:
--   (C.3)–(C.5), pp. 33–34 — one-sided derivatives, the Bregman divergence $D_h$ and the set $\Delta_p$
-- statement:
--   Let $\Delta$ be the simplex over a finite set $B$, $h:\Delta\to\mathbb R$ a function and $p\in\Delta$.
--
--   1. **The set $\Delta_p$ (C.5).** $\Delta_p=\{x\in\Delta:\ x_\alpha>0 \text{ whenever } p_\alpha>0\}$ is the set of points of $\Delta$ whose support contains the support of $p$; it is the union of the relative interiors of the faces of $\Delta$ that contain $p$.
--   2. **One-sided derivative (C.3).** For $x,z$, the statement "$h'(x;z)=d$" means that the real number $d$ is the limit
--   $$
--   h'(x;z)=\lim_{t\to0^+}\frac{h(x+tz)-h(x)}{t}.
--   $$
--   3. **Bregman divergence (C.4).** With $z=p-x$, $D_h(p,x)=h(p)-h(x)-h'(x;p-x)$. When $h'(x;p-x)=-\infty$ the page sets $D_h(p,x)=+\infty$.
--
--   The Bregman divergence (C.4) is defined at boundary points of the simplex where $h$ has no gradient; it is the quantity that the Fenchel coupling equals on $\Delta_p$ (Proposition C.3).
--
--   **Formalization Note** The one-sided derivative is a predicate `HasOneSidedDeriv h x z d` asserting convergence to a real number $d$, so $D_h(p,x)$ appears in statements as $h(p)-h(x)-d$ for a $d$ satisfying the predicate. The page's value $+\infty$ corresponds to the case where no real $d$ exists; it is not represented as a real number (a `limUnder` would assign it a junk value). For $x,p\in\Delta$ the points $x+t(p-x)$, $t\in[0,1]$, lie in $\Delta$, so the limit only uses values of $h$ on $\Delta$.
-- source:
--   Mertikopoulos & Sandholm, Learning in games via reinforcement and regularization, arXiv:1407.6267v2, pp. 33–34, (C.3), (C.4), (C.5)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_ReinfRegGames_Extinction_Model

namespace ReinfRegGames.Extinction

open Filter Topology

/-- The set `Δ_p` of (C.5) (arXiv:1407.6267v2, p. 34): the points `x` of the simplex `Δ(B)`
whose support contains the support of `p`, i.e. `x_α > 0` whenever `p_α > 0`. -/
def deltaP {B : Type*} [Fintype B] (p : B → ℝ) : Set (B → ℝ) :=
  {x | x ∈ stdSimplex ℝ B ∧ ∀ α, 0 < p α → 0 < x α}

/-- `HasOneSidedDeriv h x z d`: the one-sided directional derivative
`h′(x; z) = lim_{t → 0⁺} t⁻¹ [h(x + t z) − h(x)]` of (C.3) (p. 33) exists and equals the real
number `d`. The Bregman divergence (C.4) is then `D_h(p, x) = h(p) − h(x) − d` with `z = p − x`;
the case `h′(x; p − x) = −∞` (where the page sets `D_h(p, x) = +∞`) is the case in which no real
`d` satisfies the predicate. -/
def HasOneSidedDeriv {B : Type*} (h : (B → ℝ) → ℝ) (x z : B → ℝ) (d : ℝ) : Prop :=
  Tendsto (fun t : ℝ => (h (x + t • z) - h x) / t) (𝓝[>] 0) (𝓝 d)

end ReinfRegGames.Extinction



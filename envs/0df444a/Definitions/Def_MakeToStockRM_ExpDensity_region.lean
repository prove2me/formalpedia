-- Prove2me | Definitions.Def_MakeToStockRM_ExpDensity_region
-- name    : MakeToStockRM_ExpDensity_region
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T11:35:43.264147+00:00
-- url     : https://prove2.me/theorems/23561cf2-e5f1-44d5-ac05-683268100503
-- title:
--   The region $\Omega$ between the rejection and idleness boundaries, (34)
-- statement:
--   Let $y_{\min}<y_{\max}$ be the bounds of the log-price, and let $\eta,\xi:\mathbb R\to\mathbb R$ be the **rejection boundary** $x=\eta(y)$ (orders are rejected when the inventory falls to it) and the **idleness boundary** $x=\xi(y)$ (production stops when the inventory rises to it). The region of the control problem is
--
--   $$
--   \Omega=\{(x,y):\ y_{\min}<y<y_{\max}\ \text{and}\ \eta(y)<x<\xi(y)\}.
--   $$
--
--   Its boundary $\partial\Omega$ consists of four pieces (35): $\partial\Omega^\eta$ on $x=\eta(y)$, $\partial\Omega^\xi$ on $x=\xi(y)$, $\partial\Omega^{\min}$ on $y=y_{\min}$ and $\partial\Omega^{\max}$ on $y=y_{\max}$. In the paper's Figure 2, $\eta$ is the lower curve (backorders side) and $\xi$ the upper one.
--
--   **Formalization Note** Points are pairs $(x,y)\in\mathbb R\times\mathbb R$ with $x$ first. The definition places no condition on $\eta,\xi$; the theorems assume $y_{\min}<y_{\max}$, $\eta,\xi$ continuous (or $C^1$) and $\eta(y)<\xi(y)$ on $[y_{\min},y_{\max}]$, so that $\Omega$ is a nonempty bounded open set.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 866, §4.1, eqs. (33)–(35) and Figure 2

import Mathlib

namespace MakeToStockRM.ExpDensity

/-- The region `Ω = {(x, y) : y_min < y < y_max, η(y) < x < ξ(y)}` of (34)
(Caldentey–Wein 2006, p. 866): points are `(x, y)` with `x` the inventory and `y` the log-price;
`η` is the rejection (lower) boundary and `ξ` the idleness (upper) boundary. -/
def region (η ξ : ℝ → ℝ) (ymin ymax : ℝ) : Set (ℝ × ℝ) :=
  {z | ymin < z.2 ∧ z.2 < ymax ∧ η z.2 < z.1 ∧ z.1 < ξ z.2}

end MakeToStockRM.ExpDensity



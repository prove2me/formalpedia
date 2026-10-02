-- Prove2me | Definitions.Def_TeschlODE_Horseshoe_horseshoeItinerary
-- name    : TeschlODE_Horseshoe_horseshoeItinerary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T05:58:34.613185+00:00
-- url     : https://prove2.me/theorems/01f5cb0c-8cbd-48e8-86fa-b43d4c0fc80c
-- title:
--   The two-sided itinerary map $\varphi : \Lambda \to \Sigma_2$ of the horseshoe (13.9)
-- statement:
--   For a horseshoe map $F$ with inverse $g$ (13.5)–(13.6), the **itinerary** of $(x, y) \in \Lambda$ is the doubly infinite sequence
--   $$\varphi(x, y)_n = \begin{cases} y_n, & n \ge 0, \ x_{-n-1}, & n < 0, \end{cases}$$
--   where $y_n \in \{0,1\}$ is defined by $F^n(x, y) \in J_{y_n}$ and $x_n \in \{0,1\}$ by $g^n(x, y) \in K_{x_n}$.
--
--   **Formalization Note.** Written as "$0$ if the iterate lies in $J_0$ (resp. $K_0$), else $1$". On $\Lambda$ every iterate lies in $J_0 \cup J_1$ (resp. $K_0 \cup K_1$) and the two strips are disjoint for $\mu > 2$, $\lambda < 1/2$, so this is the book's rule. $\varphi$ takes the horseshoe map $F$ as an argument.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), pp. 332–333, §13.1, Eq. (13.9)

import Mathlib
import Definitions.Def_TeschlODE_Horseshoe_horseshoeInv

namespace TeschlODE.Horseshoe

/-- Teschl, §13.1, pp. 332–333, (13.9): the itinerary map `ϕ : Λ → Σ₂ = {0, 1}^ℤ` of the
horseshoe map `F`, `ϕ(x, y)ₙ = yₙ` for `n ≥ 0` and `ϕ(x, y)ₙ = x₋ₙ₋₁` for `n < 0`, where `yₙ` is
defined by `Fⁿ(x, y) ∈ J_{yₙ}` (`J₀ = [0, 1] × [0, 1/µ]`) and `xₙ` by `gⁿ(x, y) ∈ K_{xₙ}`
(`K₀ = [0, λ] × [0, 1]`), `g` the inverse (13.5)–(13.6). Written as "`0` if in `J₀` (resp. `K₀`),
else `1`", which is the book's rule on `Λ`, where every iterate lies in `J₀ ∪ J₁` (resp.
`K₀ ∪ K₁`) and the two strips are disjoint. -/
noncomputable def horseshoeItinerary (lam μ : ℝ) (F : ℝ × ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℤ → Fin 2 :=
  fun n =>
    if 0 ≤ n then
      (if F^[n.toNat] p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (1 / μ) then 0 else 1)
    else
      (if (horseshoeInv lam μ)^[(-n - 1).toNat] p ∈ Set.Icc (0 : ℝ) lam ×ˢ Set.Icc (0 : ℝ) 1
        then 0 else 1)

end TeschlODE.Horseshoe



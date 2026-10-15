-- Prove2me | Definitions.Def_StallEconomy_TripLength_Setting
-- name    : StallEconomy_TripLength_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:44.964823+00:00
-- url     : https://prove2.me/theorems/db6f3712-a46a-464d-9c6f-ff73385901cc
-- title:
--   §3.2–§3.3, pp. 9–13, 44, 49–51 — diamond service zone, inner diamond, Manhattan distance, trip length L_r, uniform expectation, 𝔼[L_r] and Var(L_r)
-- statement:
--   This file fixes the probabilistic model of the within-radius repositioning trip of a mobile stall (Cao and Qi, *Stall Economy*, §3.2–§3.3 and the proofs of Propositions 1 and 3 in Appendix B).
--
--   **Service zone.** A stall serves a square service zone rotated by $45^\circ$ (a "diamond") with edge length $R>0$ in the Euclidean norm; the paper takes $R = R(\rho) = 1/\sqrt{\rho}$ for stall density $\rho$. In Manhattan coordinates centred at the middle of the zone,
--   $$\mathcal Z_R = \{(x,y)\in\mathbb R^2 : |x|+|y| \le R/\sqrt2\},$$
--   a set of area $R^2$.
--
--   **Inner diamond.** For a walking radius $0\le r\le R/\sqrt2$, the inner diamond lying $r$ inward from the boundary is
--   $$\mathcal I_{R,r} = \{(x,y) : |x|+|y| \le R/\sqrt2 - r\},$$
--   a diamond of edge length $R-\sqrt2\,r$. It is the image of $\mathcal Z_R$ under multiplication by the scale factor $s_{R,r} = 1-\sqrt2\,r/R \in [0,1]$; at $r = R/\sqrt2$ it is the single centre point.
--
--   **Distances.** Trip lengths are measured in the $\ell_1$ (Manhattan) metric, $|A-B| = |a_1-b_1|+|a_2-b_2|$. When the stall is at $A$ and the next customer at $B$, and the customer walks up to $r$ to meet the stall, the stall's repositioning trip length is
--   $$L_r(A,B) = \max\{|A-B| - r,\ 0\}.$$
--
--   **The law.** The stall's position $A$ is uniform on the inner diamond $\mathcal I_{R,r}$ and the customer's position $B$ is uniform on the zone $\mathcal Z_R$, independently. For a function $F$ of the pair,
--   $$\mathbb E[F(A,B)] = \frac{1}{R^4}\int_{\mathcal Z_R}\int_{\mathcal Z_R} F(s_{R,r}\,u,\ b)\,db\,du,$$
--   that is, $A = s_{R,r}U$ with $U$ uniform on $\mathcal Z_R$. For $r<R/\sqrt2$ this is the joint density $1/(R^2(R-\sqrt2 r)^2)$ on $\mathcal I_{R,r}\times\mathcal Z_R$ used in the paper. Finally
--   $$\mathbb E[L_r] \quad\text{and}\quad \operatorname{Var}(L_r) = \mathbb E[L_r^2]-\mathbb E[L_r]^2$$
--   are defined from this expectation. At $r=0$ the scale factor is $1$, and $A$, $B$ are two independent uniform points of the zone (the door-to-door case of Proposition 1).
--
--   These objects are shared by every statement of the mission: Proposition 1, the intermediate moments of the proof of Proposition 3, and Proposition 3 itself.
--
--   **Formalization Note.** Points are elements of `ℝ × ℝ` with Lebesgue measure. `zone R`, `innerZone R r`, `shrink R r`, `l1`, `Lr r`, `E R r F`, `meanL R r` and `varL R r` are the objects above. The stall's uniform law is realised as the push-forward of the uniform law on `zone R` under `u ↦ shrink R r • u`, which keeps the closed range $0\le r\le R/\sqrt2$ without dividing by $(R-\sqrt2r)^2$; `innerZone` is not used by the expectation and documents the image. Every statement using `E` assumes $R>0$; all integrands used are bounded and measurable on the bounded zone, so the integrals are genuine.
-- source:
--   Cao, Qi, Stall Economy: The Value of Mobility in Retail on Wheels, SSRN 3711896 (manuscript), p. 9 (l1 metric), p. 11 (edge length R(ρ) = 1/√ρ), p. 13 (inner diamond), p. 44 (proof of Proposition 1), pp. 49–51 (proof of Proposition 3: L_r = max{L′₀ − r, 0}, joint density, Var(L_r) = 𝔼[L_r²] − 𝔼[L_r]²)

import Mathlib
open MeasureTheory

namespace StallEconomy.TripLength

/-- The service zone of one stall (Cao–Qi, p. 44: "a squared diamond service zone with the edge
length of `R`"), in centred Manhattan coordinates: the diamond `|x| + |y| ≤ R / √2`. Its edge
length in the Euclidean norm is `R` and its area is `R²`. -/
def zone (R : ℝ) : Set (ℝ × ℝ) := {p | |p.1| + |p.2| ≤ R / Real.sqrt 2}

/-- The inner diamond, `r` inward from the boundary of the zone (p. 13; edge length `R − √2 r`,
p. 49): `|x| + |y| ≤ R / √2 − r`. For `0 ≤ r ≤ R / √2` it is the image of `zone R` under
multiplication by `shrink R r`. -/
def innerZone (R r : ℝ) : Set (ℝ × ℝ) := {p | |p.1| + |p.2| ≤ R / Real.sqrt 2 - r}

/-- The scale factor `1 − √2 r / R` carrying `zone R` onto `innerZone R r`. -/
noncomputable def shrink (R r : ℝ) : ℝ := 1 - Real.sqrt 2 * r / R

/-- The Manhattan (`l₁`) distance between two points of the plane (p. 9). -/
def l1 (a b : ℝ × ℝ) : ℝ := |a.1 - b.1| + |a.2 - b.2|

/-- The within-radius repositioning trip length (p. 49): `L_r = max {|A − B| − r, 0}`, for the
stall at `a` and the customer at `b`, with `|A − B|` the Manhattan distance. -/
noncomputable def Lr (r : ℝ) (a b : ℝ × ℝ) : ℝ := max (l1 a b - r) 0

/-- Expectation of `F(A, B)` when the stall `A` is uniform on the inner diamond `innerZone R r`
and the customer `B` is uniform on `zone R`, independently. `A` is realised as
`shrink R r • U` with `U` uniform on `zone R`; each uniform law has density `1 / R²`. -/
noncomputable def E (R r : ℝ) (F : ℝ × ℝ → ℝ × ℝ → ℝ) : ℝ :=
  (1 / R ^ 4) * ∫ u in zone R, ∫ b in zone R, F (shrink R r • u) b

/-- The mean repositioning trip length `𝔼[L_r]`. -/
noncomputable def meanL (R r : ℝ) : ℝ := E R r (Lr r)

/-- The variance `Var(L_r) = 𝔼[L_r²] − 𝔼[L_r]²` (p. 51). -/
noncomputable def varL (R r : ℝ) : ℝ := E R r (fun a b => Lr r a b ^ 2) - meanL R r ^ 2

end StallEconomy.TripLength



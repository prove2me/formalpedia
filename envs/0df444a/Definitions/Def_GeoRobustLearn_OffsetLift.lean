-- Prove2me | Definitions.Def_GeoRobustLearn_OffsetLift
-- name    : GeoRobustLearn_OffsetLift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:20.99613+00:00
-- url     : https://prove2.me/theorems/c0209f7e-3e00-44e2-9b2c-730c1a67de41
-- title:
--   Spatial and offset coordinates, the signed distance $\mathrm{sdist}_f$ and the offset lift $B_f$
-- statement:
--   Points of $\mathbb R^{d+1}$ are written $(x,a)\in\mathbb R^d\times\mathbb R$, with $x$ the **spatial** coordinates and $a$ the **offset** coordinate. For a Boolean $f$ on $\mathbb R^d$, the **signed distance** is
--
--   $$\mathrm{sdist}_f(x)=\begin{cases}\operatorname{dist}(x,f^{-1}(0)),& f(x)=1,\\ -\operatorname{dist}(x,f^{-1}(1)),& f(x)=0,\end{cases}$$
--
--   and the **offset lift** is $B_f(x,a)=\mathbf 1[\mathrm{sdist}_f(x)\ge -a]$: positive offsets expand the accepted set by $a$, negative offsets erode it by $|a|$. For $F:\mathbb R^{d+1}\to\mathbb R$, write $m_F(a)=\mathbb E_{x\sim\gamma}[F(x,a)]$.
--
--   The smoothed and truncated offset lift is the witness that the paper's convex program has a good feasible point.
--
--   **Formalization Note** $\mathbb R^{d+1}$ is `Space (d+1)` with the offset as the last coordinate, so the published Gaussian, Ornstein–Uhlenbeck operator and Hermite truncation of the companion mission apply verbatim on $\mathbb R^{d+1}$. The signed distance is extended-real valued, with the distance to the empty set equal to $+\infty$: for $f\equiv1$ the lift is $\equiv1$ (a real distance to $\emptyset$ would be $0$ and give $\mathbf 1[a\ge0]$ instead).
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), §3, p.13; §4, p.16; §4.1, p.16

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Spatial and offset coordinates, the signed distance and the offset lift

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…): §3 (p.13), §4 (pp.15–16), §4.1 (p.16).

**Formalization Note.** A point `(x, a) ∈ ℝ^d × ℝ` is a point of `Space (d+1)` whose last coordinate
(`Fin.last d`) is the offset `a` and whose first `d` coordinates are the spatial part `x`. Then the
published `gaussian (d+1)` is `γ_{d+1}`, the published `ou s` on `Space (d+1)` is `T_s` acting on
`(x, a)`, and the published `truncation` is `F^{≤k}`. The signed distance takes values in `EReal`
and is built from `Metric.infEDist`, so that the distance to the empty set is `+∞`.
-/

/-- `(x, a) ↦` the point of `ℝ^{d+1}` with spatial part `x` and offset `a`. -/
noncomputable def lift {d : ℕ} (x : Space d) (a : ℝ) : Space (d+1) :=
  WithLp.toLp 2 (Fin.snoc (fun i : Fin d => x i) a : Fin (d+1) → ℝ)

/-- The spatial part `x` of `(x, a)`. -/
noncomputable def spatial {d : ℕ} (z : Space (d+1)) : Space d :=
  WithLp.toLp 2 (fun i : Fin d => z i.castSucc)

/-- The offset coordinate `a` of `(x, a)`. -/
def offset {d : ℕ} (z : Space (d+1)) : ℝ := z (Fin.last d)

/-- The signed distance function (§4.1, p.16): `sdist_f(x) = dist(x, f⁻¹(0))` if `f(x) = 1` and
`−dist(x, f⁻¹(1))` if `f(x) = 0`.

**Formalization Note.** Extended-real valued, from `Metric.infEDist`, so `sdist_f ≡ +∞` for `f ≡ 1`
and `≡ −∞` for `f ≡ 0` (a real `infDist` would be `0` there and would change `B_f`). -/
noncomputable def sdist {d : ℕ} (f : Space d → ℝ) (x : Space d) : EReal :=
  if f x = 1 then (Metric.infEDist x {y | f y = 0} : EReal)
  else -(Metric.infEDist x {y | f y = 1} : EReal)

/-- The offset lift (§4.1, p.16): `B_f(x, a) = 1[sdist_f(x) ≥ −a]`. -/
noncomputable def offsetLift {d : ℕ} (f : Space d → ℝ) (z : Space (d+1)) : ℝ :=
  if -((offset z : ℝ) : EReal) ≤ sdist f (spatial z) then 1 else 0

/-- `m_F(a) = E_{x∼γ}[F(x, a)]` (p.16, p.18). -/
noncomputable def offsetMean {d : ℕ} (F : Space (d+1) → ℝ) (a : ℝ) : ℝ :=
  ∫ x, F (lift x a) ∂gaussian d

end GeoRobustLearn



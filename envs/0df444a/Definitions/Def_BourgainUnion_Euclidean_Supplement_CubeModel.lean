-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Supplement_CubeModel
-- name    : BourgainUnion_Euclidean_Supplement_CubeModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:33:05.512546+00:00
-- url     : https://prove2.me/theorems/cbacabda-015f-4680-9ef8-c905dd55c627
-- title:
--   The two-layer cube $X_m$ of (22)
-- statement:
--   Let $Q_m=\{0,1\}^m$ with Hamming distance $\mathrm{Ham}$, and let $X_m=A\cup B$ consist of two copies $A=\{a_x\}$ and $B=\{b_x\}$ of $Q_m$. For $r>0$ put $s=\sqrt{r^2+1}-r$ and define
--   $$d(a_x,a_y)=\sqrt{\mathrm{Ham}(x,y)},\qquad d(a_x,b_y)=\sqrt{r^2+\mathrm{Ham}(x,y)},\qquad d(b_x,b_y)=\min\{s\,\mathrm{Ham}(x,y),\sqrt{\mathrm{Ham}(x,y)}\}.$$
--   This is (22). The definition gives it as a raw distance function on the point set; that it is a metric is Lemma 6.2.
--
--   **Formalization Note** $X_m$ is the type $\mathrm{Bool}\times(\mathrm{Fin}\,m\to\mathrm{Bool})$ under a fresh name with no metric instance: $(\mathrm{false},x)$ is $a_x$ and $(\mathrm{true},x)$ is $b_x$. $\mathrm{Ham}$ is Mathlib's `hammingDist`.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 26, §6.1, equation (22)

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

/-- The point set `X_m = A ⊔ B` of §6.1, p. 26: `(false, x)` is `a_x` and `(true, x)` is `b_x`,
for `x ∈ Q_m = {0,1}^m`. A plain type synonym, carrying no metric instance. -/
def Cube (m : ℕ) : Type := Bool × (Fin m → Bool)

instance (m : ℕ) : Fintype (Cube m) := inferInstanceAs (Fintype (Bool × (Fin m → Bool)))

/-- `s = √(r² + 1) − r`, p. 26. -/
def cubeS (r : ℝ) : ℝ := Real.sqrt (r^2 + 1) - r

/-- The distance (22), p. 26, as a raw function, with `Ham` the Hamming distance on `Q_m`. -/
def cubeDist (m : ℕ) (r : ℝ) : Cube m → Cube m → ℝ
  | (false, x), (false, y) => Real.sqrt (hammingDist x y)
  | (false, x), (true, y) => Real.sqrt (r^2 + hammingDist x y)
  | (true, x), (false, y) => Real.sqrt (r^2 + hammingDist x y)
  | (true, x), (true, y) => min (cubeS r * hammingDist x y) (Real.sqrt (hammingDist x y))

/-- The layer `A = {a_x : x ∈ Q_m}`. -/
def layerA (m : ℕ) : Set (Cube m) := {p | p.1 = false}

end BourgainUnion.Euclidean.Supplement



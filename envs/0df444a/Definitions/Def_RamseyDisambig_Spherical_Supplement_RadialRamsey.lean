-- Prove2me | Definitions.Def_RamseyDisambig_Spherical_Supplement_RadialRamsey
-- name    : RamseyDisambig_Spherical_Supplement_RadialRamsey
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:24:26.637862+00:00
-- url     : https://prove2.me/theorems/c8e4c5b3-1797-4e7b-930f-dbcae48939b0
-- title:
--   Homotheties, near-spanning and radial copies of cubes; the Near-Spanning Radial Ramsey Conjecture
-- statement:
--   Let $Q_n=\{0,1\}^n$ with Hamming distance $d$. A map $\varphi:Q_m\to Q_n$ is a **homothety** if there is a real ratio $\lambda>0$ with
--   $$d(\varphi(x),\varphi(x'))=\lambda\, d(x,x')\qquad\text{for all }x,x'\in Q_m.$$
--   It is **$\varepsilon$-near-spanning** if $\operatorname{diam}\varphi(Q_m)\ge(1-\varepsilon)\operatorname{diam}Q_n$. Given a coloring $c:Q_n\times Q_n\to\{0,1\}$, $\varphi$ is **$c$-radial** if $c(\varphi(x),\varphi(x'))$ depends only on the distance $d(x,x')$ in $Q_m$. A coloring is **symmetric** if $c(x,y)=c(y,x)$ for all $x,y$.
--
--   The **Near-Spanning Radial Ramsey Conjecture** (Conjecture 6) is the proposition: for all $0<\varepsilon<1/2$ and $m\in\mathbb N$ there is $N\in\mathbb N$ such that every symmetric coloring $c:Q_N\times Q_N\to\{0,1\}$ admits a $c$-radial $\varepsilon$-near-spanning homothetic copy of $Q_m$.
--
--   The conjecture is defined, never assumed: it is the conclusion of Theorem 21 and Lemma 35.
--
--   **Formalization Note** Cubes, Hamming distance and the finite diameter are the published `Cube`, `cubeDistance` and `finiteDiameter`; the diameter of the image is the supremum of $d(\varphi(x),\varphi(x'))$ over $x,x'\in Q_m$. The conjecture quantifies over every $m:\mathbb N$, including $m=0$, whose instance holds with $N=0$.
-- source:
--   Romain Bourneuf, Antonin Kiladjian, Stephan Thomasse, Ramsey Obstructions to Disambiguation, STOC 2027 submission #220 (October 2026), Appendix A, pp. 23–24; Conjecture 6, pp. 6, 24; p. 6 footnote 3 (printed = PDF); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/220.pdf

import Definitions.Def_RamseyDisambig_Spherical_Cube

set_option autoImplicit false

noncomputable section

namespace RamseyDisambig.Spherical.Supplement

open RamseyDisambig.Spherical

/-- A homothety `ϕ : Q_m → Q_n` (p. 23): for some real ratio `t > 0`,
`d(ϕ x, ϕ x') = t · d(x, x')` for all `x, x'` (Hamming distances). -/
def IsHomothety {m n : ℕ} (ϕ : Cube m → Cube n) : Prop :=
  ∃ t : ℝ, 0 < t ∧ ∀ x x' : Cube m, cubeDistance (ϕ x) (ϕ x') = t * cubeDistance x x'

/-- `ϕ` is `ε`-near-spanning (p. 24): `diam ϕ(Q_m) ≥ (1 − ε) · diam Q_n`, both diameters
being suprema of Hamming distances in `Q_n`. -/
def IsNearSpanning {m n : ℕ} (ε : ℝ) (ϕ : Cube m → Cube n) : Prop :=
  (1 - ε) * finiteDiameter (fun y y' : Cube n => cubeDistance y y') ≤
    finiteDiameter (fun x x' : Cube m => cubeDistance (ϕ x) (ϕ x'))

/-- Given `c : Q_n × Q_n → {0,1}`, `ϕ` is `c`-radial (p. 24): `c(ϕ x, ϕ x')` depends only on
the distance `d(x, x')` in the source cube `Q_m`. -/
def IsRadial {m n : ℕ} (c : Cube n → Cube n → Bool) (ϕ : Cube m → Cube n) : Prop :=
  ∃ f : ℝ → Bool, ∀ x x' : Cube m, c (ϕ x) (ϕ x') = f (cubeDistance x x')

/-- A symmetric coloring (p. 6, footnote 3): `c(x, y) = c(y, x)` for all `x, y`. -/
def IsSymmetricColoring {n : ℕ} (c : Cube n → Cube n → Bool) : Prop :=
  ∀ x y : Cube n, c x y = c y x

/-- Conjecture 6 (Near-Spanning Radial Ramsey), pp. 6, 24, as a proposition (never assumed):
for all `0 < ε < 1/2` and `m`, there is `N` such that every symmetric coloring
`c : Q_N × Q_N → {0,1}` admits a `c`-radial `ε`-near-spanning homothetic copy of `Q_m`. -/
def NearSpanningRadialRamsey : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ m : ℕ, ∃ N : ℕ,
    ∀ c : Cube N → Cube N → Bool, IsSymmetricColoring c →
      ∃ ϕ : Cube m → Cube N, IsHomothety ϕ ∧ IsNearSpanning ε ϕ ∧ IsRadial c ϕ

end RamseyDisambig.Spherical.Supplement



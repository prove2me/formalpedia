-- Prove2me | Definitions.Def_AvramDividend_Classical_ScaleFunction
-- name    : AvramDividend_Classical_ScaleFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:55:32.865097+00:00
-- url     : https://prove2.me/theorems/e6610c46-99bb-43cf-af87-4d07e25d1631
-- title:
--   $q$-scale function $W^{(q)}$, barrier level $c^*$ and barrier value functions $v_a$
-- statement:
--   Let $X$ be a spectrally negative Lévy process with Laplace exponent $\psi$, and let $q\ge0$. A function $W=W^{(q)}:\mathbb R\to\mathbb R$ is the **$q$-scale function** of $X$ if $W(y)=0$ for $y<0$, $W$ is nonnegative, continuous and nondecreasing on $[0,\infty)$, and
--   $$\int_0^\infty e^{-\theta y}W(y)\,dy=\frac{1}{\psi(\theta)-q}\qquad\text{for every }\theta>\Phi(q),$$
--   where $\Phi(q)$ is the largest root of $\psi(\theta)=q$. By uniqueness of Laplace transforms there is exactly one such function.
--
--   With $W'$ the derivative of $W$ on $(0,\infty)$, write $W'(0+)=\lim_{y\downarrow0}W'(y)\in[0,\infty]$, and read $W'(0)$ as $W'(0+)$. The **barrier level** is
--   $$c^*=\inf\{a>0:\ W'(a)\le W'(x)\text{ for all }x>0\}$$
--   when this set is nonempty; when it is empty, $c^*=0$ if $W'(0+)\le W'(x)$ for all $x>0$, and $c^*=\infty$ otherwise ($\inf\emptyset=\infty$). Thus $c^*\in[0,\infty]$.
--   For $a\ge0$ the **barrier value function** is
--   $$v_a(x)=\begin{cases}0,&x<0,\\[2pt] \dfrac{W(x)}{W'(a)},&0\le x\le a,\\[6pt] x-a+\dfrac{W(a)}{W'(a)},&x>a,\end{cases}$$
--   with the convention $W(0)/W'(0+)=0$ when $W'(0+)=\infty$; in particular $v_0(x)=x+W(0)/W'(0+)$ for $x\ge0$. Finally $v_{c^*}$ denotes $v_a$ at $a=c^*$.
--
--   These are the candidates of the classical dividend problem: $v_a$ is the value of paying dividends by a reflecting barrier at level $a$, and $c^*$ is the level at which the derivative of the scale function attains its minimum.
--
--   **Formalization Note.** The scale function is a hypothesis `IsScaleFunction X q W` on a function argument rather than a chosen object. The range $\theta>\Phi(q)$ is written as $\{\theta\ge0:\psi(\theta)>q\}$, which is the same set for $q\ge0$ because $\psi$ is convex with $\psi(0)=0$; this avoids a supremum defining $\Phi$. The Laplace transform is required together with integrability of $e^{-\theta y}W(y)$. The paper prints $e^{-\theta x}$ inside the $dy$ integral of (3.4); $e^{-\theta y}$ is meant. $W'(0+)$ is an extended real (a $\liminf$ at $0^+$, equal to the limit whenever it exists), because it is $+\infty$ for processes of unbounded variation without Gaussian part. Definition (5.2) is printed as $\inf\{a>0: W'(a)\le W'(x)\text{ for all }x\}$; read literally it is empty when $W'$ is increasing on $(0,\infty)$ (e.g. Brownian motion with nonpositive drift), which contradicts the paper's statements that $c^*=0$ there and that $c^*<\infty$ always. The formalization keeps the printed set $\{a>0\}$ (with "for all $x$" over $x>0$, since $W'=0$ on $(-\infty,0)$) whenever it is nonempty, and assigns $c^*=0$ when it is empty and $W'(0+)\le W'(x)$ for all $x>0$, which is the second alternative in the proof of Lemma 2(i) and the paper's value for Brownian motion with nonpositive drift. $c^*=\infty$ is kept for the remaining case, so that Lemma 2(i) is not true by definition. The value $c^*$ lives in $[0,\infty]$; $v_{c^*}$ uses its real value, which is meaningful because $c^*<\infty$ (Lemma 2(i)).
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, p. 5 (Section 3.2, eq. (3.4)), p. 8 (after (3.14)), p. 13 (eqs. (5.1), (5.2)), p. 20 (Section 5.5, extension by 0)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

/-!
The `q`-scale function `W = W^{(q)}` (p. 5, (3.4)), the one-sided derivative `W'(0+)`, the barrier
level `c*` (p. 13, (5.2)) and the barrier value functions `v_a` (p. 13, (5.1)) of Avram, Palmowski,
Pistorius, arXiv:math/0702893v1.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- `W` is the `q`-scale function of `X` (p. 5, (3.4)): `W = 0` on `(-∞, 0)`; on `[0, ∞)` it is
nonnegative, continuous and nondecreasing; and its Laplace transform is
`∫_0^∞ e^{-θy} W(y) dy = 1/(ψ(θ) - q)` for every `θ > Φ(q)`. For `q ≥ 0` the set
`{θ > Φ(q)}` equals `{θ ≥ 0 : ψ(θ) > q}` (`ψ` is convex with `ψ(0) = 0` and `Φ(q)` is the largest
root of `ψ = q`), which is how it is written here. -/
def IsScaleFunction (L : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ) : Prop :=
  (∀ y < 0, W y = 0) ∧ (∀ y, 0 ≤ y → 0 ≤ W y) ∧ ContinuousOn W (Ici 0) ∧
    MonotoneOn W (Ici 0) ∧
    ∀ θ : ℝ, 0 ≤ θ → q < L.ψ θ →
      IntegrableOn (fun y => Real.exp (-(θ * y)) * W y) (Ioi 0) ∧
        ∫ y in Ioi (0 : ℝ), Real.exp (-(θ * y)) * W y = (L.ψ θ - q)⁻¹

/-- `W'(0+) = lim_{y ↓ 0} W'(y) ∈ [0, ∞]`, taken in `EReal` so that the value `+∞` (unbounded
variation with `σ = 0`, p. 5) is represented. Written as a `liminf`, which equals the limit
whenever the limit exists. -/
noncomputable def derivZeroPlus (W : ℝ → ℝ) : EReal :=
  Filter.liminf (fun y => ((deriv W y : ℝ) : EReal)) (𝓝[>] (0 : ℝ))

/-- `W'(a)` for `a ≥ 0`, with `W'(0)` read as `W'(0+)` (p. 8 after (3.14), p. 15 proof of
Lemma 2(i)). -/
noncomputable def scaleDeriv (W : ℝ → ℝ) (a : ℝ) : EReal :=
  if a = 0 then derivZeroPlus W else ((deriv W a : ℝ) : EReal)

/-- `y / d` for a denominator `d ∈ (0, ∞]`, with `y / ∞ = 0`. -/
noncomputable def divE (y : ℝ) (d : EReal) : ℝ :=
  if d = ⊤ then 0 else y / d.toReal

/-- The set of (5.2): the levels `a > 0` with `W'(a) ≤ W'(x)` for all `x > 0`. -/
def cstarSet (W : ℝ → ℝ) : Set ℝ :=
  {a | 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x}

open scoped _root_.Classical in
/-- The barrier level (5.2): `c* = inf {a > 0 : W'(a) ≤ W'(x) for all x > 0}` when this set is
nonempty. When it is empty, `c* = 0` if `W'(0+) ≤ W'(x)` for all `x > 0` (the paper's value for
Brownian motion with drift `µ ≤ 0`, p. 14, and the second case of the proof of Lemma 2(i),
p. 15), and `c* = ∞` otherwise (`inf ∅ = ∞`). -/
noncomputable def cstar (W : ℝ → ℝ) : ℝ≥0∞ :=
  if (cstarSet W).Nonempty then ⨅ a ∈ cstarSet W, ENNReal.ofReal a
  else if ∀ x : ℝ, 0 < x → derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) then 0 else ⊤

/-- The barrier value function (5.1), extended by `0` to `(-∞, 0)` (p. 20):
`v_a(x) = W(x)/W'(a)` for `0 ≤ x ≤ a`, `v_a(x) = x - a + W(a)/W'(a)` for `x > a`; for `a = 0`
this is `v_0(x) = x + W(0)/W'(0+)` (p. 13), with `W(0)/∞ = 0`. -/
noncomputable def barrierValue (W : ℝ → ℝ) (a x : ℝ) : ℝ :=
  if x < 0 then 0
  else if x ≤ a then divE (W x) (scaleDeriv W a)
  else x - a + divE (W a) (scaleDeriv W a)

/-- The candidate value function `v_{c*}` (with `c*` read as a real number; `c* < ∞` is
Lemma 2(i)). -/
noncomputable def vcstar (W : ℝ → ℝ) : ℝ → ℝ :=
  barrierValue W (cstar W).toReal

end AvramDividend.Classical



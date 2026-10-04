-- Prove2me | Definitions.Def_OnlineRandomization_Tightness_MatesGame
-- name    : OnlineRandomization_Tightness_MatesGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:15:18.249817+00:00
-- url     : https://prove2.me/theorems/cdecdb40-b37e-4802-afe3-2dd5e38700c1
-- title:
--   The mates game, the uniform algorithm $G$, and the parameters $m(t)$, $M(t)$
-- statement:
--   This file defines the request-answer game used on p. 12 to show that Theorem 2.2 is tight.
--
--   **The mates game.** Fix a positive integer $t$ and reals $m, M$. The request set $R$ and the answer set $A$ are both the set $\{1, \dots, t\} \times \{0, 1\}$ of $2t$ elements, grouped into the $t$ disjoint pairs $\{(i,0), (i,1)\}$; the two elements of a pair are called *mates*, and $\bar x$ denotes the mate of $x$. For $n \ge 2$ the cost of a request sequence $(r_1, \dots, r_n)$ and an answer sequence $(a_1, \dots, a_n)$ depends only on $a_1$ and $r_2$:
--   $$
--   f_n(\underline r, \underline a) = \begin{cases} 1 & \text{if } a_1 = r_2,\\ M & \text{if } a_1 = \bar r_2,\\ m & \text{otherwise.}\end{cases}
--   $$
--   For shorter plays, $f_0 = 0$ and $f_1 \equiv 1$.
--
--   **The algorithm $G$.** $G$ draws its first answer $a_1$ uniformly at random from $A$; its other answers are irrelevant (here they all equal $a_1$).
--
--   **The parameters.** For reals $\alpha, \beta$ and an integer $t \ge 2$,
--   $$
--   m(t) = \frac{1 + (2t-1)(2t\beta - 1) - 2\alpha}{(2t-2)(\alpha + 2t - 1)}, \qquad M(t) = \frac{2t\alpha\beta + \alpha - 1}{\alpha + 2t - 1},
--   $$
--   the solution of the paper's simultaneous equations $\beta = \frac{(2t-2)m + M + 1}{2t}$ and $\alpha = \frac{1 + (2t-1)M}{2 + (2t-2)m}$.
--
--   These are the ingredients of the tightness construction: $G$ is $\alpha$-competitive against adaptive on-line adversaries and $\beta$-competitive against oblivious ones, while an adaptive off-line adversary forces ratio $M(t)$, which approaches $\alpha\beta$.
--
--   **Formalization Note.** The ground set is `Fin t × Bool` and the mate of $(i, b)$ is $(i, \lnot b)$. The paper does not define $f_0$ and $f_1$; the choice $f_0 = 0$, $f_1 \equiv 1$ is a disclosed pin. With $f_1 \equiv 1$ an adversary gains nothing by stopping after one request; with $f_1 \equiv 0$ an adaptive on-line adversary could stop after one request whenever $a_1 = b_1$ and $G$ would not be $\alpha$-competitive. The coin space of $G$ is $A$ itself with the uniform probability measure (and the discrete σ-algebra), and on coin $\omega$ the algorithm answers $\omega$ to every request; this needs $t \ge 1$. The closed forms for $m(t)$ and $M(t)$ are used only for $t \ge 2$; at $t = 1$ the denominator of $m(t)$ vanishes and Lean's division returns $0$.
-- source:
--   Ben-David, Borodin, Karp, Tardos and Wigderson, On the power of randomization in on-line algorithms, Algorithmica 11 (1994), manuscript p. 12, §2 (the request-answer game of the tightness construction, the algorithm G, and the equations for m and M)

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model

namespace OnlineRandomization.Tightness

open MeasureTheory

/-- p. 12: the request set and the answer set are both `Fin t × Bool`, a set of `2t` elements
in the `t` disjoint pairs `{(i, false), (i, true)}`; the two elements of a pair are *mates*. -/
def mate {t : ℕ} (x : Fin t × Bool) : Fin t × Bool :=
  (x.1, !x.2)

/-- p. 12: the cost determined by the first answer `a₁` and the second request `r₂`:
`1` if `a₁ = r₂`, `M` if `a₁` is the mate of `r₂`, and `m` otherwise. -/
def pairCost {t : ℕ} (m M : ℝ) (a₁ r₂ : Fin t × Bool) : ℝ :=
  if a₁ = r₂ then 1 else if a₁ = mate r₂ then M else m

/-- p. 12: the cost `f_n(r, a)` of the mates game. For `n ≥ 2` it is `pairCost m M a₁ r₂`
(the page). The page leaves `f_0` and `f_1` undefined; here `f_0 = 0` (no request, no cost)
and `f_1 ≡ 1` (a play with a single request costs `1`, for the algorithm and for the
adversary alike). The last clause (at least two requests and no answer) concerns lists of
different lengths and is never used. -/
def matesCost {t : ℕ} (m M : ℝ) : List (Fin t × Bool) → List (Fin t × Bool) → ℝ
  | [], _ => 0
  | [_], _ => 1
  | _ :: r₂ :: _, a₁ :: _ => pairCost m M a₁ r₂
  | _ :: _ :: _, [] => 0

/-- p. 12: the mates request-answer game with parameters `t`, `m`, `M`. -/
def matesGame (t : ℕ) (m M : ℝ) : Game (Fin t × Bool) (Fin t × Bool) :=
  ⟨matesCost m M⟩

/-- p. 12: the algorithm `G`, which draws its first answer `a₁` uniformly from `A`; its other
answers are irrelevant, and here every answer equals `a₁`. The coin space is `A = Fin t × Bool`
itself with the uniform probability measure (its σ-algebra is the discrete one), and on the
coin `ω` the algorithm answers `ω` to every request. -/
noncomputable def unifAlg (t : ℕ) [NeZero t] :
    RandAlg (Fin t × Bool) (Fin t × Bool) (Fin t × Bool) where
  μ := (PMF.uniformOfFintype (Fin t × Bool)).toMeasure
  isProb := inferInstance
  alg ω := fun _ => ω
  meas _ _ := MeasurableSet.of_discrete

/-- p. 12: the parameter `m = m(t)`, the closed-form solution for `m` of the simultaneous
equations `β = ((2t − 2)m + M + 1)/(2t)`, `α = (1 + (2t − 1)M)/(2 + (2t − 2)m)`:
`m(t) = (1 + (2t − 1)(2tβ − 1) − 2α) / ((2t − 2)(α + 2t − 1))`. Only `t ≥ 2` is used
(at `t = 1` the denominator vanishes and Lean's division returns `0`). -/
noncomputable def paramSmall (α β : ℝ) (t : ℕ) : ℝ :=
  (1 + (2 * (t : ℝ) - 1) * (2 * (t : ℝ) * β - 1) - 2 * α) /
    ((2 * (t : ℝ) - 2) * (α + 2 * (t : ℝ) - 1))

/-- p. 12: the parameter `M = M(t)`, the closed-form solution for `M` of the same equations:
`M(t) = (2tαβ + α − 1) / (α + 2t − 1)`. -/
noncomputable def paramLarge (α β : ℝ) (t : ℕ) : ℝ :=
  (2 * (t : ℝ) * α * β + α - 1) / (α + 2 * (t : ℝ) - 1)

end OnlineRandomization.Tightness



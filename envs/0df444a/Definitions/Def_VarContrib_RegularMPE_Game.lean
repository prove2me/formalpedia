-- Prove2me | Definitions.Def_VarContrib_RegularMPE_Game
-- name    : VarContrib_RegularMPE_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:12:45.602619+00:00
-- url     : https://prove2.me/theorems/81ea67f4-bb65-4352-b44e-a4818eb385da
-- title:
--   (4), (6), §2.4, pp. 10, 15–16 — the value V of (4), the rate u of (6), and the regular control Markov perfect equilibrium
-- statement:
--   For a threshold $\theta$ and a coefficient $A$, the function $V$ of (4) is
--   $$V(x)=\begin{cases}k(x-\theta)+V(\theta) & x<\theta,\\ (R\pi)(x)+A\varphi(x) & x\ge\theta,\end{cases}\qquad V(\theta)=(R\pi)(\theta)+A\varphi(\theta),$$
--   and the contribution rate $u$ of (6), computed from $V$, is
--   $$u(x)=\begin{cases}-\tfrac1k\big(\mathcal AV(x)+\pi(x)\big) & x<\theta,\\ 0 & x\ge\theta.\end{cases}$$
--
--   Two players contribute at **regular feedback rates** $d\xi_{it}=u_i(Z_t)\,dt$, $i=1,2$. This profile is a **regular control Markov perfect equilibrium** if
--
--   1. each $u_i$ belongs to $\mathcal U$ and is nonnegative on $I$;
--   2. for each player $i$, its opponent $j\ne i$, every initial state $x\in I$ and every solution $Z$ of $dZ_t=[\mu+u_1+u_2](Z_t)dt+\sigma(Z_t)dW_t$, $Z_0=x$: player $i$'s discounted running payoff $e^{-rt}(\pi(Z_t)-k\,u_i(Z_t))$ is $P\otimes dt$-integrable, and for every control $\zeta$ and every solution $Z'$ of $dZ'_t=[\mu+u_j](Z'_t)dt+\sigma(Z'_t)dW_t+d\zeta_t$, $Z'_{0-}=x$, with $\zeta$ admissible,
--   $$\mathbb E\Big[\int_0^\infty e^{-rt}\pi(Z'_t)dt-\int_{[0,\infty)}e^{-rt}k\,d\zeta_t\Big]\le \mathbb E\int_0^\infty e^{-rt}\big(\pi(Z_t)-k\,u_i(Z_t)\big)dt .$$
--
--   The equilibrium is the object of Theorem 2; $V$ and $u$ are the explicit candidates it is about.
--
--   **Formalization Note.** Markov perfection (a subgame perfect equilibrium in Markov strategies, pp. 4, 13) is posed as the best-response property from every initial state, which is what it means for stationary feedback strategies of a time-homogeneous state. Deviations range over all of $\Xi$, and the opponent keeps its feedback rule on the deviated path. Statements quantify over every solution of the state equations; existence of solutions is not posed. Players are indexed by `Fin 2`.
-- source:
--   Kwon, Game of Variable Contributions to the Common Good under Uncertainty, arXiv:1904.00500v1, pp. 4, 10, 13–16, (4), (6), §2.3–§2.4 (MPE, regular control MPE)

import Mathlib
import Definitions.Def_VarContrib_RegularMPE_Model
import Definitions.Def_VarContrib_RegularMPE_Setting

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace VarContrib.RegularMPE

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The function `V` of (4) with threshold `θ` and coefficient `A`:
`V(x) = k(x − θ) + V(θ)` for `x < θ` and `V(x) = (Rπ)(x) + Aφ(x)` for `x ≥ θ`, where
`V(θ) = (Rπ)(θ) + Aφ(θ)`. -/
noncomputable def Vsol (m : Model) (S : Setting Ω) (θ A : ℝ) (x : ℝ) : ℝ :=
  if x < θ then m.k * (x - θ) + (R m S m.π θ + A * S.φ θ) else R m S m.π x + A * S.φ x

/-- The contribution rate `u` of (6), computed from `V` of (4):
`u(x) = −(1/k)(𝒜V(x) + π(x))` for `x < θ` and `u(x) = 0` for `x ≥ θ`. -/
noncomputable def uEq (m : Model) (S : Setting Ω) (θ A : ℝ) (x : ℝ) : ℝ :=
  if x < θ then -(gen m (Vsol m S θ A) x + m.π x) / m.k else 0

/-- The players `Fin 2` contribute at the regular feedback rates `dξ_{it} = u_i(Z_t) dt`, and
this profile is a Markov perfect equilibrium (pp. 4, 13–15):
1. each rate `u_i` is in the class `𝒰` and is nonnegative on `I`;
2. for each player `i`, its opponent `j ≠ i`, every initial state `x ∈ I` and every solution `Z`
   of `dZ = (μ + u_0 + u_1)(Z) dt + σ(Z) dW`, `Z_0 = x`:
   * player `i`'s discounted running payoff `e^{−rt}(π(Z_t) − k u_i(Z_t))` is
     `P ⊗ dt`-integrable, and
   * no admissible deviation does better: for every control `ζ` of player `i` and every
     solution `Z′` of `dZ′ = (μ + u_j)(Z′) dt + σ(Z′) dW + dζ`, `Z′_{0−} = x` (the opponent keeps
     its feedback rule on the deviated path) with `ζ` admissible, the deviation payoff is at most
     player `i`'s equilibrium payoff.

Markov perfection is the best-response property from every initial state. -/
def IsRegularMPE (m : Model) (S : Setting Ω) (u : Fin 2 → ℝ → ℝ) : Prop :=
  (∀ i, InU m (u i) ∧ ∀ y ∈ m.I, 0 ≤ u i y) ∧
  ∀ i j : Fin 2, j ≠ i → ∀ x ∈ m.I, ∀ Z : ℝ≥0 → Ω → ℝ,
    IsStateSol m S (fun y => m.μ y + u 0 y + u 1 y) x (fun _ _ => 0) Z →
      Integrable (fun p : Ω × ℝ => Real.exp (-(m.r * p.2)) *
          (m.π (Z p.2.toNNReal p.1) - m.k * u i (Z p.2.toNNReal p.1)))
        (S.P.prod (volume.restrict (Ioi (0 : ℝ)))) ∧
      ∀ ζ Z' : ℝ≥0 → Ω → ℝ, IsStateSol m S (fun y => m.μ y + u j y) x ζ Z' → Adm m S ζ Z' →
        devPay m S ζ Z' ≤ regPay m S (u i) Z

end VarContrib.RegularMPE



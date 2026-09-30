-- Prove2me | Definitions.Def_StochFictPlay_ZeroSumESS_Symmetric
-- name    : StochFictPlay_ZeroSumESS_Symmetric
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T09:29:41.400844+00:00
-- url     : https://prove2.me/theorems/8316cfe7-041c-40d8-aa15-1ab46dec6440
-- title:
--   Symmetric games: interior ESS, the dynamics (SP) and (SPV), the function $\hat\Lambda$, and symmetric stochastic fictitious play
-- statement:
--   A symmetric two player game with strategy set $\{0,\dots,m-1\}$ is given by one matrix $A$: $u^1(i,j) = A_{ij}$ and $u^2(i,j) = A_{ji}$, so $u^1(s^1,s^2) = u^2(s^2,s^1)$. Player 1's payoff vector is $U^1(z) = Az$.
--
--   1. **Interior ESS.** $x^* \in \operatorname{int}(\Delta S^1)$ is an interior ESS if there is a neighbourhood $N$ of $x^*$ with
--   $$x^*\cdot Ax > x\cdot Ax \quad\text{for all mixed } x \in N,\ x \neq x^*.$$
--   2. **(SP)** $\dot x = C(Ax) - x$, where $C$ is the choice function of the shock density $f$; **(SPV)** $\dot x = \tilde C(Ax) - x$ for the argmax map $\tilde C$ of a perturbation $V$.
--   3. **Hofbauer's function** $\hat\Lambda(x) = x\cdot Ax - V(x) - W(Ax)$.
--   4. **Symmetric stochastic fictitious play.** Two roles play at each time; the state is
--   $$\hat Z_t = \frac1{2t}\sum_{u=1}^t \big(\hat\zeta^1_u + \hat\zeta^2_u\big) \in \Delta S^1,$$
--   the initial choices $\hat\zeta^1_1, \hat\zeta^2_1$ are arbitrary, and for $t \ge 1$ the player in role $r$ plays at time $t+1$ the pure strategy maximizing $(A\hat Z_t)_k + (\varepsilon^r_t)_k$.
--   5. **Shocks.** $(\varepsilon^r_t)_{t, r}$ are independent, each with the same density $f$.
--
--   These are the objects of the paper's symmetric model (p. 11) and of the interior-ESS case of §4.1.
--
--   **Formalization Note** The symmetry condition holds by construction, so it is no hypothesis. The paper's ESS definition omits $x \ne x^*$; without it the strict inequality fails at $x = x^*$ and no ESS would exist, so the exclusion is added. Roles 1, 2 are indexed $0, 1$. Ties in the argmax are broken by the smallest index (a probability-zero event). $W$ is `perturbedMax`.
-- source:
--   Hofbauer and Sandholm, On the Global Convergence of Stochastic Fictitious Play, Econometrica 70 (2002); authors' manuscript of February 21, 2002, p. 11 (symmetric games, symmetric SFP), p. 12 ((SP)), p. 15 ((SPV)), p. 16 (ESS, the function Λ̂)

import Mathlib
import Definitions.Def_StochFictPlay_ZeroSumESS_ChoiceModel
import Definitions.Def_StochFictPlay_ZeroSumESS_Game

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StochFictPlay.ZeroSumESS

/-!
A symmetric two player game (Hofbauer–Sandholm 2002, manuscript p. 11) with strategy set
`Fin m` for both players is given by one payoff matrix `A`: `u¹(i, j) = A i j` and
`u²(i, j) = A j i`, which is exactly the symmetry condition `u¹(s¹, s²) = u²(s², s¹)`.
Player 1's payoff vector is `U¹(z) = A *ᵥ z`.
-/

/-- An interior evolutionarily stable strategy (manuscript p. 16): `x*` lies in `int(∆S¹)` and
`x* · U¹(x) > x · U¹(x)` for every mixed strategy `x ≠ x*` in a neighbourhood of `x*`.
(The page omits `x ≠ x*`; at `x = x*` the strict inequality cannot hold.) -/
def IsInteriorESS {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (xstar : Fin m → ℝ) : Prop :=
  xstar ∈ openSimplex m ∧ ∃ N ∈ nhds xstar, ∀ x ∈ stdSimplex ℝ (Fin m) ∩ N, x ≠ xstar →
    x ⬝ᵥ (A *ᵥ x) < xstar ⬝ᵥ (A *ᵥ x)

/-- The vector field of the symmetric perturbed best response dynamic
`(SP) ẋ = B̃¹(x) − x` (p. 12), where `B̃¹(x) = C(U¹(x))` and `C = choiceProb f`. -/
noncomputable def symField {m : ℕ} (f : (Fin m → ℝ) → ℝ≥0∞) (A : Matrix (Fin m) (Fin m) ℝ) :
    (Fin m → ℝ) → (Fin m → ℝ) :=
  fun x => choiceProb f (A *ᵥ x) - x

/-- The vector field of `(SPV) ẋ = argmax_{y ∈ int(∆S¹)} (y · U¹(x) − V¹(y)) − x` (p. 15),
with the argmax supplied as the map `Ct` (see `IsPerturbedArgmax`). -/
noncomputable def spvField {m : ℕ} (Ct : (Fin m → ℝ) → (Fin m → ℝ))
    (A : Matrix (Fin m) (Fin m) ℝ) : (Fin m → ℝ) → (Fin m → ℝ) :=
  fun x => Ct (A *ᵥ x) - x

/-- Hofbauer's function of §4.1 (p. 16): `Λ̂(x) = x · U¹(x) − V¹(x) − W¹(U¹(x))`, with `W¹` the
function of (9) for `V¹`. -/
noncomputable def lambdaHat {m : ℕ} (V : (Fin m → ℝ) → ℝ) (Ct : (Fin m → ℝ) → (Fin m → ℝ))
    (A : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) : ℝ :=
  x ⬝ᵥ (A *ᵥ x) - V x - perturbedMax V Ct (A *ᵥ x)

/-- Cumulative play `∑_{u=1}^t (ζ̂¹_u + ζ̂²_u)` of symmetric stochastic fictitious play
(p. 11). `ζ̂^r_1 = e_{s₁ r}` are arbitrary initial pure choices of the two roles `r = 0, 1`
(the paper's roles 1, 2), and for `t ≥ 1` the role-`r` player plays the (smallest) maximizer of
`U¹_k(Ẑ_t) + (ε^r_t)_k`, with `Ẑ_t = (1/(2t)) ∑_{u ≤ t} (ζ̂¹_u + ζ̂²_u)`. Value `0` at `t = 0`,
never used. -/
noncomputable def symCum {Ω : Type*} {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (s₁ : Fin 2 → Fin m)
    (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) : ℕ → Ω → (Fin m → ℝ)
  | 0 => fun _ => 0
  | 1 => fun _ => Pi.single (s₁ 0) (1 : ℝ) + Pi.single (s₁ 1) (1 : ℝ)
  | (t + 2) => fun ω =>
      symCum A s₁ ε (t + 1) ω +
        ∑ r : Fin 2, argmaxVec (fun k =>
          (A *ᵥ ((1 / (2 * ((t + 1 : ℕ) : ℝ))) • symCum A s₁ ε (t + 1) ω)) k + ε (t + 1) r ω k)

/-- The state `Ẑ_t = (1/(2t)) ∑_{u=1}^t (ζ̂¹_u + ζ̂²_u) ∈ ∆S¹` of symmetric SFP (p. 11),
for `t ≥ 1`. -/
noncomputable def symBelief {Ω : Type*} {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ)
    (s₁ : Fin 2 → Fin m) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) (t : ℕ) (ω : Ω) : Fin m → ℝ :=
  (1 / (2 * (t : ℝ))) • symCum A s₁ ε t ω

/-- The shocks of symmetric SFP (p. 11): `ε t r` for time `t` and role `r` are independent and
identically distributed, each with density `f`. -/
def IsSymShockFamily {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m : ℕ}
    (f : (Fin m → ℝ) → ℝ≥0∞) (ε : ℕ → Fin 2 → Ω → (Fin m → ℝ)) : Prop :=
  (∀ t r, Measurable (ε t r)) ∧
  (∀ t r, P.map (ε t r) = volume.withDensity f) ∧
  iIndepFun (fun (i : ℕ × Fin 2) ω => ε i.1 i.2 ω) P

end StochFictPlay.ZeroSumESS



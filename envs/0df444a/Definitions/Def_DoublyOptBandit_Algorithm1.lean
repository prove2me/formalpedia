-- Prove2me | Definitions.Def_DoublyOptBandit_Algorithm1
-- name    : DoublyOptBandit_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:41.780297+00:00
-- url     : https://prove2.me/theorems/f1fb6e97-d66f-4ef2-9ec9-0f2795ea069e
-- title:
--   Algorithm 1: mirror descent self-concordant barrier bandit learning (single agent)
-- statement:
--   Let $X\subseteq\mathbb R^n$ have nonempty interior, $R$ a barrier for $X$, $\beta>0$, step sizes $\eta_t>0$, reward functions $u_t$ and directions $z_t$ on the unit sphere. **Algorithm 1** starts at $x_1=\operatorname{argmin}R$ and in round $t=1,2,\dots$:
--
--   1. sets $A_t=(\nabla^2R(x_t)+\eta_t\beta(t+1)I_n)^{-1/2}$;
--   2. plays $\hat x_t=x_t+A_tz_t$ and receives $\hat u_t=u_t(\hat x_t)$;
--   3. sets $\hat v_t=n\,\hat u_t\,A_t^{-1}z_t$;
--   4. updates $x_{t+1}=P_R(x_t,\hat v_t,\eta_t)$ with the prox-mapping (2.5).
--
--   The descent inequality Lemma 2.12 is stated for these iterates.
--
--   **Formalization Note** The iterates are defined pathwise, as deterministic functions of the sequence of directions; the random draws $z_t\sim\mathbb S^n$ enter the theorems as a realization. Rounds are indexed from $t=1$.
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Algorithm 1, p.9; (2.5), p.8

import Mathlib
import Definitions.Def_DoublyOptBandit_Components

open scoped InnerProductSpace

namespace DoublyOptBandit

/-! **Algorithm 1** (Mirror Descent Self-Concordant Barrier Bandit Learning), Ba, Lin, Zhang &
Zhou, arXiv:2112.02856v4, p.9:

```
1: Input: step size ηt > 0, module β > 0 and barrier R : int(X) ↦ R.
2: Initialization: x1 = argmin_{x∈X} R(x).
3: for t = 1, 2, . . . do
4:   set At ← (∇²R(xt) + ηtβ(t + 1)In)^{−1/2}.
5:   draw zt ∼ Sⁿ.
6:   play x̂t ← xt + Atzt.
7:   receive ût ← ut(x̂t).
8:   set v̂t ← n · ût(At)⁻¹zt.
9:   update xt+1 ← PR(xt, v̂t, ηt).
10: end for
```

The iterates are defined pathwise: for a given sequence of reward functions `u t` and a given
sequence of directions `z t` (a realization of the draws `zt ∼ Sⁿ`), all quantities are
deterministic functions of the data. Rounds are indexed from `t = 1`. -/

variable {m : ℕ}

/-- One round of Algorithm 1 (lines 4–9, p.9): from the iterate `x = xₜ` and the direction
`z = zₜ`, form `Aₜ = (∇²R(xₜ) + ηₜβ(t+1)I)^{−1/2}`, play `x̂ₜ = xₜ + Aₜzₜ`, observe `uₜ(x̂ₜ)`, set
`v̂ₜ = n uₜ(x̂ₜ) Aₜ⁻¹zₜ` and return `xₜ₊₁ = P_R(xₜ, v̂ₜ, ηₜ)` with the prox-mapping (2.5), p.8, whose
quadratic coefficient is `ηₜβ(t+1)/2`. -/
noncomputable def alg1Step (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (t : ℕ) (x z : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  let c := η t * β * ((t : ℝ) + 1)
  let A := scalingMatrix R x c
  proxPoint X R (η t) c (ellipsoidalEstimate A (u t (x + Matrix.toEuclideanLin A z)) z) x

/-- Auxiliary sequence: `alg1Seq … k = x^{k+1}`, with `x¹ = argmin_{int X} R` (line 2). -/
noncomputable def alg1Seq (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin m)) :
    ℕ → EuclideanSpace ℝ (Fin m)
  | 0 => barrierCenter X R
  | k + 1 => alg1Step X R β η u (k + 1) (alg1Seq X R β η u z k) (z (k + 1))

/-- The iterate `xₜ` of Algorithm 1 at round `t ≥ 1` (so `x₁ = argmin_{int X} R` and
`xₜ₊₁ = alg1Step … t xₜ zₜ`). The value at `t = 0` is not used. -/
noncomputable def alg1Iter (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin m)) (t : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  alg1Seq X R β η u z (t - 1)

/-- The scaling matrix `Aₜ = (∇²R(xₜ) + ηₜβ(t+1)Iₙ)^{−1/2}` of round `t` (line 4). -/
noncomputable def alg1Scaling (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin m)) (t : ℕ) :
    Matrix (Fin m) (Fin m) ℝ :=
  scalingMatrix R (alg1Iter X R β η u z t) (η t * β * ((t : ℝ) + 1))

/-- The played action `x̂ₜ = xₜ + Aₜzₜ` of round `t` (line 6). -/
noncomputable def alg1Played (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin m)) (t : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  alg1Iter X R β η u z t + Matrix.toEuclideanLin (alg1Scaling X R β η u z t) (z t)

/-- The gradient estimate `v̂ₜ = n · uₜ(x̂ₜ)(Aₜ)⁻¹zₜ` of round `t` (lines 7–8). -/
noncomputable def alg1Estimate (X : Set (EuclideanSpace ℝ (Fin m)))
    (R : EuclideanSpace ℝ (Fin m) → ℝ) (β : ℝ) (η : ℕ → ℝ)
    (u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ) (z : ℕ → EuclideanSpace ℝ (Fin m)) (t : ℕ) :
    EuclideanSpace ℝ (Fin m) :=
  ellipsoidalEstimate (alg1Scaling X R β η u z t) (u t (alg1Played X R β η u z t)) (z t)

end DoublyOptBandit



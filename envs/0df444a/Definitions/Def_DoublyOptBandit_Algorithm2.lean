-- Prove2me | Definitions.Def_DoublyOptBandit_Algorithm2
-- name    : DoublyOptBandit_Algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:27:50.320235+00:00
-- url     : https://prove2.me/theorems/c80edfc4-0ab8-427c-af4f-11c3e1695dfc
-- title:
--   Algorithm 2: multi-agent mirror descent self-concordant barrier bandit learning, and the step size of Theorem 3.8
-- statement:
--   Each player $i$ has a set $X_i\subseteq\mathbb R^{n_i}$ with nonempty interior, a barrier $R_i$, a weight $\lambda_i>0$, and all share $\beta>0$ and step sizes $\eta_t>0$. **Algorithm 2** starts at $x_i^1=\operatorname{argmin}R_i$ and in round $t=1,2,\dots$:
--
--   1. every player sets $A_i^t=(\nabla^2R_i(x_i^t)+\frac{\eta_t\beta(t+1)}{\lambda_i}I_{n_i})^{-1/2}$, draws $z_i^t$ on the unit sphere and plays $\hat x_i^t=x_i^t+A_i^tz_i^t$;
--   2. every player receives $\hat u_i^t=u_i(\hat x^t)$ and sets $\hat v_i^t=n_i\,\hat u_i^t\,(A_i^t)^{-1}z_i^t$;
--   3. every player updates $x_i^{t+1}=P_{R_i}(x_i^t,\hat v_i^t,\eta_t,\lambda_i,\beta)$ with the prox-mapping (3.3).
--
--   The step size of Theorem 3.8 is
--   $$
--   \eta_t=\frac1{2nL\sqrt t},\qquad n=\sum_in_i .
--   $$
--
--   Lemma 3.10 and Theorem 3.8 are stated for these iterates.
--
--   **Formalization Note** The iterates are defined pathwise from a realization of the directions $z_i^t$. Rounds are indexed from $t=1$. The weights are called `lam` because `λ` is reserved in Lean.
-- source:
--   Ba, Lin, Zhang & Zhou, Doubly Optimal No-Regret Online Learning in Strongly Monotone Games with Bandit Feedback, arXiv:2112.02856v4, Algorithm 2, p.15; (3.3), p.14; step size, Theorem 3.8, p.15; n = Σ nᵢ, Appendix E, p.33

import Mathlib
import Definitions.Def_DoublyOptBandit_Components

open scoped InnerProductSpace

namespace DoublyOptBandit

/-! **Algorithm 2** (Multi-Agent Mirror Descent Self-Concordant Barrier Bandit Learning), Ba, Lin,
Zhang & Zhou, arXiv:2112.02856v4, p.15:

```
1: Input: step size ηt > 0, weight λi > 0, module β > 0, and barrier Ri : int(Xi) ↦ R.
2: Initialization: x1i = argmin_{xi∈Xi} Ri(xi).
3: for t = 1, 2, . . . do
4:   for i ∈ N do
5:     set Ati ← (∇²Ri(xti) + (ηtβ(t+1)/λi) Ini)^{−1/2}.
6:     draw zti ∼ S^{ni}.
7:     play x̂ti ← xti + Atizti.
8:   end for
9:   receive ûti ← ui(x̂t) for all i ∈ N.
10:  for i ∈ N do
11:    set v̂ti ← ni ûti(Ati)⁻¹zti.
12:    update xt+1i ← PRi(xti, v̂ti, ηt, λi, β).
13:  end for
14: end for
```

The iterates are defined pathwise from a realization `z t i` of the directions; the rewards
`uᵢ : X → ℝ` are fixed. Rounds are indexed from `t = 1`. The weights are written `lam`
(`λ` is reserved in Lean). -/

variable {N : ℕ} {n : Fin N → ℕ}

/-- The coefficient `ηₜβ(t+1)/λᵢ` of Algorithm 2 line 5 and of the prox-mapping (3.3), p.14. -/
noncomputable def alg2Coeff (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  η t * β * ((t : ℝ) + 1) / lam i

/-- One round of Algorithm 2 (lines 5–12, p.15): from the profile `x = xᵗ` and the directions
`z = zᵗ`, every player forms `Aᵢᵗ = (∇²Rᵢ(xᵢᵗ) + (ηₜβ(t+1)/λᵢ)I)^{−1/2}`, the profile
`x̂ᵗ = (xᵢᵗ + Aᵢᵗzᵢᵗ)ᵢ` is played, player `i` observes `uᵢ(x̂ᵗ)`, sets
`v̂ᵢᵗ = nᵢ uᵢ(x̂ᵗ)(Aᵢᵗ)⁻¹zᵢᵗ` and moves to `xᵢᵗ⁺¹ = P_{Rᵢ}(xᵢᵗ, v̂ᵢᵗ, ηₜ, λᵢ, β)`, the prox-mapping
(3.3) with quadratic coefficient `ηₜβ(t+1)/(2λᵢ)`. -/
noncomputable def alg2Step (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (t : ℕ) (x : Joint n)
    (z : ∀ i, EuclideanSpace ℝ (Fin (n i))) : Joint n :=
  let A := fun i => scalingMatrix (R i) (x i) (alg2Coeff lam β η t i)
  WithLp.toLp 2 (fun i => proxPoint (X i) (R i) (η t) (alg2Coeff lam β η t i)
    (ellipsoidalEstimate (A i) (u i (perturb A x z)) (z i)) (x i))

/-- Auxiliary sequence: `alg2Seq … k = x^{k+1}`, with `x¹ᵢ = argmin_{int Xᵢ} Rᵢ` (line 2). -/
noncomputable def alg2Seq (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (z : ℕ → ∀ i, EuclideanSpace ℝ (Fin (n i))) :
    ℕ → Joint n
  | 0 => WithLp.toLp 2 (fun i => barrierCenter (X i) (R i))
  | k + 1 => alg2Step X R u lam β η (k + 1) (alg2Seq X R u lam β η z k) (z (k + 1))

/-- The profile `xᵗ` of Algorithm 2 at round `t ≥ 1` (so `x¹ᵢ = argmin_{int Xᵢ} Rᵢ` and
`xᵗ⁺¹ = alg2Step … t xᵗ zᵗ`). The value at `t = 0` is not used. -/
noncomputable def alg2Iter (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (z : ℕ → ∀ i, EuclideanSpace ℝ (Fin (n i)))
    (t : ℕ) : Joint n :=
  alg2Seq X R u lam β η z (t - 1)

/-- The scaling matrix `Aᵢᵗ = (∇²Rᵢ(xᵢᵗ) + (ηₜβ(t+1)/λᵢ)Iₙᵢ)^{−1/2}` of round `t` (line 5). -/
noncomputable def alg2Scaling (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (z : ℕ → ∀ i, EuclideanSpace ℝ (Fin (n i)))
    (t : ℕ) (i : Fin N) : Matrix (Fin (n i)) (Fin (n i)) ℝ :=
  scalingMatrix (R i) (alg2Iter X R u lam β η z t i) (alg2Coeff lam β η t i)

/-- The played profile `x̂ᵗ = (xᵢᵗ + Aᵢᵗzᵢᵗ)ᵢ` of round `t` (line 7). -/
noncomputable def alg2Played (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (z : ℕ → ∀ i, EuclideanSpace ℝ (Fin (n i)))
    (t : ℕ) : Joint n :=
  perturb (alg2Scaling X R u lam β η z t) (alg2Iter X R u lam β η z t) (z t)

/-- Player `i`'s gradient estimate `v̂ᵢᵗ = nᵢ uᵢ(x̂ᵗ)(Aᵢᵗ)⁻¹zᵢᵗ` of round `t` (lines 9, 11). -/
noncomputable def alg2Estimate (X : ∀ i, Set (EuclideanSpace ℝ (Fin (n i))))
    (R : ∀ i, EuclideanSpace ℝ (Fin (n i)) → ℝ) (u : Fin N → Joint n → ℝ)
    (lam : Fin N → ℝ) (β : ℝ) (η : ℕ → ℝ) (z : ℕ → ∀ i, EuclideanSpace ℝ (Fin (n i)))
    (t : ℕ) (i : Fin N) : EuclideanSpace ℝ (Fin (n i)) :=
  ellipsoidalEstimate (alg2Scaling X R u lam β η z t i)
    (u i (alg2Played X R u lam β η z t)) (z t i)

/-- The step size of Theorem 3.8, `ηₜ = 1/(2nL√t)` with `n = Σᵢ nᵢ` (arXiv:2112.02856v4,
Theorem 3.8, p.15; `n = Σ_{i∈N} nᵢ` in the multi-agent setting, Appendix E, p.33). -/
noncomputable def stepSize (n : Fin N → ℕ) (L : ℝ) (t : ℕ) : ℝ :=
  1 / (2 * (∑ i, (n i : ℝ)) * L * Real.sqrt t)

end DoublyOptBandit



-- Prove2me | Definitions.Def_RobustCtxPricing_Algorithm4
-- name    : RobustCtxPricing_Algorithm4
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:47.203203+00:00
-- url     : https://prove2.me/theorems/4ffcd0b4-5a79-4813-be18-9901abd215c9
-- title:
--   Algorithm 4 (Robust Contextual Pricing) with $\bar C=\lceil 5C+20d\log T\rceil$ and $\epsilon=T^{-3}$
-- statement:
--   **Algorithm 4** of Castiglioni–Stradi, for a known corruption budget $C$. Its parameters are
--   $$
--   \epsilon=T^{-3},\qquad \bar C=\lceil 5C+20d\log T\rceil .
--   $$
--   It starts from the uniform density $\mu_1$ over $\Theta$ and $2\bar C+1$ empty evidence sets $\mathcal H_1,\dots,\mathcal H_{2\bar C+1}$. In each round $t=1,\dots,T$ it observes the context $u_t$ and
--
--   1. **commits** if every $\mathcal H_j$ predicts $u_t$ in the sense of (1): for coefficients $\lambda^j$ achieving (1) it posts the $(\bar C+1)$-st largest of the lower endpoints $\hat v_j(u_t)-\frac1{8T}$ and keeps its state;
--   2. **explores** otherwise: it posts an $\epsilon$-window median $m_t$ of $\mu_t$ in direction $u_t$, observes the (possibly corrupted) sale feedback $Y_t$, appends $(u_t,m_t)$ to one evidence set that does not predict $u_t$, and replaces $\mu_t$ by Update-Density$(\mu_t,u_t,m_t,Y_t)$.
--
--   A *run* records the density and the evidence sets at the start of every round and the posted prices; `IsAlg4Run` says which runs are runs of Algorithm 4 on given contexts and feedback.
--
--   **Formalization Note** The paper fixes no tie-breaking rule, and the run relation admits all of them: any solution of (3) as the median, any non-predicting evidence set as the receiving set, any coefficients satisfying (1) in the commit step. The logarithm is natural. Rounds are numbered $0,\dots,T-1$.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §4.1, p.20 (C̄ and ϵ), Algorithm 4, p.21; with Algorithm 2 (p.13) and Algorithm 3 (p.15)

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density

namespace RobustCtxPricing

/-- **The window width `ϵ = T⁻³`.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in Robust
Contextual Pricing*, arXiv:2607.11210, Algorithm 4, Line 1, p.21 (and §4.1, p.20: "we still set
`ϵ = T⁻³`"). -/
noncomputable def epsT (T : ℕ) : ℝ :=
  ((T : ℝ) ^ 3)⁻¹

/-- **The corruption parameter `C̄ = ⌈5C + 20d log T⌉`.** Castiglioni–Stradi, arXiv:2607.11210,
§4.1, p.20: "The first main difference is the corruption parameter: `C̄ = ⌈5C + 20d log T⌉`".

**Formalization Note.** `log` is the natural logarithm (`Real.log`); the ceiling is `Nat.ceil`
(the argument is nonnegative for `T ≥ 1`). -/
noncomputable def cbar (d T C : ℕ) : ℕ :=
  ⌈5 * (C : ℝ) + 20 * (d : ℝ) * Real.log T⌉₊

/-- **A run of Algorithm 4: the trajectory of its state and prices.** For a round `t` (`0`-based),
`μ t` is the density `µ_{t+1}` held at the start of round `t`, `H t j` the evidence set `𝓗_j` at
the start of round `t` (a list of samples `(u_i, p_i)` in insertion order), and `p t` the price
posted in round `t`. The number of evidence sets is the parameter `n` (`2C̄ + 1` in Algorithm 4).
Which trajectories are runs of Algorithm 4 is said by `IsAlg4Run`. -/
structure Run (d n : ℕ) where
  /-- the density held at the start of each round -/
  μ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ
  /-- the evidence sets held at the start of each round -/
  H : ℕ → Fin n → List (EuclideanSpace ℝ (Fin d) × ℝ)
  /-- the posted prices -/
  p : ℕ → ℝ

/-- **Algorithm 4 (Robust Contextual Pricing), as a relation on runs.** Castiglioni–Stradi,
arXiv:2607.11210, §4.1, Algorithm 4, p.21, with Commit (Algorithm 2, p.13), the prediction test (1)
(p.13), the interval (2) (p.14), the ϵ-window median (3) (p.14) and Update-Density (Algorithm 3,
p.15):

```
Require: Horizon T, corruption parameter C̄
1: Set ϵ = T⁻³
2: Initialize µ₁ as the uniform density over Θ
3: Initialize 2C̄ + 1 empty evidence sets 𝓗₁, …, 𝓗_{2C̄+1} ← ∅
4: for t = 1, …, T do
5:   Observe context u_t
6:   if every 𝓗_j satisfies Equation (1) for u_t then        ▷ Commit Check
7:     Commit()
8:     Continue
9:   end if
10:  Let m_t be the ϵ-window median of µ_t in direction u_t, as in Equation (3)
11:  Post price p_t = m_t
12:  Observe sale feedback Y_t
13:  Insert (u_t, m_t) into a set 𝓗_j that does not satisfy Equation (1)   ▷ Evidence Collection
14:  Update-Density()                                           ▷ Density Update
15: end for
```

`IsAlg4Run T C u Y r` says that `r` is a run of Algorithm 4 with horizon `T` and parameter
`C̄ = cbar d T C` (§4.1) on the contexts `u` and the observed feedback `Y`: the initial density is
uniform, the `2C̄ + 1` evidence sets start empty, and in every round `t < T`

* **commit** (every `𝓗_j` predicts `u_t`): for coefficients `λ^j` satisfying (1) for each `j`, the
  posted price is the `(C̄ + 1)`-st largest lower endpoint `v̂_j(u_t) − 1/(8T)`, and the state is
  unchanged (Algorithm 2, Line 4: `µ_{t+1} = µ_t`);
* **explore** (some `𝓗_j` does not predict `u_t`): the posted price is an ϵ-window median of the
  current density in direction `u_t`, the sample `(u_t, p_t)` is appended to one evidence set that
  does not predict `u_t`, and the density is replaced by Update-Density with feedback `Y_t`.

**Formalization Note.** The paper fixes no tie-breaking rule; the relation admits every choice:
any solution of (3) as the median, any evidence set not satisfying (1) as the receiving set, and any
coefficients `λ^j` satisfying (1) in the commit (the paper "uses the solution to the inequality",
p.14). The feedback `Y t` is read only in exploration rounds. Rounds are `0, …, T−1`; the state
after the last round is `μ T`, `H T`. -/
def IsAlg4Run {d : ℕ} (T C : ℕ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Bool)
    (r : Run d (2 * cbar d T C + 1)) : Prop :=
  r.μ 0 = uniformDensity d ∧ (∀ j, r.H 0 j = []) ∧
  ∀ t < T,
    ((∀ j, Predicts (epsT T) T (r.H t j) (u t)) ∧
      ∃ lam : ∀ j, Fin (r.H t j).length → ℝ,
        (∀ j, PredictsWith (epsT T) T (r.H t j) (u t) (lam j)) ∧
        r.p t = commitPrice T (cbar d T C) (r.H t) lam ∧
        r.μ (t + 1) = r.μ t ∧ r.H (t + 1) = r.H t) ∨
    ((¬ ∀ j, Predicts (epsT T) T (r.H t j) (u t)) ∧
      IsWindowMedian (epsT T) (r.μ t) (u t) (r.p t) ∧
      (∃ j, ¬ Predicts (epsT T) T (r.H t j) (u t) ∧
        r.H (t + 1) = Function.update (r.H t) j (r.H t j ++ [(u t, r.p t)])) ∧
      r.μ (t + 1) = updateDensity (epsT T) (r.μ t) (u t) (r.p t) (Y t))

end RobustCtxPricing



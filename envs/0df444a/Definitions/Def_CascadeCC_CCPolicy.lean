-- Prove2me | Definitions.Def_CascadeCC_CCPolicy
-- name    : CascadeCC_CCPolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:32:49.179296+00:00
-- url     : https://prove2.me/theorems/133f915c-7873-4cea-a8ec-224b8200bfc6
-- title:
--   The Cascade Correction policy
-- statement:
--   Fix a horizon $N$, an initial inventory $Y\in\mathbb N^J$, and rates $a$ (the stationary solution $a^D$), and put $v^D_j=\sigma_j(a)a_j$. The state before period $t$ is the remaining inventory $y_t$ and the correction $\delta^v_t$, with $y_1=Y$ and $\delta^v_1=0$. In period $t$:
--
--   1. Set $\hat v_t=v^D-\delta^v_t$, and compute $\hat\sigma_{t,1}=\lambda$, $\hat\sigma_{t,j+1}=\zeta_j(\hat\sigma_{tj}-\hat v_{tj})$.
--   2. Set $\hat\alpha_{tj}=\hat v_{tj}/\hat\sigma_{tj}$.
--   3. The applied rate is $\alpha_{tj}=\hat\alpha_{tj}$ if $y_{tj}>0$ and $\hat\alpha_{tj}\in\Omega_\alpha$; otherwise it is the turn-off.
--   4. On the outcome, a sold product loses one unit, and with $\Delta_{tj}=D_{tj}-\sigma_j(\alpha_t)\alpha_{tj}$, computed at the applied rates,
--
--   $$
--   \delta^v_{t+1}=\delta^v_t+\frac{\Delta_t}{N-t},\qquad\text{that is}\qquad \delta^v_t=\sum_{s=1}^{t-1}\frac{\Delta_s}{N-s}.
--   $$
--
--   The correction acts on expected purchase rates and not on the conditional rates, so the applied rate is a ratio of two linearly corrected terms. $V^{k,CC}$ is the value of this policy.
--
--   **Formalization Note** The recursion for $\hat\sigma$ is the system (15) solved row by row: $\hat\sigma_{t,2:J}=A^{-1}M^{-1}\hat v_{t,1:J-1}+A^{-1}c$. Rate $0$ is the turn-off. At $\hat\sigma_{tj}=0$, Lean's $x/0=0$ gives rate $0$, which is the applied rate there in any reading. The state is computed by a fold along the history, so the policy depends on the past outcomes only. With $t$ 0-based the weight is $1/(N-t-1)$; at the last period it is $1/0=0$, a value no period reads. Inventories are natural numbers; a sale of a sold-out product has probability $0$, since its applied rate is $0$.
-- source:
--   Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, (15), (16), p.24; Definition 2, p.25; p.22 (V^{k,π})

import Mathlib
import Definitions.Def_CascadeCC_Model

namespace CascadeCC

variable {J : ℕ}

/-- The state of the Cascade Correction policy at the beginning of a period: the remaining inventory
y_t and the correction δ^v_t (Najafi, Duenyas, Jasin, Uichanco, Multi-product Dynamic Pricing with Limited Inventories under a Cascade Click Model, SSRN abstract_id=3362921, (16), p.24, and Definition 2, p.25). -/
structure CCState (J : ℕ) where
  /-- The remaining inventory. -/
  inv : Fin J → ℕ
  /-- The correction δ^v_t. -/
  corr : Fin J → ℝ

/-- The corrected expected purchase rates v̂_t = v^D − δ^v_t, Definition 2 (i), p.25, with v^D_j = σ_j(a) a_j
(SSRN abstract_id=3362921). -/
noncomputable def hatPurchase (M : Instance J) (a δ : Fin J → ℝ) (j : Fin J) : ℝ :=
  purchase M a j - δ j

/-- The arrival rates σ̂ induced by expected purchase rates v̂: σ̂_1 = λ, σ̂_{j+1} = ζ_j (σ̂_j − v̂_j).

**Formalization Note** This recursion is the system σ̂_{2:J} = A⁻¹ M⁻¹ v̂_{1:J−1} + A⁻¹ c of (15), p.24, and
Definition 2 (i), p.25, solved row by row, with no matrices (the row j of (15) reads
−v_j ζ_j = σ_{j+1} − ζ_j σ_j). The index is a natural number, 0-based; values past `J` are 0 and unused. -/
noncomputable def hatArrival (M : Instance J) (v : Fin J → ℝ) : ℕ → ℝ
  | 0 => M.lam
  | j + 1 => if h : j < J then M.zeta ⟨j, h⟩ * (hatArrival M v j - v ⟨j, h⟩) else 0

/-- The ideal rates α̂_tj = v̂_tj / σ̂_tj, Definition 2 (ii), p.25 (SSRN abstract_id=3362921); for the first
product σ̂_t1 = λ.

**Formalization Note** At σ̂_tj = 0, Lean's `x / 0 = 0` gives α̂_tj = 0, the turn-off, which is the
applied rate there in any reading. -/
noncomputable def hatRate (M : Instance J) (a δ : Fin J → ℝ) (j : Fin J) : ℝ :=
  hatPurchase M a δ j / hatArrival M (hatPurchase M a δ) j

open scoped Classical in
/-- The applied rates, Definition 2 (iii), p.25 (SSRN abstract_id=3362921): α̂_tj if the remaining inventory
of `j` is positive and α̂_tj ∈ Ω_α, and otherwise the turn-off, rate 0.

**Formalization Note** Rate 0 is p̄_j. The test is on [0, u], which covers both forms of Ω_α: for
Ω_α = (0, u], α̂_tj = 0 falls to the "otherwise" branch, which is the same rate. -/
noncomputable def appliedRate (M : Instance J) (a : Fin J → ℝ) (s : CCState J) (j : Fin J) : ℝ :=
  if 0 < s.inv j ∧ hatRate M a s.corr j ∈ Set.Icc 0 M.u then hatRate M a s.corr j else 0

open scoped Classical in
/-- One update of the state, on outcome `o` in the period with `t` earlier periods, of `N`: the inventory
falls by one for a sold product (Definition 2 (iv), p.25), and
δ^v_{t+1} = δ^v_t + ∆_t / (N − t) in 1-based periods ((16), p.24, SSRN abstract_id=3362921), where
∆_tj = D_tj − σ_j(α_t) α_tj is taken at the applied rates α_t.

**Formalization Note** With `t` 0-based the weight is 1 / (N − t − 1), in real subtraction. For the last
period it is 1 / 0 = 0, and that value is never read, since no period follows. The natural-number
`s.inv j - 1` does not truncate on any path of positive probability, since the applied rate of a sold-out
product is 0. -/
noncomputable def ccStep (M : Instance J) (N : ℕ) (a : Fin J → ℝ) (t : ℕ) (s : CCState J)
    (o : Option (Fin J)) : CCState J where
  inv := fun j => if o = some j then s.inv j - 1 else s.inv j
  corr := fun j => s.corr j +
    ((if o = some j then (1 : ℝ) else 0) - purchase M (appliedRate M a s) j) / ((N : ℝ) - t - 1)

/-- The fold of `ccStep` along a list of outcomes, oldest first, the head being the period with `t` earlier
periods. -/
noncomputable def ccFold (M : Instance J) (N : ℕ) (a : Fin J → ℝ) :
    ℕ → CCState J → List (Option (Fin J)) → CCState J
  | _, s, [] => s
  | t, s, o :: h => ccFold M N a (t + 1) (ccStep M N a t s o) h

/-- The state after a history `h`, for horizon `N` and initial inventory `Y`: y_1 = Y, δ^v_1 = 0, then
`ccStep` along `h`. Here `a` is a^D. -/
noncomputable def ccState (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ)
    (h : List (Option (Fin J))) : CCState J :=
  ccFold M N a 0 ⟨Y, 0⟩ h

/-- The Cascade Correction policy, Definition 2, p.25 (SSRN abstract_id=3362921), for horizon `N`, initial
inventory `Y` and stationary rates `a`. -/
noncomputable def ccPolicy (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) : RatePolicy J :=
  fun h => appliedRate M a (ccState M N Y a h)

/-- The expected total revenue V^{k,CC} of the Cascade Correction policy (SSRN abstract_id=3362921, p.22). -/
noncomputable def ccValue (M : Instance J) (N : ℕ) (Y : Fin J → ℕ) (a : Fin J → ℝ) : ℝ :=
  policyValue M N (ccPolicy M N Y a)

end CascadeCC



-- Prove2me | Definitions.Def_FocusSetRB_focusLaw
-- name    : FocusSetRB_focusLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:19:26.505653+00:00
-- url     : https://prove2.me/theorems/a452cba4-0cf4-4223-9d63-6e1ed82f1495
-- title:
--   Focus-set policies (Algorithm 1): update kernels, rectifiers and the reward of the process
-- statement:
--   A **focus-set policy** (Algorithm 1) runs as follows at every step $t=0,1,2,\dots$, starting from $S_0$ and an initial focus set $D_{-1}$:
--
--   1. choose a focus set $D_t\subseteq[N]$ based on $X_t$ and $D_{t-1}$ (set update);
--   2. sample ideal actions $\hat A_t(i)\sim\bar\pi^*(\cdot\mid S_t(i))$ independently for $i\in[N]$;
--   3. choose $A_t(i)$ for $i\in D_t$ to maximize $|\{i\in D_t: A_t(i)=\hat A_t(i)\}|$ subject to
--   $$
--   \alpha N-(N-|D_t|)\le\sum_{i\in D_t}A_t(i)\le\alpha N; \tag{4}
--   $$
--   4. choose $A_t(i)$ for $i\notin D_t$ so that $\sum_{i\in[N]}A_t(i)=\alpha N$; (5)
--   5. apply the actions and observe $S_{t+1}$.
--
--   The set update is any probability kernel from $(X_t,D_{t-1})$ to subsets of $[N]$. A **rectifier** is any probability kernel from $(X_t,D_t,\hat A_t)$ to action vectors whose every possible output satisfies (5), the constraint of (4), and maximal conformity on $D_t$ among all action vectors satisfying that constraint. The pair $(X_t,D_{t-1})$ is a Markov chain; its law at time $t$ determines the expected reward per arm at time $t$ and the liminf average reward $R^-(\pi,S_0)$ of the policy. A pair $(x,D)$ is **charged** if $(X_t,D_t)=(x,D)$ has positive probability for some $t$.
--
--   **Formalization Note** Kernels are real probability vectors. Constraint (4) is evaluated in the integers, so $\alpha N-(N-|D_t|)$ is never truncated. Ties and the choice of actions outside $D_t$ are left to the rectifier: Algorithm 2's uniform tie-breaking (lines 6–15) is one rectifier.
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Algorithm 1, eqs. (4)–(5), p.8; R⁻: §3.1, p.5

import Mathlib
import Definitions.Def_FocusSetRB_HRPolicy

namespace FocusSetRB

open Finset

variable {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}

/-- A **focus-set update kernel** (arXiv:2402.05689v4, Algorithm 1, line 2, p.8: "Choose a focus
set `D_t ⊆ [N]` based on `X_t` and `D_{t−1}`"): `sel x Dprev D` is the probability of choosing
`D_t = D` when the system state is `x` and the previous focus set is `Dprev`.

**Formalization Note.** A real-valued probability kernel; deterministic rules are Dirac
kernels. -/
def IsSelectorKernel (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ) : Prop :=
  (∀ x Dprev D, 0 ≤ sel x Dprev D) ∧ ∀ x Dprev, ∑ D, sel x Dprev D = 1

/-- An **action rectifier** of a focus-set policy (arXiv:2402.05689v4, Algorithm 1, lines 4–5,
eqs. (4)–(5), p.8): `rect x D Â A` is the probability of the action vector `A` given the system
state `x`, the focus set `D` and the ideal actions `Â`. Every `A` it can output
1. satisfies (5): `∑_{i ∈ [N]} A(i) = αN = k`;
2. satisfies the constraint of (4): `αN − (N − |D|) ≤ ∑_{i ∈ D} A(i) ≤ αN`;
3. maximizes `|{i ∈ D : A(i) = Â(i)}|` among all action vectors satisfying the constraint of (4)
   (line 4 of Algorithm 1).

**Formalization Note.** `k : ℕ` is `αN`. The constraint of (4) is in `ℤ`, so `k − (N − |D|)` is
not truncated. Ties in (4) and the choice of actions outside `D` in (5) are left to the kernel:
Algorithm 2's lines 6–15 (uniform tie-breaking) are one such rectifier. -/
def IsRectifier (k : ℕ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ) : Prop :=
  (∀ x D Ahat A, 0 ≤ rect x D Ahat A) ∧
  (∀ x D Ahat, ∑ A, rect x D Ahat A = 1) ∧
  ∀ x D Ahat A, 0 < rect x D Ahat A →
    IsBudgetFeasible k A ∧
    ((k : ℤ) - ((N : ℤ) - D.card) ≤ ((D.filter fun i => A i = true).card : ℤ) ∧
      ((D.filter fun i => A i = true).card : ℤ) ≤ k) ∧
    ∀ A' : Fin N → Bool,
      ((k : ℤ) - ((N : ℤ) - D.card) ≤ ((D.filter fun i => A' i = true).card : ℤ) ∧
        ((D.filter fun i => A' i = true).card : ℤ) ≤ k) →
      (D.filter fun i => A' i = Ahat i).card ≤ (D.filter fun i => A i = Ahat i).card

/-- One transition of the **focus-set policy** (arXiv:2402.05689v4, Algorithm 1, p.8) on the
augmented state `z = (X_t, D_{t−1})`: choose `D_t = D ∼ sel(X_t, D_{t−1})` (line 2), sample
`Â_t(i) ∼ π̄*(· | S_t(i))` independently (line 3), rectify `A_t ∼ rect(X_t, D_t, Â_t)`
(lines 4–5), and move the arms (line 6); the new augmented state is `(X_{t+1}, D_t)`. -/
noncomputable def focusStep (M : SingleArmMDP S) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (z z' : (Fin N → S) × Finset (Fin N)) : ℝ :=
  sel z.1 z.2 z'.2 *
    ∑ Ahat, idealLaw y z.1 Ahat * ∑ A, rect z.1 z'.2 Ahat A * stepProb M z.1 A z'.1

/-- The law at time `t` of `(X_t, D_{t−1})` under the focus-set policy started from the initial
state vector `S₀` and the initial focus set `D_{−1} = Dinit` (arXiv:2402.05689v4, Algorithm 1,
p.8). -/
noncomputable def focusLaw (M : SingleArmMDP S) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (S0 : Fin N → S) (Dinit : Finset (Fin N)) : ℕ → (Fin N → S) × Finset (Fin N) → ℝ
  | 0, z => if z = (S0, Dinit) then 1 else 0
  | t + 1, z' => ∑ z, focusLaw M y sel rect S0 Dinit t z * focusStep M y sel rect z z'

/-- The expected reward per arm at time `t` under the focus-set policy,
`(1/N) ∑_i 𝔼[r(S_t(i), A_t(i))]` (arXiv:2402.05689v4, §3.1, p.5, and Algorithm 1, p.8). -/
noncomputable def focusReward (M : SingleArmMDP S) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (S0 : Fin N → S) (Dinit : Finset (Fin N)) (t : ℕ) : ℝ :=
  ∑ z, focusLaw M y sel rect S0 Dinit t z *
    ∑ D, sel z.1 z.2 D * ∑ Ahat, idealLaw y z.1 Ahat *
      ∑ A, rect z.1 D Ahat A * ((1 / (N : ℝ)) * ∑ i, M.r (z.1 i) (A i))

/-- The liminf average reward `R⁻(π, S₀)` of the focus-set policy `π` given by `sel` and `rect`
(arXiv:2402.05689v4, §3.1, p.5). -/
noncomputable def focusRminus (M : SingleArmMDP S) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (S0 : Fin N → S) (Dinit : Finset (Fin N)) : ℝ :=
  cesaroLiminf (focusReward M y sel rect S0 Dinit)

/-- `(x, D)` is **charged** by the focus-set policy: for some `t ≥ 0`, `(X_t, D_t) = (x, D)` has
positive probability. A property holding at every charged pair holds almost surely at every time
step, which is how the "a.s." of Conditions 1–3 (arXiv:2402.05689v4, §5.1, pp.13–14) is read. -/
def IsChargedPair (M : SingleArmMDP S) (y : S → Bool → ℝ)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (S0 : Fin N → S) (Dinit : Finset (Fin N)) (x : Fin N → S) (D : Finset (Fin N)) : Prop :=
  ∃ t : ℕ, ∃ Dprev : Finset (Fin N), 0 < focusLaw M y sel rect S0 Dinit t (x, Dprev) * sel x Dprev D

end FocusSetRB



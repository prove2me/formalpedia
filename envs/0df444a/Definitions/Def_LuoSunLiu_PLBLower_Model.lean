-- Prove2me | Definitions.Def_LuoSunLiu_PLBLower_Model
-- name    : LuoSunLiu_PLBLower_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T19:14:22.887367+00:00
-- url     : https://prove2.me/theorems/5927f0ff-b5ce-4b62-8feb-d0c6ba3f55d1
-- title:
--   §2.2.4, p. 14 and §3.1, p. 22 — perturbed linear bandit, PB(ξ̃, C_p), randomized algorithms, trajectory and PLB regret
-- statement:
--   This file sets up the **perturbed linear bandit** (PLB) of Luo, Sun and Liu and the objects needed for its regret lower bound.
--
--   1. **Parameter set.** For a "central" parameter $\tilde\xi\in\mathbb R^d$ and a perturbation constant $C_p$,
--   $$PB(\tilde\xi, C_p)=\{\xi\in\mathbb R^d:\ \|\xi-\tilde\xi\|_\infty\le C_p/2\}.$$
--   2. **Perturbation.** A parameter sequence $(\xi_t)$ has perturbation $C_p$ if $\|\xi_s-\xi_t\|_\infty\le C_p$ for all periods $s,t$.
--   3. **Algorithms.** A (possibly randomized) algorithm has all its randomness in a sample point $\omega$ of a measurable space $\Omega$. Before period $t\ge1$ it has observed the past actions and rewards $(A_1,Z_1),\dots,(A_{t-1},Z_{t-1})$ and the current finite action set $\mathcal A_t\subset\mathbb R^d$; it then plays an action $A_t$, which must lie in $\mathcal A_t$ whenever $\mathcal A_t$ is nonempty. For each period and each action set the decision is jointly measurable in $\omega$ and the observed history.
--   4. **Trajectory.** Given deterministic parameters $(\xi_t)_{t\ge1}$, deterministic action sets $(\mathcal A_t)_{t\ge1}$ and a noise process $(\eta_t)_{t\ge1}$ on $\Omega$, the interaction is defined recursively: in period $t$ the algorithm plays $A_t$ from the history and $\mathcal A_t$, and observes the reward
--   $$Z_t=\langle\xi_t, A_t\rangle+\eta_t.$$
--   5. **Regret.** With $A^*_t\in\arg\max_{a\in\mathcal A_t}\langle\xi_t,a\rangle$, the PLB regret over $T_0$ periods is
--   $$R^{PLB}_{T_0}=\sum_{t=1}^{T_0}\langle\xi_t, A^*_t-A_t\rangle=\sum_{t=1}^{T_0}\Big(\max_{a\in\mathcal A_t}\langle\xi_t,a\rangle-\langle\xi_t,A_t\rangle\Big).$$
--
--   These objects are shared by every statement of the mission: the goal (Proposition 2) quantifies over all algorithms and constructs the parameters and action sets.
--
--   **Formalization Note** Periods are 1-based as in the paper; the algorithm's decision function is indexed by the number $n=t-1$ of completed periods, and entry $i$ of the history (type `Fin n`) is period $i+1$. Arms are coordinates `Fin d` (0-based). The norm on `Fin d → ℝ` is Mathlib's sup norm, which is $\|\cdot\|_\infty$. The algorithm sees the whole sample point $\omega$, so its decision may depend on the noise as well as on its own randomness; this only enlarges the class of algorithms. The maximum over an empty action set is set to $0$; every statement of the mission requires nonempty action sets. The paper's conditional sub-Gaussianity of $\eta_t$ is not part of these definitions; the goal theorem quantifies over every measurable noise process instead.
-- source:
--   Luo, Sun and Liu, arXiv:2109.07340v2, p. 14, §2.2.4 (definition of PLB); p. 22, §3.1 (PB(ξ̃, C_p)); App. A, proofs of Lemma 3 (p. 42) and Proposition 2 (p. 45) (regret r_t = ⟨ξ_t, A*_t − A_t⟩ and the expectation)

import Mathlib

namespace LuoSunLiu.PLBLower

open MeasureTheory

/-- The parameter set `PB(ξ̃, C_p) = {ξ ∈ ℝ^d : ‖ξ − ξ̃‖_∞ ≤ C_p / 2}` (p. 22). The norm on
`Fin d → ℝ` is Mathlib's default sup norm, i.e. `‖·‖_∞`. -/
def PB {d : ℕ} (ξc : Fin d → ℝ) (Cp : ℝ) : Set (Fin d → ℝ) :=
  {ξ | ‖ξ - ξc‖ ≤ Cp / 2}

/-- The perturbation condition of a perturbed linear bandit (p. 14): the parameters satisfy
`‖ξ_s − ξ_t‖_∞ ≤ C_p` for all periods `s, t`. -/
def IsPerturbed {d : ℕ} (ξ : ℕ → Fin d → ℝ) (Cp : ℝ) : Prop :=
  ∀ s t, ‖ξ s - ξ t‖ ≤ Cp

/-- A (possibly randomized, history-dependent) algorithm for a perturbed linear bandit with `d`
coordinates, whose randomness lives on the measurable space `Ω`.

Before period `n + 1` (paper's 1-based period), having observed the `n` past pairs
`(A_1, Z_1), …, (A_n, Z_n)` (encoded as `Fin n → (Fin d → ℝ) × ℝ`, entry `i` being period
`i + 1`) and the current action set `S = 𝒜_{n+1}`, the algorithm plays `decide n ω h S`.
The sample point `ω` carries the algorithm's internal randomness. -/
structure Algorithm (d : ℕ) (Ω : Type*) [MeasurableSpace Ω] where
  /-- The action played in period `n + 1`. -/
  decide : (n : ℕ) → Ω → (Fin n → (Fin d → ℝ) × ℝ) → Finset (Fin d → ℝ) → (Fin d → ℝ)
  /-- The action is taken from the current action set whenever that set is nonempty. -/
  decide_mem : ∀ n ω h S, S.Nonempty → decide n ω h S ∈ S
  /-- For every period and every action set, the action is jointly measurable in the
  randomness and the observed history. -/
  measurable_decide : ∀ n S,
    Measurable (fun p : Ω × (Fin n → (Fin d → ℝ) × ℝ) => decide n p.1 p.2 S)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The history `((A_1, Z_1), …, (A_n, Z_n))` after `n` periods, when the algorithm `alg` interacts
with the perturbed linear bandit with (deterministic) parameters `ξ`, (deterministic) action sets
`𝒜` and noise `η`: in period `t` it plays `A_t = alg.decide (t-1) ω (history) (𝒜 t)` and
observes `Z_t = ⟨ξ_t, A_t⟩ + η_t`. Entry `i : Fin n` is period `i + 1`. -/
noncomputable def history (alg : Algorithm d Ω) (ξ : ℕ → Fin d → ℝ)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) :
    (n : ℕ) → Ω → Fin n → (Fin d → ℝ) × ℝ
  | 0, _ => Fin.elim0
  | n + 1, ω =>
    Fin.snoc (α := fun _ => (Fin d → ℝ) × ℝ) (history alg ξ 𝒜 η n ω)
      (alg.decide n ω (history alg ξ 𝒜 η n ω) (𝒜 (n + 1)),
        ξ (n + 1) ⬝ᵥ alg.decide n ω (history alg ξ 𝒜 η n ω) (𝒜 (n + 1)) + η (n + 1) ω)

/-- The action `A_t` played in period `t ≥ 1` (1-based; the value at `t = 0` is not used). -/
noncomputable def action (alg : Algorithm d Ω) (ξ : ℕ → Fin d → ℝ)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : Fin d → ℝ :=
  alg.decide (t - 1) ω (history alg ξ 𝒜 η (t - 1) ω) (𝒜 t)

/-- The reward `Z_t = ⟨ξ_t, A_t⟩ + η_t` in period `t ≥ 1`. -/
noncomputable def reward (alg : Algorithm d Ω) (ξ : ℕ → Fin d → ℝ)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  ξ t ⬝ᵥ action alg ξ 𝒜 η t ω + η t ω

/-- The best expected reward `max_{a ∈ 𝒜_t} ⟨ξ_t, a⟩` in period `t`; on an empty action set
(excluded by every statement of the mission) it is `0`. -/
noncomputable def bestValue (ξ : ℕ → Fin d → ℝ) (𝒜 : ℕ → Finset (Fin d → ℝ)) (t : ℕ) : ℝ :=
  if h : (𝒜 t).Nonempty then (𝒜 t).sup' h (fun a => ξ t ⬝ᵥ a) else 0

/-- The PLB regret `R^{PLB}_{T_0} = ∑_{t=1}^{T_0} ⟨ξ_t, A*_t − A_t⟩` with
`A*_t ∈ argmax_{a ∈ 𝒜_t} ⟨ξ_t, a⟩` (proofs of Lemma 3 and Proposition 2). -/
noncomputable def regret (alg : Algorithm d Ω) (ξ : ℕ → Fin d → ℝ)
    (𝒜 : ℕ → Finset (Fin d → ℝ)) (η : ℕ → Ω → ℝ) (T0 : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T0, (bestValue ξ 𝒜 t - ξ t ⬝ᵥ action alg ξ 𝒜 η t ω)

end LuoSunLiu.PLBLower



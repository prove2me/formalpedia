-- Prove2me | Definitions.Def_DecodablePOMDP_POMDP
-- name    : DecodablePOMDP_POMDP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:23:04.460957+00:00
-- url     : https://prove2.me/theorems/4f34211f-21cf-4fa1-a5c6-bdef66d538cf
-- title:
--   Finite-horizon POMDP $\mathcal P=(H,\mathcal S,\mathcal A,\mathcal O,\mu_1,T,K,r)$ and its validity
-- statement:
--   A **finite-horizon partially observable Markov decision process** (POMDP) $\mathcal P=(H,\mathcal S,\mathcal A,\mathcal O,\mu_1,T,K,r)$ consists of a state space $\mathcal S$, an action space $\mathcal A$, an observation space $\mathcal O$, a horizon $H$, an initial law $\mu_1$ of the state $s_1$, transition kernels $T_h(s'\mid s,a)$, observation channels $K_h(y\mid s)$ and rewards $r_h(y)$.
--
--   $\mathcal P$ is **valid** when
--
--   1. $H\ge 1$ and $\mu_1$ is a probability vector on $\mathcal S$;
--   2. $T_h(\cdot\mid s,a)$ is a probability vector on $\mathcal S$ for every $h\in[1:H-1]$, $s$, $a$;
--   3. $K_h(\cdot\mid s)$ is a probability vector on $\mathcal O$ for every $h\in[2:H]$ and $s$;
--   4. $0\le r_h(y)\le 1$ for every $h\in[2:H]$ and $y$.
--
--   At time $h\in[1:H-1]$ the action $a_h$ moves the state to $s_{h+1}\sim T_h(\cdot\mid s_h,a_h)$; for $h\ge2$ the planner observes $y_h\sim K_h(\cdot\mid s_h)$ and receives $r_h(y_h)$. This is the model of every statement of the mission; the augmented and killed POMDPs of §3 are again POMDPs in this sense, on larger state and observation spaces.
--
--   **Formalization Note** The kernels are indexed by every natural number $h$; only the indices listed above are read and constrained.
-- source:
--   Dobson, Jog, Shiu, Quasipolynomial-Time Planning for Decodable POMDPs (preprint, sha256 c1256cbe…3584b), §2, pp.5–6

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist

namespace DecodablePOMDP

open CalibratedCE.Forecast

/-- **Finite-horizon POMDP** `P = (H, S, A, O, μ₁, T, K, r)`.

Dobson, Jog, Shiu, *Quasipolynomial-Time Planning for Decodable POMDPs* (preprint, sha256
c1256cbe…3584b), §2, pp.5–6: "A partially observable Markov decision process (POMDP) P consists of
a state space S of size S, an action space A of size A, an observation space O of size O, and a
finite time horizon H. At time h = 1, the initial state s1 of the POMDP is drawn from a known
distribution µ1. An action ah ∈ A at time h ∈ [1 : H − 1] updates the state sh ∈ S to
sh+1 ∼ Th(·|sh, ah). … For h ≥ 2, the planner observes yh ∈ O, which is the hidden state sh passed
through an observation channel Kh … the collection of reward functions rh : O → [0, 1]".

Fields: `H` the horizon, `μ₁ s` the initial law, `T h s a s'` = `T_h(s' | s, a)`, `K h s y` =
`K_h(y | s)`, `r h y` = `r_h(y)`.

**Formalization Note.** The state, action and observation spaces are the types `S`, `A`, `O`
(finite in every use). The kernels are indexed by every `h : ℕ`; only `T_h` for `h ∈ [1 : H−1]`,
`K_h` and `r_h` for `h ∈ [2 : H]` are ever read, and only those are constrained by `IsValid`. -/
structure POMDP (S A O : Type) where
  H : ℕ
  μ₁ : S → ℝ
  T : ℕ → S → A → S → ℝ
  K : ℕ → S → O → ℝ
  r : ℕ → O → ℝ

/-- **Validity of a POMDP** (§2, pp.5–6): `H ≥ 1`; `μ₁` is a probability vector; every
`T_h(· | s, a)`, `h ∈ [1 : H−1]`, and every `K_h(· | s)`, `h ∈ [2 : H]`, is a probability vector;
and `r_h(y) ∈ [0, 1]` for `h ∈ [2 : H]`.

Dobson, Jog, Shiu (preprint, sha256 c1256cbe…3584b), §2, pp.5–6.

**Formalization Note.** Out-of-range kernels are unconstrained and never read. -/
def POMDP.IsValid {S A O : Type} [Fintype S] [Fintype O] (P : POMDP S A O) : Prop :=
  1 ≤ P.H ∧ IsDist P.μ₁ ∧
  (∀ h, 1 ≤ h → h ≤ P.H - 1 → ∀ s a, IsDist (P.T h s a)) ∧
  (∀ h, 2 ≤ h → h ≤ P.H → ∀ s, IsDist (P.K h s)) ∧
  (∀ h, 2 ≤ h → h ≤ P.H → ∀ y, 0 ≤ P.r h y ∧ P.r h y ≤ 1)

end DecodablePOMDP



-- Prove2me | Definitions.Def_UninformedMG_enr
-- name    : UninformedMG_enr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:00.30981+00:00
-- url     : https://prove2.me/theorems/de7fd7dd-e4f4-44cc-9484-4eb636396a08
-- title:
--   Values $V^{\mu,\nu}_h$, the empirical Nash value $V^{\mathrm{emp}}_h$ (1) and empirical Nash-value regret $\mathrm{Enr}_K$ (2)
-- statement:
--   For policies $(\mu,\nu)$ the **state value** is $V^{\mu,\nu}_{H+1}=0$ and, for $h\in[H]$ and $s\in S_h$,
--   $$V^{\mu,\nu}_h(s)=\mathbb E_{a\sim\mu_h(\cdot\mid s),\,b\sim\nu_h(\cdot\mid s)}\big[\ell_h(s,a,b)+P_hV^{\mu,\nu}_{h+1}(s,a,b)\big],\qquad P_hf(s,a,b)=\sum_{s'}P_h(s'\mid s,a,b)f(s').$$
--
--   For opponent policies $\nu^1,\dots,\nu^K$, the **empirical Nash value** is $V^{\mathrm{emp}}_{H+1}=0$ and
--   $$V^{\mathrm{emp}}_h(s)=\min_{x\in\Delta(A_h)}\ \max_{\nu\in\{\nu^1_h(\cdot\mid s),\dots,\nu^K_h(\cdot\mid s)\}}\ \sum_{a\in A_h}\sum_{b\in B_h}x(a)\nu(b)\big[\ell_h(s,a,b)+P_hV^{\mathrm{emp}}_{h+1}(s,a,b)\big].$$
--   The maximum is taken separately at each state, so different states may use different opponent policies. For learner policies $\mu^k$ and initial states $s^k_1$, the **empirical Nash-value regret** is
--   $$\mathrm{Enr}_K=\sum_{k=1}^K\big[V^{\mu^k,\nu^k}_1(s^k_1)-V^{\mathrm{emp}}_1(s^k_1)\big].$$
--
--   $\mathrm{Enr}_K$ is the performance measure of Theorem 2.1. It recovers external regret when the opponent is fixed.
--
--   **Formalization Note** The paper defines $V^{\mu,\nu}$ as an expected cumulative loss and states the Bellman equation. Here $V^{\mu,\nu}$ is defined by that backward recursion, which determines it. The minimum is the real infimum over the simplex subtype, which is attained. The maximum is the real supremum over $j\in\{1,\dots,K\}$, a maximum for $K\ge1$.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Section 1.1, Eqs. (1)–(2) and the Bellman equation, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_UninformedMG_Game

namespace UninformedMG

variable {H : ℕ}

/-- `P_h f (s, a, b) = ∑_{s'} P_h(s' | s, a, b) f(s')` for a function `f` on the next layer (p.2). -/
noncomputable def PV (G : Game H) (h : Fin H) (f : G.St h.succ → ℝ) (s : G.St h.castSucc)
    (a : G.Act h) (b : G.Opp h) : ℝ :=
  ∑ s', G.trans h s a b s' * f s'

/-- The one-step Bellman expression `E_{a∼x, b∼y}[ℓ_h(s,a,b) + P_h f(s,a,b)]` for distributions
`x` on `A_h` and `y` on `B_h` (p.2, and the bracket of Eq. (1)). -/
noncomputable def stageVal (G : Game H) (h : Fin H) (x : G.Act h → ℝ) (y : G.Opp h → ℝ)
    (f : G.St h.succ → ℝ) (s : G.St h.castSucc) : ℝ :=
  ∑ a, ∑ b, x a * y b * (G.loss h s a b + PV G h f s a b)

/-- **State value function** `V^{μ,ν}_h(s)` (p.2): `V^{μ,ν}_{H+1} = 0` and the Bellman equation
`V^{μ,ν}_h(s) = E_{a∼μ_h(·|s), b∼ν_h(·|s)}[ℓ_h(s,a,b) + P_h V^{μ,ν}_{h+1}(s,a,b)]`.

**Formalization Note.** The paper defines `V` as the expected cumulative loss of the trajectory
and notes that it satisfies the Bellman equation; here `V` is defined by that backward
recursion, which determines it. Lean layer `h` is paper step `h + 1`; `Fin.last H` is the
terminal layer, where the value is `0`. -/
noncomputable def value (G : Game H) (μ : LPolicy G) (ν : OPolicy G) :
    (h : Fin (H + 1)) → G.St h → ℝ :=
  Fin.reverseInduction (motive := fun h => G.St h → ℝ) (fun _ => 0)
    (fun i f s => stageVal G i (μ i s) (ν i s) f s)

/-- **Empirical Nash value** (Eq. (1), p.2 = PDF p.4). For the realized opponent policies
`ν^1, …, ν^K`, `V^emp_{H+1} = 0` and, at each step `h` and state `s ∈ S_h`,
`V^emp_h(s) = min_{x ∈ Δ(A_h)} max_{ν ∈ {ν^1_h(·|s), …, ν^K_h(·|s)}} ∑_{a,b} x(a) ν(b)
 [ℓ_h(s,a,b) + P_h V^emp_{h+1}(s,a,b)]`.

**Formalization Note.** The maximum is over `j : Fin K`, separately at each state, so different
states may use different `j`. The minimum is the real infimum over the simplex subtype (a
nonempty compact set on which the objective is continuous, so it is attained); the maximum is
the real supremum over `Fin K`, which is a maximum for `K ≥ 1` (every statement of the mission
assumes `K ≥ 1`). -/
noncomputable def empValue (G : Game H) {K : ℕ} (ν : Fin K → OPolicy G) :
    (h : Fin (H + 1)) → G.St h → ℝ :=
  Fin.reverseInduction (motive := fun h => G.St h → ℝ) (fun _ => 0)
    (fun i f s => ⨅ x : stdSimplex ℝ (G.Act i), ⨆ j : Fin K, stageVal G i x.1 (ν j i s) f s)

/-- **Empirical Nash-value regret** (Eq. (2), p.2 = PDF p.4):
`Enr_K = ∑_{k=1}^K [V^{μ^k,ν^k}_1(s^k_1) − V^emp_1(s^k_1)]`, for the learner's policies `μ^k`,
the opponent's policies `ν^k` and the initial states `s^k_1` (Lean episodes `0, …, K − 1`). -/
noncomputable def enr (G : Game H) {K : ℕ} (μ : Fin K → LPolicy G) (ν : Fin K → OPolicy G)
    (s₁ : Fin K → G.St 0) : ℝ :=
  ∑ k, (value G (μ k) (ν k) 0 (s₁ k) - empValue G ν 0 (s₁ k))

end UninformedMG



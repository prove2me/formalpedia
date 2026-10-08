-- Prove2me | Definitions.Def_TwiceRegMDP_RobustReg_Robust
-- name    : TwiceRegMDP_RobustReg_Robust
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T13:26:33.26005+00:00
-- url     : https://prove2.me/theorems/8f082bfb-b57e-4ace-b4a8-f9a2bfad4b53
-- title:
--   Robust Bellman operator $T^{\pi,\mathcal U}$, the s-rectangular sets $(P_0+\mathcal P)\times(r_0+\mathcal R)$ and $\{P_0\}\times(r_0+\mathcal R)$, and the matrix $v\cdot\pi_s$
-- statement:
--   A **robust MDP** has an uncertain model $(P,r)$ ranging over an uncertainty set $\mathcal U$. For a policy $\pi$ and $v\in\mathbb R^{\mathcal S}$, the **robust Bellman evaluation operator** is
--   $$[T^{\pi,\mathcal U}v](s) := \min_{(P,r)\in\mathcal U} T^\pi_{(P,r)}v(s), \qquad s\in\mathcal S .$$
--
--   Given a nominal transition kernel $P_0$ and reward $r_0$, and for each state $s$ a set $\mathcal P_s\subseteq\mathbb R^{\mathcal X}$ of transition perturbations (with entries $P_s(s',a)$) and a set $\mathcal R_s\subseteq\mathbb R^{\mathcal A}$ of reward perturbations, the **s-rectangular uncertainty set** $\mathcal U = (P_0+\mathcal P)\times(r_0+\mathcal R)$ consists of all models
--   $$P(s'\mid s,a) = P_0(s'\mid s,a) + P_s(s',a),\qquad r(s,a) = r_0(s,a) + r_s(a),$$
--   where $P_s\in\mathcal P_s$ and $r_s\in\mathcal R_s$ are chosen independently for every $s$. The **reward-robust** set $\mathcal U = \{P_0\}\times(r_0+\mathcal R)$ keeps the transition at $P_0$ and perturbs only the reward in the same way.
--
--   Finally, for $v\in\mathbb R^{\mathcal S}$, a policy $\pi$ and a state $s$, the matrix $v\cdot\pi_s\in\mathbb R^{\mathcal X}$ is $[v\cdot\pi_s](s',a) := v(s')\pi_s(a)$.
--
--   These objects carry the robust-to-regularized equivalences of Sections 3 and 4 of the paper.
--
--   **Formalization Note.** The minimum is the real `sInf` of the values over $\mathcal U$; it is the true minimum when $\mathcal U$ is nonempty and compact, which every theorem assumes. A perturbation $P_s$ is a function on `S × A` (the paper's $\mathbb R^{\mathcal X}$, indexed $(s',a)$).
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 4 (Robust MDPs: T^{π,U}, rectangular sets), p. 5 (uncertainty sets (P_0 + P) × (r_0 + R) and {P_0} × (r_0 + R)), p. 6 (Theorem 4.1: [v · π_s](s', a))

import Mathlib
import Definitions.Def_TwiceRegMDP_RobustReg_MDP

namespace TwiceRegMDP.RobustReg

/-- The robust Bellman evaluation operator of an uncertainty set `U` of models `(P, r)`
(Derman–Geist–Mannor, arXiv:2110.06267v1, p. 4):
`[T^{π,U} v](s) := min_{(P,r) ∈ U} T^π_{(P,r)} v(s)`, written as the real `sInf` of the values.
It is the true minimum when `U` is nonempty and compact, which every theorem using it assumes. -/
noncomputable def robustOp {S A : Type} [Fintype S] [Fintype A] (γ : ℝ)
    (U : Set ((S → A → S → ℝ) × (S → A → ℝ))) (π : S → A → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => sInf ((fun m : (S → A → S → ℝ) × (S → A → ℝ) => evalOp γ m.1 m.2 π v s) '' U)

/-- The s-rectangular uncertainty set `U = (P₀ + 𝒫) × (r₀ + ℛ)` around a nominal model `(P₀, r₀)`
(pp. 4–5), with `𝒫 = ×_s 𝒫_s` and `ℛ = ×_s ℛ_s`. The perturbation `P_s ∈ 𝒫_s ⊆ ℝ^{S×A}` of the
transition block at `s` is indexed as in the paper, `P_s(s', a)`, and is added to `P₀(s'|s, a)`;
the reward perturbation `r_s ∈ ℛ_s ⊆ ℝ^A` is added to `r₀(s, ·)`. -/
def rectUncertainty {S A : Type} (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Pset : S → Set (S × A → ℝ)) (Rset : S → Set (A → ℝ)) :
    Set ((S → A → S → ℝ) × (S → A → ℝ)) :=
  {m | ∃ (Pp : S → S × A → ℝ) (rp : S → A → ℝ), (∀ s, Pp s ∈ Pset s ∧ rp s ∈ Rset s) ∧
    m = (fun s a s' => P₀ s a s' + Pp s (s', a), fun s a => r₀ s a + rp s a)}

/-- The reward-robust uncertainty set `U = {P₀} × (r₀ + ℛ)` with `ℛ = ×_s ℛ_s` (p. 5): the
transition model is the nominal `P₀`, the reward is `r₀(s, ·) + r_s` with `r_s ∈ ℛ_s`. -/
def rewardUncertainty {S A : Type} (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ)
    (Rset : S → Set (A → ℝ)) : Set ((S → A → S → ℝ) × (S → A → ℝ)) :=
  {m | ∃ rp : S → A → ℝ, (∀ s, rp s ∈ Rset s) ∧ m = (P₀, fun s a => r₀ s a + rp s a)}

/-- The matrix `v · π_s ∈ ℝ^{S×A}`, `[v · π_s](s', a) := v(s') π_s(a)` (p. 6). -/
def vDotPi {S A : Type} (v : S → ℝ) (π : S → A → ℝ) (s : S) : S × A → ℝ :=
  fun x => v x.1 * π s x.2

end TwiceRegMDP.RobustReg



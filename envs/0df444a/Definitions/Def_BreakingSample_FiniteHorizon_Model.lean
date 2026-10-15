-- Prove2me | Definitions.Def_BreakingSample_FiniteHorizon_Model
-- name    : BreakingSample_FiniteHorizon_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:08.726226+00:00
-- url     : https://prove2.me/theorems/ca437732-bf15-4579-bf71-2d5084f1ac37
-- title:
--   §2.2, p. 6, §7.1–7.2, p. 20 — time-inhomogeneous finite-horizon MDP: V^π_h, Q^π_h, V⋆_h, Q⋆_h, the DP planner, Var and the auxiliary sequence (62)
-- statement:
--   This module fixes the time-inhomogeneous finite-horizon Markov decision process of §2.2 and the objects of its analysis in §7.
--
--   Let $\mathcal S$ be a finite state space, $\mathcal A$ a finite nonempty action space and $H$ the horizon. For each step $h\in[H]=\{1,\dots,H\}$ there is a transition kernel $P_h(s'\mid s,a)$ and a reward $r_h(s,a)$.
--
--   1. **The setting.** The pair $(\{P_h\},\{r_h\})$ is a finite-horizon MDP if every $P_h(\cdot\mid s,a)$ is a probability vector on $\mathcal S$ and every reward lies in $[0,1]$.
--   2. **Backward propagation.** For a deterministic nonstationary policy $\pi=\{\pi_h\}$ (with $\pi_h:\mathcal S\to\mathcal A$) and step rewards $\rho_h:\mathcal S\to\mathbb R$, define $V_{H+1}=0$ and
--   $$V_h=\rho_h+P_{h,\pi}V_{h+1},\qquad (P_{h,\pi}V)(s)=\sum_{s'}P_h(s'\mid s,\pi_h(s))\,V(s').$$
--   3. **Values.** $V^\pi_h$ is the propagation of $\rho_h(s)=r_h(s,\pi_h(s))$, the Bellman equation (60); $Q^\pi_h(s,a)=r_h(s,a)+\sum_{s'}P_h(s'\mid s,a)V^\pi_{h+1}(s')$, the Bellman equation (58).
--   4. **Optimal values.** $V^\star_h(s)=\max_\pi V^\pi_h(s)$, the maximum over the finitely many deterministic nonstationary policies, and $Q^\star_h(s,a)=r_h(s,a)+\sum_{s'}P_h(s'\mid s,a)V^\star_{h+1}(s')$. A policy $\pi^\star$ is optimal if $V^{\pi^\star}_h=V^\star_h$ at every step.
--   5. **The DP planner** of §4.1. A tie-breaking rule $\mathrm{sel}$ picks, at each step $h$ and state $s$, a maximizer $\mathrm{sel}_h(s,q)\in\arg\max_a q(a)$ of any vector $q\in\mathbb R^{\mathcal A}$. The planner of the MDP $(\{P_h\},\{r_h\})$ is the greedy policy $\pi_h(s)=\mathrm{sel}_h\big(s,Q^\star_h(s,\cdot)\big)$.
--   6. **Variances.** $\mathrm{Var}_{P_{h,\pi}}(V)(s)=\sum_{s'}P_h(s'\mid s,\pi_h(s))V(s')^2-\big(\sum_{s'}P_h(s'\mid s,\pi_h(s))V(s')\big)^2$ and $\mathrm{Var}_{P_h}(V)(s,a)$, the same quantity under $P_h(\cdot\mid s,a)$.
--   7. **The auxiliary sequence (62).** $r^{(0)}_h=r^\pi_h$ and $r^{(l)}_h=\sqrt{\mathrm{Var}_{P_{h,\pi}}(V^{(l-1)}_{h+1})}$ for $l\ge1$, where $V^{(l)}$ is the propagation of $r^{(l)}$ through the true kernels. The empirical counterpart $\widehat V^{(l)}$ propagates the same $r^{(l)}$ through another family of kernels $\widehat P_h$.
--
--   These objects are the vocabulary of Theorem 4 and of its proof in §7 and Appendix C. With rewards in $[0,1]$ all values lie in $[0,H]$.
--
--   **Formalization Note** Steps are `Fin H`, 0-based: the paper's step $h$ is Lean's $h-1$, and the propagation returns $0$ at every index $\ge H$, which encodes $V_{H+1}=0$. $V^\pi_h$ is defined by the backward recursion rather than as the trajectory expectation of p. 6; for a deterministic policy the two agree (tower property). $Q^\star_h$ is defined by the one-step formula $r_h+P_hV^\star_{h+1}$, which equals $\max_\pi Q^\pi_h$ in a finite MDP. The planner takes the tie-breaking rule as an argument, so that the policy it returns is a fixed function of the empirical kernels; ties in the empirical $Q$-values occur with positive probability. The policy argument of the propagation is used only at steps $<H$.
-- source:
--   arXiv:2005.12900v8, §2.2, p. 6; §4.1, p. 10; §7.1, (58)–(60), p. 20; §7.2, (61)–(62), p. 20; (28), p. 13

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel

namespace BreakingSample.FiniteHorizon

open FoundationsML.ReinforcementLearning

/-- The standing setting of §2.2 (arXiv:2005.12900v8, p. 6): a kernel `P h` and a reward `r h ∈ [0,1]` at
every step. Steps are `Fin H`: the paper's step `h ∈ [H]` is `⟨h - 1, _⟩`. -/
def IsFHMDP {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) : Prop :=
  (∀ h, IsTransitionKernel (P h)) ∧ ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1

/-- Backward propagation `V_h = ρ_h + P_{h,π} V_{h+1}`, `V_{H+1} = 0` (the recursions (60) and (62), p. 20),
indexed by `h : ℕ` from `0`; `0` for `h ≥ H`. -/
noncomputable def propagate {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ)
    (π : Fin H → S → A) (ρ : Fin H → S → ℝ) : ℕ → S → ℝ
  | h, s =>
    if hh : h < H then
      ρ ⟨h, hh⟩ s + ∑ s', P ⟨h, hh⟩ s (π ⟨h, hh⟩ s) s' * propagate P π ρ (h + 1) s'
    else 0
  termination_by h => H - h
  decreasing_by all_goals omega

/-- `V^π_h(s)` (§2.2, p. 6) by the Bellman equation (60), p. 20. -/
noncomputable def value {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ)
    (r : Fin H → S → A → ℝ) (π : Fin H → S → A) : ℕ → S → ℝ :=
  propagate P π (fun h s => r h s (π h s))

/-- `Q^π_h(s,a) = r_h(s,a) + P_h V^π_{h+1}` (58), p. 20. -/
noncomputable def qValue {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ)
    (r : Fin H → S → A → ℝ) (π : Fin H → S → A) (h : Fin H) (s : S) (a : A) : ℝ :=
  r h s a + ∑ s', P h s a s' * value P r π (h.val + 1) s'

/-- `V⋆_h(s) = max_π V^π_h(s)` over the finitely many deterministic nonstationary policies (p. 6). -/
noncomputable def optValue {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (h : ℕ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun π : Fin H → S → A => value P r π h s)

/-- `Q⋆_h(s,a) = r_h(s,a) + P_h V⋆_{h+1}` (equal to `max_π Q^π_h(s,a)`, p. 6). -/
noncomputable def optQ {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (h : Fin H) (s : S) (a : A) : ℝ :=
  r h s a + ∑ s', P h s a s' * optValue P r (h.val + 1) s'

/-- `π` is an optimal policy of `(P, r)`: `V^π_h(s) = V⋆_h(s)` at every step and state (the policy `π⋆` of
p. 6, with `V⋆_h = V^{π⋆}_h` as used under (65), p. 21). -/
def IsOptimal {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (π : Fin H → S → A) : Prop :=
  ∀ (h : Fin H) (s : S), value P r π h.val s = optValue P r h.val s

/-- A tie-breaking rule for the DP: `sel h s q` maximizes `q`. -/
def IsArgmaxRule {S A : Type*} {H : ℕ} (sel : Fin H → S → (A → ℝ) → A) : Prop :=
  ∀ h s (q : A → ℝ) a, q a ≤ q (sel h s q)

/-- The DP planner of §4.1, p. 10: greedy for `Q⋆_h` of the MDP `(P, r)`, with the rule `sel`. -/
noncomputable def dpPolicy {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] {H : ℕ}
    (P : Fin H → S → A → S → ℝ) (r : Fin H → S → A → ℝ) (sel : Fin H → S → (A → ℝ) → A) :
    Fin H → S → A :=
  fun h s => sel h s (optQ P r h s)

/-- `Var_{P_{h,π}}(V)(s)` (§7.1, p. 20, with (28)). -/
def varStep {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ) (π : Fin H → S → A)
    (h : Fin H) (V : S → ℝ) (s : S) : ℝ :=
  ∑ s', P h s (π h s) s' * V s' ^ 2 - (∑ s', P h s (π h s) s' * V s') ^ 2

/-- `Var_{P_h}(V)(s,a)`, the variance of `V` under `P_h(·|s,a)` (§6.1, p. 12, used in (66), p. 21). -/
def varSA {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ)
    (h : Fin H) (V : S → ℝ) (s : S) (a : A) : ℝ :=
  ∑ s', P h s a s' * V s' ^ 2 - (∑ s', P h s a s' * V s') ^ 2

/-- The auxiliary rewards `r⁽ˡ⁾_h` of (62), p. 20 (built from the true kernel `P`). -/
noncomputable def auxReward {S A : Type*} [Fintype S] {H : ℕ} (P : Fin H → S → A → S → ℝ)
    (r : Fin H → S → A → ℝ) (π : Fin H → S → A) : ℕ → Fin H → S → ℝ
  | 0 => fun h s => r h s (π h s)
  | l + 1 => fun h s => Real.sqrt (varStep P π h (propagate P π (auxReward P r π l) (h.val + 1)) s)

end BreakingSample.FiniteHorizon



-- Prove2me | Definitions.Def_FlexCommitRO_BoxExt_WorstCaseDP
-- name    : FlexCommitRO_BoxExt_WorstCaseDP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T03:59:48.284565+00:00
-- url     : https://prove2.me/theorems/7168f6ac-b362-430e-8698-18e01407fd9b
-- title:
--   Appendix, pp. 269–270 — convex polyhedral functions, the worst-case multistage problem P[F_0, …, F_T] of Lemma 2, its optimal value, and Φ_T, φ
-- statement:
--   **Convex polyhedral functions.** Following Lemma 2 of the Appendix, a function $f : \mathbb R^m \to \mathbb R \cup \{+\infty\}$ is a **convex polyhedral function (c.p.f.)** if it never takes the value $-\infty$, its domain $\operatorname{Dom} f = \{s : f(s) < \infty\}$ is exactly the solution set $\{s : Gs \le g\}$ of finitely many nonstrict linear inequalities, and $f$ is convex and lower semicontinuous on $\operatorname{Dom} f$.
--
--   **The worst-case multistage problem.** Fix dimensions $n_\tau, m_t, k_t$, matrices $A_t$, $B_t$, $C_t$, vectors $b_t$, functions $f_t$ on $\mathbb R^{m_t}$, a bound $R$, and sets $F_\tau \subseteq \mathbb R^{n_\tau}$. Trajectories are $d = (d_0, d_1, \dots, d_T)$ with $d_\tau \in F_\tau$; write $\mathbb F_T = F_0 \times \dots \times F_T$. A policy is a family of decision rules $S_t(d^{t-1}) \in \mathbb R^{m_t}$, $t = 1,\dots,T+1$, depending only on $d_0,\dots,d_{t-1}$. It is feasible for $(P[F_0,\dots,F_T])$ if for all $d \in \mathbb F_T$
--   $$
--   A_1 S_1(d^0) \ge b_1,\qquad A_{t+1}S_{t+1}(d^t) \ge B_{t+1} d_t + C_{t+1} S_t(d^{t-1}) + b_{t+1}\ (1 \le t \le T),\qquad \|S_t(d^{t-1})\|_\infty \le R\ (1 \le t \le T+1).
--   $$
--   The optimal value is
--   $$
--   \operatorname{opt}(P[F_0,\dots,F_T]) = \inf_{\text{feasible } S}\ \sup_{d \in \mathbb F_T} \sum_{t=1}^{T+1} f_t\big(S_t(d^{t-1})\big) \in [-\infty, +\infty].
--   $$
--
--   **Bellman quantities** (proof of Lemma 2, p. 270): $\Phi_T(s_T, d_T) = \min\{f_{T+1}(s_{T+1}) : A_{T+1}s_{T+1} \ge B_{T+1}d_T + C_{T+1}s_T + b_{T+1},\ \|s_{T+1}\|_\infty \le R\}$ and $\varphi(s_T) = \max_{d_T \in F_T} \Phi_T(s_T, d_T)$, both as extended-real infimum and supremum.
--
--   These objects carry Lemma 2 (worst-case problems over polytopes have the same value over the extreme points), which is the engine of Proposition 1.
--
--   **Formalization Note** The families are $\mathbb N$-indexed with the paper's own indices ($d_\tau$ for $\tau = 0,\dots,T$, $S_t$ for $t = 1,\dots,T+1$); Lean's `B t` and `C t` stand for the paper's $B_{t+1}$ and $C_{t+1}$, and `Phi … t` is the paper's $\Phi_t$. Coordinates of a trajectory beyond $T$ are unconstrained and irrelevant. The norm on `Fin m → ℝ` is Mathlib's default sup norm, which is $\|\cdot\|_\infty$. Optimal values are `EReal` (`⊤` if infeasible). The minimization over the epigraph variable $E$ is written directly as the supremum over trajectories.
-- source:
--   Ben-Tal, Golany, Nemirovski & Vial, Retailer-supplier flexible commitments contracts: a robust optimization approach, MSOM 7(3) (2005), pp. 269–270, Appendix, Lemma 2 (problem P[F_0, …, F_T], definition of c.p.f.) and proof of Lemma 2 (Φ_T, φ)

import Mathlib

namespace FlexCommitRO.BoxExt

open Matrix

/-- Convex polyhedral function (c.p.f.) in the sense of Lemma 2 (p. 269): `f` takes real values and
the value `+∞` (never `−∞`), its domain `{s | f s < ∞}` is exactly the solution set of finitely
many nonstrict linear inequalities `G s ≤ g`, and `f` is convex and lower semicontinuous on its
domain. -/
def IsCPF {m : ℕ} (f : (Fin m → ℝ) → EReal) : Prop :=
  (∀ s, f s ≠ ⊥) ∧
  (∃ (k : ℕ) (G : Matrix (Fin k) (Fin m) ℝ) (g : Fin k → ℝ),
      {s | f s ≠ ⊤} = {s | G *ᵥ s ≤ g}) ∧
  ConvexOn ℝ {s | f s ≠ ⊤} (fun s => (f s).toReal) ∧
  LowerSemicontinuousOn (fun s => (f s).toReal) {s | f s ≠ ⊤}

/-- The set `𝔽_T = F_0 × ⋯ × F_T` of trajectories `d = (d_0, …, d_T)`; a trajectory is an
`ℕ`-indexed family `d τ ∈ ℝ^{n_τ}`, and coordinates beyond `T` are unconstrained. -/
def traj {n : ℕ → ℕ} (F : (τ : ℕ) → Set (Fin (n τ) → ℝ)) (T : ℕ) :
    Set ((τ : ℕ) → Fin (n τ) → ℝ) :=
  {d | ∀ τ ≤ T, d τ ∈ F τ}

/-- Feasibility of a policy `S` (with `S t d ∈ ℝ^{m_t}` the decision of stage `t`) for the
constraints of `(P[F_0, …, F_T])` (Lemma 2, p. 269): nonanticipativity on `𝔽_T` (`S_t` depends
only on `d_0, …, d_{t−1}`), `A_1 S_1 ≥ b_1`, the linking constraints
`A_{t+1} S_{t+1} ≥ B_{t+1} d_t + C_{t+1} S_t + b_{t+1}` for `t = 1, …, T`, and
`‖S_t‖_∞ ≤ R` for `t = 1, …, T + 1`. Here `B t`, `C t` stand for the paper's `B_{t+1}`, `C_{t+1}`. -/
def DPFeasible {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (R : ℝ) (F : (τ : ℕ) → Set (Fin (n τ) → ℝ))
    (S : (t : ℕ) → ((τ : ℕ) → Fin (n τ) → ℝ) → Fin (m t) → ℝ) : Prop :=
  (∀ t, 1 ≤ t → t ≤ T + 1 → ∀ d ∈ traj F T, ∀ d' ∈ traj F T,
      (∀ τ, τ < t → d τ = d' τ) → S t d = S t d') ∧
  ∀ d ∈ traj F T,
    b 1 ≤ A 1 *ᵥ S 1 d ∧
    (∀ t, 1 ≤ t → t ≤ T → B t *ᵥ d t + C t *ᵥ S t d + b (t + 1) ≤ A (t + 1) *ᵥ S (t + 1) d) ∧
    (∀ t, 1 ≤ t → t ≤ T + 1 → ‖S t d‖ ≤ R)

/-- The optimal value of `(P[F_0, …, F_T])` (Lemma 2, p. 269), in `EReal`: the infimum over
feasible policies of the worst case over `𝔽_T` of `f_1(S_1(d^0)) + ⋯ + f_{T+1}(S_{T+1}(d^T))`. -/
noncomputable def opt {n m k : ℕ → ℕ} (T : ℕ)
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (F : (τ : ℕ) → Set (Fin (n τ) → ℝ)) : EReal :=
  ⨅ (S : (t : ℕ) → ((τ : ℕ) → Fin (n τ) → ℝ) → Fin (m t) → ℝ)
    (_ : DPFeasible T A B C b R F S),
    ⨆ d ∈ traj F T, ∑ t ∈ Finset.Icc 1 (T + 1), f t (S t d)

/-- `Φ_t(s_t, d_t) = min {f_{t+1}(s_{t+1}) : A_{t+1} s_{t+1} ≥ B_{t+1} d_t + C_{t+1} s_t + b_{t+1},
‖s_{t+1}‖_∞ ≤ R}` (proof of Lemma 2, p. 270), as an `EReal` infimum (`⊤` if infeasible). -/
noncomputable def Phi {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (t : ℕ) (s : Fin (m t) → ℝ) (d : Fin (n t) → ℝ) : EReal :=
  ⨅ s' ∈ {s' : Fin (m (t + 1)) → ℝ |
      B t *ᵥ d + C t *ᵥ s + b (t + 1) ≤ A (t + 1) *ᵥ s' ∧ ‖s'‖ ≤ R}, f (t + 1) s'

/-- `φ(s_t) = max_{d_t ∈ F_t} Φ_t(s_t, d_t)` (proof of Lemma 2, p. 270), as an `EReal` supremum. -/
noncomputable def phi {n m k : ℕ → ℕ}
    (A : (t : ℕ) → Matrix (Fin (k t)) (Fin (m t)) ℝ)
    (B : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (n t)) ℝ)
    (C : (t : ℕ) → Matrix (Fin (k (t + 1))) (Fin (m t)) ℝ)
    (b : (t : ℕ) → Fin (k t) → ℝ) (f : (t : ℕ) → (Fin (m t) → ℝ) → EReal) (R : ℝ)
    (F : (τ : ℕ) → Set (Fin (n τ) → ℝ)) (t : ℕ) (s : Fin (m t) → ℝ) : EReal :=
  ⨆ d ∈ F t, Phi A B C b f R t s d

end FlexCommitRO.BoxExt



-- Prove2me | Definitions.Def_TwiceRegMDP_R2Bellman_R2Ops
-- name    : TwiceRegMDP_R2Bellman_R2Ops
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T03:21:29.3261+00:00
-- url     : https://prove2.me/theorems/47281b03-7eaa-404a-992f-dca4fe42b2a1
-- title:
--   R² Bellman operators, greedy policies and the bounded-radius Assumption 5.1
-- statement:
--   Fix a finite discounted MDP with nominal transition kernel $P_0$, nominal reward $r_0$ and discount $\gamma$, and radii $\alpha^r_s,\alpha^P_s$ for every state $s$. All norms are $\ell_2$-norms.
--
--   1. **R² regularizer** (Definition 5.1). For $v\in\mathbb R^{\mathcal S}$ and $\pi_s\in\Delta_{\mathcal A}$,
--   $$\Omega_{v,\mathrm R^2}(\pi_s)=\|\pi_s\|\,\big(\alpha^r_s+\alpha^P_s\gamma\|v\|\big).$$
--   2. **R² Bellman evaluation operator**: $[T^{\pi,\mathrm R^2}v](s)=T^\pi_{(P_0,r_0)}v(s)-\Omega_{v,\mathrm R^2}(\pi_s)$.
--   3. **R² Bellman optimality operator**: with $q_s(a)=r_0(s,a)+\gamma\langle P_0(\cdot\mid s,a),v\rangle$,
--   $$[T^{*,\mathrm R^2}v](s)=\max_{p\in\Delta_{\mathcal A}}\Big(\sum_{a}p(a)\,q_s(a)-\|p\|\big(\alpha^r_s+\alpha^P_s\gamma\|v\|\big)\Big),$$
--   which is the paper's $\max_{\pi\in\Delta^{\mathcal S}_{\mathcal A}}[T^{\pi,\mathrm R^2}v](s)$, since that quantity depends on $\pi$ only through $\pi_s$.
--   4. **Greedy policy**: a policy $\pi$ is greedy for $v$ when $T^{\pi,\mathrm R^2}v=T^{*,\mathrm R^2}v$.
--   5. **Assumption 5.1 (bounded radius)** with explicit witnesses $\epsilon$: for every state $s$, $\epsilon_s>0$ and
--   $$\alpha^P_s\le\min\Big(\frac{1-\gamma-\epsilon_s}{\gamma\sqrt{|\mathcal S|}}\,;\ \min_{\substack{u\in\mathbb R^{\mathcal A}_+,\|u\|=1\\ w\in\mathbb R^{\mathcal S}_+,\|w\|=1}}\ \sum_{a}\sum_{s'}u(a)\,P_0(s'\mid s,a)\,w(s')\Big).$$
--   6. $\epsilon_*=\min_{s\in\mathcal S}\epsilon_s$.
--
--   These operators regularize the nominal Bellman operators both in the policy (through $\|\pi_s\|$) and in the value (through $\|v\|$); they are the operators of the R² MDPs of Section 5.
--
--   **Formalization Note.** The maximum in item 3 is the real supremum of the image of the simplex, and the inner minimum of item 5 is the real infimum over nonnegative $\ell_2$-unit vectors; both sets are nonempty and compact when $\mathcal S,\mathcal A$ are nonempty, and the objectives are continuous, so the supremum and infimum are the attained maximum and minimum. Greedy policies are a predicate, not a function: their uniqueness is part of Theorem 5.1. The inner minimum is $0$ whenever some $P_0(s'\mid s,a)=0$, which then forces $\alpha^P_s=0$; this is the assumption as printed.
-- source:
--   Derman, Geist and Mannor, Twice regularized MDPs and the equivalence between robustness and regularization, arXiv:2110.06267v1, p. 7, Definition 5.1 (R² Bellman operators) and Assumption 5.1 (Bounded radius); p. 8, Proposition 5.1 (iii) (ϵ_∗)

import Mathlib
import Definitions.Def_TwiceRegMDP_R2Bellman_MDP

namespace TwiceRegMDP.R2Bellman

open Finset

/-- The R² regularizer of Definition 5.1 (p. 7) at state `s`:
`Ω_{v,R²}(π_s) = ‖π_s‖ (α^r_s + α^P_s γ ‖v‖)`, both norms ℓ². -/
noncomputable def r2Reg {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (αr αP : S → ℝ)
    (v : S → ℝ) (s : S) (p : A → ℝ) : ℝ :=
  l2norm p * (αr s + αP s * γ * l2norm v)

/-- The R² Bellman evaluation operator (Definition 5.1, p. 7):
`[T^{π,R²} v](s) = T^π_{(P₀,r₀)} v(s) − Ω_{v,R²}(π_s)`. -/
noncomputable def evalOpR2 {S A : Type} [Fintype S] [Fintype A] (γ : ℝ)
    (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ) (π : S → A → ℝ)
    (v : S → ℝ) : S → ℝ :=
  fun s => evalOp γ P₀ r₀ π v s - r2Reg γ αr αP v s (π s)

/-- The R² Bellman optimality operator (Definition 5.1, p. 7):
`[T^{∗,R²} v](s) = max_{π ∈ Δ_A^S} [T^{π,R²} v](s)
  = max_{p ∈ Δ_A} (∑_a p(a) q_s(a) − ‖p‖ (α^r_s + α^P_s γ ‖v‖))`,
written as the real supremum over the simplex (a nonempty compact set on which the objective is
continuous, so the supremum is the attained maximum when `A` is nonempty). -/
noncomputable def optOpR2 {S A : Type} [Fintype S] [Fintype A] (γ : ℝ)
    (P₀ : S → A → S → ℝ) (r₀ : S → A → ℝ) (αr αP : S → ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => sSup ((fun p : A → ℝ => ∑ a, p a * qfun γ P₀ r₀ v s a - r2Reg γ αr αP v s p) ''
    stdSimplex ℝ A)

/-- `π` is a greedy policy for `v` (Definition 5.1, p. 7): a policy with
`T^{π,R²} v = T^{∗,R²} v`. Uniqueness is not built in. -/
def IsGreedy {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P₀ : S → A → S → ℝ)
    (r₀ : S → A → ℝ) (αr αP : S → ℝ) (v : S → ℝ) (π : S → A → ℝ) : Prop :=
  TwiceRegMDP.RobustReg.IsPolicy π ∧ ∀ s, evalOpR2 γ P₀ r₀ αr αP π v s = optOpR2 γ P₀ r₀ αr αP v s

/-- The inner minimum of Assumption 5.1 (p. 7) at state `s`:
`min { u^⊤ P₀(·|s,·) w : u ∈ ℝ^A_+, ‖u‖ = 1, w ∈ ℝ^S_+, ‖w‖ = 1 }`,
`u^⊤ P₀(·|s,·) w = ∑_a ∑_{s'} u(a) P₀(s'|s,a) w(s')`, ℓ² norms, taken as the real infimum of
the image of a nonempty compact set (nonempty when `S` and `A` are nonempty). -/
noncomputable def innerMin {S A : Type} [Fintype S] [Fintype A] (P₀ : S → A → S → ℝ)
    (s : S) : ℝ :=
  sInf ((fun uw : (A → ℝ) × (S → ℝ) => ∑ a, ∑ s', uw.1 a * P₀ s a s' * uw.2 s') ''
    {uw | (∀ a, 0 ≤ uw.1 a) ∧ l2norm uw.1 = 1 ∧ (∀ s', 0 ≤ uw.2 s') ∧ l2norm uw.2 = 1})

/-- Assumption 5.1 (Bounded radius, p. 7), with its witnesses `ϵ` made explicit:
for every `s`, `ϵ_s > 0` and
`α^P_s ≤ min((1 − γ − ϵ_s)/(γ √|S|), innerMin s)`. -/
def BoundedRadius {S A : Type} [Fintype S] [Fintype A] (γ : ℝ) (P₀ : S → A → S → ℝ)
    (αP : S → ℝ) (ϵ : S → ℝ) : Prop :=
  ∀ s, 0 < ϵ s ∧ αP s ≤ (1 - γ - ϵ s) / (γ * Real.sqrt (Fintype.card S)) ∧
    αP s ≤ innerMin P₀ s

/-- `ϵ_∗ := min_{s ∈ S} ϵ_s` (Proposition 5.1 (iii), p. 8). -/
noncomputable def epsStar {S : Type} [Fintype S] [Nonempty S] (ϵ : S → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty ϵ

end TwiceRegMDP.R2Bellman



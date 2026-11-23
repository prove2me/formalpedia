-- Prove2me | Definitions.Def_MeanRiskBellman_Recursion_Supplement_WeakMinimizer
-- name    : MeanRiskBellman_Recursion_Supplement_WeakMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:14:16.596335+00:00
-- url     : https://prove2.me/theorems/efaf69a2-4f83-4ecb-85a4-23f5b820e9a9
-- title:
--   (2.6), p. 9 and Definition 3, p. 10 — interior cone int L_t(ℝ²_+), weak minimizers of D_t(v_t), time consistency w.r.t. weak minimizers
-- statement:
--   Work with the market data of §2 under the published model’s standing assumptions (Assumption 2.2, items 1, 2 and 4): a finite filtered probability space $(\Omega,\mathcal F,(\mathcal F_t)_{t=0}^T,P)$ in which every nonempty event has positive probability, adapted prices $S_t$, trading constraints $\Phi_t$, and a time consistent dynamic convex risk measure $(\rho_t)$. For a strategy $\psi$ write $V_T(\psi)=(v_T^\psi,v_T^\psi)$ with $v_T^\psi=S_T^\top\psi_{T-1}$, let $\Gamma_t(X)=(-\mathbb E_t(X_1),\rho_t(X_2))$ be the mean-risk function, $\Psi_t(v_t)$ the feasible portfolios for wealth $v_t$, and $\Gamma_t(\Psi_t(v_t))=\{\Gamma_t(V_T(\psi))\mid\psi\in\Psi_t(v_t)\}$ the image of the mean-risk problem $D_t(v_t)$. This item adds three notions.
--
--   1. **Interior of the ordering cone.** $\operatorname{int}L_t(\mathbb R^2_+)$ is the interior of the cone $L_t(\mathbb R^2_+)$ in the space $L_t(\mathbb R^2)$ of $\mathcal F_t$-measurable random vectors: the $\mathcal F_t$-measurable $r$ with $r_1(\omega)>0$ and $r_2(\omega)>0$ for every $\omega$.
--   2. **Weak minimizer (2.6).** A feasible $\psi\in\Psi_t(v_t)$ is a weak minimizer of $D_t(v_t)$ if
--   $$\bigl(\Gamma_t(V_T(\psi))-\operatorname{int}L_t(\mathbb R^2_+)\bigr)\cap\Gamma_t(\Psi_t(v_t))=\emptyset .$$
--   3. **Time consistency w.r.t. weak minimizers (Definition 3).** The family $\mathcal D=\{D_t(v_t)\}$ is time consistent w.r.t. weak minimizers if for every time $t$ with $t+1<T$, every $\mathcal F_t$-measurable $v_t$ and every strategy $\psi$: if $(\psi_s)_{s=t,\dots,T-1}$ is a weak minimizer of $D_t(v_t)$, then $(\psi_s)_{s=t+1,\dots,T-1}$ is a weak minimizer of $D_{t+1}(S_{t+1}^\top\psi_t)$.
--
--   Weak minimizers are the weakly efficient portfolios (Lemma 2.5): no feasible portfolio has strictly larger conditional mean and strictly smaller conditional risk in every node. Definition 3 is the principle of optimality for weakly efficient frontiers.
--
--   **Formalization Note** On the finite space with positive atom probabilities, $L_t(\mathbb R^2)$ is finite-dimensional and the interior of the cone is the set of pointwise strictly positive $\mathcal F_t$-measurable vectors; the interior taken in the space of all functions $\Omega\to\mathbb R^2$ would be empty whenever $\mathcal F_t\ne\mathcal F$, and is not used. Set membership and equalities are pointwise, which agrees with almost-sure equality for $\mathcal F_t$-measurable vectors under positive probabilities. Strategies are indexed by $\mathbb N$; the problem $D_{t+1}$ reads only the indices $t+1,\dots,T-1$, so the truncated strategy is $\psi$ itself. Definition 3 is stated for the times $t$ with $t+1<T$: at $t=T-1$ the truncated strategy is empty and $D_T$ is not a member of $\mathcal D$.
--
--   Differences from the source:
--   - reading: Definition 3 quantifies over t = 0, …, T−1 → t + 1 < T; reason: at t = T−1 the truncated strategy is empty and D_T is not a problem of the family D (p. 8), so the clause has no content there.
--   - encoding: int L_t(ℝ²_+) and P-a.s. relations in L_t(ℝ²) → F_t-measurable vectors strictly positive in both components at every ω, pointwise relations; reason: on a finite space with positive atom probabilities these are the same sets and relations.
--   - encoding: the truncation (ψ_s)_{s=t+1,…,T−1} → the same ℕ-indexed ψ; reason: D_{t+1} reads only the indices t+1, …, T−1.
-- source:
--   Kováčová & Rudloff, Time consistency of the mean-risk problem, arXiv:1806.10981v2, p. 4 (int L_t), p. 8 (the family D), p. 9 (2.6), p. 10 Definition 3

import Mathlib
import Definitions.Def_MeanRiskBellman_Recursion_Model

namespace MeanRiskBellman.Recursion.Supplement

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- p. 4 and (2.6), p. 9: the interior `int L_t(ℝ²_+)` of the ordering cone, taken in `L_t(ℝ²)` (the
`F_t`-measurable random vectors).  On the finite space with positive atom probabilities this is the
set of `F_t`-measurable `r` with both components strictly positive at every `ω`.  (The interior in the
ambient function space `Ω → ℝ × ℝ` is not meant: it is empty whenever `F_t ≠ F`.) -/
def intCone (M : Market Ω) (t : ℕ) : Set (Ω → ℝ × ℝ) :=
  {r | StronglyMeasurable[M.ℱ t] r ∧ ∀ ω, 0 < (r ω).1 ∧ 0 < (r ω).2}

/-- (2.6), p. 9: a feasible portfolio `ψ ∈ Ψ_t(v_t)` is a weak minimizer of the mean-risk problem
`D_t(v_t)` if `(Γ_t(V_T(ψ)) − int L_t(ℝ²_+)) ∩ Γ_t(Ψ_t(v_t)) = ∅`. -/
def IsWeakMinimizer (M : Market Ω) (t : ℕ) (v : Ω → ℝ) (ψ : ℕ → Ω → Fin M.d → ℝ) : Prop :=
  ψ ∈ feasible M t v ∧ ∀ r ∈ intCone M t, Γ M t (VT M ψ) - r ∉ image M t v

/-- Definition 3, p. 10: the family `D = {D_t(v_t) | t < T, v_t F_t-measurable}` of mean-risk problems
is time consistent w.r.t. weak minimizers if, for every `t` and every `F_t`-measurable `v_t`, a weak
minimizer `(ψ_s)_{s=t,…,T-1}` of `D_t(v_t)` truncates to a weak minimizer `(ψ_s)_{s=t+1,…,T-1}` of
`D_{t+1}(S_{t+1}^⊤ψ_t)`.  Strategies are `ℕ`-indexed and `D_{t+1}` reads only the indices
`t+1, …, T-1`, so the truncation is `ψ` itself.  The times are those with `t + 1 < T`, the ones for
which `D_{t+1}` is a member of `D`. -/
def TimeConsistentWeak (M : Market Ω) : Prop :=
  ∀ t : ℕ, t + 1 < M.T → ∀ v : Ω → ℝ, StronglyMeasurable[M.ℱ t] v →
    ∀ ψ : ℕ → Ω → Fin M.d → ℝ, IsWeakMinimizer M t v ψ →
      IsWeakMinimizer M (t + 1) (value M (t + 1) (ψ t)) ψ

end MeanRiskBellman.Recursion.Supplement



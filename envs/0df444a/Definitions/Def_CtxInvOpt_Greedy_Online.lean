-- Prove2me | Definitions.Def_CtxInvOpt_Greedy_Online
-- name    : CtxInvOpt_Greedy_Online
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:29:23.19929+00:00
-- url     : https://prove2.me/theorems/dddcc7e2-820f-4a36-b460-e5c3b82c8767
-- title:
--   (5)–(6), p. 9 — the online knowledge set C(𝓘_t) and the cumulative regret R^π_T
-- statement:
--   In the online setting a decision-maker faces, in each period $t=1,\dots,T$, a feasible set $\mathcal X_t$ and a context function $f_t$, picks an action $x^\pi_t\in\mathcal X_t$, and afterwards observes an optimal action $x^\star_t$ of the true but unknown cost $c^\star$. Starting from an initial knowledge set $C_0\subseteq S^d$, the **knowledge set** after the first $t-1$ periods is
--
--   $$C(\mathcal I_t)=\{c\in C_0:\ c'f_s(x^\star_s)\le c'f_s(x)\ \ \forall x\in\mathcal X_s,\ s=1,\dots,t-1\},$$
--
--   the set of costs consistent with every observed optimal action (5). The **regret** over $T$ periods is
--
--   $$R^\pi_T(c^\star,\vec{\mathcal X}_T,\vec f_T)=\sum_{t=1}^T\big(f_t(x^\pi_t)-f_t(x^\star_t)\big)'c^\star\qquad(6).$$
--
--   These two objects define every online policy of the paper and its performance measure.
--
--   **Formalization Note** Lean periods are $0$-based: Lean period $t$ is the paper's period $t+1$. The Lean knowledge set at $t$ uses the Lean periods $s<t$, so it is the paper's $C(\mathcal I_{t+1})$, and at $t=0$ it is $C_0$. The regret sums over the Lean periods $t<T$, i.e. the paper's periods $1,\dots,T$.
-- source:
--   Besbes, Fonseca, Lobel, Contextual Inverse Optimization: Offline and Online Learning, arXiv:2106.14015v3, p. 9, (5), (6)

import Mathlib
import Definitions.Def_CtxInvOpt_Offline_Geometry

namespace CtxInvOpt.Greedy

/-- **(5), p. 9.** The knowledge set `C(I_t) = {c ∈ C₀ : c′f_s(x⋆_s) ≤ c′f_s(x), ∀ x ∈ X_s, s < t}`.
Lean periods are 0-based: `knowledgeSet C0 X f xstar t` uses the Lean periods `s < t`, i.e. the paper's
periods `1, …, t`, and is the paper's `C(I_{t+1})`; `knowledgeSet … 0 = C₀`. -/
def knowledgeSet {n d : ℕ} (C0 : Set (EuclideanSpace ℝ (Fin d)))
    (X : ℕ → Set (EuclideanSpace ℝ (Fin n)))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xstar : ℕ → EuclideanSpace ℝ (Fin n)) (t : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {c | c ∈ C0 ∧ ∀ s < t, ∀ x ∈ X s, inner ℝ (f s (xstar s)) c ≤ inner ℝ (f s x) c}

/-- **(6), p. 9.** The regret over `T` periods, `Σ_{t=1}^T (f_t(x^π_t) − f_t(x⋆_t))′c⋆`
(Lean sums over the 0-based periods `t < T`). -/
noncomputable def cumRegret {n d : ℕ} (cstar : EuclideanSpace ℝ (Fin d))
    (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (xpi xstar : ℕ → EuclideanSpace ℝ (Fin n)) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, inner ℝ (f t (xpi t) - f t (xstar t)) cstar

end CtxInvOpt.Greedy



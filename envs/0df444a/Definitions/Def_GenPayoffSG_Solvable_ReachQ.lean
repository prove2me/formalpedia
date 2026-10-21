-- Prove2me | Definitions.Def_GenPayoffSG_Solvable_ReachQ
-- name    : GenPayoffSG_Solvable_ReachQ
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:43.419242+00:00
-- url     : https://prove2.me/theorems/a9f5a285-6fa1-41f2-a034-a1e3d4bdfeea
-- title:
--   §4.4 Step 1, p. 18 — Λ_i(h, a_i) of (8) and the fictitious hitting count ζ_i(r, n, ℓ) of (9)
-- statement:
--   This file defines the two quantities of Step 1 of the proof of Theorem 4.9.
--
--   Let $Q\subseteq H$ be a set of histories, $\sigma$ a strategy profile and $i$ a player. For a history $h$ and an action $a_i\in A_i$,
--   $$\Lambda_i(h,a_i)=\sum_{\{a_{-i}\in A_{-i},\ s\in S\,:\,(h,(a_i,a_{-i}),s)\in Q\}}\sigma_{-i}(a_{-i}\mid h)\,p(s\mid s_h,a_i,a_{-i}),\tag{8}$$
--   the probability that the history of the next stage lies in $Q$ when player $i$ plays $a_i$ at $h$ and the opponents follow $\sigma_{-i}$; here $\sigma_{-i}(a_{-i}\mid h)=\prod_{j\ne i}\sigma_j(h)(a_j)$.
--
--   For a run $r$, a stage $n\ge 2$ and $\ell\in\mathbb N\cup\{\infty\}$,
--   $$\zeta_i(r,n,\ell)=\sum_{k=n}^{\ell}\Lambda_i\big(r^{k-1},a_i^{(k-1)}\big)\tag{9}$$
--   if $n\le\ell$, and $\zeta_i(r,n,\ell)=0$ if $n>\ell$, where $a_i^{(k-1)}$ is the action player $i$ takes at the history $r^{k-1}$.
--
--   **Formalization Note** Both quantities take values in $[0,\infty]$ (`ℝ≥0∞`), so the sums need no convergence side condition; for $\ell=\infty$ the paper's sum may diverge, and its value is then $+\infty$. Histories of all lengths are packed as a dependent pair `⟨n, h⟩`. In Lean indices, `fictCount G σ Q i r m₀ L` sums over the target prefixes `frestrictLe m r` with $m_0\le m\le L$, where $m=k-1$ is the Lean index of the paper's $r^k$; so paper $n$ is $m_0+1$ and paper $\ell$ is $L+1$. The paper prints the summand of (9) as $\Lambda_i(r^{k-1},a^k_i)$; since runs are $(s^1,a^1,s^2,\dots)$ the action chosen at $r^{k-1}$ is $a^{k-1}_i$, and this is how (12) and p. 26 use it, so the Lean summand pairs the prefix with the action taken at that prefix (Lean coordinate $m$).
-- source:
--   Flesch & Solan, Stochastic Games with General Payoff Functions, arXiv:2208.12096v1, p. 18, §4.4 Step 1, Eq. (8); pp. 18–19, Eq. (9)

import Mathlib
import Definitions.Def_GenPayoffSG_Solvable_Game

namespace GenPayoffSG.Solvable

open MeasureTheory ProbabilityTheory Finset ENNReal

variable {I S : Type} [Fintype I] [DecidableEq I] [Nonempty I]
  [Countable S] [Nonempty S] {A : I → Type}
  [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]

open scoped Classical in
/-- (8): `Λᵢ(h, aᵢ) = ∑_{a₋ᵢ, s : (h, (aᵢ, a₋ᵢ), s) ∈ Q} σ₋ᵢ(a₋ᵢ | h) · p(s | s_h, aᵢ, a₋ᵢ)`,
the probability that the history of the next stage lies in `Q` when player `i` plays `aᵢ` at
`h` and the opponents follow `σ₋ᵢ`. Histories of all lengths are packed as `Σ n, Hist n`. -/
noncomputable def reachProb (G : Game I S A) (σ : Profile G)
    (Q : Set (Σ n, Hist I S A n)) (i : I) {n : ℕ} (h : Hist I S A n) (ai : A i) : ℝ≥0∞ :=
  ∑' (a : ∀ j, A j) (s : S),
    if a i = ai ∧ (⟨n + 1, extend h a s⟩ : Σ m, Hist I S A m) ∈ Q then
      (∏ j ∈ univ.erase i, σ j n h (a j)) * G.p (lastState h) a s
    else 0

open scoped Classical in
/-- (9), in Lean indices: `fictCount G σ Q i r m₀ L = ∑ Λᵢ(r^{k−1}, aᵢ)` over the paper stages
`k` whose Lean index `m = k − 1` satisfies `m₀ ≤ m ≤ L`; the summand pairs the prefix `r^{k−1}`
(Lean `frestrictLe (m − 1) r`) with the action player `i` chooses at that prefix (Lean
coordinate `m`). Paper `n ≥ 2` is `m₀ ≥ 1`; `L = ⊤` is `ℓ = ∞`; the sum is `0` when `m₀ > L`. -/
noncomputable def fictCount (G : Game I S A) (σ : Profile G)
    (Q : Set (Σ n, Hist I S A n)) (i : I) (r : Run I S A) (m₀ : ℕ) (L : ℕ∞) : ℝ≥0∞ :=
  ∑' j : ℕ,
    if m₀ ≤ j + 1 ∧ ((j + 1 : ℕ) : ℕ∞) ≤ L then
      reachProb G σ Q i (Preorder.frestrictLe j r) (coordAction (r (j + 1)) i)
    else 0

end GenPayoffSG.Solvable



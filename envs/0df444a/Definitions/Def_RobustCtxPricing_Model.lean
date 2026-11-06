-- Prove2me | Definitions.Def_RobustCtxPricing_Model
-- name    : RobustCtxPricing_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:27.417866+00:00
-- url     : https://prove2.me/theorems/59878586-d449-4ff9-983d-ab79dc25f44c
-- title:
--   The robust contextual pricing model — parameter ball $\Theta$, regret $R_T$, corruption constraint
-- statement:
--   This module fixes the model of §2 of Castiglioni–Stradi.
--
--   1. **Parameter and context set.** $\Theta=\mathcal B_d(0,1)=\{x\in\mathbb R^d:\ \|x\|_2\le 1\}$ is the closed Euclidean unit ball. The unknown parameter $\theta^\star$ and every context $u_t$ lie in it.
--   2. **Regret.** For a horizon $T$, a parameter $\theta^\star$, contexts $u_1,\dots,u_T$ and posted prices $p_1,\dots,p_T$, with valuations $v_t=\langle\theta^\star,u_t\rangle$,
--   $$
--   R_T=\sum_{t=1}^T\big(v_t-p_t\,\mathbb I\{p_t\le v_t\}\big).
--   $$
--   3. **Corruption constraint.** The true sale bit is $y_t=\mathbb I\{p_t\le v_t\}$ and the seller observes $Y_t\in\{0,1\}$. The feedback is *corrupted with budget $C$* if there is a set $S\subseteq[T]$ with $|S|\le C$ such that $Y_t=y_t$ for every $t\notin S$.
--
--   These are the objects in which Theorem 4.2 is stated: the clairvoyant benchmark posts $p_t^\star=v_t$, and the regret is the revenue lost against it.
--
--   **Formalization Note** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)`. Rounds are numbered $0,\dots,T-1$ and sequences are indexed by $\mathbb N$; only the first $T$ entries matter. Bits are Booleans. The corruption constraint is evaluated on the prices actually posted by the seller, which is how an adaptive adversary (who may decide to corrupt round $t$ after seeing $p_t$) is represented when one quantifies over all feedback sequences.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §2.1–§2.2, pp.10–11 (Notation; valuation, sale bit, regret R_T; corrupted signal Y_t, set S with |S| ≤ C)

import Mathlib

namespace RobustCtxPricing

/-- **The parameter set `Θ = 𝓑_d(0,1)`.** Castiglioni–Stradi, *Decoupling Corruption and Horizon in
Robust Contextual Pricing*, arXiv:2607.11210, §2.1, p.10–11: "a context `u_t ∈ 𝓑_d(0, 1)` …
an unknown parameter `θ⋆ ∈ Θ := 𝓑_d(0, 1)`".

**Formalization Note.** `ℝ^d` is `EuclideanSpace ℝ (Fin d)` (Euclidean norm `‖·‖₂` and inner
product `⟨·,·⟩`, as in the Notation paragraph of p.10). The ball is the **closed** unit ball; the
analysis uses `‖u_t‖₂ ≤ 1` and `‖θ⋆‖₂ ≤ 1` (pp.18, 21). Contexts range over the same set. -/
def Theta (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) :=
  Metric.closedBall 0 1

/-- **Regret `R_T`.** Castiglioni–Stradi, arXiv:2607.11210, §2.1, p.11:
`R_T := ∑_{t=1}^T (v_t − p_t 𝕀{p_t ≤ v_t})` with valuation `v_t := ⟨θ⋆, u_t⟩`.

**Formalization Note.** Rounds are `0, …, T−1` (the paper's `1, …, T`); contexts `u` and prices
`p` are sequences indexed by `ℕ` of which only the first `T` entries matter. -/
noncomputable def regret {d : ℕ} (T : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (p : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (inner ℝ θ (u t) - if p t ≤ inner ℝ θ (u t) then p t else 0)

/-- **The corruption constraint.** Castiglioni–Stradi, arXiv:2607.11210, §2.2, p.11: "There is a set
of corrupted rounds `S ⊆ [T]` with `|S| ≤ C` such that `Y_t = y_t` for every `t ∉ S`", where
`y_t := 𝕀{p_t ≤ v_t}` (p.11) is the true sale bit and `Y_t ∈ {0,1}` the observed signal.

`IsCorrupted T C θ u p Y` says that the observed feedback `Y` differs from the true sale bit of the
prices `p` in at most `C` of the rounds `0, …, T−1`.

**Formalization Note.** Bits are `Bool` (`true` = 1 = sale). The constraint is evaluated on the
run's own posted prices `p`; quantifying over every `(u, Y)` and every run satisfying it covers the
adaptive adversary of §2.2 (which may decide on `t ∈ S` after seeing `p_t`), because the seller's
run is determined by `(u, Y)` and its tie-breaking choices. -/
def IsCorrupted {d : ℕ} (T C : ℕ) (θ : EuclideanSpace ℝ (Fin d))
    (u : ℕ → EuclideanSpace ℝ (Fin d)) (p : ℕ → ℝ) (Y : ℕ → Bool) : Prop :=
  ∃ S : Finset ℕ, S ⊆ Finset.range T ∧ S.card ≤ C ∧
    ∀ t < T, t ∉ S → Y t = decide (p t ≤ inner ℝ θ (u t))

end RobustCtxPricing



-- Prove2me | Definitions.Def_OfflineStochMatch_Attenuation_SideProb
-- name    : OfflineStochMatch_Attenuation_SideProb
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-16T08:22:12.554195+00:00
-- url     : https://prove2.me/theorems/4adccc0e-876a-45eb-b7b2-99d23e71c449
-- title:
--   One-sided relaxed safety event at an endpoint of $e$ and its probability at arrival probability $x$
-- statement:
--   Fix an edge $e$ of the graph $G$ in the attenuation setting and an endpoint $r$ of $e$. Write $E(r)=\delta(r)\setminus\{e\}$ for the other edges at $r$ (notation of p. 11).
--
--   **Arrival indicators.** For a processing order $\sigma$, `arrivedBefore σ e` is the indicator vector $B$ with $B_f=1$ exactly when $f$ is processed before $e$.
--
--   **One-sided relaxed condition.** For indicators $B$ and the coins $Y,A,P$ of Algorithm 1, $\mathrm{SideOK}_r(B,Y,A,P)$ means:
--
--   1. no $f\in E(r)$ has $B_f=Y_f=A_f=P_f=1$;
--   2. $\#\{f\in E(r) : B_f=Y_f=A_f=1\}+1\le t_r$ (that is, at most $t_r-1$ such edges; no subtraction in $\mathbb{N}\cup\{\infty\}$).
--
--   It depends only on the coordinates in $E(r)$. Any probe made before $e$ to an edge of $\delta(r)$ is at an edge $f\in E(r)$ with $B_f=Y_f=A_f=1$. Hence $\mathrm{SideOK}_u$ and $\mathrm{SideOK}_v$ for $B=$ `arrivedBefore σ e` together imply that $e=\{u,v\}$ is safe.
--
--   **Probability.** $\mathrm{sideProb}_r(x)$ is the probability of $\mathrm{SideOK}_r$ when all coordinates are independent with $B_f\sim\mathrm{Bernoulli}(x)$, $Y_f\sim\mathrm{Bernoulli}(y_f)$, $A_f\sim\mathrm{Bernoulli}(\tilde a(p_f y_f))$, $P_f\sim\mathrm{Bernoulli}(p_f)$:
--   $$\mathrm{sideProb}_r(x)=\sum_{B,Y,A,P}\ \prod_f \mathrm{bern}(x,B_f)\,\mathrm{bern}(y_f,Y_f)\,\mathrm{bern}(a_f,A_f)\,\mathrm{bern}(p_f,P_f)\ \mathbf 1[\mathrm{SideOK}_r(B,Y,A,P)].$$
--   This is the conditional probability, given arrival time $\pi(e)=x$, of the paper's one-sided sufficient condition for safety (p. 11, the display before Lemma 3 and the bound by $\Pr[Q_0(r)<t_r\mid\pi(e)=x]$), here stated for arbitrary $p_f\in[0,1]$ before the reduction of Lemma 2.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, §3.2 pp. 10–12: per-endpoint sufficient condition for safety (display before Lemma 3, Eqs. (8)–(10))

import Mathlib
import Definitions.Def_OfflineStochMatch_Attenuation_Setting

namespace OfflineStochMatch.Attenuation

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `E(r)`, the edges other than `e` incident to the vertex `r` (p. 11). -/
def otherIncident (G : EdmondsMatching65.Polyhedron.Graph V E) (e : E) (r : V) : Finset E :=
  (incident G r).erase e

/-- Arrival indicators induced by the order `σ`: `true` at `f` exactly when `f` comes before `e`. -/
def arrivedBefore {n : ℕ} (σ : E ≃ Fin n) (e : E) : E → Bool :=
  fun f => decide (σ f < σ e)

/-- One-sided relaxed condition at the endpoint `r` of `e`, given arrival indicators `B` and the
coins `Y`, `A`, `P`: (1) no `f ∈ E(r)` with `B f = Y f = A f = P f = true`, and (2) the number of
`f ∈ E(r)` with `B f = Y f = A f = true`, plus one, is at most `t r`. -/
def SideOK (G : EdmondsMatching65.Polyhedron.Graph V E) (t : V → ℕ∞) (e : E) (r : V)
    (B Y A P : E → Bool) : Prop :=
  (∀ f ∈ otherIncident G e r, ¬ (B f = true ∧ Y f = true ∧ A f = true ∧ P f = true)) ∧
  ((((otherIncident G e r).filter
      (fun f => B f = true ∧ Y f = true ∧ A f = true)).card : ℕ∞) + 1 ≤ t r)

open Classical in
/-- Probability of `SideOK` when each edge independently arrives before `e` with probability `x`
and the coins are `Y_f ~ Bernoulli(y_f)`, `A_f ~ Bernoulli(ã(p_f y_f))`, `P_f ~ Bernoulli(p_f)`. -/
noncomputable def sideProb (G : EdmondsMatching65.Polyhedron.Graph V E) (p : E → ℝ) (t : V → ℕ∞)
    (y : E → ℝ) (aT : ℝ → ℝ) (e : E) (r : V) (x : ℝ) : ℝ :=
  ∑ B : E → Bool, ∑ Y : E → Bool, ∑ A : E → Bool, ∑ P : E → Bool,
    coinWeight (fun _ => x) B * coinWeight y Y * coinWeight (attProb aT p y) A *
      coinWeight p P * (if SideOK G t e r B Y A P then 1 else 0)

end OfflineStochMatch.Attenuation



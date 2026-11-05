-- Prove2me | Definitions.Def_OnlineMatchFrameworks_LP
-- name    : OnlineMatchFrameworks_LP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:30:55.810063+00:00
-- url     : https://prove2.me/theorems/e0022476-f79e-4437-b137-f7bfde388795
-- title:
--   Linear program (1): feasibility, objective $c(x)$, $\mathrm{OPT}_{\mathrm{LP}}$, valid budgets
-- statement:
--   The value of linear program (1) is
--   $$
--   \mathrm{OPT}_{\mathrm{LP}}=\max\ c(x)=\sum_{u\in U}\sum_{v\in V}x_{u,v}p_{u,v}w_u
--   $$
--   subject to
--
--   1. $\sum_{v}x_{u,v}p_{u,v}\le 1$ for all $u$ (1a);
--   2. $\sum_{u}x_{u,v}p_{u,v}\le 1$ for all $v$ (1b);
--   3. $\sum_{u}x_{u,v}\le E_v$ for all $v$ (1c);
--   4. $\sum_{u\in U'}x_{u,v}p_{u,v}w_u\le\mathrm{OPT}(U',v)$ for all $U'\subseteq U$, $v\in V$ (1d);
--   5. $0\le x_{u,v}\le 1$.
--
--   A budget $E$ is **valid** if $\mathrm{probes}_v(l)\le E_v$ for all $v$ and all policies $l$. The printed right side $\mathbb E[\theta_v]$ of (1c) is a valid budget, and so is $E_v=\infty$.
--
--   **Formalization Note** Lean keeps $E_v$ in $[0,\infty]$, so an infinite $\mathbb E[\theta_v]$ is not truncated.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, LP (1), p.15; Appendix A, proof of Lemma 1, p.39

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators ENNReal

namespace OnlineMatchFrameworks

variable {U V : Type*} [Fintype U] [Fintype V]

namespace Instance

/-- **The objective `c(x)` of LP (1).** arXiv:1907.03963v6, (1), p.15, and proof of Lemma 2, p.39:
`c(x) = ∑_{u∈U} ∑_{v∈V} x_{u,v} p_{u,v} w_u`. -/
def objective (G : Instance U V) (x : U → V → ℝ) : ℝ :=
  ∑ u, ∑ v, x u v * G.p u v * G.w u

/-- **The feasible set of LP (1).** arXiv:1907.03963v6, (1a)–(1d), p.15. `E` is the right side of
(1c).

**Formalization Note.** `E v` lies in `ℝ≥0∞`, so (1c) is stated through `ENNReal.ofReal`. The printed
value is `tailBudget q`, and `E[θ_v]` may be infinite. (1d) uses the same `starOpt` as the
black-box hypothesis. -/
structure IsFeasible (G : Instance U V) (E : V → ℝ≥0∞) (x : U → V → ℝ) : Prop where
  /-- (1a) -/
  item_le_one : ∀ u, ∑ v, x u v * G.p u v ≤ 1
  /-- (1b) -/
  customer_le_one : ∀ v, ∑ u, x u v * G.p u v ≤ 1
  /-- (1c) -/
  probes_le_budget : ∀ v, ENNReal.ofReal (∑ u, x u v) ≤ E v
  /-- (1d) -/
  star_le_opt : ∀ (U' : Finset U) (v : V), ∑ u ∈ U', x u v * G.p u v * G.w u ≤ G.starOpt U' v
  /-- `0 ≤ x_{u,v}` -/
  nonneg : ∀ u v, 0 ≤ x u v
  /-- `x_{u,v} ≤ 1` -/
  le_one : ∀ u v, x u v ≤ 1

/-- **`OPT_LP(G)`, the value of LP (1).** arXiv:1907.03963v6, (1), p.15.

**Formalization Note.** `x = 0` is feasible and `c(x) ≤ ∑_u ∑_v p_{u,v} w_u` on the feasible set, so the
real supremum has its intended value; both facts are proved in the sanity file. -/
noncomputable def OPTLP (G : Instance U V) (E : V → ℝ≥0∞) : ℝ :=
  sSup (G.objective '' {x | G.IsFeasible E x})

/-- **A budget valid for (1c).** arXiv:1907.03963v6, proof of Lemma 1, p.39: `E v` bounds the expected
number of probes of every policy for `v`. The printed `E[θ_v]` qualifies (`tailBudget`, proved in
the sanity file), and so does `E v = ⊤`. -/
def ValidBudget (G : Instance U V) (E : V → ℝ≥0∞) : Prop :=
  ∀ v (l : Policy U), ENNReal.ofReal (G.probes v l.1) ≤ E v

end Instance

end OnlineMatchFrameworks



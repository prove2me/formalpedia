-- Prove2me | Definitions.Def_QuerySampleRev_Learner
-- name    : QuerySampleRev_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:34:51.754502+00:00
-- url     : https://prove2.me/theorems/e71ab839-7bd0-4e25-815a-8fe0c9b8a91e
-- title:
--   Randomized adaptive learner with sample and pricing-query access
-- statement:
--   A **learning algorithm** interacts with an unknown value distribution $F$ in rounds $t=0,1,2,\dots$. In each round it chooses one of three actions:
--   1. **sample**: observe a fresh value $s_t\sim F$;
--   2. **query at price $p$**: observe only the bit $z_t=\mathbf 1[v_t\ge p]$ for a fresh $v_t\sim F$;
--   3. **stop and output a price $p^A$**.
--
--   The choice in round $t$ is a measurable function of an internal random seed $u\in[0,1]$ and of the observations of rounds $0,\dots,t-1$. Access type, query prices and the stopping decision may therefore depend adaptively on past observations and internal randomness, as in §2.2. Every run is described by an **outcome** $\omega=(u,v)$, a seed together with the stream $v=(v_0,v_1,\dots)$ of value draws, where round $t$ uses $v_t$.
--
--   **Formalization Note** One uniform seed generates any internal randomization. Query and output prices are real numbers; the paper's prices $p\ge0$ are a special case (a query at $p\le0$ is answered $1$ almost surely).
-- source:
--   Jin, Tang, Wang, Zhang, Query-Sample Tradeoffs for Revenue Maximization (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF p.15), the paragraphs on sample access, pricing-query access and adaptivity

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace QuerySampleRev

/-- **Observations of a learner.** Jin, Tang, Wang, Zhang, *Query-Sample Tradeoffs for Revenue
Maximization* (manuscript, sha256 c31ea3d3…), §2.2, p.13 (PDF 15): "In a sample round `t`, the algorithm
observes a fresh value sample `s_t ∼ F`"; "In a query round `t`, the algorithm selects a price `p_t` and
observes only the binary feedback `z_t ≜ 1[v_t ≥ p_t]`".

An observation is either a sample value `Sum.inl s` or a query price with its feedback
`Sum.inr (p, z)`. -/
abbrev Obs : Type := ℝ ⊕ (ℝ × Bool)

/-- **Actions of a learner** (same source, §2.2, p.13): take a value sample, post a pricing query at a
price `p`, or stop and output a price `p`. Encoded as `Unit ⊕ ℝ ⊕ ℝ`; see `Act.sample`, `Act.query`,
`Act.stop`. -/
abbrev Act : Type := Unit ⊕ (ℝ ⊕ ℝ)

/-- The action "draw a value sample". -/
def Act.sample : Act := Sum.inl ()

/-- The action "post a pricing query at price `p`". -/
def Act.query (p : ℝ) : Act := Sum.inr (Sum.inl p)

/-- The action "stop and output the price `p`". -/
def Act.stop (p : ℝ) : Act := Sum.inr (Sum.inr p)

/-- **Learning algorithm.** Same source, §2.2, p.13 (PDF 15): "A learning algorithm `A` initially knows
the distribution family but does not know the distribution `F`. The algorithm can acquire information
through two forms of access: … Sample access … Pricing-query access … The algorithm may choose the access
type, query price, and stopping decision adaptively, based on its previous observations and internal
randomness. At termination, the algorithm outputs a price `p^A`."

A learner is a rule `act t u h` choosing the action of round `t = 0, 1, 2, …` from the internal random
seed `u ∈ [0, 1]` and the history `h : Fin t → Obs` of the observations of rounds `0, …, t − 1`; the rule
is jointly measurable in `(u, h)`.

**Formalization Note.** All internal randomness is one uniform seed `u` (it generates any countable family
of independent randomizations), so the class contains every randomized, adaptive learner that interleaves
sample and query rounds and stops adaptively. Query and output prices range over `ℝ`, a superset of the
paper's `p ≥ 0` (a query at `p ≤ 0` is answered `1` almost surely and carries no information). -/
structure Learner where
  /-- The action at round `t`, given the seed and the observations of rounds `0, …, t − 1`. -/
  act : (t : ℕ) → unitInterval → (Fin t → Obs) → Act
  /-- The action rule is jointly measurable in the seed and the history. -/
  act_meas : ∀ t, Measurable (fun x : unitInterval × (Fin t → Obs) => act t x.1 x.2)

/-- **Outcomes of a run**: the internal seed `u ∈ [0, 1]` and the stream `v : ℕ → ℝ` of values, where
round `t` (a sample or a query) uses the value `v t`. Same source, §2.2, p.13: "Every sample or query uses
an independent draw from the value distribution." -/
abbrev Outcome : Type := unitInterval × (ℕ → ℝ)

end QuerySampleRev



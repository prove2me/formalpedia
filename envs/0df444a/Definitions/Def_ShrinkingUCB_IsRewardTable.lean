-- Prove2me | Definitions.Def_ShrinkingUCB_IsRewardTable
-- name    : ShrinkingUCB_IsRewardTable
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:17:32.094473+00:00
-- url     : https://prove2.me/theorems/7902f9d2-4742-4129-867a-1f63afdf572a
-- title:
--   The reward table: independent binary outcomes $r_{t,i}$ with mean $\mu(i)$
-- statement:
--   Let $(\Omega,P)$ be a probability space. A **reward table** for an instance is a family of binary random variables $r_{t,i}\in\{0,1\}$, for $t\in[T]$ and $i\in[N]$, that are jointly independent and satisfy
--
--   $$
--   \mathbb E[r_{t,i}]=P(r_{t,i}=1)=\mu(i).
--   $$
--
--   The outcome $r_{t,i}$ says whether the sales of product $i$ in period $t$ are positive. An algorithm observes $r_{t,i}$ only for the products it offers in period $t$.
--
--   An **outcome table** is a realization $o=(o_{t,i})$, and the table realized at $\omega$ is $o_{t,i}=r_{t,i}(\omega)$. The binary value is turned into a real number by $\mathrm{true}\mapsto1$, $\mathrm{false}\mapsto0$.
--
--   **Formalization Note** The source speaks of $r_{t,i}$ for $i\in S_t$ only. The table has every entry and the algorithm reads the offered ones, which is the standard representation. Outcomes are of type `Bool`, so the observed history is discrete.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §2, p.9

import Definitions.Def_ShrinkingUCB_LinearSemiBandit

open MeasureTheory ProbabilityTheory

namespace ShrinkingUCB

/-- A realized table of binary outcomes: `o t i` is the outcome `r_{t,i}` of product `i` in period
`t`. Periods are `1, 2, …`; the entry at period `0` is never read. -/
abbrev OutcomeTable (N : ℕ) : Type := ℕ → Fin N → Bool

/-- The table realized at the outcome `ω`. -/
def tableAt {Ω : Type*} {N : ℕ} (r : ℕ → Fin N → Ω → Bool) (ω : Ω) : OutcomeTable N :=
  fun t i => r t i ω

/-- The value of a binary outcome as a real number, `true ↦ 1`, `false ↦ 0`. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

/-- The reward model (arXiv:1903.07844v2, §2, p.9): the outcomes `r_{t,i} ∈ {0, 1}`, for
`t ∈ [T]` and `i ∈ [N]`, are measurable, jointly independent, and have expected value
`E[r_{t,i}] = P(r_{t,i} = 1) = µ(i)`.

**Formalization Note.** The page has `r_{t,i}` only for `i ∈ S_t`, "independent across products
and across time periods". This is the standard table representation: every entry exists, and the
algorithm reads the entries with `i ∈ S_t` only. Outcomes are `Bool`, which makes the observed
history discrete. -/
structure IsRewardTable {Ω : Type*} [MeasurableSpace Ω] {d N : ℕ} (I : LinearSemiBandit d N)
    (P : Measure Ω) (T : ℕ) (r : ℕ → Fin N → Ω → Bool) : Prop where
  measurable : ∀ t ∈ Finset.Icc 1 T, ∀ i, Measurable (r t i)
  indep : iIndepFun (fun p : Fin T × Fin N => r ((p.1 : ℕ) + 1) p.2) P
  mean : ∀ t ∈ Finset.Icc 1 T, ∀ i, P.real {ω | r t i ω = true} = I.μ i

end ShrinkingUCB



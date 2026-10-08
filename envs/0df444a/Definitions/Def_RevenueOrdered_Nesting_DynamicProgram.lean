-- Prove2me | Definitions.Def_RevenueOrdered_Nesting_DynamicProgram
-- name    : RevenueOrdered_Nesting_DynamicProgram
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T04:17:47.965966+00:00
-- url     : https://prove2.me/theorems/b79cb099-09d2-401e-91f2-f9263f0e60e4
-- title:
--   §5, p. 25 — the revenue-ordered multi-period dynamic program 𝒥_t(q, ℓ), 𝒥_t(q), ℓ∗_t(q) and ∆𝒥_t(q)
-- statement:
--   A firm sells a single resource over a finite horizon. In each period it offers a choice set and one customer arrives and buys at most one item from it, following the choice probabilities $\mathcal P$; each sale uses one unit of inventory. The firm restricts itself to **revenue-ordered assortments** $S_\ell=\{x : r(x)\ge r_\ell\}$, $\ell\in[k]$.
--
--   Let $t$ be the number of periods remaining and $q$ the number of units left. The values $\mathcal J_t(q,\ell)$ (offer $S_\ell$ now and follow the revenue-ordered strategy afterwards) and $\mathcal J_t(q)$ are defined by
--   $$
--   \mathcal J_t(q)=\max_{\ell\in[k]}\mathcal J_t(q,\ell),
--   $$
--   $$
--   \mathcal J_t(q,\ell)=\sum_{x\in S_\ell}\mathcal P(x,S_\ell)\,\bigl(r(x)+\mathcal J_{t-1}(q-1)\bigr)+\mathcal P(0,S_\ell)\,\mathcal J_{t-1}(q)\qquad(t>0,\ q>0),
--   $$
--   and $\mathcal J_t(q,\ell)=0$ if $q=0$ or $t=0$. Here $\mathcal P(0,S)=1-\sum_{x\in S}\mathcal P(x,S)$.
--
--   The **optimal revenue-ordered index** is the smallest maximiser,
--   $$
--   \ell^*_t(q)=\min\{\ell\in[k] : \mathcal J_t(q,\ell)=\mathcal J_t(q)\},
--   $$
--   so $S_{\ell^*_t(q)}$ is the largest revenue-ordered assortment that is optimal at that state. The **marginal value of capacity** is
--   $$
--   \Delta\mathcal J_t(q)=\mathcal J_t(q)-\mathcal J_t(q-1)\qquad(q\ge 1).
--   $$
--
--   This recursion is the multi-period model of Talluri and van Ryzin restricted to revenue-ordered offer sets; Theorem 5.1 of the paper concerns how $\ell^*_t(q)$ varies with $t$ and $q$.
--
--   **Formalization Note** The recursion is the definition: `jIdx P r t q ℓ` is $\mathcal J_t(q,\ell)$, defined by structural recursion on $t$, with $\mathcal J_{t-1}(\cdot)$ written as the maximum over $[k]$ of $\mathcal J_{t-1}(\cdot,\ell')$; `jVal P r t q` is $\mathcal J_t(q)$ (so $\mathcal J_t(0)=\mathcal J_0(q)=0$); `optLevel P r t q` is $\ell^*_t(q)$, the `Finset.min'` of the nonempty set of maximisers; `marginalValue P r t q` is $\Delta\mathcal J_t(q)$, used only for $q\ge 1$ (at $q=0$ natural-number subtraction gives $0$). Indices $\ell$ are 1-based natural numbers in $[k]$, as in the paper. No stochastic process is built; "expected revenue of the revenue-ordered strategy" is the paper's interpretation of the recursion.
-- source:
--   Berbeglia & Joret, Assortment Optimisation Under a General Discrete Choice Model: A Tight Analysis of Revenue-Ordered Assortments, arXiv:1606.01371v3, p. 25, §5 (𝒥_t(q), 𝒥_t(q, ℓ), ℓ∗_t(q)), and p. 36, Appendix B (∆𝒥_t′(q′))

import Mathlib
import Definitions.Def_RevenueOrdered_Nesting_RevenueOrdered

namespace RevenueOrdered.Nesting

noncomputable section

variable {C : Type*} [Fintype C] [Nonempty C]

/-- `𝒥_t(q, ℓ)` (§5, p. 25): the expected revenue when `t` periods remain, `q` units are left,
the set `S_ℓ` is offered now and the revenue-ordered strategy is followed afterwards. For
`t > 0` and `q > 0`,
`𝒥_t(q, ℓ) = ∑_{x ∈ S_ℓ} 𝒫(x, S_ℓ)(r(x) + 𝒥_{t−1}(q − 1)) + 𝒫(0, S_ℓ) 𝒥_{t−1}(q)`,
with `𝒥_{t−1}(q') = max_{ℓ' ∈ [k]} 𝒥_{t−1}(q', ℓ')`; and `𝒥_t(q, ℓ) = 0` if `q = 0` or `t = 0`.
Defined by structural recursion on `t`. -/
def jIdx (P : C → Finset C → ℝ) (r : C → ℝ) : ℕ → ℕ → ℕ → ℝ
  | 0, _, _ => 0
  | _ + 1, 0, _ => 0
  | t + 1, q + 1, ℓ =>
      ∑ x ∈ RevenueOrdered.Ratio.roSet r ℓ, P x (RevenueOrdered.Ratio.roSet r ℓ) *
          (r x + (levels r).sup' (levels_nonempty r) (jIdx P r t q)) +
        RevenueOrdered.Ratio.noPurchase P (RevenueOrdered.Ratio.roSet r ℓ) * (levels r).sup' (levels_nonempty r) (jIdx P r t (q + 1))

/-- `𝒥_t(q) = max_{ℓ ∈ [k]} 𝒥_t(q, ℓ)` (§5, p. 25): the expected revenue of the
revenue-ordered strategy over the remaining `t` periods with `q` units left. -/
def jVal (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) : ℝ :=
  (levels r).sup' (levels_nonempty r) (jIdx P r t q)

/-- `ℓ∗_t(q) := min{ℓ ∈ [k] : 𝒥_t(q, ℓ) = 𝒥_t(q)}` (§5, p. 25): the smallest index, hence the
largest revenue-ordered assortment, attaining the maximum. -/
def optLevel (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) : ℕ :=
  (argmaxLevels r (jIdx P r t q)).min' (argmaxLevels_nonempty r _)

/-- The marginal value of capacity `∆𝒥_t(q) := 𝒥_t(q) − 𝒥_t(q − 1)` (App. B, p. 36), used for
`q ≥ 1` (at `q = 0` the natural-number subtraction makes it `0`; that value is never used). -/
def marginalValue (P : C → Finset C → ℝ) (r : C → ℝ) (t q : ℕ) : ℝ :=
  jVal P r t q - jVal P r t (q - 1)

end

end RevenueOrdered.Nesting



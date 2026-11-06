-- Prove2me | Definitions.Def_MethodFulfillment_mu
-- name    : MethodFulfillment_mu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:57.684198+00:00
-- url     : https://prove2.me/theorems/3e2d7db4-5cb5-4bef-be60-c1620df414ac
-- title:
--   Consumption probabilities $\mu^t_{ik}$ of (12)
-- statement:
--   For a pair $(i,k)$ and a period $t$,
--   $$\mu^t_{ik}=\sum_{m\in M,\,(i,k)\in m}y^t_m,\qquad y^t_m=\frac{y_m\,p_t(q)}{p_a(q)}\ (m\in M(q)),$$
--   the probability that the method drawn in period $t$ uses the pair $(i,k)$. These are the inputs of the magician $(i,k)$ in Algorithm 2. The companion `mu'` lists $\mu^1_{ik},\mu^2_{ik},\dots$ as a sequence indexed from $0$ and extended by $0$ after the horizon.
--
--   **Formalization Note** When $p_a(q)=0$ the division returns $0$, and then $p_t(q)=0$, so the term is $0$ either way.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), (12), p.15; (10), p.11

import Mathlib
import Definitions.Def_MethodFulfillment_Instance
import Definitions.Def_MethodFulfillment_pa

namespace MethodFulfillment

/-- The consumption probability of pair `(i, k)` at Lean time `t` (Amil, Makhdoumi & Wei,
manuscript, PDF sha256 197c13b9…, (12), p.15, with (10), p.11):
`μ^t_{ik} = ∑_{m ∋ (i,k)} y^t_m` with `y^t_m = y_m p_t(q) / pa(q)`, the probability that the
method drawn at `t` contains `(i, k)`.

**Formalization Note.** When `pa q = 0` the division returns `0`; then `p t q = 0`, so the term
is `0` either way. -/
noncomputable def mu {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ) (t : Fin T) (i : I) (k : K) : ℝ :=
  ∑ q, ∑ m ∈ (P.methods q).filter (fun m => (i, k) ∈ m), y q m * P.p t q / pa P q

/-- The sequence `t ↦ μ^{t+1}_{ik}` extended by `0` after the horizon, the input of the magician
recursion `magF`. -/
noncomputable def mu' {I K Q : Type} [DecidableEq I] [DecidableEq K] [Fintype Q] {T : ℕ}
    (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ) (i : I) (k : K) (t : ℕ) : ℝ :=
  if h : t < T then mu P y ⟨t, h⟩ i k else 0

end MethodFulfillment



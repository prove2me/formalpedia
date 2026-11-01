-- Prove2me | Definitions.Def_ShrinkingUCB_ConsUCB
-- name    : ShrinkingUCB_ConsUCB
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:18:20.744766+00:00
-- url     : https://prove2.me/theorems/5201b637-7493-422e-8280-72cf08e10404
-- title:
--   The ConsUCB algorithm: $A_t$, $b_t$, $\theta_t$, $A_{t,k}$, $p_{t,k}$, $i_{t,k}$, $S_t$
-- statement:
--   **ConsUCB** with input parameter $\alpha$, for a tie-break and $K$ selections per period, is the following procedure on an outcome table.
--
--   Initialize $A_0=I_{d\times d}$ and $b_0=0$. For each period $t=1,2,\dots$:
--
--   1. Set $\theta_t=A_{t-1}^{-1}b_{t-1}$ and $A_{t,0}=A_{t-1}$, and start from the empty selection.
--   2. For $k=1,\dots,K$: compute, for all $i\in[N]$,
--   $$
--   p_{t,k}(i)=x_i^\top\theta_t-\alpha\sqrt{x_i^\top A_{t-1}^{-1}x_i}+2\alpha\sqrt{x_i^\top A_{t,k-1}^{-1}x_i};
--   $$
--   let $i_{t,k}$ be the tie-break's choice in the arg max of $p_{t,k}$ over the products not selected yet in the period, and set $A_{t,k}=A_{t,k-1}+x_{i_{t,k}}x_{i_{t,k}}^\top$.
--   3. Offer the set $S_t$ of the $K$ selected products and observe $r_{t,i}$ for $i\in S_t$.
--   4. Update $A_t=A_{t-1}+\sum_{i\in S_t}x_ix_i^\top$ and $b_t=b_{t-1}+\sum_{i\in S_t}r_{t,i}x_i$.
--
--   The estimate $\theta_t$ is fixed within a period, while the second radical shrinks after each selection. No outcome of period $t$ is read before step 3.
--
--   **Formalization Note** The run is a recursion on a table, so all objects are deterministic functions of the table and become random variables at the table realized at $\omega$. It has no horizon: the objects of period $T+1$ read the outcomes of periods $1,\dots,T$ only. Periods and selections are $1$-based, so the index $t-1$ is used at $t\ge1$ only. $A^{-1}$ is Lean's total matrix inverse; every $A_{t,k}$ dominates the identity, so it is a true inverse.
-- source:
--   Jin, Simchi-Levi, Wang, Wang, Yang, Shrinking the Upper Confidence Bound: A Dynamic Product Selection Problem for Urban Warehouses, arXiv:1903.07844v2, §4.1, p.15

import Definitions.Def_ShrinkingUCB_IsRewardTable
import Definitions.Def_ShrinkingUCB_TieBreak

open Matrix

namespace ShrinkingUCB

variable {d N : ℕ}

/-- What ConsUCB carries from period to period: `A_t`, `b_t` and the observed history. -/
structure RunState (d N : ℕ) where
  /-- The design matrix `A_t`. -/
  A : Matrix (Fin d) (Fin d) ℝ
  /-- The response vector `b_t`. -/
  b : Fin d → ℝ
  /-- The observed history of periods `1, …, t`. -/
  hist : History N

/-- What ConsUCB carries from selection to selection inside a period: `A_{t,k}` and the products
`i_{t,1}, …, i_{t,k}`, in order. -/
structure Selections (d N : ℕ) where
  /-- The matrix `A_{t,k}`. -/
  A : Matrix (Fin d) (Fin d) ℝ
  /-- The products selected so far in the period, in order. -/
  sel : List (Fin N)

/-- The product score of step 2(b)i, p.15, for a period with previous matrix `A_{t-1}` (`Aprev`),
estimate `θ_t` (`θ`) and current matrix `A_{t,k-1}` (`Acur`):
`p_{t,k}(i) = x_iᵀθ_t − α√(x_iᵀA_{t-1}⁻¹x_i) + 2α√(x_iᵀA_{t,k-1}⁻¹x_i)`. -/
noncomputable def score (I : LinearSemiBandit d N) (α : ℝ)
    (Aprev Acur : Matrix (Fin d) (Fin d) ℝ) (θ : Fin d → ℝ) (i : Fin N) : ℝ :=
  I.x i ⬝ᵥ θ - α * √(I.x i ⬝ᵥ Aprev⁻¹ *ᵥ I.x i) + 2 * α * √(I.x i ⬝ᵥ Acur⁻¹ *ᵥ I.x i)

open Classical in
/-- The set `arg max_{i ∈ C} f(i)`. -/
noncomputable def argmaxOn (f : Fin N → ℝ) (C : Finset (Fin N)) : Finset (Fin N) :=
  C.filter fun i => ∀ j ∈ C, f j ≤ f i

/-- Step 2(b)ii, p.15: the next product, chosen by the tie-break from the arg max of the scores
over the products not selected yet in the period. Here `s` is the state after the previous
period and `c` holds the selections so far. Note that the estimate is `A_{t-1}⁻¹b_{t-1}`, fixed
within the period. -/
noncomputable def nextPick (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ)
    (s : RunState d N) (c : Selections d N) : Fin N :=
  tb.choose s.hist c.sel
    (argmaxOn (score I α s.A c.A (s.A⁻¹ *ᵥ s.b)) (Finset.univ \ c.sel.toFinset))

/-- The loop 2(b), p.15: the state after `k` selections of the period that starts from `s`, with
`A_{t,0} = A_{t-1}`, `A_{t,k} = A_{t,k-1} + x_j x_jᵀ` and `j = i_{t,k}`. The loop reads no outcome
of the period. -/
noncomputable def selections (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ)
    (s : RunState d N) : ℕ → Selections d N
  | 0 => ⟨s.A, []⟩
  | k + 1 =>
    let c := selections I tb α s k
    let j := nextPick I tb α s c
    ⟨c.A + vecMulVec (I.x j) (I.x j), c.sel ++ [j]⟩

/-- Steps 2(c)–(d), p.15: the set `S_t` is offered, its outcomes `o_t` are observed, and
`A_t = A_{t-1} + ∑_{i ∈ S_t} x_i x_iᵀ`, `b_t = b_{t-1} + ∑_{i ∈ S_t} r_{t,i} x_i`. -/
noncomputable def closePeriod (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ) (K : ℕ)
    (s : RunState d N) (o_t : Fin N → Bool) : RunState d N :=
  let S := (selections I tb α s K).sel.toFinset
  ⟨s.A + ∑ i ∈ S, vecMulVec (I.x i) (I.x i),
   s.b + ∑ i ∈ S, bit (o_t i) • I.x i,
   s.hist ++ [S.image fun i => (i, o_t i)]⟩

/-- ConsUCB with input parameter `α` and `K` selections per period (arXiv:1903.07844v2, §4.1,
p.15), on the outcome table `o`: the state after `t` periods, from `A_0 = I`, `b_0 = 0`.

**Formalization Note.** The run is a function of the table `o`, so every object below is
deterministic, and it becomes a random variable by evaluating at `tableAt r ω`. The loop has no
horizon: `runState … T` is the state one needs for the objects of period `T + 1`. -/
noncomputable def runState (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ) (K : ℕ)
    (o : OutcomeTable N) : ℕ → RunState d N
  | 0 => ⟨1, 0, []⟩
  | t + 1 => closePeriod I tb α K (runState I tb α K o t) (o (t + 1))

variable (I : LinearSemiBandit d N) (tb : TieBreak N) (α : ℝ) (K : ℕ) (o : OutcomeTable N)

/-- The estimate `θ_t = A_{t-1}⁻¹ b_{t-1}`, step 2(a), for periods `t ≥ 1`. -/
noncomputable def theta (t : ℕ) : Fin d → ℝ :=
  (runState I tb α K o (t - 1)).A⁻¹ *ᵥ (runState I tb α K o (t - 1)).b

/-- The matrix `A_{t,k}` of periods `t ≥ 1`; `A_{t,0} = A_{t-1}`. -/
noncomputable def innerA (t k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (selections I tb α (runState I tb α K o (t - 1)) k).A

/-- The product `i_{t,k}`, the `k`-th selection of period `t`, for `t, k ≥ 1`. -/
noncomputable def pick (t k : ℕ) : Fin N :=
  nextPick I tb α (runState I tb α K o (t - 1))
    (selections I tb α (runState I tb α K o (t - 1)) (k - 1))

/-- The set `S_t` offered in period `t ≥ 1`. -/
noncomputable def offered (t : ℕ) : Finset (Fin N) :=
  (selections I tb α (runState I tb α K o (t - 1)) K).sel.toFinset

/-- The score `p_{t,k}(i)`, step 2(b)i, for `t, k ≥ 1`. -/
noncomputable def scoreAt (t k : ℕ) (i : Fin N) : ℝ :=
  score I α (runState I tb α K o (t - 1)).A (innerA I tb α K o t (k - 1))
    (theta I tb α K o t) i

end ShrinkingUCB



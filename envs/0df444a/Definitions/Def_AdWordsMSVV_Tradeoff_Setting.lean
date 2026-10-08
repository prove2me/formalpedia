-- Prove2me | Definitions.Def_AdWordsMSVV_Tradeoff_Setting
-- name    : AdWordsMSVV_Tradeoff_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T10:29:55.88376+00:00
-- url     : https://prove2.me/theorems/2bcdd1fa-4985-4b0d-876d-4aff1edd555a
-- title:
--   §2–§5, pp. 5–11 — the adwords instance with unit budgets, capped spend, slabs, runs of the discrete tradeoff algorithm, revenue, types, ALG(q) and slab(q)
-- statement:
--   This file fixes the **adwords problem** of Mehta, Saberi, Vazirani and Vazirani (§2) with unit budgets, and the **discrete tradeoff algorithm** of §3.
--
--   There are $N$ bidders $b$ and a sequence of $M$ queries $q_1,\dots,q_M$ arriving online. The instance is the bid matrix $c_{b,t}\in\mathbb R$, the bid of bidder $b$ for the query at position $t$. Every bidder has budget $1$. An **allocation** $\sigma$ sends each query either to one bidder or nowhere.
--
--   1. **Spend.** The money spent by bidder $b$ before position $t$ is
--   $$\mathrm{spend}_\sigma(b,t)=\min\Bigl(1,\sum_{s<t,\ \sigma(s)=b} c_{b,s}\Bigr),$$
--   and $b$ is **alive** at $t$ if $\mathrm{spend}_\sigma(b,t)<1$.
--   2. **Slabs.** The budget is divided into $k$ equal slabs $1,\dots,k$. A spent fraction $s$ lies in slab $\mathrm{slab}_k(s)=\max(1,\lceil ks\rceil)$, i.e. slab $j$ for $s\in((j-1)/k,j/k]$ and slab $1$ for $s=0$.
--   3. **Runs.** Given a tradeoff function $\psi$, an allocation $\sigma$ is a **run of the algorithm** if, at every position $t$: when some bidder is alive, $\sigma(t)$ is an alive bidder $b$ maximizing
--   $$c_{b,t}\,\psi\bigl(\mathrm{slab}_k(\mathrm{spend}_\sigma(b,t))\bigr)$$
--   among the alive bidders (ties broken arbitrarily); when no bidder is alive, the query is unassigned.
--   4. **Revenue.** The revenue of an allocation is $\sum_b \min\bigl(1,\sum_{t:\sigma(t)=b} c_{b,t}\bigr)$: no bidder pays more than its budget.
--   5. **Type of a bidder** (p. 10): the slab of its final spend $\mathrm{spend}_\sigma(b,M)$.
--   6. **ALG(q) and slab(q)** (p. 11): for the query at $t$, the bid $c_{\sigma(t),t}$ of the bidder the run chooses, and the slab $\mathrm{slab}_k(\mathrm{spend}_\sigma(\sigma(t),t))$ of that bidder when the query arrives (both $0$ if the query is unassigned).
--
--   These objects are the model of Theorem 8 and Lemmas 6–7; the offline optimum is not a separate object, since the theorems compare with every allocation.
--
--   **Formalization Note** Bidders are `Fin N` and query positions `Fin M`, zero-based; slabs keep the paper's 1-based numbering. The run is a predicate on the whole allocation: the condition at position $t$ reads only spends computed from positions $<t$, so it is an online rule, and every tie-breaking rule produces a run. A query may stay unassigned only when every budget is exhausted ("each query must be assigned to some bidder", p. 5). ALG(q) is the full bid of the chosen bidder (the quantity the algorithm compares), while the revenue is capped at the budget.
-- source:
--   Mehta, Saberi, Vazirani, Vazirani, AdWords and generalized on-line matching, J. ACM (2007), DOI 10.1145/1284320.1284321, p. 5 (§2), pp. 5–6 (§3, slabs and Discrete Version of the Algorithm), p. 10 (types), p. 11 (Definition of ALG(q), OPT(q), slab(q))

import Mathlib

namespace AdWordsMSVV.Tradeoff

open Finset

variable {N M : ℕ}

/-! The adwords instance of §2 (p. 5) with unit budgets: `bid b t` is the bid c_{b q_t} of bidder
`b : Fin N` for the query at position `t : Fin M` of the arrival sequence q_1 … q_M (zero-based
positions). An allocation is `σ : Fin M → Option (Fin N)`, with `none` meaning "unassigned". -/

/-- Total bids of bidder `b` on the queries at positions `< t` that `σ` assigns to `b`. -/
noncomputable def assignedBefore (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N))
    (b : Fin N) (t : ℕ) : ℝ :=
  ∑ j ∈ univ.filter (fun j : Fin M => (j : ℕ) < t ∧ σ j = some b), bid b j

/-- Money spent by bidder `b` on the queries before position `t`, capped at the unit budget. -/
noncomputable def spend (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) (b : Fin N)
    (t : ℕ) : ℝ :=
  min 1 (assignedBefore bid σ b t)

/-- Bidder `b` still has unspent budget just before position `t`. -/
def Alive (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) (b : Fin N) (t : ℕ) : Prop :=
  spend bid σ b t < 1

/-- The slab (`1, …, k`) containing a spent fraction `s` of the budget: slab `j` for
`s ∈ ((j-1)/k, j/k]`, and slab `1` for `s = 0` (the convention of p. 10). -/
noncomputable def slabOf (k : ℕ) (s : ℝ) : ℕ := max 1 ⌈(k : ℝ) * s⌉₊

/-- `σ` is a run of the discrete algorithm of §3 (p. 6) with tradeoff function `ψ` and `k` slabs:
at every position `t`, if some bidder still has budget then the query goes to a bidder with budget
that maximizes `bid × ψ(slab)` among the bidders with budget (ties broken arbitrarily); the query
is left unassigned only when every bidder's budget is exhausted. -/
def IsRun (ψ : ℕ → ℝ) (k : ℕ) (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) : Prop :=
  ∀ t : Fin M,
    match σ t with
    | none => ∀ b, ¬ Alive bid σ b (t : ℕ)
    | some b => Alive bid σ b (t : ℕ) ∧ ∀ b', Alive bid σ b' (t : ℕ) →
        bid b' t * ψ (slabOf k (spend bid σ b' (t : ℕ))) ≤
          bid b t * ψ (slabOf k (spend bid σ b (t : ℕ)))

/-- Revenue of an allocation: each bidder pays the sum of its assigned bids, up to its unit
budget. -/
noncomputable def revenue (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) : ℝ :=
  ∑ b, min 1 (∑ j ∈ univ.filter (fun j : Fin M => σ j = some b), bid b j)

/-- The type of bidder `b` at the end of the run `σ` (p. 10): the slab of its final spend. -/
noncomputable def typeOf (k : ℕ) (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N))
    (b : Fin N) : ℕ :=
  slabOf k (spend bid σ b M)

/-- ALG(q) (p. 11): the bid of the bidder to whom the run assigns the query at `t`
(`0` if unassigned). -/
noncomputable def algRev (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) (t : Fin M) : ℝ :=
  match σ t with
  | none => 0
  | some b => bid b t

/-- slab(q) (p. 11): the slab from which the run pays for the query at `t`, i.e. the active slab of
the chosen bidder when the query arrives (`0` if unassigned). -/
noncomputable def slabQ (k : ℕ) (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N))
    (t : Fin M) : ℕ :=
  match σ t with
  | none => 0
  | some b => slabOf k (spend bid σ b (t : ℕ))

end AdWordsMSVV.Tradeoff



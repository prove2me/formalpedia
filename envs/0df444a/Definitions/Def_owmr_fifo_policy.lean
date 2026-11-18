-- Prove2me | Definitions.Def_owmr_fifo_policy
-- name    : owmr_fifo_policy
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T00:54:21.421289+00:00
-- url     : https://prove2.me/theorems/a06dadd6-63fe-44f1-aef8-a96d170d92ae
-- title:
--   The deterministic FIFO policy $\pi_{\rm FIFO}$ (Definition 1)
-- statement:
--   For a retailer $i$ with $K_i>0$, let $(\hat s_i,\hat S_i)$ be a canonical optimum of its single-location problem with planning setup cost $5K_i/3$ and lead time $L_i$ (cost $F_i$, demand $D_i$), and let $(s_i',S_i')$ be a best half window of $[\hat s_i,\hat S_i]$. The **deterministic FIFO policy** $\pi_{\rm FIFO}$ follows three rules.
--
--   1. *Retailer policies.* Retailer $i$ uses whichever of $(\hat s_i,\hat S_i)$ and $(s_i',S_i')$ has the smaller augmented cost if $K_i>0$, and base stock at a minimizer of $F_i$ if $K_i=0$. Its fixed mirror center $a_i$ is a mirror center of the selected policy, and the base-stock level if $K_i=0$.
--   2. *Requests and dispatch.* Retailer $i$ applies its policy, in each period after the scheduled receipts, to its inventory position including outstanding requests, $\widehat P_{i,t}=P_{i,t}+\Delta_{i,t}$. Each positive order joins one FIFO queue of requests; after the supplier order, the warehouse fills requests in queue order from available stock, the last one possibly in part, and sends all portions for retailer $i$ in that period as one dispatch.
--   3. *Supplier orders.* The warehouse orders with an $(s,S)$ policy that attains the supplier value $J_0(K_0+K_{\max})$, applied to the aggregate position $W_t+O_t+\sum_i(P_{i,t}-a_i)$.
--
--   *Initialization* (Appendix B). No orders or dispatches are placed until all prescribed pipelines have arrived, retaining warehouse stock, and then until every retailer position is at most its selected target $\Gamma_i$. In the first period in which this holds, each retailer with $\Gamma_i-P_i>0$ receives one initial request of that size, and the three rules run from that period on.
--
--   The policy is an echelon stock $(s,S)$ policy with FIFO service; Theorem 1 bounds its long-run average cost.
--
--   **Formalization Note** The choices in the definition (the canonical optimum, the best half window, the selected pair, the mirror centers $a_i$, and the supplier pair) are parameters `c : FIFOChoice n`, constrained by `IsFIFOChoice N c`; when the two candidates tie, either may be selected. Simultaneous requests join the queue in increasing retailer index, a fixed tie-breaking rule (retailer labels are arbitrary). With $T_{\rm pipe}=\max(L_0,\max_iL_i)$, the policy starts in the first period $t$ with $T_{\rm pipe}\le t+1$ in which, after the receipts, every retailer net inventory (its position, as nothing is in transit) is at most its target. The policy is a deterministic function of the initial state and the past demands.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 3, Definition 1 and the two paragraphs before it (pp. 7-8), and the initialization in Appendix B, Step 1 of the proof of Proposition 2 (p. E.4).

import Definitions.Def_owmr_queue_engine

/-!
# The deterministic FIFO policy `π_FIFO` (Definition 1)

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems", Section 3, Definition 1, the paragraphs before it, and the
initialization in Appendix B (Step 1 of the proof of Proposition 2).

The definition involves choices (an optimal `(s,S)` pair satisfying the canonical conditions,
a minimizing half window, a mirror center, an optimal supplier `(s,S)` pair, and tie-breaking).
They are collected in `FIFOChoice`; `IsFIFOChoice` states the properties Definition 1 requires of
them. Simultaneous requests join the queue in increasing retailer index (a fixed tie-breaking
rule; retailer labels are arbitrary).

Initialization (Appendix B, Step 1): no orders or dispatches are placed until all prescribed
pipelines have arrived (the last can arrive in period `Tpipe - 1`, where
`Tpipe = max(L₀, max_i L_i)`), retaining warehouse stock, and then until every retailer position
`P_i` (= net inventory, as nothing is in transit) is at most its selected target `Γ_i = S_i`.
In the first period `t` with `Tpipe ≤ t + 1` in which, after the receipts, every `P_i ≤ Γ_i`,
the policy starts: each retailer with `Γ_i - P_i > 0` gets one initial request of that size,
after which the supplier rule and the queue run as in Definition 1 from that period on.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

variable {n : ℕ}

/-- The choices made in Definition 1: retailer `(s_i, S_i)` (base stock when `s_i = S_i`), mirror
centers `a_i`, and the supplier `(s₀, S₀)`. -/
structure FIFOChoice (n : ℕ) where
  s : Fin n → ℝ
  S : Fin n → ℝ
  a : Fin n → ℝ
  s0 : ℝ
  S0 : ℝ

/-- The requirements of Definition 1 on the choices.
* (i) If `K_i > 0`: for some optimal `(ŝ_i, Ŝ_i)` satisfying the canonical conditions for the
  single-location problem of retailer `i` with planning setup cost `5K_i/3` and lead time `L_i`,
  and some half window `(s'_i, S'_i)` of `[ŝ_i, Ŝ_i]` with the smallest average holding and
  backlog cost, retailer `i` uses whichever of the two has the smaller augmented cost (either one
  in case of a tie), and `a_i` is a mirror center of the selected policy. If `K_i = 0`: base
  stock (`s_i = S_i`) at a minimizer of `F_i`, with `a_i = S_i`.
* (iii) The supplier `(s₀, S₀)` policy attains the supplier value `J₀(K₀ + K_max)`. -/
def IsFIFOChoice (N : Network n) (c : FIFOChoice n) : Prop :=
  (∀ i, 0 < N.K i →
    ∃ sh Sh s' S' : ℝ,
      IsCanonicalOptimum (N.marginal i) (N.F i) (5 * N.K i / 3) sh Sh ∧
      IsBestHalfWindow (N.marginal i) (N.F i) sh Sh s' S' ∧
      ((c.s i = sh ∧ c.S i = Sh ∧ N.augCost i sh Sh ≤ N.augCost i s' S') ∨
        (c.s i = s' ∧ c.S i = S' ∧ N.augCost i s' S' ≤ N.augCost i sh Sh)) ∧
      mirrorAvg (N.marginal i) N.h N.p (c.s i) (c.S i) (c.a i)
        = mirrorCost (N.marginal i) N.h N.p (c.s i) (c.S i)) ∧
  (∀ i, N.K i = 0 → c.s i = c.S i ∧ (∀ y, N.F i (c.S i) ≤ N.F i y) ∧ c.a i = c.S i) ∧
  c.s0 ≤ c.S0 ∧
  ssAvgCost N.aggregate N.fL0 (N.K0 + N.Kmax) c.s0 c.S0 = N.J0 (N.K0 + N.Kmax)

/-- The queue parameters of `π_FIFO`: every allocation ships at once, and the supplier position
uses the mirror centers `a_i`. -/
def FIFOChoice.params (c : FIFOChoice n) : EngParams n where
  s := c.s
  S := c.S
  center := c.a
  batch := fun _ => false
  s0 := c.s0
  S0 := c.S0

/-- One period of `π_FIFO` (including the initialization): returns the state before demand, the
supplier order, and the dispatches. -/
def fifoStep (N : Network n) (c : FIFOChoice n) (t : ℕ) (st0 : EngState n) :
    EngState n × ℝ × (Fin n → ℝ) :=
  let st := receive st0 t
  if st.running then runStep N.L0 N.L c.params (fun _ _ _ _ _ => 0) t st
  else if N.Tpipe ≤ t + 1 ∧ ∀ i, st.I i ≤ c.S i then
    runStep N.L0 N.L c.params (fun _ _ _ _ _ => 0) t
      (startWith st t (fun i => c.S i - st.I i) (fun _ => 0))
  else (st, 0, 0)

/-- The state of `π_FIFO` at the start of period `t` along the demand sequence `d`. -/
def fifoRun (N : Network n) (x : InitState n) (c : FIFOChoice n) (d : ℕ → DemandVec n) :
    ℕ → EngState n
  | 0 => initEngState N x
  | t + 1 => applyDemand (fifoStep N c t (fifoRun N x c d t)).1 (d t)

/-- The deterministic FIFO policy `π_FIFO` of Definition 1, from the initial state `x`. -/
def fifoPolicy (N : Network n) (x : InitState n) (c : FIFOChoice n) : DetPolicy n where
  order t d := (fifoStep N c t (fifoRun N x c d t)).2.1
  dispatch t d := (fifoStep N c t (fifoRun N x c d t)).2.2

end OWMR



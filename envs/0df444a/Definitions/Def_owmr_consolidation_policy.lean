-- Prove2me | Definitions.Def_owmr_consolidation_policy
-- name    : owmr_consolidation_policy
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T00:54:46.737722+00:00
-- url     : https://prove2.me/theorems/98121be3-a2cf-4c08-a78a-cb7c52306c50
-- title:
--   The deterministic consolidation policy $\pi^{(m)}_{\rm con}$ (Definition 2)
-- statement:
--   Fix $m\ge1$ and define, as in (33),
--
--   $$\bar\gamma_m=\frac{13}{3}+\frac{32}{57m},\quad g_m=\frac{\bar\gamma_m}2,\quad\zeta_m=\frac{g_m}{g_m-1},\quad B_m=2(g_m-1),\quad u_m=\frac{3\zeta_m(1+1/m)}{4(4+\zeta_m/m)}.$$
--
--   Retailer $i$ plans at setup cost $k_i=\zeta_mK_i$; write $G_i=J_i(k_i)$ and $\Lambda_i=\min_xF_i(x)$. If $K_i>0$, let $\hat w_i=\hat S_i-\hat s_i$ be the width of a canonical optimum at setup cost $k_i$, and $u_i=k_i/[G_iM_i(\hat w_i)]$ its setup-cost share. The **consolidation policy** $\pi^{(m)}_{\rm con}$ follows four rules.
--
--   1. *Retailer policies.* Retailer $i$ uses base stock at a minimizer of $F_i$ if $\Lambda_i+K_i\le B_mG_i$ (an **immediate** retailer). Otherwise it is a **batch** retailer and uses the best half window of $[\hat s_i,\hat S_i]$ if $u_i\le u_m$, and the full window $[\hat s_i,\hat S_i]$ otherwise.
--   2. *Requests and allocation.* Retailer $i$ applies its policy to $\widehat P_{i,t}=P_{i,t}+\Delta_{i,t}+R_{i,t}$. Requests join one FIFO queue, and after the supplier order the warehouse allocates its unallocated stock to requests in queue order, the last one possibly in part.
--   3. *Dispatch.* Allocations to immediate retailers are dispatched at once. A request of a batch retailer, of size $Q$, receives at creation an offset $\vartheta\in(0,1)$ and ships its entire reserve in each period in which its cumulative allocation rises to or past $3Q\vartheta/4$, or past $3Q(1+\vartheta)/4$ when $\vartheta<1/3$, or reaches $Q$.
--   4. *Supplier orders.* If $K_0>0$, the warehouse uses $(\hat s_0+a_0,\hat S_0+a_0)$, where $(\hat s_0,\hat S_0)$ is a canonical optimum attaining $J_0(g_mK_0)$ and $a_0=(-\hat s_0)^+$; if $K_0=0$, base stock at a nonnegative minimizer of $f_{L_0}$. It applies this policy to $W_t+O_t+\sum_i(P_{i,t}-\Gamma_i)$, with $\Gamma_i$ the selected targets.
--
--   *Offsets* (Appendix C.7). Ordinary requests are indexed $j=1,2,\dots$ in creation order. For request $j$ of a batch retailer $i$, of size $Q_j$, created in period $\tau_j$, the credited full-lifetime proxy (C.29) is
--
--   $$\mathcal Z_j(\vartheta)=K_i[1+N_j(\vartheta)]+(h+p)\sum_{t=\tau_j}^{\tau_j+L_0}(R_{j,t}(\vartheta)-X_t)^+,$$
--
--   where $N_j(\vartheta)$ is the number of interior thresholds, $R_{j,t}(\vartheta)$ the stock allocated to request $j$ and retained at the warehouse in period $t$, and $X_t=\sum_i(\Gamma_i-\widehat P_{i,t})$ the total ideal depletion. With $z_j(\vartheta)$ its average over the fresh demand vectors of periods $\tau_j,\dots,\tau_j+L_0-1$ given the state at creation, and $\bar z_j=\int_0^1z_j(\vartheta)\,d\vartheta$, the offset is the first rational $\vartheta$ in a fixed enumeration of $\mathbb Q\cap(0,1)$ with $z_j(\vartheta)<\bar z_j+2^{-j}$ (Lemma C.7).
--
--   *Initialization* (Appendix C.8). Prescribed pipelines arrive without new orders, the remaining warehouse stock is sent to a fixed retailer, and no further action is taken until it is received and every retailer net inventory $I_i$ is at most $\Gamma_i$. Then retailer $i$ receives an initial request of size $\Gamma_i-I_i$ (if positive), initial requests of batch retailers get fixed offsets, and the four rules run, so the first supplier order raises the supplier position to its shifted target.
--
--   Theorem 2 bounds the long-run average cost of this policy for arbitrary nonnegative setup costs.
--
--   **Formalization Note** The choices (canonical optima, best half windows, minimizers, the supplier pair, the fixed retailer, the fixed initial offsets in $(0,1)$, and the enumeration) are parameters `c : ConChoice n`, constrained by `IsConChoice N m c`; $G_i$ and $u_i$ are compared in $[0,\infty]$. Simultaneous requests are queued and indexed in increasing retailer index. With $T_{\rm pipe}=\max(L_0,\max_iL_i)$, the stock is sent in period $T_{\rm pipe}-1$ (period $0$ if $T_{\rm pipe}=0$), after its receipts, and the policy starts in the first later period, no earlier than the arrival of that shipment, in which every $I_i\le\Gamma_i$ after the receipts. The averages $z_j$ are computed by simulating the ideal dynamics (supplier orders, requests, and allocations, which do not depend on offsets) over the next $L_0$ periods; the value $1/2$ used when no rational satisfies the inequality is a formal default that Lemma C.7 shows is never used. $\bar z_j$ is a Lebesgue integral over $(0,1)$ in $[0,\infty]$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 6, equation (33) and Definition 2 (p. 27), Appendix C.2 (pp. E.10-E.12), Appendix C.7 with equation (C.29) and Lemma C.7 (p. E.20), and Appendix C.8 (p. E.21).

import Definitions.Def_owmr_queue_engine

/-!
# The deterministic consolidation policy `π_con^{(m)}` (Definition 2)

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems", Section 6 (equation (33) and Definition 2), Appendix C.2
(policy and allocation), Appendix C.7 (deterministic offset selection, Lemma C.7 and the
credited full-lifetime proxy (C.29)), and Appendix C.8 (initialization).

The definition involves choices (canonical optima, minimizing half windows, minimizers, a fixed
retailer for the initialization, fixed offsets of the initial requests, and an enumeration of
the rationals in `(0,1)`). They are collected in `ConChoice`; `IsConChoice` states the properties
Definition 2 requires of them. Simultaneous requests join the queue, and are indexed, in
increasing retailer index (a fixed tie-breaking rule; retailer labels are arbitrary).

Initialization (Appendix C.8): no orders or dispatches until all prescribed pipelines have
arrived (the last can arrive in period `Tpipe - 1`, where `Tpipe = max(L₀, max_i L_i)`; with
truncated subtraction, `Tpipe - 1 = 0` if `Tpipe = 0`); in period `Tpipe - 1`, after its
receipts, the whole warehouse stock is sent to the fixed retailer `sendTo`; no further action
until that shipment has arrived and every retailer net inventory is at most its selected target
`Γ_i = S_i` (checked after the receipts of each period `t > Tpipe - 1`). In the first such period
the policy starts: retailer `i` gets an initial request of size `Γ_i - I_i`
(if positive), the initial requests of batch retailers get the fixed offsets, and the supplier
rule and the queue then run as in Definition 2 (its first order raises the supplier position to
the shifted target).

Offsets of ordinary requests of batch retailers (Appendix C.7): ordinary requests are indexed
`j = 1, 2, …` in creation order. For request `j` (retailer `i`, size `Q_j`, created in period
`τ_j`) and an offset `ϑ`, the credited full-lifetime proxy is
`𝒵_j(ϑ) = K_i (1 + N_j(ϑ)) + (h + p) ∑_{t=τ_j}^{τ_j+L₀} (R_{j,t}(ϑ) - X_t)⁺`, where `N_j(ϑ)` is
the number of interior thresholds (`2` if `ϑ < 1/3`, else `1`), `R_{j,t}(ϑ)` the stock allocated
to request `j` and retained at the warehouse in period `t`, and `X_t` the total ideal depletion
`∑_i (Γ_i - P̂_{i,t})`. It depends on the ideal state at creation and on the fresh demand vectors
of periods `τ_j, …, τ_j + L₀ - 1`. With `z_j(ϑ)` its conditional expectation given the state at
creation and `z̄_j = ∫_0^1 z_j(ϑ) dϑ`, the offset is the first rational `ϑ` in the enumeration with
`z_j(ϑ) < z̄_j + 2^{-j}`.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

variable {n : ℕ}

/-- `γ̄_m = 13/3 + 32/(57m)` from (33). -/
def conGammaBar (m : ℝ) : ℝ := 13 / 3 + 32 / (57 * m)

/-- `g_m = γ̄_m / 2` from (33). -/
def conG (m : ℝ) : ℝ := conGammaBar m / 2

/-- `ζ_m = g_m / (g_m - 1)` from (33). -/
def conZeta (m : ℝ) : ℝ := conG m / (conG m - 1)

/-- `B_m = 2 (g_m - 1)` from (33). -/
def conB (m : ℝ) : ℝ := 2 * (conG m - 1)

/-- `u_m = 3 ζ_m (1 + 1/m) / (4 (4 + ζ_m/m))` from (33). -/
def conU (m : ℝ) : ℝ := 3 * conZeta m * (1 + 1 / m) / (4 * (4 + conZeta m / m))

/-- The choices made in Definition 2: retailer `(s_i, S_i)` (base stock when `s_i = S_i`) and
batch flags, the supplier `(s₀, S₀)`, the fixed retailer that receives the initial warehouse
stock, the fixed offsets of initial requests, and the enumeration of `ℚ ∩ (0,1)`. -/
structure ConChoice (n : ℕ) where
  s : Fin n → ℝ
  S : Fin n → ℝ
  batch : Fin n → Bool
  s0 : ℝ
  S0 : ℝ
  sendTo : Fin n
  initOffset : Fin n → ℝ
  enum : ℕ ≃ {q : ℚ // 0 < q ∧ q < 1}

/-- The requirements of Definition 2 (with `k_i = ζ_m K_i`, `G_i = J_i(k_i)`,
`Λ_i = min_x F_i(x)`):
* (i) if `Λ_i + K_i ≤ B_m G_i`, retailer `i` is a non-batch (immediate) retailer using base stock
  at a minimizer of `F_i`; otherwise it is a batch retailer and, for a canonical optimum
  `(ŝ_i, Ŝ_i)` at setup cost `k_i` with width `ŵ_i` and setup share
  `u_i = k_i / (G_i M_i(ŵ_i))`, it uses a minimizing half window of `[ŝ_i, Ŝ_i]` if `u_i ≤ u_m`
  and `(ŝ_i, Ŝ_i)` otherwise;
* (iv) if `K₀ > 0`, the supplier uses `(ŝ₀ + a₀, Ŝ₀ + a₀)` for a canonical optimum `(ŝ₀, Ŝ₀)`
  attaining `J₀(g_m K₀)`, with `a₀ = (-ŝ₀)⁺`; if `K₀ = 0`, base stock at a nonnegative minimizer
  of `f_{L₀}`;
* the fixed offsets of initial requests lie in `(0,1)`. -/
def IsConChoice (N : Network n) (m : ℝ) (c : ConChoice n) : Prop :=
  (∀ i,
    (ENNReal.ofReal ((⨅ y, N.F i y) + N.K i)
        ≤ ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i) →
      c.batch i = false ∧ c.s i = c.S i ∧ ∀ y, N.F i (c.S i) ≤ N.F i y) ∧
    (ENNReal.ofReal (conB m) * N.J i (conZeta m * N.K i)
        < ENNReal.ofReal ((⨅ y, N.F i y) + N.K i) →
      c.batch i = true ∧ ∃ sh Sh : ℝ,
        IsCanonicalOptimum (N.marginal i) (N.F i) (conZeta m * N.K i) sh Sh ∧
        (ENNReal.ofReal (conZeta m * N.K i)
              / (N.J i (conZeta m * N.K i) * renewalM (N.marginal i) (Sh - sh))
            ≤ ENNReal.ofReal (conU m) →
          IsBestHalfWindow (N.marginal i) (N.F i) sh Sh (c.s i) (c.S i)) ∧
        (ENNReal.ofReal (conU m)
            < ENNReal.ofReal (conZeta m * N.K i)
              / (N.J i (conZeta m * N.K i) * renewalM (N.marginal i) (Sh - sh)) →
          c.s i = sh ∧ c.S i = Sh))) ∧
  (0 < N.K0 → ∃ sh Sh : ℝ, IsCanonicalOptimum N.aggregate N.fL0 (conG m * N.K0) sh Sh ∧
    c.s0 = sh + max (-sh) 0 ∧ c.S0 = Sh + max (-sh) 0) ∧
  (N.K0 = 0 → c.s0 = c.S0 ∧ 0 ≤ c.S0 ∧ ∀ y, N.fL0 c.S0 ≤ N.fL0 y) ∧
  (∀ i, 0 < c.initOffset i ∧ c.initOffset i < 1)

/-- The queue parameters of `π_con`: centers `Γ_i = S_i` in the supplier position. -/
def ConChoice.params (c : ConChoice n) : EngParams n where
  s := c.s
  S := c.S
  center := c.S
  batch := c.batch
  s0 := c.s0
  S0 := c.S0

/-! ## Deterministic offset selection (Appendix C.7) -/

/-- Ideal forward simulation from a state `σ` at creation in period `t0` (after the requests and
the supplier order of `t0`), with demand vectors `ds k` in periods `t0 + k`: the state after the
requests and supplier order of period `t0 + k`. Every allocation ships at once here, which does
not change the ideal quantities (positions including outstanding requests, supplier position,
allocations). -/
def idealA (N : Network n) (P : EngParams n) (σ : EngState n) (t0 : ℕ) (ds : ℕ → DemandVec n) :
    ℕ → EngState n
  | 0 => σ
  | k + 1 =>
    (phaseA N.L0 N.L { P with batch := fun _ => false } (fun _ _ _ _ _ => 0) (t0 + k + 1)
      (receive (applyDemand (phaseB N.L { P with batch := fun _ => false } (t0 + k)
        (idealA N P σ t0 ds k)).1 (ds k)) (t0 + k + 1))).1

/-- Cumulative allocation of the request created by retailer `i` in period `t0`, of size `Q`,
after the allocation of period `t0 + k` along the ideal simulation (it is `Q` once the request
has left the queue). -/
def idealAlloc (N : Network n) (P : EngParams n) (σ : EngState n) (t0 : ℕ) (i : Fin n) (Q : ℝ)
    (ds : ℕ → DemandVec n) (k : ℕ) : ℝ :=
  match ((phaseB N.L { P with batch := fun _ => false } (t0 + k)
      (idealA N P σ t0 ds k)).1.queue.find? (fun r => r.born = t0 ∧ r.ret = i)) with
  | some r => r.alloc
  | none => Q

/-- Total ideal depletion `X_{t0+k} = ∑_i (Γ_i - P̂_{i,t0+k})` after the requests of period
`t0 + k`. -/
def idealDepletion (N : Network n) (P : EngParams n) (σ : EngState n) (t0 : ℕ)
    (ds : ℕ → DemandVec n) (k : ℕ) : ℝ :=
  ∑ i, (P.S i - phat N.L (idealA N P σ t0 ds k) (t0 + k) i)

/-- Quantity of a batch request (size `Q`, offset `ϑ`) shipped by the end of period `t0 + k`,
along the allocation path `A k` (cumulative allocation after the allocation of period `t0 + k`;
the allocation before creation is `0`). -/
def shippedPath (Q θ : ℝ) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => if crossesThreshold Q θ 0 (A 0) then A 0 else 0
  | k + 1 => if crossesThreshold Q θ (A k) (A (k + 1)) then A (k + 1) else shippedPath Q θ A k

/-- The credited full-lifetime proxy (C.29) of request `j` (retailer `i`, size `Q`, created in
period `t0` with state `σ`) for offset `ϑ`, given the demand vectors `ds` of periods
`t0, …, t0 + L₀ - 1`. -/
def proxy (N : Network n) (P : EngParams n) (σ : EngState n) (t0 : ℕ) (i : Fin n) (Q θ : ℝ)
    (ds : ℕ → DemandVec n) : ℝ :=
  N.K i * (1 + if θ < 1 / 3 then 2 else 1)
    + (N.h + N.p) * ∑ k ∈ Finset.range (N.L0 + 1),
      max (idealAlloc N P σ t0 i Q ds k - shippedPath Q θ (idealAlloc N P σ t0 i Q ds) k
        - idealDepletion N P σ t0 ds k) 0

/-- `z_j(ϑ)`: the proxy averaged over the fresh demand vectors of periods
`t0, …, t0 + L₀ - 1`. -/
def proxyMean (N : Network n) (P : EngParams n) (σ : EngState n) (t0 : ℕ) (i : Fin n)
    (Q θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ ds, ENNReal.ofReal (proxy N P σ t0 i Q θ (padHist N.L0 ds))
    ∂(Measure.pi fun _ : Fin N.L0 => N.μ)

open Classical in
/-- The deterministic offset rule of Lemma C.7: the first rational `ϑ ∈ (0,1)` in the enumeration
with `z_j(ϑ) < z̄_j + 2^{-j}`, where `z̄_j = ∫_0^1 z_j(ϑ) dϑ`. (Lemma C.7 shows such a `ϑ` exists;
the value `1/2` is only a formal default.) -/
def conRule (N : Network n) (c : ConChoice n) : OffsetRule n := fun σ t0 j i Q =>
  let z : ℝ → ℝ≥0∞ := fun θ => proxyMean N c.params σ t0 i Q θ
  let zbar : ℝ≥0∞ := ∫⁻ θ in Set.Ioo (0 : ℝ) 1, z θ
  if h : ∃ k : ℕ, z ((c.enum k : ℚ) : ℝ) < zbar + (2 : ℝ≥0∞)⁻¹ ^ j then
    ((c.enum (Nat.find h) : ℚ) : ℝ)
  else 1 / 2

/-! ## The policy -/

/-- One period of `π_con` (including the initialization): returns the state before demand, the
supplier order, and the dispatches. -/
def conStep (N : Network n) (c : ConChoice n) (t : ℕ) (st0 : EngState n) :
    EngState n × ℝ × (Fin n → ℝ) :=
  let st := receive st0 t
  if st.running then runStep N.L0 N.L c.params (conRule N c) t st
  else if t = N.Tpipe - 1 then
    (sendOut N.L t (Pi.single c.sendTo st.Wbar) { st with Wbar := 0 }, 0,
      Pi.single c.sendTo st.Wbar)
  else if N.Tpipe - 1 < t ∧ N.Tpipe - 1 + N.L c.sendTo ≤ t ∧ ∀ i, st.I i ≤ c.S i then
    runStep N.L0 N.L c.params (conRule N c) t
      (startWith st t (fun i => c.S i - st.I i) c.initOffset)
  else (st, 0, 0)

/-- The state of `π_con` at the start of period `t` along the demand sequence `d`. -/
def conRun (N : Network n) (x : InitState n) (c : ConChoice n) (d : ℕ → DemandVec n) :
    ℕ → EngState n
  | 0 => initEngState N x
  | t + 1 => applyDemand (conStep N c t (conRun N x c d t)).1 (d t)

/-- The deterministic consolidation policy `π_con^{(m)}` of Definition 2 (the dependence on `m`
is through the choices `c`, constrained by `IsConChoice N m c`), from the initial state `x`. -/
def conPolicy (N : Network n) (x : InitState n) (c : ConChoice n) : DetPolicy n where
  order t d := (conStep N c t (conRun N x c d t)).2.1
  dispatch t d := (conStep N c t (conRun N x c d t)).2.2

end OWMR



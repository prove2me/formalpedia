-- Prove2me | Definitions.Def_GOLiQ_CycleSystem
-- name    : GOLiQ_CycleSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:51:26.017775+00:00
-- url     : https://prove2.me/theorems/0e4b05de-ee9f-401d-96f5-5744b6e041d8
-- title:
--   The queue operated in cycles under a sequence of policies (§3.3), on one sample path
-- statement:
--   Fix cycle lengths $D_k\ge1$, policies $(\mu_k,p_k)$ for cycles $k\ge1$ and a sample path $(u_j,v_j)$ of the primitives. Customers are numbered $j=0,1,2,\dots$ in order of arrival (FIFO). With $N_0=0$ and $N_k=D_1+\dots+D_k$, customer $j$ with $N_{k-1}<j\le N_k$ is customer $n=j-N_{k-1}$ of cycle $k$, so $W^k_n=W_{N_{k-1}+n}$ and $X^k_n=X_{N_{k-1}+n}$.
--
--   1. Customer $0$ arrives at time $A_0=0$ to an empty system: $W_0=X_0=0$.
--   2. Cycle $m\ge2$ starts at $\sigma_m=A_{N_{m-1}}+W_{N_{m-1}}$, when the last customer of cycle $m-1$ enters service; $\sigma_1=0$. The service time of customer $j-1$ is $S_j=v_j/\mu_k$, $k$ the cycle of customer $j$.
--   3. Customer $j$ pays $\pi_j=p_{c(j-1)}$, where $c(i)$ is the last cycle that started strictly before the arrival of customer $i$ (or $1$): the fee changes to $p_k$ only after the first new arrival of cycle $k$, who still pays $p_{k-1}$.
--   4. $\tau_j=u_j/\lambda(\pi_j)$, $A_j=A_{j-1}+\tau_j$, $W_j=(W_{j-1}+S_j-\tau_j)^+$, $X_j=(X_{j-1}+\tau_j)\mathbf 1\{W_j>0\}$.
--
--   The cycle length is $T_k=\sigma_{k+1}-\sigma_k$, and $Q_k$ (with $Q_1=0$) is the number of customers present when cycle $k$ starts: the customer entering service plus those waiting. The module also defines the cycle-indexed quantities $W^k_n$, $X^k_n$, $S^k_n=V^k_n/\mu_k$, $p^k_n$, $U^k_n$, $V^k_n$, and the random system under a random policy.
--
--   This is the transient queue whose cost defines the regret.
-- source:
--   Chen, Liu, Hong, An Online Learning Approach to Dynamic Pricing and Capacity Sizing in Service Systems, arXiv:2009.02911v3, §3.3, pp.14–17, recursions (6)–(7), Figure 1

import Mathlib
import Definitions.Def_GOLiQ_Model
import Definitions.Def_GOLiQ_Primitives

open scoped Classical

namespace GOLiQ

/-- **The queue operated in cycles under a sequence of policies** (Chen, Liu, Hong,
arXiv:2009.02911v3, §3.3, pp.14–17, recursions (6)–(7) and Figure 1), along one sample path.

Data: the model; deterministic cycle lengths `Dₖ` (`k ≥ 1`); the policy `(µₖ, pₖ)` used in cycle `k`;
and the sample path `uⱼ, vⱼ` (`j ≥ 1`) of the primitives `Uⱼ, Vⱼ`.

**Global customer index.** Customers are numbered `j = 0, 1, 2, …` in order of arrival (= order of
service, FIFO). With `N₀ = 0` and `Nₖ = D₁ + ⋯ + Dₖ`, customer `j ≥ 1` with `Nₖ₋₁ < j ≤ Nₖ` is
"customer `n = j − Nₖ₋₁` of cycle `k`" of the paper, so `Wₙᵏ = W_{Nₖ₋₁+n}`, `Xₙᵏ = X_{Nₖ₋₁+n}`,
`Sₙᵏ = V_{Nₖ₋₁+n}/µₖ` and `pₙᵏ = π_{Nₖ₋₁+n}`; in particular `W₀ᵏ = W_{Nₖ₋₁} = W^{k−1}_{D_{k−1}}`.

**Dynamics.** Customer `0` arrives at time `A₀ = 0` to an empty system: `W₀ = X₀ = 0`. Cycle `m ≥ 2`
starts at `σₘ = A_{N_{m−1}} + W_{N_{m−1}}`, when the `D_{m−1}`-th customer of cycle `m − 1` enters
service; `σ₁ = 0`. For `j ≥ 1`:

* the service time of customer `j − 1` is `Sⱼ = vⱼ/µₖ`, `k` the cycle of customer `j`
  (p.15: "The service time of customer `n − 1` in cycle `k` is `Sₙᵏ = Vₙᵏ/µₖ`");
* customer `j` pays `πⱼ = p_{c(j−1)}`, where `c(i) = max({1} ∪ {m ≥ 2 : σₘ < Aᵢ})` is the cycle in
  progress at the arrival of customer `i`: the fee switches from `p_{k−1}` to `pₖ` only after the
  first new arrival of cycle `k`, who is still charged `p_{k−1}` (p.15);
* `τⱼ = uⱼ/λ(πⱼ)`, `Aⱼ = Aⱼ₋₁ + τⱼ`, `Wⱼ = (Wⱼ₋₁ + Sⱼ − τⱼ)⁺`, `Xⱼ = (Xⱼ₋₁ + τⱼ)·1{Wⱼ > 0}`.

The length of cycle `k` is `Tₖ = σₖ₊₁ − σₖ`, and the leftover `Qₖ` is the number of customers present
at the start of cycle `k` (customer `0` of the cycle, who just entered service, plus the `Qₖ − 1`
customers waiting), with `Q₁ = 0`.

**Formalization Note.** `hist j` is the history of `(Aᵢ, Wᵢ, Xᵢ)` for `i ≤ j`. In `cycleAt` the
search over `m` is restricted to `N_{m−1} < i`; a cycle with `N_{m−1} ≥ i` cannot have started before
`Aᵢ`, since arrival times are nondecreasing and waiting times nonnegative. -/
structure CycleSystem where
  /-- The model (rates, costs, box). -/
  model : Model
  /-- The cycle lengths `Dₖ`. -/
  D : ℕ → ℕ
  /-- The service rate `µₖ` of cycle `k`. -/
  mu : ℕ → ℝ
  /-- The fee `pₖ` of cycle `k`. -/
  price : ℕ → ℝ
  /-- The sample path `uⱼ` of `Uⱼ`. -/
  u : ℕ → ℝ
  /-- The sample path `vⱼ` of `Vⱼ`. -/
  v : ℕ → ℝ

namespace CycleSystem

variable (S : CycleSystem)

/-- `Nₖ = D₁ + ⋯ + Dₖ`, the number of customers that enter service in cycles `1, …, k`. -/
def N (k : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 k, S.D i

/-- The cycle `k` of customer `j ≥ 1`: the least `k ≥ 1` with `j ≤ Nₖ`. -/
noncomputable def cycleOf (j : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ j ≤ S.N k}

/-- `c(i)`: the cycle in progress at the arrival epoch of customer `i`, computed from a history
`h` of `(A, W, X)` valid at indices `≤ i`. -/
noncomputable def cycleAt (h : ℕ → ℝ × ℝ × ℝ) (i : ℕ) : ℕ :=
  max 1 (((Finset.Icc 2 i).filter (fun m => S.N (m - 1) < i ∧
    (h (S.N (m - 1))).1 + (h (S.N (m - 1))).2.1 < (h i).1)).sup id)

/-- The history `i ↦ (Aᵢ, Wᵢ, Xᵢ)` for `i ≤ j`. -/
noncomputable def hist : ℕ → ℕ → ℝ × ℝ × ℝ
  | 0 => fun _ => (0, 0, 0)
  | j + 1 =>
      let τ := S.u (j + 1) / S.model.lam (S.price (S.cycleAt (hist j) j))
      let s := S.v (j + 1) / S.mu (S.cycleOf (j + 1))
      let w := max ((hist j j).2.1 + s - τ) 0
      Function.update (hist j) (j + 1)
        ((hist j j).1 + τ, w, if 0 < w then (hist j j).2.2 + τ else 0)

/-- `Aⱼ`, the arrival epoch of customer `j`. -/
noncomputable def arrival (j : ℕ) : ℝ := (S.hist j j).1

/-- `Wⱼ`, the waiting time of customer `j`. -/
noncomputable def wait (j : ℕ) : ℝ := (S.hist j j).2.1

/-- `Xⱼ`, the busy time observed by customer `j`. -/
noncomputable def busy (j : ℕ) : ℝ := (S.hist j j).2.2

/-- `πⱼ = p_{c(j−1)}`, the fee paid by customer `j ≥ 1`. -/
noncomputable def custPrice (j : ℕ) : ℝ := S.price (S.cycleAt (S.hist (j - 1)) (j - 1))

/-- `σₘ`, the start epoch of cycle `m` (`σ₁ = 0`). -/
noncomputable def start (m : ℕ) : ℝ :=
  if m ≤ 1 then 0 else S.arrival (S.N (m - 1)) + S.wait (S.N (m - 1))

/-- `Tₖ = σₖ₊₁ − σₖ`, the length of cycle `k`. -/
noncomputable def length (k : ℕ) : ℝ := S.start (k + 1) - S.start k

/-- `Qₖ`, the number of customers present at the start of cycle `k` (`Q₁ = 0`). -/
noncomputable def leftover (k : ℕ) : ℕ∞ :=
  if k ≤ 1 then 0 else 1 + {j : ℕ | S.N (k - 1) < j ∧ S.arrival j < S.start k}.encard

/-- `Wₙᵏ = W_{Nₖ₋₁+n}`. -/
noncomputable def cycleWait (k n : ℕ) : ℝ := S.wait (S.N (k - 1) + n)

/-- `Xₙᵏ = X_{Nₖ₋₁+n}`. -/
noncomputable def cycleBusy (k n : ℕ) : ℝ := S.busy (S.N (k - 1) + n)

/-- `Sₙᵏ = Vₙᵏ/µₖ`. -/
noncomputable def cycleService (k n : ℕ) : ℝ := S.v (S.N (k - 1) + n) / S.mu k

/-- `pₙᵏ`, the fee of customer `n` of cycle `k`. -/
noncomputable def cyclePrice (k n : ℕ) : ℝ := S.custPrice (S.N (k - 1) + n)

/-- `Uₙᵏ = U_{Nₖ₋₁+n}`. -/
def cycleU (k n : ℕ) : ℝ := S.u (S.N (k - 1) + n)

/-- `Vₙᵏ = V_{Nₖ₋₁+n}`. -/
def cycleV (k n : ℕ) : ℝ := S.v (S.N (k - 1) + n)

end CycleSystem

/-- The cycle system on the sample path `ω`, under the (random) policy `xₖ = (µₖ, pₖ)` and cycle
lengths `Dₖ`. -/
noncomputable def Model.system {Ω : Type*} [MeasurableSpace Ω] (M : Model) (Pr : Primitives Ω)
    (D : ℕ → ℕ) (x : ℕ → Ω → Point) (ω : Ω) : CycleSystem :=
  ⟨M, D, fun k => x k ω 0, fun k => x k ω 1, fun j => Pr.U j ω, fun j => Pr.V j ω⟩

end GOLiQ


